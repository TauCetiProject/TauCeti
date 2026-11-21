/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.LinearAlgebra.Dual.DoubleDual

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.Integer

/-!
# Linear-functional criterion for finite generation over a Noetherian domain

Let `R` be a Noetherian integral domain with fraction field `K` and let `V` be a finite-dimensional
`K`-vector space. An `R`-submodule `N ⊆ V` is finitely generated if and only if its algebraic dual
`Module.Dual R N` separates nonzero elements of `N`, equivalently the canonical evaluation map
`Module.Dual.eval R N` into the double dual is injective ([bosch-guntzer-remmert], §4.1,
Proposition 4).

The forward direction is `TauCeti.Module.Dual.injective_eval_of_finite` (in
`TauCeti.LinearAlgebra.Dual.DoubleDual`), which holds for any finitely generated torsion-free
`R`-module over an integral domain `R` without Noetherianity or an ambient vector space. Conversely,
if `Module.Dual R N` separates points and `V` is finite-dimensional over `K`, any functional
`φ : N →ₗ[R] R` that is nonzero at `x₀ ∈ N` has finitely generated image (as `R` is Noetherian)
while the `K`-span of `ker φ` avoids `x₀` (clearing denominators in `K = Frac(R)`), lowering the
`K`-dimension and concluding by induction.

In particular, the integral closure `C` of a Noetherian domain `R` in a module-finite `K`-algebra
`L` is a finite `R`-module if and only if `Module.Dual.eval R C` is injective.

## Main results

* `Submodule.fg_of_forall_exists_dual_ne_zero`: over a Noetherian domain `R` with fraction field
  `K`, an `R`-submodule of a finite-dimensional `K`-vector space whose `R`-dual separates points is
  finitely generated.
* `Submodule.fg_iff_injective_dual_eval` and `Submodule.finite_iff_injective_dual_eval`: the
  resulting equivalence for submodules.
* `LinearMap.finite_iff_injective_dual_eval_of_injective` and
  `Module.Finite.of_injective_of_forall_exists_dual_ne_zero`: the corresponding statements for an
  `R`-module admitting an injective `R`-linear map into a finite-dimensional `K`-vector space.
* `TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval`: characterization of finiteness of an
  integral closure in a module-finite `K`-algebra.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §4.1, Proposition 4.
-/

public section

section Noetherian

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] (K : Type*) [Field K]
  [Algebra R K] [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V] [FiniteDimensional K V]
include K

private theorem fg_of_finrank_le_aux :
    ∀ (n : ℕ) (P : Submodule R V) (U : Submodule K V),
      Module.finrank K U ≤ n →
      P ≤ U.restrictScalars R →
      (∀ x : P, x ≠ 0 → ∃ φ : Module.Dual R P, φ x ≠ 0) →
      P.FG
  | 0, P, U, hU, hPU, _ => by
    rw [Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU), Submodule.restrictScalars_bot,
      le_bot_iff] at hPU
    exact hPU ▸ Submodule.fg_bot
  | n + 1, P, U, hU, hPU, hsep => by
    by_cases hP0 : P = ⊥
    · exact hP0 ▸ Submodule.fg_bot
    obtain ⟨v₀, hv₀P, hv₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    let x₀ : P := ⟨v₀, hv₀P⟩
    obtain ⟨φ, hφx₀⟩ := hsep x₀ (Subtype.coe_ne_coe.mp hv₀_ne)
    -- Restrict to `ker φ`, viewed inside `V` as `P'`.
    let P' : Submodule R V := Submodule.map P.subtype (LinearMap.ker φ)
    have hP'_le_P : P' ≤ P := Submodule.map_subtype_le P (LinearMap.ker φ)
    let U' : Submodule K V := Submodule.span K (P' : Set V) ⊓ U
    -- `v₀` cannot lie in the `K`-span of `P'`, since clearing denominators would kill `φ x₀`.
    have hv₀_notMem : v₀ ∉ Submodule.span K (P' : Set V) := fun hv₀_span ↦ by
      obtain ⟨m, c, y, hsum⟩ := Submodule.mem_span_set'.mp hv₀_span
      have hy (i : Fin m) : ∃ z : P, φ z = 0 ∧ (z : V) = (y i : V)
          := by simpa [P'] using (y i).property
      choose z hz_ker hz_val using hy
      obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
      choose a ha using hs
      have hsx₀ : (s : R) • x₀ = ∑ i, a i • z i := Subtype.ext <| by
        simp only [SetLike.val_smul, AddSubmonoidClass.coe_finsetSum, x₀]
        rw [← hsum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← smul_assoc, ← hz_val, ← ha i, IsScalarTower.algebraMap_smul K]
      have hkill : (s : R) * φ x₀ = 0 := by
        rw [← smul_eq_mul, ← map_smul, hsx₀, map_sum]
        exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, hz_ker i, smul_zero]
      exact mul_ne_zero (nonZeroDivisors.ne_zero s.property) hφx₀ hkill
    have hU'_lt : U' < U := lt_of_le_not_ge inf_le_right fun hle ↦ hv₀_notMem (hle (hPU hv₀P)).1
    have hP'_fg : P'.FG := fg_of_finrank_le_aux n P' U'
      (Nat.lt_succ_iff.mp ((Submodule.finrank_lt_finrank_of_lt hU'_lt).trans_le hU))
      (fun _ hv ↦ ⟨Submodule.subset_span hv, hPU (hP'_le_P hv)⟩)
      fun z hz ↦
        let ⟨ψ, hψ⟩ := hsep _ ((map_ne_zero_iff _ (Submodule.inclusion_injective hP'_le_P)).mpr hz)
        ⟨ψ.comp (Submodule.inclusion hP'_le_P), hψ⟩
    have hker_fg : (LinearMap.ker φ).FG :=
      Submodule.fg_of_fg_map_injective P.subtype P.injective_subtype hP'_fg
    exact (Submodule.fg_top P).mp <|
      Submodule.fg_of_fg_map_of_fg_inf_ker φ (IsNoetherian.noetherian _) (by simpa using hker_fg)

/-- **Linear-functional finiteness criterion** ([bosch-guntzer-remmert], §4.1, Proposition 4).
Let `R` be a Noetherian domain with fraction field `K` and `V` a finite-dimensional `K`-vector
space. An `R`-submodule `N ⊆ V` whose `R`-linear dual separates nonzero elements is finitely
generated. -/
theorem Submodule.fg_of_forall_exists_dual_ne_zero {N : Submodule R V}
    (hsep : ∀ x : N, x ≠ 0 → ∃ φ : Module.Dual R N, φ x ≠ 0) : N.FG :=
  fg_of_finrank_le_aux K (Module.finrank K (⊤ : Submodule K V)) N ⊤ le_rfl (fun _ _ ↦ trivial) hsep

/-- Over a Noetherian domain `R` with fraction field `K`, an `R`-submodule `N` of a
finite-dimensional `K`-vector space is finitely generated if and only if `Module.Dual.eval R N` is
injective. -/
theorem Submodule.fg_iff_injective_dual_eval {N : Submodule R V} :
    N.FG ↔ Function.Injective (Module.Dual.eval R N) :=
  ⟨fun hN ↦ by
    have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
    have : Module.IsTorsionFree R N := .of_smul_eq_zero fun r x hrx ↦ by
      have h : algebraMap R K r • (x : V) = 0 := by
        rw [algebraMap_smul, ← SetLike.val_smul, hrx, ZeroMemClass.coe_zero]
      exact (smul_eq_zero.mp h).imp (map_eq_zero_iff _ (IsFractionRing.injective R K)).mp
        ZeroMemClass.coe_eq_zero.mp
    exact TauCeti.Module.Dual.injective_eval_of_finite,
  fun h ↦ Submodule.fg_of_forall_exists_dual_ne_zero K
    (TauCeti.Module.Dual.injective_eval_iff.mp h)⟩

/-- Over a Noetherian domain `R` with fraction field `K`, an `R`-submodule `N` of a
finite-dimensional `K`-vector space is a finite `R`-module if and only if `Module.Dual.eval R N` is
injective. -/
theorem Submodule.finite_iff_injective_dual_eval {N : Submodule R V} :
    Module.Finite R N ↔ Function.Injective (Module.Dual.eval R N) := by
  rw [Module.Finite.iff_fg, Submodule.fg_iff_injective_dual_eval K]

/-- For an `R`-module `M` admitting an injective `R`-linear map into a finite-dimensional vector
space over `K = Frac(R)` (`R` a Noetherian domain), `M` is finite over `R` if and only if
`Module.Dual.eval R M` is injective. -/
theorem LinearMap.finite_iff_injective_dual_eval_of_injective {M : Type*} [AddCommGroup M]
    [Module R M] {f : M →ₗ[R] V} (hf : Function.Injective f) :
    Module.Finite R M ↔ Function.Injective (Module.Dual.eval R M) := by
  let e : M ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  rw [Module.Finite.equiv_iff e, Submodule.finite_iff_injective_dual_eval K,
    TauCeti.Module.Dual.injective_eval_iff, TauCeti.Module.Dual.injective_eval_iff]
  exact ⟨fun h x hx ↦ let ⟨φ, hφ⟩ := h (e x) ((map_ne_zero_iff e e.injective).mpr hx)
      ⟨φ.comp e.toLinearMap, hφ⟩,
    fun h y hy ↦ let ⟨φ, hφ⟩ := h (e.symm y) ((map_ne_zero_iff e.symm e.symm.injective).mpr hy)
      ⟨φ.comp e.symm.toLinearMap, hφ⟩⟩

/-- If `M` embeds `R`-linearly into a finite-dimensional vector space over `K = Frac(R)` (`R` a
Noetherian domain) and `Module.Dual R M` separates nonzero points of `M`, then `M` is a finite
`R`-module ([bosch-guntzer-remmert], §4.1, Proposition 4). -/
theorem Module.Finite.of_injective_of_forall_exists_dual_ne_zero {M : Type*} [AddCommGroup M]
    [Module R M] {f : M →ₗ[R] V} (hf : Function.Injective f)
    (hsep : ∀ x : M, x ≠ 0 → ∃ φ : Module.Dual R M, φ x ≠ 0) :
    Module.Finite R M :=
  (f.finite_iff_injective_dual_eval_of_injective K hf).mpr
    (TauCeti.Module.Dual.injective_eval_iff.mpr hsep)

end Noetherian

namespace TauCeti.IsIntegralClosure

/-- Let `R` be a Noetherian domain with fraction field `K`, `L` a module-finite `K`-algebra, and
`C` an integral closure of `R` in `L`. Then `C` is a finite `R`-module if and only if
`Module.Dual.eval R C` is injective. -/
theorem finite_iff_injective_dual_eval (R : Type*) (K : Type*) (L : Type*) (C : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [Module.Finite K L]
    [CommRing C] [Algebra R C] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L] :
    Module.Finite R C ↔ Function.Injective (Module.Dual.eval R C) :=
  (IsScalarTower.toAlgHom R C L).toLinearMap.finite_iff_injective_dual_eval_of_injective K
    (IsIntegralClosure.algebraMap_injective C R L)

end TauCeti.IsIntegralClosure
