/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Linear-functional criterion for finite generation over a Noetherian domain

Let `R` be a Noetherian integral domain with fraction field `K` and let `V` be a finite-dimensional
`K`-vector space. An `R`-submodule `N ⊆ V` is finitely generated if and only if its algebraic dual
`Module.Dual R N` separates nonzero elements of `N`, equivalently the canonical evaluation map
`Module.Dual.eval R N` into the double dual is injective ([bosch-guntzer-remmert], §4.1,
Proposition 4).

The forward direction needs neither Noetherianity of `R` nor finite dimensionality of `V`: clearing
a common denominator of the values of a `K`-linear functional on a finite generating set produces a
separating `R`-linear functional on `N`. Conversely, if `Module.Dual R N` separates points and `V`
is finite-dimensional over `K`, any functional `φ : N →ₗ[R] R` that is nonzero at `x₀ ∈ N` has
finitely generated image (as `R` is Noetherian) while the `K`-span of `ker φ` avoids `x₀` (clearing
denominators in `K = Frac(R)`), lowering the `K`-dimension and concluding by induction.

In particular, the integral closure `C` of a Noetherian domain `R` in a finite extension `L` of
`K` is a finite `R`-module if and only if `Module.Dual.eval R C` is injective.

## Main results

* `Module.Dual.injective_eval_iff`: `Module.Dual.eval R M` is injective if and only if every nonzero
  element of `M` is not killed by some `R`-linear functional.
* `Submodule.injective_dual_eval_of_fg`: over any domain `R` with fraction field `K`, a finitely
  generated `R`-submodule of a `K`-vector space has injective double-dual evaluation.
* `Submodule.fg_of_forall_exists_dual_ne_zero`: over a Noetherian domain `R` with fraction field
  `K`, an `R`-submodule of a finite-dimensional `K`-vector space whose `R`-dual separates points is
  finitely generated.
* `Submodule.fg_iff_injective_dual_eval` and `Submodule.finite_iff_injective_dual_eval`: the
  resulting equivalence for submodules.
* `LinearMap.finite_iff_injective_dual_eval` and
  `Module.Finite.of_injective_of_forall_exists_dual_ne_zero`: the corresponding statements for an
  `R`-module admitting an injective `R`-linear map into a finite-dimensional `K`-vector space.
* `TauCeti.IsIntegralClosure.finite_iff_injective_dual_eval`: characterization of finiteness of an
  integral closure in a finite extension of the fraction field.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §4.1, Proposition 4.
-/

public section

/-- The canonical evaluation map `Module.Dual.eval R M` into the double dual is injective if and
only if `Module.Dual R M` separates nonzero points of `M`. -/
theorem Module.Dual.injective_eval_iff {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] :
    Function.Injective (Module.Dual.eval R M) ↔
      ∀ x : M, x ≠ 0 → ∃ φ : Module.Dual R M, φ x ≠ 0 := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · by_contra! hall
    exact hx (h x (LinearMap.ext hall))
  · by_contra hx0
    obtain ⟨φ, hφ⟩ := h x hx0
    exact hφ (by simpa using LinearMap.congr_fun hx φ)

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V]
include K

/-- Over an integral domain `R` with fraction field `K`, a finitely generated `R`-submodule `N` of
any `K`-vector space `V` has separating `R`-dual: clearing a common denominator of the values of a
`K`-linear functional on a finite generating set yields an `R`-linear functional on `N`. Neither
`IsNoetherianRing R` nor `FiniteDimensional K V` is needed. -/
theorem Submodule.injective_dual_eval_of_fg {N : Submodule R V} (hN : N.FG) :
    Function.Injective (Module.Dual.eval R N) := by
  classical
  rw [Module.Dual.injective_eval_iff]
  obtain ⟨s, hs⟩ := hN
  intro x hx
  have hxV : (x : V) ≠ 0 := Subtype.coe_ne_coe.mpr hx
  have hinjK : Function.Injective (Module.Dual.eval K V) :=
    (Module.Basis.ofVectorSpace K V).eval_injective
  obtain ⟨ψ, hψx⟩ := (Module.Dual.injective_eval_iff.mp hinjK) (x : V) hxV
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun y : s ↦ ψ y.1)
  have hmem : ∀ v ∈ N, (d : R) • ψ v ∈ LinearMap.range (Algebra.linearMap R K) := by
    let W : Submodule R V :=
      (LinearMap.range (Algebra.linearMap R K)).comap ((d : R) • ψ.restrictScalars R)
    suffices N ≤ W from fun v hv ↦ this hv
    rw [← hs, Submodule.span_le]
    intro v hv
    obtain ⟨r, hr⟩ := hd ⟨v, hv⟩
    exact ⟨r, hr⟩
  let φ : Module.Dual R N :=
    (((d : R) • ψ.restrictScalars R).domRestrict N).codRestrictOfInjective
      (Algebra.linearMap R K) (IsFractionRing.injective R K) fun z ↦ hmem z.1 z.2
  refine ⟨φ, fun hφ0 ↦ ?_⟩
  have hmap : algebraMap R K (φ x) = algebraMap R K (d : R) * ψ x := by
    simpa [φ, Algebra.smul_def] using
      LinearMap.codRestrictOfInjective_comp_apply (((d : R) • ψ.restrictScalars R).domRestrict N)
        (Algebra.linearMap R K) (IsFractionRing.injective R K) (fun z : N ↦ hmem z.1 z.2) x
  rw [hφ0, map_zero] at hmap
  exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2) hψx hmap.symm

section Noetherian

variable [IsNoetherianRing R] [FiniteDimensional K V]

private theorem fg_of_finrank_le_aux :
    ∀ (n : ℕ) (P : Submodule R V) (U : Submodule K V),
      Module.finrank K U ≤ n →
      P ≤ U.restrictScalars R →
      (∀ x : P, x ≠ 0 → ∃ φ : Module.Dual R P, φ x ≠ 0) →
      P.FG
  | 0, P, U, hU, hPU, _ => by
    have hU0 : U = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)
    rw [hU0, Submodule.restrictScalars_bot, le_bot_iff] at hPU
    exact hPU ▸ Submodule.fg_bot
  | n + 1, P, U, hU, hPU, hsep => by
    by_cases hP0 : P = ⊥
    · exact hP0 ▸ Submodule.fg_bot
    obtain ⟨v₀, hv₀P, hv₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    let x₀ : P := ⟨v₀, hv₀P⟩
    have hx₀_ne : x₀ ≠ 0 := Subtype.coe_ne_coe.mp hv₀_ne
    obtain ⟨φ, hφx₀⟩ := hsep x₀ hx₀_ne
    -- Restrict to `ker φ`, viewed inside `V` as `P'`.
    let P' : Submodule R V := Submodule.map P.subtype (LinearMap.ker φ)
    have hP'_le_P : P' ≤ P := Submodule.map_subtype_le P (LinearMap.ker φ)
    let U' : Submodule K V := Submodule.span K (P' : Set V) ⊓ U
    -- `v₀` cannot lie in the `K`-span of `P'`, since clearing denominators would kill `φ x₀`.
    have hv₀_notMem : v₀ ∉ Submodule.span K (P' : Set V) := by
      intro hv₀_span
      obtain ⟨m, c, y, hsum⟩ := Submodule.mem_span_set'.mp hv₀_span
      have hy (i : Fin m) : ∃ z : P, φ z = 0 ∧ (z : V) = (y i : V) := by
        simpa [P'] using (y i).2
      choose z hz_ker hz_val using hy
      obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
      choose a ha using hs
      have hsx₀ : (s : R) • x₀ = ∑ i, a i • z i := by
        apply Subtype.ext
        rw [SetLike.val_smul, AddSubmonoidClass.coe_finsetSum]
        calc (s : R) • v₀
            = (s : R) • ∑ i, c i • (y i : V) := by rw [hsum]
          _ = ∑ i, ((s : R) • c i) • (z i : V) := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ ↦ by rw [smul_assoc, hz_val]
          _ = ∑ i, (a i • z i : P).1 := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [← ha i, IsScalarTower.algebraMap_smul K, SetLike.val_smul]
      have hkill : (s : R) * φ x₀ = 0 := by
        calc (s : R) * φ x₀
            = φ ((s : R) • x₀) := by rw [map_smul, smul_eq_mul]
          _ = ∑ i, a i * φ (z i) := by simp [hsx₀]
          _ = 0 := Finset.sum_eq_zero fun i _ ↦ by rw [hz_ker i, mul_zero]
      exact mul_ne_zero (nonZeroDivisors.ne_zero s.2) hφx₀ hkill
    have hU'_lt : U' < U := lt_of_le_not_ge inf_le_right fun hle ↦
      hv₀_notMem ((hle (hPU hv₀P)).1)
    have hfinrank : Module.finrank K U' ≤ n :=
      Nat.lt_succ_iff.mp ((Submodule.finrank_lt_finrank_of_lt hU'_lt).trans_le hU)
    have hP'_le_U' : P' ≤ U'.restrictScalars R := fun v hv ↦
      ⟨Submodule.subset_span hv, hPU (hP'_le_P hv)⟩
    have hP'_sep : ∀ z : P', z ≠ 0 → ∃ ψ : Module.Dual R P', ψ z ≠ 0 := fun z hz ↦ by
      have hzP : Submodule.inclusion hP'_le_P z ≠ 0 :=
        (map_ne_zero_iff _ (Submodule.inclusion_injective hP'_le_P)).mpr hz
      obtain ⟨ψ, hψ⟩ := hsep _ hzP
      exact ⟨ψ.comp (Submodule.inclusion hP'_le_P), hψ⟩
    have hP'_fg : P'.FG := fg_of_finrank_le_aux n P' U' hfinrank hP'_le_U' hP'_sep
    have hker_fg : (LinearMap.ker φ).FG :=
      Submodule.fg_of_fg_map_injective P.subtype P.injective_subtype hP'_fg
    have htop_fg : (⊤ : Submodule R P).FG :=
      Submodule.fg_of_fg_map_of_fg_inf_ker φ (IsNoetherian.noetherian _) (by simpa using hker_fg)
    exact (Submodule.fg_top P).mp htop_fg

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
  ⟨Submodule.injective_dual_eval_of_fg K, fun h ↦
    Submodule.fg_of_forall_exists_dual_ne_zero K (Module.Dual.injective_eval_iff.mp h)⟩

/-- Over a Noetherian domain `R` with fraction field `K`, an `R`-submodule `N` of a
finite-dimensional `K`-vector space is a finite `R`-module if and only if `Module.Dual.eval R N` is
injective. -/
theorem Submodule.finite_iff_injective_dual_eval {N : Submodule R V} :
    Module.Finite R N ↔ Function.Injective (Module.Dual.eval R N) := by
  rw [Module.Finite.iff_fg, Submodule.fg_iff_injective_dual_eval K]

/-- For an `R`-module `M` admitting an injective `R`-linear map into a finite-dimensional vector
space over `K = Frac(R)` (`R` a Noetherian domain), `M` is finite over `R` if and only if
`Module.Dual.eval R M` is injective. -/
theorem LinearMap.finite_iff_injective_dual_eval {M : Type*} [AddCommGroup M] [Module R M]
    {f : M →ₗ[R] V} (hf : Function.Injective f) :
    Module.Finite R M ↔ Function.Injective (Module.Dual.eval R M) := by
  let e : M ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  rw [Module.Finite.equiv_iff e, Submodule.finite_iff_injective_dual_eval K,
    Module.Dual.injective_eval_iff, Module.Dual.injective_eval_iff]
  refine ⟨fun h x hx ↦ ?_, fun h y hy ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := h (e x) ((map_ne_zero_iff e e.injective).mpr hx)
    exact ⟨φ.comp e.toLinearMap, hφ⟩
  · obtain ⟨φ, hφ⟩ := h (e.symm y) ((map_ne_zero_iff e.symm e.symm.injective).mpr hy)
    exact ⟨φ.comp e.symm.toLinearMap, hφ⟩

/-- If `M` embeds `R`-linearly into a finite-dimensional vector space over `K = Frac(R)` (`R` a
Noetherian domain) and `Module.Dual R M` separates nonzero points of `M`, then `M` is a finite
`R`-module ([bosch-guntzer-remmert], §4.1, Proposition 4). -/
theorem Module.Finite.of_injective_of_forall_exists_dual_ne_zero {M : Type*} [AddCommGroup M]
    [Module R M] {f : M →ₗ[R] V} (hf : Function.Injective f)
    (hsep : ∀ x : M, x ≠ 0 → ∃ φ : Module.Dual R M, φ x ≠ 0) :
    Module.Finite R M :=
  (f.finite_iff_injective_dual_eval K hf).mpr (Module.Dual.injective_eval_iff.mpr hsep)

end Noetherian

end Domain

namespace TauCeti.IsIntegralClosure

/-- Let `R` be a Noetherian domain with fraction field `K`, `L / K` a finite extension, and `C` an
integral closure of `R` in `L`. Then `C` is a finite `R`-module if and only if
`Module.Dual.eval R C` is injective. -/
theorem finite_iff_injective_dual_eval (R : Type*) (K : Type*) (L : Type*) (C : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    [CommRing C] [Algebra R C] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L] :
    Module.Finite R C ↔ Function.Injective (Module.Dual.eval R C) :=
  (IsScalarTower.toAlgHom R C L).toLinearMap.finite_iff_injective_dual_eval K
    (IsIntegralClosure.algebraMap_injective C R L)

end TauCeti.IsIntegralClosure
