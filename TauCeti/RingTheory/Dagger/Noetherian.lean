/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra
public import TauCeti.RingTheory.Dagger.GaussNorm
public import TauCeti.RingTheory.Dagger.Weierstrass
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Monsky–Washnitzer algebras are noetherian

Over a complete ultrametric normed field `K`, the Monsky–Washnitzer algebra `K⟨X⟩†` in finitely
many variables is a noetherian ring.

The proof is the classical induction on the number of variables via Weierstrass theory. Write
`W = K⟨X⟩†` and `W' = K⟨X, Y⟩†`, with `Y = X none`, and regard `W'` as a `W`-algebra through
`washnitzerAlgebra.optionC`. A nonzero ideal `I` of `W'` contains a nonzero series `f`, and a
triangular automorphism of `W'` makes `f` distinguished in `Y` of some degree `s`, with a unit
coefficient in degree `s`. Overconvergent Weierstrass division by `f` shows that `W' ⧸ (f)` is
spanned over `W` by `1, Y, …, Y ^ (s - 1)`, so it is a finite `W`-module. If `W` is noetherian,
`W' ⧸ (f)` is then a noetherian module, hence `I` is finitely generated.

The Weierstrass-division finiteness step is also exposed for any finite map annihilating a
distinguished series with a unit coefficient in the distinguished degree. A Weierstrass polynomial
`ω ∈ K⟨X⟩†[Y]`, monic with coefficients of Gauss norm at most `1`, is such a series, so a finite
map whose kernel contains `ω` is finite over `K⟨X⟩†`. Dagger algebras, the quotients of
Monsky–Washnitzer algebras, are noetherian.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.finite_comp_optionC_of_isDistinguished`: a finite map
  annihilating such a distinguished series is finite over the algebra in one fewer variable.
* `TauCeti.Dagger.washnitzerAlgebra.finite_comp_optionC_of_isMonicOfDegree`: the same for a
  finite map annihilating a Weierstrass polynomial.
* `TauCeti.Dagger.washnitzerAlgebra.isNoetherianRing`: `K⟨X⟩†` is noetherian for finitely many
  variables.
* `TauCeti.Dagger.IsDaggerAlgebra.isNoetherianRing`: dagger algebras are noetherian.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3 (iii) and §1.4 (1).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, Theorem 1 (the same argument for
  Tate algebras).
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W" => washnitzerAlgebra σ K
local notation "W'" => washnitzerAlgebra (Option σ) K
local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- Division makes the polynomials of bounded degree surject onto an algebra in which a
distinguished series vanishes. -/
private theorem finite_comp_optionC_of_surjective {A : Type*}
    [CommRing A] [Algebra K A] {π : W' →ₐ[K] A}
    (hπ : Function.Surjective π) {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate)))
    (hzero : π g = 0) : (π.comp (washnitzerAlgebra.optionC (R := K))).Finite := by
  let : Algebra W A := (π.comp (washnitzerAlgebra.optionC (R := K))).toRingHom.toAlgebra
  let ev : Polynomial W →ₐ[W] A := Polynomial.aeval (π (X (Option σ) K none))
  let φ : Polynomial.degreeLT W s →ₗ[W] A :=
    ev.toLinearMap ∘ₗ (Polynomial.degreeLT W s).subtype
  have hev (r : Polynomial W) : π (polynomialToOption r) = ev r := by
    have h : (π : W' →+* A).comp polynomialToOption = (ev : Polynomial W →+* A) :=
      Polynomial.ringHom_ext (fun a ↦ by simp [ev, RingHom.algebraMap_toAlgebra]) (by simp [ev])
    exact RingHom.congr_fun h r
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨f, rfl⟩ := hπ a
    obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
    have hf : f = q * g + polynomialToOption r :=
      optionSeries_injective (by simpa using hqr.symm)
    refine ⟨⟨r, Polynomial.mem_degreeLT.mpr hr⟩, ?_⟩
    simp [hf, hzero, hev, φ]
  have : Module.Finite W (Polynomial.degreeLT W s) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv W s).symm
  exact Module.Finite.of_surjective φ hφ

/-- A finite map annihilating a distinguished series is already finite over the algebra in
one fewer variable. The distinguished coefficient must be a unit; no reducedness or
surjectivity of the map is required. -/
theorem finite_comp_optionC_of_isDistinguished {A : Type*}
    [CommRing A] [Algebra K A] {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate)))
    {π : W' →ₐ[K] A} (hπ : π.Finite) (hzero : π g = 0) :
    (π.comp (washnitzerAlgebra.optionC (R := K))).Finite := by
  have hsmall : (π.rangeRestrict.comp (washnitzerAlgebra.optionC (R := K))).Finite :=
    finite_comp_optionC_of_surjective π.rangeRestrict_surjective hg hu (Subtype.ext hzero)
  have hval : π.range.val.Finite := by
    apply AlgHom.Finite.of_comp_finite (f := π.rangeRestrict)
    rwa [AlgHom.val_comp_rangeRestrict]
  have hfin := hval.comp hsmall
  rwa [← AlgHom.comp_assoc, AlgHom.val_comp_rangeRestrict] at hfin

/-- A finite map annihilating a Weierstrass polynomial `ω ∈ K⟨X⟩†[Y]`, evaluated at `Y`, is
already finite over `K⟨X⟩†`. Here `ω` is monic of degree `s` and its lower coefficients have
Gauss norm at most `1`; such an `ω` is distinguished of degree `s` in `Y` at unit radius, with
leading coefficient `1`. -/
theorem finite_comp_optionC_of_isMonicOfDegree {A : Type*} [CommRing A] [Algebra K A]
    {ω : Polynomial W} {s : ℕ} (hm : ω.IsMonicOfDegree s) (hle : ∀ k < s, ‖ω.coeff k‖ ≤ 1)
    {π : W' →ₐ[K] A} (hπ : π.Finite) (hzero : π (polynomialToOption ω) = 0) :
    (π.comp (washnitzerAlgebra.optionC (R := K))).Finite := by
  have hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate) := by
    rw [restrictedOptionEquiv_toTate_polynomialToOption]
    exact PowerSeries.isDistinguished_of_isMonicOfDegree one_pos
      ⟨by rw [hm.monic.natDegree_map, hm.natDegree_eq], hm.monic.map _⟩ fun k hk ↦ by
        simpa [Polynomial.coeff_map, norm_toTate] using hle k hk
  have hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate)) := by
    simp [restrictedOptionEquiv_toTate_polynomialToOption, Polynomial.coeff_coe,
      ← hm.natDegree_eq, hm.monic.coeff_natDegree]
  exact finite_comp_optionC_of_isDistinguished hg hu hπ hzero

/-- An ideal of `K⟨X, Y⟩†` containing a series which is distinguished in `Y`, with a unit
coefficient in the distinguished degree, is finitely generated as soon as `K⟨X⟩†` is
noetherian: by Weierstrass division, the quotient by that series is a finite `K⟨X⟩†`-module. -/
private theorem fg_of_isDistinguished_mem [IsNoetherianRing W] {I : Ideal W'} {g : W'}
    (hgI : g ∈ I) {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) : I.FG := by
  let : Algebra W W' := (optionC (σ := σ) (R := K)).toRingHom.toAlgebra
  let J : Ideal W' := Ideal.span {g}
  let π : W' →ₐ[K] W' ⧸ J := Ideal.Quotient.mkₐ K J
  have hgJ : g ∈ J := Ideal.subset_span (Set.mem_singleton g)
  have hz : π g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hgJ
  have hsur : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hfin := finite_comp_optionC_of_surjective (σ := σ) (K := K)
    (A := W' ⧸ J) (π := π) hsur hg hu hz
  have : Module.Finite W (W' ⧸ J) :=
    (RingHom.finite_algebraMap (A := W) (B := W' ⧸ J)).mp hfin
  have : IsNoetherian W' (W' ⧸ J) :=
    isNoetherian_of_tower W (isNoetherian_of_isNoetherianRing_of_finite W (W' ⧸ J))
  refine Submodule.fg_of_fg_map_of_fg_inf_ker J.mkQ (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgI))]
  exact ⟨{g}, by simp [Ideal.span]⟩

/-- If `K⟨X⟩†` is noetherian, so is `K⟨X, Y⟩†`. -/
private theorem isNoetherianRing_option [Finite σ] [IsNoetherianRing W] : IsNoetherianRing W' := by
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun I ↦ ?_
  by_cases hI : I = ⊥
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨f, hfI, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨α, hα, s, hd, hu⟩ := exists_triangularEquiv_isDistinguished_isUnit f hf
  let e : W' ≃+* W' := (triangularEquiv α hα).toRingEquiv
  have h := fg_of_isDistinguished_mem (I := I.map (e : W' →+* W'))
    (Ideal.mem_map_of_mem (e : W' →+* W') hfI) hd hu
  rw [← Ideal.map_of_equiv (I := I) e]
  exact h.map _

omit [CompleteSpace K] in
/-- Renaming the variables along an equivalence preserves noetherianity of `K⟨X⟩†`. -/
private theorem isNoetherianRing_of_equiv {τ : Type*} (e : σ ≃ τ)
    [IsNoetherianRing W] : IsNoetherianRing (washnitzerAlgebra τ K) := by
  exact isNoetherianRing_of_ringEquiv W (renameAlgEquiv (R := K) e).toRingEquiv

omit [CompleteSpace K] in
/-- With no variables, `K⟨X⟩† = K` is noetherian. -/
private theorem isNoetherianRing_of_isEmpty [IsEmpty σ] : IsNoetherianRing W := by
  exact isNoetherianRing_of_surjective K W (algebraMap K W) algebraMap_surjective

/-- **Monsky–Washnitzer algebras are noetherian.** Over a complete ultrametric normed field `K`,
the algebra `K⟨X⟩†` of overconvergent power series in finitely many variables is a noetherian
ring. No characteristic or nontrivial-norm assumption is needed. -/
instance isNoetherianRing [Finite σ] : IsNoetherianRing (washnitzerAlgebra σ K) :=
  Finite.induction_empty_option
    (P := fun σ ↦ ∀ [Finite σ], IsNoetherianRing (washnitzerAlgebra σ K))
    (fun {α β} e h _ ↦
      have : Finite α := .of_equiv β e.symm
      have := h
      isNoetherianRing_of_equiv e)
    isNoetherianRing_of_isEmpty
    (fun {_} _ h _ ↦
      have := h
      isNoetherianRing_option) σ

end TauCeti.Dagger.washnitzerAlgebra

namespace TauCeti.Dagger.IsDaggerAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

include K in
/-- **Dagger algebras are noetherian.** Over a complete ultrametric normed field `K`, every
`K`-dagger algebra is a quotient of a noetherian Monsky–Washnitzer algebra. -/
theorem isNoetherianRing : IsNoetherianRing A := by
  obtain ⟨n, π, hπ⟩ := exists_surjective (K := K) (A := A)
  exact isNoetherianRing_of_surjective _ _ π.toRingHom hπ

end TauCeti.Dagger.IsDaggerAlgebra
