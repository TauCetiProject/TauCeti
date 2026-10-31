/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.RingTheory.LaurentSeries.Lattice

/-!
# The continuous residue dual of module-valued Laurent series

Let `R` be a commutative ring with the discrete topology and `V` an `R`-module, and give
`V((t)) = HahnModule ℤ R V` its lattice topology, in which the lattices `U_a(V) = tᵃ V⟦t⟧` form a
basis of neighbourhoods of zero. A continuous `R`-linear functional on `V((t))` is then one that
vanishes on some lattice `U_a(V)` (`LinearMap.continuous_iff_exists_hahnModule_lattice_le_ker`).

A series `g ∈ V*((t)) = HahnModule ℤ R (Module.Dual R V)` with coefficients in the dual module
defines the functional

`f ↦ Res(g(f) dt) = ∑ₙ g₋₁₋ₙ(fₙ)`

on `V((t))`, contracting the coefficients of `g` and `f` and taking the residue. Only finitely
many terms of the sum are nonzero, since both supports are bounded below. This file proves that
every continuous `R`-linear functional on `V((t))` arises in this way from a unique `g`. That is,
`V*((t)) dt` is the continuous dual of `V((t))`. The coefficient at `n` of the series
representing a functional `ℓ` is `v ↦ ℓ(v t⁻¹⁻ⁿ)`. Under this identification the functionals
vanishing on `U_a(V)` are exactly the series in `U_(-a)(V*)`. The pairing is compatible with
coefficientwise linear maps `u : V → W` and their transposes `u* : W* → V*`.

No finiteness of `V` is needed. This is the module-valued analogue of
`TauCeti.LaurentSeries.residueDualEquiv`, which treats `K⸨X⸩` over a field with its valuation
topology. The reconstruction of a functional from its values on monomials uses the density of
finite sums of monomials, `TauCeti.HahnModule.continuousLinearMap_ext_single`.

## Main definitions

* `HahnModule.residueDual g`: the continuous functional `f ↦ Res(g(f) dt)` on `V((t))` attached
  to `g ∈ V*((t))`.
* `HahnModule.residueDualEquiv`: the linear equivalence between `V*((t))` and the
  continuous dual of `V((t))`.

## Main results

* `HahnModule.lattice_le_ker_residueDual_iff`: the functional attached to `g` vanishes on
  `U_a(V)` exactly when `g ∈ U_(-a)(V*)`.
* `LinearMap.residueDual_of_map`: compatibility with coefficientwise linear maps.
* `ContinuousLinearMap.coeff_hahnModule_residueDualEquiv_symm`: the coefficients of the series
  representing a continuous functional `ℓ` are `v ↦ ℓ(v t⁻¹⁻ⁿ)`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.
-/

public section

open HahnSeries Topology

namespace HahnModule

open TauCeti.HahnModule

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The contraction-residue sum `∑ₙ g₋₁₋ₙ(fₙ)` has finitely many nonzero terms: the term at `n`
vanishes unless `ord f ≤ n ≤ -1 - ord g`. -/
private theorem hasFiniteSupport_coeff_apply (g : HahnModule ℤ R (Module.Dual R V))
    (f : HahnModule ℤ R V) :
    Function.HasFiniteSupport fun n : ℤ ↦
      ((of R).symm g).coeff (-1 - n) (((of R).symm f).coeff n) := by
  refine (Set.finite_Icc ((of R).symm f).order (-1 - ((of R).symm g).order)).subset fun n hn ↦ ?_
  rw [Function.mem_support] at hn
  have hf : ((of R).symm f).coeff n ≠ 0 := fun h ↦ hn (by rw [h, map_zero])
  have hg : ((of R).symm g).coeff (-1 - n) ≠ 0 := fun h ↦ hn (by rw [h, LinearMap.zero_apply])
  have h₁ := order_le_of_coeff_ne_zero hf
  have h₂ := order_le_of_coeff_ne_zero hg
  exact ⟨h₁, by omega⟩

/-- The contraction-residue functional `f ↦ ∑ₙ g₋₁₋ₙ(fₙ)`, before continuity is proved. -/
private noncomputable def residueDualLinearMap (g : HahnModule ℤ R (Module.Dual R V)) :
    HahnModule ℤ R V →ₗ[R] R where
  toFun f := ∑ᶠ n : ℤ, ((of R).symm g).coeff (-1 - n) (((of R).symm f).coeff n)
  map_add' f f' := by
    simp only [of_symm_add, coeff_add, map_add]
    exact finsum_add_distrib (hasFiniteSupport_coeff_apply g f)
      (hasFiniteSupport_coeff_apply g f')
  map_smul' c f := by
    simp only [of_symm_smul', HahnSeries.coeff_smul, map_smul, RingHom.id_apply]
    exact (smul_finsum' c (hasFiniteSupport_coeff_apply g f)).symm

/-- If `g ∈ U_(-a)(V*)`, every term of the contraction-residue sum vanishes on `U_a(V)`. -/
private theorem residueDualLinearMap_eq_zero {g : HahnModule ℤ R (Module.Dual R V)} {a : ℤ}
    (hg : g ∈ lattice R (Module.Dual R V) (-a)) {f : HahnModule ℤ R V} (hf : f ∈ lattice R V a) :
    residueDualLinearMap g f = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun n ↦ ?_
  rcases lt_or_ge n a with hn | hn
  · rw [(mem_lattice_iff R V).mp hf n hn, map_zero]
  · rw [(mem_lattice_iff R (Module.Dual R V)).mp hg (-1 - n) (by omega), LinearMap.zero_apply]

variable [TopologicalSpace R] [DiscreteTopology R]

/-- The continuous functional `f ↦ Res(g(f) dt) = ∑ₙ g₋₁₋ₙ(fₙ)` on `V((t)) = HahnModule ℤ R V`
attached to a series `g` with coefficients in the dual module `Module.Dual R V`. -/
noncomputable def residueDual (g : HahnModule ℤ R (Module.Dual R V)) :
    HahnModule ℤ R V →L[R] R where
  toLinearMap := residueDualLinearMap g
  cont := (LinearMap.continuous_iff_exists_hahnModule_lattice_le_ker _).mpr
    ⟨-((of R).symm g).order, fun _ hf ↦ residueDualLinearMap_eq_zero
      ((mem_lattice_iff R _).mpr fun _ hn ↦ coeff_eq_zero_of_lt_order (by omega)) hf⟩

/-- The value of `residueDual g` on `f` is the contraction-residue sum `∑ₙ g₋₁₋ₙ(fₙ)`. -/
theorem residueDual_apply (g : HahnModule ℤ R (Module.Dual R V)) (f : HahnModule ℤ R V) :
    residueDual g f = ∑ᶠ n : ℤ, ((of R).symm g).coeff (-1 - n) (((of R).symm f).coeff n) :=
  (rfl)

/-- Pairing with the monomial `v tⁿ` evaluates the coefficient of `g` at `-1 - n` on `v`. -/
@[simp]
theorem residueDual_of_single (g : HahnModule ℤ R (Module.Dual R V)) (n : ℤ) (v : V) :
    residueDual g (of R (single n v)) = ((of R).symm g).coeff (-1 - n) v := by
  rw [residueDual_apply, finsum_eq_single _ n fun m hm ↦ by
    rw [Equiv.symm_apply_apply, coeff_single_of_ne hm, map_zero]]
  rw [Equiv.symm_apply_apply, coeff_single_same]

/-- The coefficient of `g` at `n` is recovered by pairing with the monomials `v t⁻¹⁻ⁿ`. -/
theorem coeff_apply_eq_residueDual_of_single (g : HahnModule ℤ R (Module.Dual R V)) (n : ℤ)
    (v : V) : ((of R).symm g).coeff n v = residueDual g (of R (single (-1 - n) v)) := by
  rw [residueDual_of_single, sub_sub_cancel]

/-- A series `g ∈ V*((t))` is determined by its residue functional. -/
theorem residueDual_injective :
    Function.Injective (residueDual : HahnModule ℤ R (Module.Dual R V) → _) := by
  intro g h hgh
  ext n : 2
  refine LinearMap.ext fun v ↦ ?_
  rw [coeff_apply_eq_residueDual_of_single, coeff_apply_eq_residueDual_of_single, hgh]

/-- **Annihilators of lattices.** The functional attached to `g` vanishes on `U_a(V)` exactly
when `g` lies in `U_(-a)(V*)`. -/
theorem lattice_le_ker_residueDual_iff (g : HahnModule ℤ R (Module.Dual R V)) (a : ℤ) :
    lattice R V a ≤ LinearMap.ker (residueDual g).toLinearMap ↔
      g ∈ lattice R (Module.Dual R V) (-a) := by
  refine ⟨fun h ↦ (mem_lattice_iff R _).mpr fun n hn ↦ LinearMap.ext fun v ↦ ?_,
    fun hg _ hf ↦ residueDualLinearMap_eq_zero hg hf⟩
  rw [coeff_apply_eq_residueDual_of_single, LinearMap.zero_apply]
  exact h ((of_mem_lattice_iff R V).mpr (TauCeti.LaurentSeries.single_mem_lattice (by omega) v))

/-- Every continuous functional `ℓ` on `V((t))` is the residue functional of the series whose
coefficient at `m` is `v ↦ ℓ(v t⁻¹⁻ᵐ)`. -/
private theorem exists_residueDual_eq (ℓ : HahnModule ℤ R V →L[R] R) :
    ∃ g : HahnModule ℤ R (Module.Dual R V), residueDual g = ℓ := by
  obtain ⟨a, ha⟩ :=
    ℓ.toLinearMap.continuous_iff_exists_hahnModule_lattice_le_ker.mp ℓ.continuous
  let c : ℤ → Module.Dual R V := fun m ↦
    ℓ.toLinearMap ∘ₗ (ofLinearEquiv R).toLinearMap ∘ₗ single.linearMap (-1 - m)
  have hc (m : ℤ) (v : V) : c m v = ℓ (of R (single (-1 - m) v)) := by
    simp [c, ofLinearEquiv_apply, single.addMonoidHom]
  have hbdd : BddBelow (Function.support c) := by
    refine ⟨-a, fun m hm ↦ ?_⟩
    by_contra! h
    refine (Function.mem_support.mp hm) (LinearMap.ext fun v ↦ ?_)
    rw [hc, LinearMap.zero_apply]
    exact ha ((of_mem_lattice_iff R V).mpr
      (TauCeti.LaurentSeries.single_mem_lattice (by omega) v))
  refine ⟨of R (ofSuppBddBelow c hbdd), continuousLinearMap_ext_single fun n v ↦ ?_⟩
  rw [residueDual_of_single, Equiv.symm_apply_apply, coeff_ofSuppBddBelow, hc, sub_sub_cancel]

variable (R V) in
/-- **The continuous dual of `V((t))`.** Residue pairing `(g, f) ↦ Res(g(f) dt)` identifies
`V*((t)) = HahnModule ℤ R (Module.Dual R V)` with the continuous `R`-linear functionals on
`V((t)) = HahnModule ℤ R V`, for `R` discrete. -/
noncomputable def residueDualEquiv :
    HahnModule ℤ R (Module.Dual R V) ≃ₗ[R] (HahnModule ℤ R V →L[R] R) :=
  LinearEquiv.ofBijective
    { toFun := residueDual
      map_add' := fun g h ↦ continuousLinearMap_ext_single fun n v ↦ by simp
      map_smul' := fun c g ↦ continuousLinearMap_ext_single fun n v ↦ by simp }
    ⟨residueDual_injective, fun ℓ ↦ exists_residueDual_eq ℓ⟩

/-- `residueDualEquiv` sends `g` to its residue functional. -/
@[simp]
theorem residueDualEquiv_apply (g : HahnModule ℤ R (Module.Dual R V)) :
    residueDualEquiv R V g = residueDual g :=
  (rfl)

/-- The zero series pairs to the zero functional. -/
@[simp]
theorem residueDual_zero : residueDual (0 : HahnModule ℤ R (Module.Dual R V)) = 0 := by
  rw [← residueDualEquiv_apply, map_zero]

/-- Residue pairing is additive in the series. -/
@[simp]
theorem residueDual_add (g h : HahnModule ℤ R (Module.Dual R V)) :
    residueDual (g + h) = residueDual g + residueDual h := by
  simp only [← residueDualEquiv_apply, map_add]

/-- Residue pairing commutes with scalar multiplication of the series. -/
@[simp]
theorem residueDual_smul (c : R) (g : HahnModule ℤ R (Module.Dual R V)) :
    residueDual (c • g) = c • residueDual g := by
  simp only [← residueDualEquiv_apply, map_smul]

/-- The series representing the residue functional of `g` is `g`. -/
@[simp]
theorem residueDualEquiv_symm_residueDual (g : HahnModule ℤ R (Module.Dual R V)) :
    (residueDualEquiv R V).symm (residueDual g) = g := by
  rw [← residueDualEquiv_apply, LinearEquiv.symm_apply_apply]

end HahnModule

namespace LinearMap

open HahnModule

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [TopologicalSpace R] [DiscreteTopology R]

/-- **Compatibility with linear maps.** For `u : V →ₗ[R] W`, pairing `g ∈ W*((t))` with the
coefficientwise image of `f ∈ V((t))` is pairing the coefficientwise transpose image of `g` in
`V*((t))` with `f`. -/
theorem residueDual_of_map (u : V →ₗ[R] W) (g : HahnModule ℤ R (Module.Dual R W))
    (f : HahnModule ℤ R V) : residueDual g (of R (((of R).symm f).map u)) =
      residueDual (of R (((of R).symm g).map u.dualMap)) f := by
  simp only [residueDual_apply, Equiv.symm_apply_apply, map_coeff, LinearMap.dualMap_apply]

end LinearMap

namespace ContinuousLinearMap

open HahnModule

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TopologicalSpace R]
  [DiscreteTopology R]

/-- The residue functional of the series representing `ℓ` is `ℓ`. -/
@[simp]
theorem hahnModule_residueDual_residueDualEquiv_symm (ℓ : HahnModule ℤ R V →L[R] R) :
    residueDual ((residueDualEquiv R V).symm ℓ) = ℓ := by
  rw [← residueDualEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The coefficient at `n` of the series representing `ℓ` is the functional `v ↦ ℓ(v t⁻¹⁻ⁿ)`. -/
@[simp]
theorem coeff_hahnModule_residueDualEquiv_symm (ℓ : HahnModule ℤ R V →L[R] R) (n : ℤ) (v : V) :
    ((of R).symm ((residueDualEquiv R V).symm ℓ)).coeff n v = ℓ (of R (single (-1 - n) v)) := by
  rw [coeff_apply_eq_residueDual_of_single, hahnModule_residueDual_residueDualEquiv_symm]

end ContinuousLinearMap
