/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Weighted restricted series with unit weights

Let `A` be a commutative topological ring and let every weight set be a single unit,
`Tᵢ = {uᵢ}` with `uᵢ ∈ Aˣ`. The weight of a multi-index `ν` is then the unit
`uᵛ = ∏ᵢ uᵢ ^ νᵢ`, and the weighted subgroup `Tν · U` is the translate `uᵛ U` of `U`. So a
coefficient `a` satisfies the weighted bound exactly when `u⁻ᵛ a ∈ U`. Since `u⁻ᵛ aᵥ` is the
coefficient of the rescaled series `f(u⁻¹ X)` (Mathlib's `MvPowerSeries.rescale`), a series `f`
is `T`-restricted exactly when `f(u⁻¹ X)` is restricted for the trivial weight, and `f` lies in the
neighbourhood `U⟨X⟩` exactly when every coefficient of `f(u⁻¹ X)` lies in `U`.

Over a normed ring whose units `uᵢ` scale norms exactly, this turns the weighted bound into the
Gauss-norm bound at the radii `‖uᵢ‖⁻¹`; that comparison is in
`TauCeti.RingTheory.Huber.Restricted.GaussNorm`.

## Main results

* `TauCeti.Huber.weightPow_singleton`: for singleton weights, `Tν` is the singleton of `uᵛ`.
* `TauCeti.Huber.mem_weightMul_units_iff`: `a ∈ uᵛ · U ↔ u⁻ᵛ a ∈ U`.
* `TauCeti.Huber.isWeightFamily_units`: unit weights satisfy Wedhorn's standing hypothesis.
* `TauCeti.Huber.isWeightedRestricted_units_iff`: `f` is restricted for the unit weights exactly
  when `f(u⁻¹ X)` is restricted for the trivial weight.
* `TauCeti.Huber.mem_weightedNhd_units_iff`: the neighbourhoods `U⟨X⟩` in the same terms.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48 and equation (5.6.1).
-/

public section

namespace TauCeti.Huber

open MvPowerSeries
open scoped Pointwise

section CommMonoid

variable {k : ℕ} {A : Type*} [CommMonoid A]

/-- For singleton weights `Tᵢ = {uᵢ}`, the weight of a multi-index `ν` is the singleton of the
monomial value `uᵛ = ∏ᵢ uᵢ ^ νᵢ`. -/
theorem weightPow_singleton (u : Fin k → A) (ν : Fin k →₀ ℕ) :
    weightPow (fun i ↦ ({u i} : Set A)) ν = {ν.prod (u · ^ ·)} := by
  rw [weightPow_def, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
  simp only [Set.singleton_pow]
  simpa only [Set.singletonMonoidHom_apply] using
    (map_prod Set.singletonMonoidHom (fun i ↦ u i ^ ν i) Finset.univ).symm

end CommMonoid

variable {k : ℕ} {A : Type*} [CommRing A]

/-- **The weighted subgroup for unit weights.** With `Tᵢ = {uᵢ}` for units `uᵢ`, the subgroup
`Tν · U` is the translate `uᵛ U`, so `a` lies in it exactly when `u⁻ᵛ a` lies in `U`. -/
theorem mem_weightMul_units_iff (u : Fin k → Aˣ) (ν : Fin k →₀ ℕ) (U : AddSubgroup A)
    (a : A) :
    a ∈ weightMul (fun i ↦ ({(u i : A)} : Set A)) ν U ↔
      ν.prod (fun i m ↦ (((u i)⁻¹ : Aˣ) : A) ^ m) * a ∈ U := by
  set p := ν.prod fun i m ↦ (((u i)⁻¹ : Aˣ) : A) ^ m
  set q := ν.prod fun i m ↦ (u i : A) ^ m
  have hpq : p * q = 1 := by
    simp only [p, q, ← Finsupp.prod_mul, ← mul_pow, Units.inv_mul, one_pow]
    exact Finset.prod_const_one
  have hU : weightMul (fun i ↦ ({(u i : A)} : Set A)) ν U = U.map (AddMonoidHom.mulLeft q) := by
    rw [weightMul_def, weightPow_singleton, Set.singleton_mul, ← AddSubgroup.closure_eq
      (U.map (AddMonoidHom.mulLeft q)), AddSubgroup.coe_map, AddMonoidHom.coe_mulLeft]
  rw [hU, AddSubgroup.mem_map]
  refine ⟨?_, fun ha ↦ ⟨p * a, ha, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [AddMonoidHom.coe_mulLeft, ← mul_assoc, hpq, one_mul]
  · rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, mul_comm q, hpq, one_mul]

/-- The coefficients of `f` satisfy the bound `uᵛ · U` exactly when those of `f(u⁻¹ X)` lie
in `U`. -/
theorem coeff_mem_weightMul_units_iff (u : Fin k → Aˣ) (U : AddSubgroup A)
    (f : MvPowerSeries (Fin k) A) (ν : Fin k →₀ ℕ) :
    coeff ν f ∈ weightMul (fun i ↦ ({(u i : A)} : Set A)) ν U ↔
      coeff ν (rescale (fun i ↦ (((u i)⁻¹ : Aˣ) : A)) f) ∈ U := by
  rw [mem_weightMul_units_iff, coeff_rescale]

variable [TopologicalSpace A]

/-- **Unit weights are admissible.** Singleton weights consisting of units satisfy Wedhorn's
standing hypothesis, since multiplication by a unit is a homeomorphism. -/
theorem isWeightFamily_units [ContinuousMul A] (u : Fin k → Aˣ) :
    IsWeightFamily (fun i ↦ ({(u i : A)} : Set A)) :=
  .of_exists_isUnit fun i ↦ ⟨u i, rfl, (u i).isUnit⟩

/-- **Restrictedness for unit weights.** A series is restricted for the weights `Tᵢ = {uᵢ}`
exactly when its rescaling `f(u⁻¹ X)` is restricted for the trivial weight. -/
theorem isWeightedRestricted_units_iff (u : Fin k → Aˣ) (f : MvPowerSeries (Fin k) A) :
    IsWeightedRestricted (fun i ↦ ({(u i : A)} : Set A)) f ↔
      IsWeightedRestricted (fun _ ↦ ({1} : Set A))
        (rescale (fun i ↦ (((u i)⁻¹ : Aˣ) : A)) f) := by
  simp only [isWeightedRestricted_iff, weightMul_one_weight, coeff_mem_weightMul_units_iff]

/-- **The neighbourhoods `U⟨X⟩` for unit weights.** A series lies in `U⟨X⟩` for the weights
`Tᵢ = {uᵢ}` exactly when every coefficient of `f(u⁻¹ X)` lies in `U`. -/
theorem mem_weightedNhd_units_iff [NonarchimedeanRing A] (u : Fin k → Aˣ)
    {hT : IsWeightFamily (fun i ↦ ({(u i : A)} : Set A))} {U : AddSubgroup A}
    {f : weightedRestrictedSubring (fun i ↦ ({(u i : A)} : Set A)) hT} :
    f ∈ weightedNhd _ hT U ↔
      ∀ ν, coeff ν (rescale (fun i ↦ (((u i)⁻¹ : Aˣ) : A)) (f : MvPowerSeries (Fin k) A)) ∈ U := by
  simp only [mem_weightedNhd, coeff_mem_weightMul_units_iff]

end TauCeti.Huber
