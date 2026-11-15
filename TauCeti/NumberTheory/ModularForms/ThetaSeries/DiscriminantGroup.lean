/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.DiscriminantCharacter
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Translation

/-!
# Coset theta series on the discriminant group

Let `L` be a lattice in a real inner product space `E`, with dual lattice `L^∨ = ZLattice.dual L`
and discriminant group `A_L = L^∨ ⧸ (L ∩ L^∨)` (`ZLattice.DiscriminantGroup L`). The theta series
`θ_{γ+L}` of a translate depends only on the class of `γ` modulo `L`
(`ZLattice.thetaCoset_eq_of_sub_mem`), so the coset theta series descend to a family
`(θ_γ)_{γ ∈ A_L}` indexed by the discriminant group, `ZLattice.thetaCosetClass L`. This descent
needs no hypothesis on `L`. This is the family that the vector-valued inversion law of coset theta
series is stated for. It satisfies `θ_0 = Θ_L` and `θ_{-γ} = θ_γ`; in particular, whenever
`A_L` has an element `γ ≠ -γ`, the family is not linearly independent.

For an even lattice `L` (in arbitrary dimension, without discreteness or fullness), every coset
theta series `θ_γ` (`γ ∈ A_L`) has period `level L` and is invariant under `T ^ level L` in every
weight (`ZLattice.IsEven.thetaCosetClass_slash_T_pow_level`), descending from the
representative-level invariance `ZLattice.IsEven.thetaCoset_slash_T_pow_level`. When `L` is an even
full lattice, the modular translation `T : τ ↦ τ + 1` acts on `θ_γ` with eigenvalue `e(q_L(γ))`
(`ZLattice.IsEven.thetaCosetClass_slash_T`), where `e(q_L(γ))` is
`ZLattice.IsEven.discriminantQuadraticChar`, and `level L` is the least positive exponent killing
all of these eigenvalues (`ZLattice.IsEven.level_dvd_iff_discriminantQuadraticChar_pow_eq_one`).

For an integral full lattice, `A_L = L^∨ ⧸ L` is finite and the theta series of the dual lattice is
the sum of the coset theta series, `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`
(`ZLattice.IsIntegral.thetaSeries_dual_eq_sum`), by splitting `L^∨` into the cosets of `L`.
Integrality is needed: for `L = ½ ℤ ⊆ ℝ` the dual `L^∨ = 2 ℤ` lies in `L`, the discriminant group
is trivial, and the identity would read `Θ_{2ℤ} = Θ_{½ℤ}`, which is false.

## Main definitions

* `ZLattice.thetaCosetClass L`: the coset theta series `θ_γ` of a class `γ` of the discriminant
  group of `L`.

## Main statements

* `ZLattice.thetaCosetClass_mk`: `θ_γ` is the theta series of the translate `γ + L`.
* `ZLattice.thetaCosetClass_zero`, `ZLattice.thetaCosetClass_neg`: `θ_0 = Θ_L`, `θ_{-γ} = θ_γ`.
* `ZLattice.IsEven.thetaCosetClass_slash_T_pow_level`: `θ_γ` is invariant under `T ^ level L` in
  every weight.
* `ZLattice.IsEven.thetaCosetClass_slash_T`, `ZLattice.IsEven.thetaCosetClass_slash_T_zpow`:
  `θ_γ ∣[k] T ^ n = e(q_L(γ))^n • θ_γ` for an even full lattice `L`.
* `ZLattice.IsIntegral.thetaSeries_dual_eq_sum`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` for integral `L`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 2.
-/

public section

open Complex
open scoped Real ModularForm UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coset theta series `θ_γ = θ_{γ+L}` of a class `γ` of the discriminant group
`L^∨ ⧸ (L ∩ L^∨)` of `L`: the theta series `thetaCoset L x` of the translate by any representative
`x ∈ L^∨` of `γ` (`thetaCosetClass_mk`). -/
noncomputable def thetaCosetClass (L : Submodule ℤ E) (γ : DiscriminantGroup L) : ℍ → ℂ :=
  Quotient.liftOn' γ (fun x : dual L => thetaCoset L (x : E)) fun x y h =>
    thetaCoset_eq_of_sub_mem L ((discriminantGroup_mk_eq_mk_iff x y).mp (Quotient.sound' h))

variable (L : Submodule ℤ E)

/-- The coset theta series of the class of `x ∈ L^∨` is the theta series of the translate
`x + L`. -/
@[simp]
theorem thetaCosetClass_mk (x : dual L) :
    thetaCosetClass L (Submodule.Quotient.mk x) = thetaCoset L (x : E) :=
  (rfl)

/-- The coset theta series of the zero class is the theta series of `L`. -/
@[simp]
theorem thetaCosetClass_zero : thetaCosetClass L 0 = thetaSeries L := by
  rw [← Submodule.Quotient.mk_zero, thetaCosetClass_mk, ZeroMemClass.coe_zero, thetaCoset_zero]

/-- The coset theta series of the classes `-γ` and `γ` agree. -/
@[simp]
theorem thetaCosetClass_neg (γ : DiscriminantGroup L) :
    thetaCosetClass L (-γ) = thetaCosetClass L γ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x => rw [← Submodule.Quotient.mk_neg, thetaCosetClass_mk, thetaCosetClass_mk,
      NegMemClass.coe_neg, thetaCoset_neg]

/-! ### Translation invariance at the level -/

section LevelTranslation

variable {L}

namespace IsEven

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, every integer multiple of `level L` is a
period of `θ_γ`. -/
theorem thetaCosetClass_intCast_vadd_of_level_dvd (hL : IsEven L) (γ : DiscriminantGroup L)
    {N : ℤ} (hN : (level L : ℤ) ∣ N) (τ : ℍ) :
    thetaCosetClass L γ ((N : ℝ) +ᵥ τ) = thetaCosetClass L γ τ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x => exact hL.thetaCoset_intCast_vadd_of_level_dvd x.2 hN τ

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` has period `level L`. -/
@[simp]
theorem thetaCosetClass_level_vadd (hL : IsEven L) (γ : DiscriminantGroup L) (τ : ℍ) :
    thetaCosetClass L γ ((level L : ℝ) +ᵥ τ) = thetaCosetClass L γ τ := by
  simpa using hL.thetaCosetClass_intCast_vadd_of_level_dvd γ dvd_rfl τ

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` is invariant under `T ^ N` in
every weight whenever `(level L : ℤ) ∣ N`. -/
theorem thetaCosetClass_slash_T_zpow_of_level_dvd (hL : IsEven L) (γ : DiscriminantGroup L)
    (k : ℤ) {N : ℤ} (hN : (level L : ℤ) ∣ N) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ N) = thetaCosetClass L γ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x => exact hL.thetaCoset_slash_T_zpow_of_level_dvd x.2 k hN

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` is invariant under
`T ^ (level L : ℤ)` in every weight. -/
theorem thetaCosetClass_slash_T_zpow_level (hL : IsEven L) (γ : DiscriminantGroup L) (k : ℤ) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ (level L : ℤ)) = thetaCosetClass L γ :=
  hL.thetaCosetClass_slash_T_zpow_of_level_dvd γ k dvd_rfl

/-- For an even lattice `L` and `γ : DiscriminantGroup L`, `θ_γ` is invariant under `T ^ level L`
in every weight. -/
@[simp]
theorem thetaCosetClass_slash_T_pow_level (hL : IsEven L) (γ : DiscriminantGroup L) (k : ℤ) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ level L) = thetaCosetClass L γ := by
  rw [← zpow_natCast, hL.thetaCosetClass_slash_T_zpow_level γ k]

end IsEven

end LevelTranslation

/-! ### Full lattices -/

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] {L}

/-- For an integral lattice `L`, the theta series of the dual lattice is the sum of the coset theta
series over the finite discriminant group `L^∨ ⧸ L`: `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ`. The discriminant
group of an integral lattice is finite (`IsIntegral.finite_discriminantGroup`), so a `Fintype`
instance is always available. -/
theorem IsIntegral.thetaSeries_dual_eq_sum (h : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (τ : ℍ) : thetaSeries (dual L) τ = ∑ γ : DiscriminantGroup L, thetaCosetClass L γ τ := by
  rw [← (hasSum_thetaCoset_out (dual L) (isIntegral_iff_le_dual.mp h) τ).tsum_eq, tsum_fintype]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← thetaCosetClass_mk, Submodule.Quotient.mk_out]

namespace IsEven

/-- The translation law of a coset theta series on the discriminant group of an even full lattice:
for `γ : DiscriminantGroup L` and `n : ℤ`, `θ_γ(τ + n) = e(q_L(γ))^n θ_γ(τ)`. -/
theorem thetaCosetClass_intCast_vadd (hL : IsEven L) (γ : DiscriminantGroup L) (n : ℤ) (τ : ℍ) :
    thetaCosetClass L γ ((n : ℝ) +ᵥ τ) =
      hL.discriminantQuadraticChar γ ^ n * thetaCosetClass L γ τ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x =>
    rw [thetaCosetClass_mk, hL.thetaCoset_intCast_vadd x.2, hL.discriminantQuadraticChar_mk,
      ← Complex.exp_int_mul]
    congr 2
    ring

/-- For an even full lattice `L` and `γ : DiscriminantGroup L`,
`θ_γ(τ + 1) = e(q_L(γ)) θ_γ(τ)`. -/
theorem thetaCosetClass_one_vadd (hL : IsEven L) (γ : DiscriminantGroup L) (τ : ℍ) :
    thetaCosetClass L γ ((1 : ℝ) +ᵥ τ) =
      hL.discriminantQuadraticChar γ * thetaCosetClass L γ τ := by
  simpa using hL.thetaCosetClass_intCast_vadd γ 1 τ

/-- In slash form, `θ_γ ∣[k] T ^ n = e(q_L(γ))^n • θ_γ` for an even full lattice `L` and
`γ : DiscriminantGroup L`. -/
theorem thetaCosetClass_slash_T_zpow (hL : IsEven L) (γ : DiscriminantGroup L) (k n : ℤ) :
    thetaCosetClass L γ ∣[k] (ModularGroup.T ^ n) =
      (hL.discriminantQuadraticChar γ ^ n) • thetaCosetClass L γ := by
  induction γ using Submodule.Quotient.induction_on with
  | H x =>
    rw [thetaCosetClass_mk, hL.thetaCoset_slash_T_zpow x.2, hL.discriminantQuadraticChar_mk,
      ← Complex.exp_int_mul]
    congr 2
    ring

/-- In slash form, `θ_γ ∣[k] T = e(q_L(γ)) • θ_γ` for an even full lattice `L` and
`γ : DiscriminantGroup L`. -/
theorem thetaCosetClass_slash_T (hL : IsEven L) (γ : DiscriminantGroup L) (k : ℤ) :
    thetaCosetClass L γ ∣[k] ModularGroup.T =
      hL.discriminantQuadraticChar γ • thetaCosetClass L γ := by
  simpa using hL.thetaCosetClass_slash_T_zpow γ k 1

end IsEven

end ZLattice
