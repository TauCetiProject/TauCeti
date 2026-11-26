/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Probability.ProductMeasure
import TauCeti.Probability.ProductMeasure

/-!
# The shift of the full shift: measurability and Bernoulli measure preservation

Mathlib's shift `SymbolicDynamics.FullShift.mulShift g x = fun h ↦ x (g * h)` on configurations
`G → A` is measurable for the product σ-algebra, and on a group it is a measurable automorphism
with inverse `mulShift g⁻¹` (`SymbolicDynamics.FullShift.mulShiftEquiv`). The additive versions are
`SymbolicDynamics.FullShift.measurable_shift` and `SymbolicDynamics.FullShift.shiftEquiv`. On a
left-cancellative monoid the shift reindexes coordinates injectively, so it preserves every
Bernoulli measure `p^{⊗G}` (`SymbolicDynamics.FullShift.measurePreserving_mulShift`). For
`G = ℤ`, the shift `shift 1`, `x ↦ (n ↦ x (n + 1))`, is invertible with inverse the right shift
`x ↦ (n ↦ x (n - 1))` (`SymbolicDynamics.FullShift.shiftEquiv_one_symm_apply`), and a set invariant
under `shift 1` is invariant under every `shift k`
(`SymbolicDynamics.FullShift.preimage_shift_eq_of_preimage_shift_one_eq`).

## Main results

* `SymbolicDynamics.FullShift.measurable_mulShift`: the shift is measurable.
* `SymbolicDynamics.FullShift.mulShiftEquiv`: the shift of a group as a measurable automorphism.
* `SymbolicDynamics.FullShift.measurePreserving_mulShift`: the shift preserves the Bernoulli
  measure `p^{⊗G}` (additively `SymbolicDynamics.FullShift.measurePreserving_shift`).
* `SymbolicDynamics.FullShift.measurePreserving_mulShiftEquiv`: on a group, the shift automorphism
  preserves `p^{⊗G}`, so it is an invertible measure-preserving system
  (additively `SymbolicDynamics.FullShift.measurePreserving_shiftEquiv`).
* `SymbolicDynamics.FullShift.shiftEquiv_one_symm_apply`: the inverse of the two-sided shift.
* `SymbolicDynamics.FullShift.preimage_shift_eq_of_preimage_shift_one_eq`: a set invariant under
  `shift 1` is invariant under every `shift k`.
-/

public section

open MeasureTheory Set

namespace SymbolicDynamics.FullShift

variable {A G : Type*} [MeasurableSpace A]

/-- The shift is measurable. -/
@[to_additive (attr := fun_prop) /-- The shift is measurable. -/]
theorem measurable_mulShift [Monoid G] (g : G) : Measurable (mulShift (A := A) g) :=
  measurable_pi_iff.2 fun h ↦ measurable_pi_apply (g * h)

/-- The shift of a group by `g` as a measurable automorphism of `G → A`, with inverse the shift by
`g⁻¹`. -/
@[to_additive /-- The shift of an additive group by `g` as a measurable automorphism of `G → A`,
with inverse the shift by `-g`. -/]
def mulShiftEquiv [Group G] (g : G) : (G → A) ≃ᵐ (G → A) where
  toFun := mulShift g
  invFun := mulShift g⁻¹
  left_inv x := by
    ext h
    simp
  right_inv x := by
    ext h
    simp
  measurable_toFun := measurable_mulShift g
  measurable_invFun := measurable_mulShift g⁻¹

/-- The automorphism `mulShiftEquiv g` is the shift by `g`. -/
@[to_additive (attr := simp) /-- The automorphism `shiftEquiv g` is the shift by `g`. -/]
theorem coe_mulShiftEquiv [Group G] (g : G) : ⇑(mulShiftEquiv (A := A) g) = mulShift g :=
  (rfl)

/-- The inverse of `mulShiftEquiv g` is the shift by `g⁻¹`. -/
@[to_additive (attr := simp) /-- The inverse of `shiftEquiv g` is the shift by `-g`. -/]
theorem coe_mulShiftEquiv_symm [Group G] (g : G) :
    ⇑(mulShiftEquiv (A := A) g).symm = mulShift g⁻¹ :=
  (rfl)

/-- **Check.** The two-sided shift on `ℤ → A` is invertible, and its inverse is the right shift
`x ↦ (n ↦ x (n - 1))`. -/
theorem shiftEquiv_one_symm_apply (x : ℤ → A) (n : ℤ) :
    (shiftEquiv (A := A) (1 : ℤ)).symm x n = x (n - 1) := by
  simp [neg_add_eq_sub]

/-- **The shift preserves the Bernoulli measure.** On a left-cancellative monoid `G`, the shift by
`g` reindexes along the injective map `h ↦ g * h`, so it preserves the product `p^{⊗G}`. -/
@[to_additive /-- **The shift preserves the Bernoulli measure.** On a left-cancellative additive
monoid `G`, the shift by `g` reindexes along the injective map `h ↦ g + h`, so it preserves the
product `p^{⊗G}`. -/]
theorem measurePreserving_mulShift [Monoid G] [IsLeftCancelMul G] (p : Measure A)
    [IsProbabilityMeasure p] (g : G) :
    MeasurePreserving (mulShift g) (Measure.infinitePi fun _ : G ↦ p)
      (Measure.infinitePi fun _ : G ↦ p) :=
  TauCeti.measurePreserving_infinitePi_comp_of_injective (fun _ ↦ p) (mul_right_injective g)

/-- **The shift automorphism preserves the Bernoulli measure.** On a group `G`, the measurable
automorphism `mulShiftEquiv g` preserves the product `p^{⊗G}`. -/
@[to_additive /-- **The shift automorphism preserves the Bernoulli measure.** On an additive group
`G`, the measurable automorphism `shiftEquiv g` preserves the product `p^{⊗G}`. -/]
theorem measurePreserving_mulShiftEquiv [Group G] (p : Measure A) [IsProbabilityMeasure p]
    (g : G) :
    MeasurePreserving (mulShiftEquiv (A := A) g) (Measure.infinitePi fun _ : G ↦ p)
      (Measure.infinitePi fun _ : G ↦ p) :=
  measurePreserving_mulShift p g

omit [MeasurableSpace A] in
/-- A set invariant under the two-sided shift is invariant under every shift `shift k`,
`k ∈ ℤ`. -/
theorem preimage_shift_eq_of_preimage_shift_one_eq {s : Set (ℤ → A)}
    (hs : shift (1 : ℤ) ⁻¹' s = s) (k : ℤ) : shift k ⁻¹' s = s := by
  have hstep (k : ℤ) : shift (k + 1) = shift (1 : ℤ) ∘ shift (A := A) k :=
    funext fun x ↦ shift_add k 1 x
  induction k using Int.induction_on with
  | zero => rw [show shift (0 : ℤ) = (id : (ℤ → A) → ℤ → A) from funext shift_zero, preimage_id]
  | succ k ih => rw [hstep, preimage_comp, hs, ih]
  | pred k ih =>
    have h := hstep (-k - 1)
    rw [sub_add_cancel] at h
    rwa [h, preimage_comp, hs] at ih

end SymbolicDynamics.FullShift
