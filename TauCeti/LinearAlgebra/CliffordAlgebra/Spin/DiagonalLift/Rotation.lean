/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DiagonalLift.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Rotation

/-!
# Plane-rotation formulas for the real diagonal Spin lift

Over `ℝ`, the diagonal lift `CliffordAlgebra.diagSpinLift` of the rotation induced by a circle
element `spinCircle Q u w` (or `spinRotation Q u w t`) is the commuting product of the two circle
elements in the first and second summands of `Q ⊕ Q`.

## Main results

* `CliffordAlgebra.diagSpinLift_spinToSpecialOrthogonal_spinCircle` and
  `CliffordAlgebra.diagSpinLift_spinToSpecialOrthogonal_spinRotation`: explicit plane-rotation
  formulas over `ℝ`.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

section RealRotation

open TauCeti.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate)
  (hsurj : Function.Surjective (spinToSpecialOrthogonal Q))

/-- **Circle-subgroup formula for `diagSpinLift`**: the diagonal lift of the rotation induced by
`spinCircle Q u w z` is the commuting product of the two circle elements in the first and second
summands of `Q ⊕ Q`. -/
theorem diagSpinLift_spinToSpecialOrthogonal_spinCircle {u w : V}
    (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) (z : Circle) :
    diagSpinLift Q hQ hsurj (spinToSpecialOrthogonal Q (spinCircle Q u w huw h z)) =
      spinCircle (Q.prod Q) (u, 0) (w, 0) (by simpa [QuadraticMap.isOrtho_def] using huw)
          (by simpa using h) z *
        spinCircle (Q.prod Q) (0, u) (0, w) (by simpa [QuadraticMap.isOrtho_def] using huw)
          (by simpa using h) z := by
  rw [diagSpinLift_spinToSpecialOrthogonal_eq_mul,
    (QuadraticMap.Isometry.inl Q Q).spinGroupMap_spinCircle huw h
      (by simpa [QuadraticMap.isOrtho_def] using huw) (by simpa using h),
    (QuadraticMap.Isometry.inr Q Q).spinGroupMap_spinCircle huw h
      (by simpa [QuadraticMap.isOrtho_def] using huw) (by simpa using h)]
  simp only [Isometry.inl_apply, Isometry.inr_apply]

/-- **Plane-rotation formula for `diagSpinLift`**: the diagonal lift of the rotation induced by
`spinRotation Q u w t` is the commuting product of the two `spinRotation` elements in the first and
second summands of `Q ⊕ Q`. -/
theorem diagSpinLift_spinToSpecialOrthogonal_spinRotation {u w : V}
    (hu : Q u = 1) (hw : Q w = 1) (huw : Q.IsOrtho u w) (t : ℝ) :
    diagSpinLift Q hQ hsurj (spinToSpecialOrthogonal Q (spinRotation Q u w hu hw huw t)) =
      spinRotation (Q.prod Q) (u, 0) (w, 0) (by simpa using hu) (by simpa using hw)
          (by simpa [QuadraticMap.isOrtho_def] using huw) t *
        spinRotation (Q.prod Q) (0, u) (0, w) (by simpa using hu) (by simpa using hw)
          (by simpa [QuadraticMap.isOrtho_def] using huw) t := by
  rw [diagSpinLift_spinToSpecialOrthogonal_eq_mul,
    (QuadraticMap.Isometry.inl Q Q).spinGroupMap_spinRotation hu hw huw t,
    (QuadraticMap.Isometry.inr Q Q).spinGroupMap_spinRotation hu hw huw t]
  simp only [Isometry.inl_apply, Isometry.inr_apply]

end

end RealRotation

end CliffordAlgebra
