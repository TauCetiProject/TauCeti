/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Rotations in real Spin groups

An orthonormal pair `x, y` determines elements of the Spin group parametrized by an angle `t`.
The element is the product of the Clifford generators of `x` and
`cos(t) x + sin(t) y`. The rotating vector has norm one, so this product belongs to Spin; at
angles zero and `π` it is respectively `1` and the canonical scalar `-1`.

## Main definitions and results

* `CliffordAlgebra.spinRotation`: the Spin element associated to an angle in an orthonormal
  two-plane.
* `CliffordAlgebra.spinRotation_zero`: the rotation at angle zero is the identity.
* `CliffordAlgebra.spinRotation_pi`: the rotation at angle `π` is the canonical scalar `-1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §6.
-/

public section

namespace CliffordAlgebra

noncomputable section

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]
  (Q : QuadraticForm ℝ V) (x y : V)

/-- The Spin element obtained by multiplying an orthonormal vector `x` by the unit vector at
angle `t` in the oriented plane spanned by `x` and `y`. -/
def spinRotation (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) (t : ℝ) : spinGroup Q :=
  ⟨ι Q x * ι Q (Real.cos t • x + Real.sin t • y),
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one x
      (Real.cos t • x + Real.sin t • y) <| by
      have hscaled : Q.IsOrtho (Real.cos t • x) (Real.sin t • y) := by
        rw [← QuadraticMap.isOrtho_polarBilin]
        simp [hxy.polar_eq_zero]
      rw [hscaled]
      simpa [Q.map_smul, hx, hy, pow_two] using Real.cos_sq_add_sin_sq t⟩

private theorem coe_spinRotation_internal (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) (t : ℝ) :
    (spinRotation Q x y hx hy hxy t : CliffordAlgebra Q) =
      ι Q x * ι Q (Real.cos t • x + Real.sin t • y) :=
  rfl

/-- The underlying Clifford element of `spinRotation`. -/
@[simp]
theorem coe_spinRotation (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) (t : ℝ) :
    (spinRotation Q x y hx hy hxy t : CliffordAlgebra Q) =
      ι Q x * ι Q (Real.cos t • x + Real.sin t • y) :=
  coe_spinRotation_internal Q x y hx hy hxy t

/-- The Spin rotation at angle zero is the identity. -/
@[simp]
theorem spinRotation_zero (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) :
    spinRotation Q x y hx hy hxy 0 = 1 := by
  apply Subtype.ext
  simp [hx]

/-- The Spin rotation at angle `π` is the canonical scalar `-1`. -/
@[simp]
theorem spinRotation_pi (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) :
    spinRotation Q x y hx hy hxy Real.pi =
      spinGroup.negOne Q (by
        intro hQ
        simp [hQ] at hx) := by
  apply Subtype.ext
  rw [spinGroup.coe_negOne]
  simp [hx]

end


end CliffordAlgebra
