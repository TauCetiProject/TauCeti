/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.Complex.Circle
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

/-!
# Rotations in real Spin groups

An orthonormal pair `x, y` determines elements of the Spin group parametrized by an angle `t`.
The element is the product of the Clifford generators of `x` and
`cos(t) x + sin(t) y`. The rotating vector has norm one, so this product belongs to Spin; at
angles zero and `π` it is respectively `1` and the canonical scalar `-1`.

More generally, let `u, w` be orthogonal vectors with `Q u * Q w = 1`, for instance an orthonormal
pair for either sign convention `Q v = ±‖v‖²`. Then the bivector `J = ι u ι w` squares to `-1`,
so `a + b i ↦ a + b J` is an algebra map from `ℂ`, and it sends the unit circle into the Spin
group (`CliffordAlgebra.spinCircle`). This circle subgroup is a one-parameter group of rotations
of the plane of `u` and `w`: the element `z` acts on vectors as the rotation by `z²` from `u`
towards `w` when `Q u < 0` (by `z⁻²` when `Q u > 0`), and fixes the orthogonal complement. For
`Q u = Q w = 1` it is `spinRotation`, reparametrized by `Circle.exp`.

## Main definitions and results

* `CliffordAlgebra.spinRotation`: the Spin element associated to an angle in an orthonormal
  two-plane.
* `CliffordAlgebra.spinRotation_zero`: the rotation at angle zero is the identity.
* `CliffordAlgebra.spinRotation_pi`: the rotation at angle `π` is the canonical scalar `-1`.
* `CliffordAlgebra.spinCircle`: the homomorphism `z ↦ Re z + Im z ι u ι w` from the unit circle
  to the Spin group.
* `CliffordAlgebra.spinRotation_eq_spinCircle`: `spinRotation` is `spinCircle ∘ Circle.exp`.
* `CliffordAlgebra.spinCircle_neg_one`: the element `-1` of the circle maps to the canonical
  scalar `-1`.
* `QuadraticMap.Isometry.spinGroupMap_spinCircle`: quadratic isometries carry circle subgroups to
  circle subgroups.
* `CliffordAlgebra.spinVectorAction_spinCircle_left`,
  `CliffordAlgebra.spinVectorAction_spinCircle_right`,
  `CliffordAlgebra.spinVectorAction_spinCircle_of_isOrtho`: `z` rotates the plane of `u` and `w`
  by `z²` from `u` towards `w` when `Q u < 0` (by `z⁻²` when `Q u > 0`) and fixes the vectors
  orthogonal to it.

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

/-! ### The circle subgroup of an orthogonal plane -/

variable {Q} {u w : V}

/-- For orthogonal `u, w` with `Q u * Q w = 1`, the algebra map `ℂ → Cl(Q)` sending `i` to the
bivector `ι u ι w`, which squares to `-1`. -/
private def planeComplex (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) :
    ℂ →ₐ[ℝ] CliffordAlgebra Q :=
  Complex.liftAux (ι Q u * ι Q w) (by rw [ι_mul_ι_mul_self_of_isOrtho huw, h, map_one])

private theorem planeComplex_apply (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) (z : ℂ) :
    planeComplex huw h z = algebraMap ℝ _ z.re + z.im • (ι Q u * ι Q w) :=
  Complex.liftAux_apply ..

/-- A complex number `z` maps to the product of `u` with `Re z Q w • u + Im z • w`. -/
private theorem planeComplex_eq_ι_mul_ι (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) (z : ℂ) :
    planeComplex huw h z = ι Q u * ι Q ((z.re * Q w) • u + z.im • w) := by
  have hre : (z.re * Q w) • algebraMap ℝ (CliffordAlgebra Q) (Q u) = algebraMap ℝ _ z.re := by
    rw [Algebra.smul_def, ← map_mul]
    congr 1
    linear_combination z.re * h
  simp only [planeComplex_apply, map_add, map_smul, mul_add, mul_smul_comm, ι_sq_scalar, hre]

/-- A unit complex number maps into the Spin group: it is the product of the two vectors `u` and
`Re z Q w • u + Im z • w`, the product of whose values under `Q` is one. -/
private theorem planeComplex_mem_spinGroup (huw : Q.IsOrtho u w) (h : Q u * Q w = 1)
    (z : Circle) : planeComplex huw h z ∈ spinGroup Q := by
  rw [planeComplex_eq_ι_mul_ι]
  refine ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ ?_
  have hscaled : Q.IsOrtho (((z : ℂ).re * Q w) • u) ((z : ℂ).im • w) := by
    rw [← QuadraticMap.isOrtho_polarBilin]
    simp [huw.polar_eq_zero]
  rw [QuadraticMap.isOrtho_def.1 hscaled, QuadraticMap.map_smul, QuadraticMap.map_smul,
    smul_eq_mul, smul_eq_mul]
  linear_combination ((z : ℂ).re ^ 2 * (Q u * Q w + 1) + (z : ℂ).im ^ 2) * h +
    Circle.re_sq_add_im_sq z

variable (Q u w) in
/-- **The circle subgroup of `Spin` in an orthogonal plane.** For orthogonal `u, w` with
`Q u * Q w = 1`, the bivector `J = ι u ι w` squares to `-1`, and a unit complex number `z` maps
to `Re z + Im z J ∈ Spin(Q)`. The element `z` acts on the plane of `u` and `w` as the rotation by
`z²` from `u` towards `w` when `Q u < 0`, and by `z⁻²` when `Q u > 0`
(`CliffordAlgebra.spinVectorAction_spinCircle_left`). -/
def spinCircle (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) : Circle →* spinGroup Q where
  toFun z := ⟨planeComplex huw h z, planeComplex_mem_spinGroup huw h z⟩
  map_one' := Subtype.ext (by simp)
  map_mul' z₁ z₂ := Subtype.ext (by simp only [Circle.coe_mul, map_mul, Submonoid.coe_mul])

/-- The underlying Clifford element of `spinCircle`: `z ↦ Re z + Im z ι u ι w`. -/
@[simp]
theorem coe_spinCircle (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) (z : Circle) :
    (spinCircle Q u w huw h z : CliffordAlgebra Q) =
      algebraMap ℝ _ (z : ℂ).re + (z : ℂ).im • (ι Q u * ι Q w) :=
  planeComplex_apply huw h z

/-- At `-1` the circle subgroup is the canonical scalar `-1` of the Spin group. -/
@[simp]
theorem spinCircle_neg_one (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) :
    spinCircle Q u w huw h (-1) = spinGroup.negOne Q (by rintro rfl; simp at h) := by
  apply Subtype.ext
  simp [spinGroup.coe_negOne]

/-- For `Q x = Q y = 1`, the Spin rotation at angle `t` is the circle element `exp (i t)`. -/
theorem spinRotation_eq_spinCircle (hx : Q x = 1) (hy : Q y = 1) (hxy : Q.IsOrtho x y) (t : ℝ) :
    spinRotation Q x y hx hy hxy t =
      spinCircle Q x y hxy (by rw [hx, hy, mul_one]) (Circle.exp t) := by
  apply Subtype.ext
  simp [mul_add, hx, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Algebra.algebraMap_eq_smul_one]

section VectorAction

variable (huw : Q.IsOrtho u w)
include huw

omit huw in
private theorem ι_mul_bivector : ι Q u * (ι Q u * ι Q w) = Q u • ι Q w := by
  rw [← mul_assoc, ι_sq_scalar, Algebra.smul_def]

private theorem bivector_mul_ι_left : ι Q u * ι Q w * ι Q u = -(Q u • ι Q w) := by
  rw [mul_assoc, ι_mul_ι_comm_of_isOrtho huw.symm, mul_neg, ι_mul_bivector]

private theorem ι_right_mul_bivector : ι Q w * (ι Q u * ι Q w) = -(Q w • ι Q u) := by
  rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho huw.symm, neg_mul, mul_assoc, ι_sq_scalar,
    ← Algebra.commutes, Algebra.smul_def]

omit huw in
private theorem bivector_mul_ι_right : ι Q u * ι Q w * ι Q w = Q w • ι Q u := by
  rw [mul_assoc, ι_sq_scalar, ← Algebra.commutes, Algebra.smul_def]

variable (h : Q u * Q w = 1)
include h

/-- **`spinCircle` rotates its plane, first vector.** The circle element `z` moves `u` to
`Re (z²) u - Im (z²) Q u w`; for `Q u = -1` this is the rotation of `u` towards `w` by `z²`. -/
theorem spinVectorAction_spinCircle_left (z : Circle) :
    spinVectorAction Q (spinCircle Q u w huw h z) u =
      ((z : ℂ) ^ 2).re • u - (((z : ℂ) ^ 2).im * Q u) • w := by
  apply spinVectorAction_eq_of_mul_ι_eq
  simp only [coe_spinCircle, map_sub, map_smul, add_mul, mul_add, sub_mul, smul_mul_assoc,
    mul_smul_comm, ← Algebra.commutes, ← Algebra.smul_def, bivector_mul_ι_left huw,
    ι_mul_bivector, ι_right_mul_bivector huw, sq, Complex.mul_re, Complex.mul_im]
  linear_combination (norm := module)
    Circle.re_sq_add_im_sq z • ((-(z : ℂ).re) • ι Q u + ((z : ℂ).im * Q u) • ι Q w) +
      h • ((-2 * (z : ℂ).re * (z : ℂ).im ^ 2) • ι Q u)

/-- **`spinCircle` rotates its plane, second vector.** The circle element `z` moves `w` to
`Re (z²) w + Im (z²) Q w u`; for `Q w = -1` this is the rotation of `w` away from `u` by `z²`. -/
theorem spinVectorAction_spinCircle_right (z : Circle) :
    spinVectorAction Q (spinCircle Q u w huw h z) w =
      ((z : ℂ) ^ 2).re • w + (((z : ℂ) ^ 2).im * Q w) • u := by
  apply spinVectorAction_eq_of_mul_ι_eq
  simp only [coe_spinCircle, map_add, map_smul, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, ← Algebra.commutes, ← Algebra.smul_def, bivector_mul_ι_right,
    ι_mul_bivector, ι_right_mul_bivector huw, sq, Complex.mul_re, Complex.mul_im]
  linear_combination (norm := module)
    Circle.re_sq_add_im_sq z • ((-(z : ℂ).re) • ι Q w - ((z : ℂ).im * Q w) • ι Q u) +
      h • ((-2 * (z : ℂ).re * (z : ℂ).im ^ 2) • ι Q w)

/-- **`spinCircle` fixes the orthogonal complement of its plane.** -/
theorem spinVectorAction_spinCircle_of_isOrtho {v : V} (hu : Q.IsOrtho u v)
    (hw : Q.IsOrtho w v) (z : Circle) : spinVectorAction Q (spinCircle Q u w huw h z) v = v := by
  apply spinVectorAction_eq_of_mul_ι_eq
  rw [coe_spinCircle]
  exact ((Algebra.commute_algebraMap_left _ _).add_left
    ((commute_ι_mul_ι_ι_of_isOrtho hu hw).smul_left _)).eq

end VectorAction

end

end CliffordAlgebra

namespace QuadraticMap.Isometry

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {Q : QuadraticForm ℝ V} {P : QuadraticForm ℝ W} {u w : V}

/-- **Quadratic isometries carry circle subgroups to circle subgroups**: the Spin-group map
induced by `f` sends `Re z + Im z ι u ι w` to `Re z + Im z ι (f u) ι (f w)`. -/
theorem spinGroupMap_spinCircle (f : Q →qᵢ P) (huw : Q.IsOrtho u w) (h : Q u * Q w = 1)
    (huw' : P.IsOrtho (f u) (f w)) (h' : P (f u) * P (f w) = 1) (z : Circle) :
    f.spinGroupMap (CliffordAlgebra.spinCircle Q u w huw h z) =
      CliffordAlgebra.spinCircle P (f u) (f w) huw' h' z := by
  apply Subtype.ext
  simp

end QuadraticMap.Isometry
