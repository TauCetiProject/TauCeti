/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# The unit circle: the unit sphere of `ℂ`, the exponential and the coordinate function

Mathlib's unit circle `Circle` is a type synonym for the unit sphere `sphere (0 : ℂ) 1`, carrying
its group structure.  This file records the identification as a homeomorphism, so that results
stated for unit spheres of real normed spaces (such as their CW structures) apply to `Circle`
without unfolding the synonym.

It also packages the exponential `t ↦ exp (i t)` as a continuous homomorphism from the real line,
and records that the coordinate function `z ↦ z` is a unitary element of `C(S¹, ℂ)`. Finally,
it parametrizes the upper semicircle by the real part, so that the circle is two closed intervals
glued at their endpoints `±1`.

## Main declarations

* `Circle.homeomorphSphere`: `Circle ≃ₜ sphere (0 : ℂ) 1`, the identity on underlying complex
  numbers.
* `Circle.expContinuousMonoidHom`: `t ↦ exp (i t)` as a continuous homomorphism
  `Multiplicative ℝ →ₜ* Circle`.
* `Circle.coordinate`: the coordinate function `z ↦ z` in `C(S¹, ℂ)`, and
  `Circle.coordinate_mem_unitary`.
* `Circle.re_sq_add_im_sq` and `Circle.coe_add_inv_coe`: `Re z ^ 2 + Im z ^ 2 = 1` and
  `z + z⁻¹ = 2 Re z` on the circle, and `Complex.re_sq_add_im_sq_of_mem_sphere`, the first
  identity for a point of `sphere (0 : ℂ) 1`.
* `Complex.zpow_mul_conj_zpow_of_mem_sphere`: `z ^ k * conj (z ^ m) = z ^ (k - m)` for a point
  of `sphere (0 : ℂ) 1`.
* `Circle.exp_pow_eq_neg_one` and `Circle.mixed_power_rotation_factor`: power identities for
  complex exponentials on the circle.
* `Circle.exists_pow_nat_eq`: every point of the circle has an `n`-th root on the circle.
* `Circle.exp_pow_eq_one_iff`: `exp (i θ)` is an `n`-th root of unity exactly when `θ` is an
  integer multiple of `2π / n`.
* `Circle.exp_neg_arg_mul_self`: rotating `x : ℂ` by `exp (-i arg x)` gives `‖x‖`.
* `Circle.inv_eq_self_iff`: the points of the circle equal to their inverses are `1` and `-1`.
* `Circle.im_coe_eq_zero_iff`: the real points of the circle are `1` and `-1`.
* `Circle.upperSemicircle`: the parametrization `x ↦ x + √(1 - x²) I` of the upper semicircle by
  `[-1, 1]`; with its inverse it covers the circle (`Circle.exists_upperSemicircle_eq_or_inv_eq`),
  meeting the lower semicircle only at `±1` (`Circle.upperSemicircle_eq_inv_iff`).
* `Circle.differentiableAt_coe_inv`: the pointwise inverse of a differentiable circle-valued map
  is differentiable.
-/

public section

noncomputable section

open Metric
open scoped ComplexConjugate

namespace Circle

/-- The unit circle `Circle` is homeomorphic to the unit sphere `sphere (0 : ℂ) 1`, by the identity
on underlying complex numbers. -/
def homeomorphSphere : Circle ≃ₜ sphere (0 : ℂ) 1 :=
  Homeomorph.refl _

@[simp]
theorem coe_homeomorphSphere_apply (z : Circle) : (homeomorphSphere z : ℂ) = z :=
  (rfl)

@[simp]
theorem coe_homeomorphSphere_symm_apply (z : sphere (0 : ℂ) 1) :
    (homeomorphSphere.symm z : ℂ) = z :=
  (rfl)

/-- The real and imaginary parts of a point of the circle satisfy `Re z ^ 2 + Im z ^ 2 = 1`. -/
theorem re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  simpa [Complex.normSq_apply, sq] using normSq_coe z

/-- The real and imaginary parts of a point of the unit sphere of `ℂ` satisfy
`Re z ^ 2 + Im z ^ 2 = 1`. -/
theorem _root_.Complex.re_sq_add_im_sq_of_mem_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    z.re ^ 2 + z.im ^ 2 = 1 := by
  simpa using re_sq_add_im_sq (homeomorphSphere.symm ⟨z, hz⟩)

/-- On the unit sphere of `ℂ`, conjugation inverts integer powers:
`z ^ k * conj (z ^ m) = z ^ (k - m)`. -/
theorem _root_.Complex.zpow_mul_conj_zpow_of_mem_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1)
    (k m : ℤ) : z ^ k * conj (z ^ m) = z ^ (k - m) := by
  have hz1 : ‖z‖ = 1 := by simpa using hz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  rw [map_zpow₀, ← Complex.inv_eq_conj hz1, inv_zpow', ← zpow_add₀ hz0, sub_eq_add_neg]

/-- For a point of the circle, `z + z⁻¹ = 2 Re z`. -/
theorem coe_add_inv_coe (z : Circle) : (z : ℂ) + (z : ℂ)⁻¹ = 2 * (z : ℂ).re := by
  rw [← coe_inv, coe_inv_eq_conj, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- Raising `exp (π * I / d)` to a nonzero natural power `d` gives `-1`. -/
theorem exp_pow_eq_neg_one (d : ℕ) (hd : d ≠ 0) :
    (Circle.exp (Real.pi / d) : ℂ) ^ d = -1 := by
  rw [Circle.coe_exp, ← Complex.exp_nat_mul]
  have hmul : (d : ℂ) * (↑(Real.pi / d) * Complex.I) = Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [hmul, Complex.exp_pi_mul_I]

/-- For distinct natural powers, rotation by `exp (π * I / |p - q|)` negates their mixed
  power. -/
theorem mixed_power_rotation_factor {p q : ℕ} (hpq : p ≠ q) :
    (Circle.exp (Real.pi / (if p < q then q - p else p - q)) : ℂ) ^ p *
      conj (Circle.exp (Real.pi / (if p < q then q - p else p - q)) : ℂ) ^ q = -1 := by
  let d := if p < q then q - p else p - q
  have hd : d ≠ 0 := by
    dsimp [d]
    split_ifs with h
    · exact Nat.sub_ne_zero_of_lt h
    · exact Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hpq))
  have hcases : p < q ∨ q < p := lt_or_gt_of_ne hpq
  let u : Circle := Circle.exp (Real.pi / d)
  have huk : (u : ℂ) ^ d = -1 := by
    simpa [u] using exp_pow_eq_neg_one d hd
  have hconj : conj (u : ℂ) = (u : ℂ)⁻¹ := (Circle.coe_inv_eq_conj u).symm
  have hfactor : (u : ℂ) ^ p * conj (u : ℂ) ^ q = -1 := by
    rcases hcases with hpq' | hqp'
    · have hq : q = p + d := by
        simpa [d, hpq', Nat.add_comm] using (Nat.sub_add_cancel (Nat.le_of_lt hpq')).symm
      rw [hconj, hq, pow_add, inv_pow, inv_pow]
      calc
        (u : ℂ) ^ p * (((u : ℂ) ^ p)⁻¹ * ((u : ℂ) ^ d)⁻¹) =
            ((u : ℂ) ^ p * ((u : ℂ) ^ p)⁻¹) * ((u : ℂ) ^ d)⁻¹ := by rw [← mul_assoc]
        _ = ((u : ℂ) ^ d)⁻¹ := by field_simp
        _ = -1 := by rw [huk]; norm_num
    · have hp : p = q + d := by
        simpa [d, not_lt_of_ge (le_of_lt hqp'), Nat.add_comm] using
          (Nat.sub_add_cancel (Nat.le_of_lt hqp')).symm
      rw [hconj, hp, pow_add, inv_pow]
      calc
        ((u : ℂ) ^ q * (u : ℂ) ^ d) * ((u : ℂ) ^ q)⁻¹ = (u : ℂ) ^ d := by field_simp
        _ = -1 := huk
  simpa only [u, d] using hfactor

/-- Every point of the circle has an `n`-th root on the circle, for `n ≠ 0`: `exp (i arg z / n)`.
-/
theorem exists_pow_nat_eq (z : Circle) {n : ℕ} (hn : n ≠ 0) : ∃ y : Circle, y ^ n = z :=
  ⟨exp (Complex.arg z / n), by
    rw [← exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), exp_arg]⟩

/-- **The `n`-th roots of unity among the exponentials.** For `n ≠ 0`, `exp (i θ) ^ n = 1` exactly
when `θ` is an integer multiple of `2π / n`. -/
theorem exp_pow_eq_one_iff {n : ℕ} (hn : n ≠ 0) {θ : ℝ} :
    exp θ ^ n = 1 ↔ ∃ m : ℤ, θ = m * (2 * Real.pi / n) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← exp_natCast_mul, exp_eq_one]
  refine exists_congr fun m ↦ ?_
  rw [mul_div_assoc', eq_div_iff hn', mul_comm θ]

/-- Rotating a complex number by minus its argument puts it on the nonnegative real axis. -/
theorem exp_neg_arg_mul_self (x : ℂ) : (exp (-Complex.arg x) : ℂ) * x = ‖x‖ := by
  rw [coe_exp]
  nth_rewrite 2 [← Complex.norm_mul_exp_arg_mul_I x]
  rw [mul_left_comm, ← Complex.exp_add]
  push_cast
  rw [neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]

/-- The pointwise inverse of a circle-valued map that is differentiable at `z`, as a map into `ℂ`,
is differentiable at `z`. -/
theorem differentiableAt_coe_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → Circle} {z : E} (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z) :
    DifferentiableAt ℝ (fun w ↦ ((u⁻¹ w : Circle) : ℂ)) z := by
  simpa only [Pi.inv_apply, coe_inv_eq_conj, Function.comp_def, Complex.conjCLE_apply] using
    Complex.conjCLE.differentiableAt.comp z hu

/-- The map `t ↦ exp (i t)` from the real line to the circle, as a continuous homomorphism
from `Multiplicative ℝ`. -/
def expContinuousMonoidHom : ContinuousMonoidHom (Multiplicative ℝ) Circle where
  toFun t := Circle.exp t.toAdd
  map_one' := Circle.exp_zero
  map_mul' _ _ := Circle.exp_add _ _
  continuous_toFun := Circle.exp.continuous.comp continuous_toAdd

@[simp]
theorem expContinuousMonoidHom_apply (t : Multiplicative ℝ) :
    expContinuousMonoidHom t = Circle.exp t.toAdd :=
  (rfl)

/-- The coordinate function `z ↦ z` on the circle. -/
def coordinate : C(Circle, ℂ) :=
  ⟨(↑), by fun_prop⟩

@[simp]
theorem coordinate_apply (z : Circle) : coordinate z = z :=
  (rfl)

@[simp]
theorem star_coordinate_mul : star coordinate * coordinate = 1 := by
  ext z
  simp [Complex.conj_mul']

@[simp]
theorem coordinate_mul_star : coordinate * star coordinate = 1 := by
  rw [mul_comm, star_coordinate_mul]

/-- The coordinate function is a unitary element of `C(S¹, ℂ)`. -/
theorem coordinate_mem_unitary : coordinate ∈ unitary C(Circle, ℂ) :=
  ⟨star_coordinate_mul, coordinate_mul_star⟩

/-- A point of the circle is its own inverse exactly when it is `1` or `-1`. -/
theorem inv_eq_self_iff (v : Circle) : v⁻¹ = v ↔ v = 1 ∨ v = -1 := by
  simp [inv_eq_iff_mul_eq_one, ← Circle.coe_inj, mul_self_eq_one_iff]

/-- A point of the circle is real exactly when it is `1` or `-1`. -/
theorem im_coe_eq_zero_iff (v : Circle) : (v : ℂ).im = 0 ↔ v = 1 ∨ v = -1 := by
  -- Being real means being fixed by conjugation, which on the circle is inversion.
  rw [← inv_eq_self_iff, ← coe_inj, coe_inv_eq_conj, Complex.conj_eq_iff_im]

/-! ### The upper semicircle -/

/-- The point `x + √(1 - x²) I` of the upper unit semicircle, for `-1 ≤ x ≤ 1`. Together with
its inverse, the point `x - √(1 - x²) I` of the lower semicircle, it parametrizes the circle by
its real part. -/
def upperSemicircle (x : Set.Icc (-1 : ℝ) 1) : Circle :=
  ⟨(x : ℝ) + √(1 - (x : ℝ) ^ 2) * Complex.I, mem_sphere_zero_iff_norm.2 (by
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by nlinarith [x.2.1, x.2.2]), add_sub_cancel,
      Real.sqrt_one])⟩

theorem coe_upperSemicircle (x : Set.Icc (-1 : ℝ) 1) :
    (upperSemicircle x : ℂ) = (x : ℝ) + √(1 - (x : ℝ) ^ 2) * Complex.I :=
  (rfl)

@[simp]
theorem re_upperSemicircle (x : Set.Icc (-1 : ℝ) 1) : (upperSemicircle x : ℂ).re = x := by
  simp [coe_upperSemicircle]

@[simp]
theorem im_upperSemicircle (x : Set.Icc (-1 : ℝ) 1) :
    (upperSemicircle x : ℂ).im = √(1 - (x : ℝ) ^ 2) := by
  simp [coe_upperSemicircle]

@[fun_prop]
theorem continuous_upperSemicircle : Continuous upperSemicircle :=
  Continuous.subtype_mk (by fun_prop) _

theorem upperSemicircle_injective : Function.Injective upperSemicircle := fun x y h ↦
  Subtype.ext (by rw [← re_upperSemicircle x, ← re_upperSemicircle y, h])

/-- The endpoints `±1` of the upper semicircle are their own inverses. -/
theorem inv_upperSemicircle_of_sq_eq_one {x : Set.Icc (-1 : ℝ) 1} (hx : (x : ℝ) ^ 2 = 1) :
    (upperSemicircle x)⁻¹ = upperSemicircle x :=
  Circle.ext (by rw [coe_inv_eq_conj]; simp [coe_upperSemicircle, hx])

/-- The upper semicircle meets the lower one only at its endpoints `±1`. -/
theorem upperSemicircle_eq_inv_iff {x y : Set.Icc (-1 : ℝ) 1} :
    upperSemicircle x = (upperSemicircle y)⁻¹ ↔ x = y ∧ (x : ℝ) ^ 2 = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hre := congrArg (fun v : Circle ↦ (v : ℂ).re) h
    have him := congrArg (fun v : Circle ↦ (v : ℂ).im) h
    simp only [coe_inv_eq_conj, Complex.conj_re, Complex.conj_im, re_upperSemicircle,
      im_upperSemicircle] at hre him
    obtain rfl : x = y := Subtype.ext hre
    refine ⟨rfl, ?_⟩
    have h0 : √(1 - (x : ℝ) ^ 2) = 0 := by linarith [Real.sqrt_nonneg (1 - (x : ℝ) ^ 2)]
    nlinarith [Real.sqrt_eq_zero'.1 h0, x.2.1, x.2.2]
  · rintro ⟨rfl, hx⟩
    exact (inv_upperSemicircle_of_sq_eq_one hx).symm

/-- Every point of the circle lies on the upper semicircle or on its inverse, the lower one. -/
theorem exists_upperSemicircle_eq_or_inv_eq (v : Circle) :
    ∃ x : Set.Icc (-1 : ℝ) 1, upperSemicircle x = v ∨ (upperSemicircle x)⁻¹ = v := by
  have hre : (v : ℂ).re ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 (by
    simpa using Complex.abs_re_le_norm (v : ℂ))
  have hsqrt : √(1 - (v : ℂ).re ^ 2) = |(v : ℂ).im| := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    linarith [re_sq_add_im_sq v]
  refine ⟨⟨(v : ℂ).re, hre⟩, ?_⟩
  rcases le_or_gt 0 (v : ℂ).im with him | him
  · left
    apply Circle.ext
    apply Complex.ext
    · simp
    · simp [hsqrt, abs_of_nonneg him]
  · right
    apply Circle.ext
    apply Complex.ext
    · simp
    · simp [hsqrt, abs_of_neg him]

end Circle
