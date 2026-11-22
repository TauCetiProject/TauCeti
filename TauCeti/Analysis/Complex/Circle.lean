/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.Path
public import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The unit circle: the unit sphere of `ℂ`, the exponential and the coordinate function

Mathlib's unit circle `Circle` is a type synonym for the unit sphere `sphere (0 : ℂ) 1`, carrying
its group structure.  This file records the identification as a homeomorphism, so that results
stated for unit spheres of real normed spaces (such as their CW structures) apply to `Circle`
without unfolding the synonym.

It also packages the exponential `t ↦ exp (i t)` as a continuous homomorphism from the real line,
computes its velocity `i exp (i t)`, and records that the coordinate function `z ↦ z` is a
unitary element of `C(S¹, ℂ)`. Finally, it parametrizes the upper semicircle by the real part, so
that the circle is two closed intervals glued at their endpoints `±1`, and packages the resulting
upper and lower semicircle paths from `1` to `-1` in `ℂ`.

## Main declarations

* `Circle.homeomorphSphere`: `Circle ≃ₜ sphere (0 : ℂ) 1`, the identity on underlying complex
  numbers, with `Circle.coe_homeomorphSphere_exp_re` and `Circle.coe_homeomorphSphere_exp_im`
  computing the real and imaginary parts of `exp (i x)` on the sphere.
* `Circle.expContinuousMonoidHom`: `t ↦ exp (i t)` as a continuous homomorphism
  `Multiplicative ℝ →ₜ* Circle`.
* `Circle.coordinate`: the coordinate function `z ↦ z` in `C(S¹, ℂ)`, and
  `Circle.coordinate_mem_unitary`.
* `Circle.re_sq_add_im_sq` and `Circle.coe_add_inv_coe`: `Re z ^ 2 + Im z ^ 2 = 1` and
  `z + z⁻¹ = 2 Re z` on the circle, and `Complex.re_sq_add_im_sq_of_mem_sphere`, the first
  identity for a point of `sphere (0 : ℂ) 1`.
* `Complex.zpow_mul_conj_zpow_of_mem_sphere`: `z ^ k * conj (z ^ m) = z ^ (k - m)` for a point
  of `sphere (0 : ℂ) 1`, and `Complex.zpow_mul_conj_sub_eq_neg_of_mem_sphere`: there
  `z ^ k * conj a - a = -(z ^ k * conj (z ^ k * conj a - a))`.
* `Circle.exp_pow_eq_neg_one` and `Circle.mixed_power_rotation_factor`: power identities for
  complex exponentials on the circle.
* `Circle.exists_pow_nat_eq`: every point of the circle has an `n`-th root on the circle.
* `Circle.exp_pow_eq_one_iff`: `exp (i θ)` is an `n`-th root of unity exactly when `θ` is an
  integer multiple of `2π / n`.
* `Circle.isOfFinOrder_exp_two_pi_mul_iff`: `exp (2π i x)` has finite order exactly when `x` is
  rational.
* `Circle.denseRange_zpow_of_not_isOfFinOrder`: the integer powers of a point of infinite order are
  dense in the circle.
* `Circle.exp_neg_arg_mul_self`: rotating `x : ℂ` by `exp (-i arg x)` gives `‖x‖`.
* `Circle.inv_eq_self_iff`: the points of the circle equal to their inverses are `1` and `-1`.
* `Circle.im_coe_eq_zero_iff`: the real points of the circle are `1` and `-1`.
* `Circle.upperSemicircle`: the parametrization `x ↦ x + √(1 - x²) I` of the upper semicircle by
  `[-1, 1]`; with its inverse it covers the circle (`Circle.exists_upperSemicircle_eq_or_inv_eq`),
  meeting the lower semicircle only at `±1` (`Circle.upperSemicircle_eq_inv_iff`).
* `Circle.semicircleCoord`: the affine homeomorphism `[0, 1] ≃ₜ [-1, 1]` sending `t` to `1 - 2t`.
* `TauCeti.upperSemicirclePath`, `TauCeti.lowerSemicirclePath`, `TauCeti.circleParam`,
  `TauCeti.mem_range_upperSemicirclePath_iff`, `TauCeti.mem_range_lowerSemicirclePath_iff`: the
  upper and lower semicircle paths from `1` to `-1` in `ℂ`, their range characterizations, and
  their shared real-part inverse.
* `Circle.differentiableAt_coe_inv`: the pointwise inverse of a differentiable circle-valued map
  is differentiable.
* `Circle.coe_mem_unitary` and `TauCeti.circleEquivUnitary`: inclusion of `Circle` into
  `unitary ℂ` and the topological group isomorphism `Circle ≃ₜ* unitary ℂ`.
* `TauCeti.hasDerivAt_coe_circleExp`: the velocity of `t ↦ exp (t i)` at `t` is `i exp (t i)`.
* `TauCeti.hasFDerivAt_circleExp_mul_ofReal` and `TauCeti.fderiv_circleExp_mul_ofReal_apply`: the
  differential of a map `e^{iθ} r` in polar form, with real-valued angle `θ` and radius `r`, is
  `e^{iθ} (dr + i r dθ)`.
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

/-- The real part of `exp (i x)`, read on the unit sphere of `ℂ`, is `cos x`. -/
theorem coe_homeomorphSphere_exp_re (x : ℝ) : (homeomorphSphere (exp x) : ℂ).re = Real.cos x := by
  rw [coe_homeomorphSphere_apply, coe_exp]
  exact Complex.exp_ofReal_mul_I_re x

/-- The imaginary part of `exp (i x)`, read on the unit sphere of `ℂ`, is `sin x`. -/
theorem coe_homeomorphSphere_exp_im (x : ℝ) : (homeomorphSphere (exp x) : ℂ).im = Real.sin x := by
  rw [coe_homeomorphSphere_apply, coe_exp]
  exact Complex.exp_ofReal_mul_I_im x

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

/-- On the unit sphere of `ℂ`, `z ^ k * conj a - a` is fixed by `b ↦ -(z ^ k * conj b)`: at
`z = e^{iθ}` it lies on the line `i e^{ikθ/2} ℝ`. -/
theorem _root_.Complex.zpow_mul_conj_sub_eq_neg_of_mem_sphere {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) (k : ℤ) (a : ℂ) :
    z ^ k * conj a - a = -(z ^ k * conj (z ^ k * conj a - a)) := by
  rw [map_sub, map_mul, Complex.conj_conj, mul_sub, ← mul_assoc,
    Complex.zpow_mul_conj_zpow_of_mem_sphere hz, sub_self, zpow_zero]
  ring

/-- For a point of the circle, `z + z⁻¹ = 2 Re z`. -/
theorem coe_add_inv_coe (z : Circle) : (z : ℂ) + (z : ℂ)⁻¹ = 2 * (z : ℂ).re := by
  rw [← coe_inv, coe_inv_eq_conj, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- Raising `exp (π * I / d)` to a nonzero natural power `d` gives `-1`. -/
theorem exp_pow_eq_neg_one (d : ℕ) (hd : d ≠ 0) :
    (Circle.exp (Real.pi / d) : ℂ) ^ d = -1 := by
  rw [Circle.coe_exp, ← Complex.exp_natCast_mul]
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

/-- **Rational rotations.** `exp (2π i x)` has finite order in the circle group exactly when `x` is
rational. -/
theorem isOfFinOrder_exp_two_pi_mul_iff {x : ℝ} :
    IsOfFinOrder (exp (2 * Real.pi * x)) ↔ ¬Irrational x := by
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  rw [isOfFinOrder_iff_pow_eq_one, Irrational, not_not]
  constructor
  · rintro ⟨n, hn, hpow⟩
    obtain ⟨m, hm⟩ := (exp_pow_eq_one_iff hn.ne').1 hpow
    refine ⟨m / n, ?_⟩
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [mul_div_assoc', eq_div_iff hn'] at hm
    push_cast
    rw [div_eq_iff hn']
    exact mul_left_cancel₀ hπ (by linear_combination -hm)
  · rintro ⟨q, rfl⟩
    refine ⟨q.den, q.den_pos, (exp_pow_eq_one_iff q.den_ne_zero).2 ⟨q.num, ?_⟩⟩
    have hd : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 q.den_ne_zero
    rw [Rat.cast_def]
    field_simp

/-- **Irrational rotations have dense orbits.** The integer powers of a point of the circle of
infinite order are dense in the circle. -/
theorem denseRange_zpow_of_not_isOfFinOrder {c : Circle} (hc : ¬IsOfFinOrder c) :
    DenseRange (c ^ · : ℤ → Circle) := by
  set x := Complex.arg c / (2 * Real.pi)
  have hcx : exp (2 * Real.pi * x) = c := by
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), exp_arg]
  have hx : Irrational x := by
    by_contra h
    exact hc (hcx ▸ isOfFinOrder_exp_two_pi_mul_iff.2 h)
  have hd : DenseRange (· • (x : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) :=
    AddCircle.denseRange_zsmul_coe_iff.2 (by simpa using hx)
  have hsurj : Function.Surjective (AddCircle.toCircle : AddCircle (1 : ℝ) → Circle) := by
    simpa only [← funext (AddCircle.homeomorphCircle_apply one_ne_zero)] using
      (AddCircle.homeomorphCircle (one_ne_zero (α := ℝ))).surjective
  convert hsurj.denseRange.comp hd AddCircle.continuous_toCircle using 1
  funext k
  simp [AddCircle.toCircle_zsmul, AddCircle.toCircle_apply_mk, hcx]

/-- Rotating a complex number by minus its argument puts it on the nonnegative real axis. -/
theorem exp_neg_arg_mul_self (x : ℂ) : (exp (-Complex.arg x) : ℂ) * x = ‖x‖ := by
  rw [coe_exp]
  nth_rewrite 2 [← Complex.norm_mul_exp_arg_mul_I x]
  rw [mul_left_comm, ← Complex.exp_add]
  push_cast
  rw [neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]

/-- For unit complex numbers, `a⁻¹ b - 1 = a⁻¹ (b - a)`. -/
theorem coe_inv_mul_sub_one (a b : Circle) :
    ((a⁻¹ * b : Circle) : ℂ) - 1 = ((a⁻¹ : Circle) : ℂ) * ((b : ℂ) - a) := by
  rw [mul_sub, ← coe_mul, ← coe_mul, inv_mul_cancel, coe_one]

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
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by nlinarith [x.property.1, x.property.2]),
        add_sub_cancel,
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
    nlinarith [Real.sqrt_eq_zero'.1 h0, x.property.1, x.property.2]
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

/-- Every point of `Circle` belongs to `unitary ℂ`. -/
theorem coe_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ := by
  simp [Unitary.mem_iff_self_mul_star, RCLike.star_def, RCLike.mul_conj]

/-- The affine homeomorphism `t ↦ 1 - 2 * t` from `unitInterval` onto `[-1, 1]`. -/
def semicircleCoord : unitInterval ≃ₜ Set.Icc (-1 : ℝ) 1 :=
  unitInterval.symmHomeomorph.trans (iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm

theorem coe_semicircleCoord (t : unitInterval) :
    (semicircleCoord t : ℝ) = 1 - 2 * (t : ℝ) := by
  simp only [semicircleCoord, Homeomorph.trans_apply, unitInterval.symmHomeomorph_apply,
    iccHomeoI_symm_apply_coe, unitInterval.coe_symm_eq]
  ring

theorem coe_semicircleCoord_symm (x : Set.Icc (-1 : ℝ) 1) :
    (semicircleCoord.symm x : ℝ) = (1 - (x : ℝ)) / 2 := by
  have h := congrArg Subtype.val (semicircleCoord.apply_symm_apply x)
  rw [coe_semicircleCoord] at h
  linarith

@[simp]
theorem coe_semicircleCoord_zero : (semicircleCoord 0 : ℝ) = 1 := by
  simp [coe_semicircleCoord]

@[simp]
theorem coe_semicircleCoord_one : (semicircleCoord 1 : ℝ) = -1 := by
  simp [coe_semicircleCoord]; norm_num

end Circle

namespace TauCeti

open Complex Set

/-- The unit circle `Circle` in `ℂ` is topologically isomorphic as a group to `unitary ℂ`. -/
def circleEquivUnitary : Circle ≃ₜ* unitary ℂ where
  toFun z := ⟨(z : ℂ), z.coe_mem_unitary⟩
  invFun u := ⟨(u : ℂ), mem_sphere_zero_iff_norm.2 <| CStarRing.norm_of_mem_unitary u.property⟩
  left_inv _ := Circle.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtypeVal : Continuous ((↑) : Circle → ℂ)) Circle.coe_mem_unitary
  continuous_invFun := Continuous.subtype_mk continuous_subtypeVal _

@[simp]
theorem coe_circleEquivUnitary (z : Circle) : (circleEquivUnitary z : ℂ) = z :=
  (rfl)

@[simp]
theorem coe_circleEquivUnitary_symm (u : unitary ℂ) : (circleEquivUnitary.symm u : ℂ) = u :=
  (rfl)

/-- Read in `ℂ`, the circle exponential `t ↦ exp (t i)` has velocity `i exp (t i)`. -/
theorem hasDerivAt_coe_circleExp (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ((Circle.exp s : Circle) : ℂ)) (I * Circle.exp t) t := by
  simp only [Circle.coe_exp]
  simpa [mul_comm] using ((ofRealCLM.hasDerivAt (x := t)).mul_const I).cexp

/-! ### Semicircle paths on the unit circle -/

/-- The upper semicircle path from `1` to `-1` in `ℂ`. -/
def upperSemicirclePath : Path (1 : ℂ) (-1 : ℂ) where
  toFun t := Circle.upperSemicircle (Circle.semicircleCoord t)
  continuous_toFun := continuous_subtypeVal.comp
    (Circle.continuous_upperSemicircle.comp Circle.semicircleCoord.continuous)
  source' := Complex.ext (by simp) (by simp)
  target' := Complex.ext (by simp) (by simp)

/-- The lower semicircle path from `1` to `-1` in `ℂ`. -/
def lowerSemicirclePath : Path (1 : ℂ) (-1 : ℂ) where
  toFun t := ((Circle.upperSemicircle (Circle.semicircleCoord t))⁻¹ : Circle)
  continuous_toFun := continuous_subtypeVal.comp
    (Circle.continuous_upperSemicircle.comp Circle.semicircleCoord.continuous).inv
  source' := Complex.ext (by simp) (by simp)
  target' := Complex.ext (by simp) (by simp)

theorem upperSemicirclePath_apply (t : unitInterval) :
    upperSemicirclePath t = Circle.upperSemicircle (Circle.semicircleCoord t) :=
  (rfl)

theorem lowerSemicirclePath_apply (t : unitInterval) :
    lowerSemicirclePath t = ((Circle.upperSemicircle (Circle.semicircleCoord t))⁻¹ : Circle) :=
  (rfl)

theorem upperSemicirclePath_mem_sphere (t : unitInterval) :
    upperSemicirclePath t ∈ sphere (0 : ℂ) 1 :=
  (Circle.upperSemicircle (Circle.semicircleCoord t)).property

theorem lowerSemicirclePath_mem_sphere (t : unitInterval) :
    lowerSemicirclePath t ∈ sphere (0 : ℂ) 1 :=
  ((Circle.upperSemicircle (Circle.semicircleCoord t))⁻¹).property

theorem upperSemicirclePath_im_nonneg (t : unitInterval) :
    0 ≤ (upperSemicirclePath t).im := by
  rw [upperSemicirclePath_apply, Circle.im_upperSemicircle]
  exact Real.sqrt_nonneg _

theorem lowerSemicirclePath_im_nonpos (t : unitInterval) :
    (lowerSemicirclePath t).im ≤ 0 := by
  rw [lowerSemicirclePath_apply, Circle.coe_inv_eq_conj, conj_im, Circle.im_upperSemicircle]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

theorem upperSemicirclePath_injective : Function.Injective upperSemicirclePath := fun _ _ h ↦
  Circle.semicircleCoord.injective (Circle.upperSemicircle_injective (Circle.coe_injective h))

theorem lowerSemicirclePath_injective : Function.Injective lowerSemicirclePath := fun _ _ h ↦
  Circle.semicircleCoord.injective
    (Circle.upperSemicircle_injective (inv_injective (Circle.coe_injective h)))

/-- The upper and lower semicircle paths cover the unit circle. -/
theorem range_upperSemicirclePath_union_lowerSemicirclePath :
    range upperSemicirclePath ∪ range lowerSemicirclePath = sphere (0 : ℂ) 1 := by
  refine Subset.antisymm (union_subset (range_subset_iff.mpr upperSemicirclePath_mem_sphere)
    (range_subset_iff.mpr lowerSemicirclePath_mem_sphere)) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := Circle.exists_upperSemicircle_eq_or_inv_eq ⟨z, hz⟩
  rcases hx with hx | hx
  · exact Or.inl ⟨Circle.semicircleCoord.symm x, by
      simpa [upperSemicirclePath_apply] using congrArg Subtype.val hx⟩
  · exact Or.inr ⟨Circle.semicircleCoord.symm x, by
      simpa [lowerSemicirclePath_apply] using congrArg Subtype.val hx⟩

/-- The upper and lower semicircle paths meet only at `1` and `-1`. -/
theorem range_upperSemicirclePath_inter_lowerSemicirclePath :
    range upperSemicirclePath ∩ range lowerSemicirclePath = {1, -1} := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
    obtain ⟨_, hsq⟩ := Circle.upperSemicircle_eq_inv_iff.mp (Circle.coe_injective hst.symm)
    rcases sq_eq_one_iff.mp hsq with hs1 | hs1
    · have hs : s = 0 := Circle.semicircleCoord.injective (Subtype.ext (by simp [hs1]))
      exact Or.inl (hs ▸ upperSemicirclePath.source)
    · have hs : s = 1 := Circle.semicircleCoord.injective (Subtype.ext (by simp [hs1]))
      exact Or.inr (hs ▸ upperSemicirclePath.target)
  · rintro z (rfl | rfl)
    · exact ⟨upperSemicirclePath.source_mem_range, lowerSemicirclePath.source_mem_range⟩
    · exact ⟨upperSemicirclePath.target_mem_range, lowerSemicirclePath.target_mem_range⟩

/-- The semicircle parameter `(1 - u.re) / 2 ∈ unitInterval` on the unit circle. -/
def circleParam (u : sphere (0 : ℂ) 1) : unitInterval :=
  Circle.semicircleCoord.symm ⟨(u : ℂ).re, abs_le.1 (by simpa using abs_re_le_norm (u : ℂ))⟩

theorem coe_circleParam (u : sphere (0 : ℂ) 1) :
    (circleParam u : ℝ) = (1 - (u : ℂ).re) / 2 :=
  Circle.coe_semicircleCoord_symm _

@[simp]
theorem coe_semicircleCoord_circleParam (u : sphere (0 : ℂ) 1) :
    (Circle.semicircleCoord (circleParam u) : ℝ) = (u : ℂ).re := by
  simp [circleParam]

@[fun_prop]
theorem continuous_circleParam : Continuous circleParam :=
  Circle.semicircleCoord.symm.continuous.comp
    (Continuous.subtype_mk (continuous_re.comp continuous_subtypeVal) _)

@[simp]
theorem circleParam_upperSemicirclePath (t : unitInterval) :
    circleParam ⟨upperSemicirclePath t, upperSemicirclePath_mem_sphere t⟩ = t :=
  Circle.semicircleCoord.injective (Subtype.ext (by simp [upperSemicirclePath_apply]))

@[simp]
theorem circleParam_lowerSemicirclePath (t : unitInterval) :
    circleParam ⟨lowerSemicirclePath t, lowerSemicirclePath_mem_sphere t⟩ = t :=
  Circle.semicircleCoord.injective (Subtype.ext (by simp [lowerSemicirclePath_apply]))

theorem upperSemicirclePath_circleParam {u : sphere (0 : ℂ) 1} (hu : 0 ≤ (u : ℂ).im) :
    upperSemicirclePath (circleParam u) = u := by
  obtain ⟨x, hx | hx⟩ := Circle.exists_upperSemicircle_eq_or_inv_eq (Circle.homeomorphSphere.symm u)
  · set t := Circle.semicircleCoord.symm x
    have ht : (upperSemicirclePath t : ℂ) = u := by
      simpa [upperSemicirclePath_apply, t] using congrArg ((↑) : Circle → ℂ) hx
    have hp : circleParam u = t := by
      simpa [ht] using circleParam_upperSemicirclePath t
    rw [hp, ht]
  · set t := Circle.semicircleCoord.symm x
    have hl : (lowerSemicirclePath t : ℂ) = u := by
      simpa [lowerSemicirclePath_apply, t] using congrArg ((↑) : Circle → ℂ) hx
    have him0 : (u : ℂ).im = 0 := le_antisymm (hl ▸ lowerSemicirclePath_im_nonpos t) hu
    have ht : (upperSemicirclePath t : ℂ) = u := by
      calc
        upperSemicirclePath t = starRingEnd ℂ (lowerSemicirclePath t) := by
          rw [upperSemicirclePath_apply, lowerSemicirclePath_apply, Circle.coe_inv_eq_conj,
            starRingEnd_self_apply]
        _ = starRingEnd ℂ (u : ℂ) := by rw [hl]
        _ = u := Complex.conj_eq_iff_im.mpr him0
    have hp : circleParam u = t := by
      simpa [ht] using circleParam_upperSemicirclePath t
    rw [hp, ht]

theorem lowerSemicirclePath_circleParam {u : sphere (0 : ℂ) 1} (hu : (u : ℂ).im ≤ 0) :
    lowerSemicirclePath (circleParam u) = u := by
  obtain ⟨x, hx | hx⟩ := Circle.exists_upperSemicircle_eq_or_inv_eq (Circle.homeomorphSphere.symm u)
  · set t := Circle.semicircleCoord.symm x
    have hu' : (upperSemicirclePath t : ℂ) = u := by
      simpa [upperSemicirclePath_apply, t] using congrArg ((↑) : Circle → ℂ) hx
    have him0 : (u : ℂ).im = 0 := le_antisymm hu (hu' ▸ upperSemicirclePath_im_nonneg t)
    have ht : (lowerSemicirclePath t : ℂ) = u := by
      calc
        lowerSemicirclePath t = starRingEnd ℂ (upperSemicirclePath t) := by
          rw [lowerSemicirclePath_apply, upperSemicirclePath_apply, Circle.coe_inv_eq_conj]
        _ = starRingEnd ℂ (u : ℂ) := by rw [hu']
        _ = u := Complex.conj_eq_iff_im.mpr him0
    have hp : circleParam u = t := by
      simpa [ht] using circleParam_lowerSemicirclePath t
    rw [hp, ht]
  · set t := Circle.semicircleCoord.symm x
    have ht : (lowerSemicirclePath t : ℂ) = u := by
      simpa [lowerSemicirclePath_apply, t] using congrArg ((↑) : Circle → ℂ) hx
    have hp : circleParam u = t := by
      simpa [ht] using circleParam_lowerSemicirclePath t
    rw [hp, ht]

/-- A complex number lies on `TauCeti.upperSemicirclePath` iff it lies on the unit circle with
nonnegative imaginary part. -/
theorem mem_range_upperSemicirclePath_iff {z : ℂ} :
    z ∈ range upperSemicirclePath ↔ z ∈ sphere (0 : ℂ) 1 ∧ 0 ≤ z.im :=
  ⟨fun ⟨t, ht⟩ ↦ ht ▸ ⟨upperSemicirclePath_mem_sphere t, upperSemicirclePath_im_nonneg t⟩,
   fun ⟨hz, him⟩ ↦ ⟨circleParam ⟨z, hz⟩, upperSemicirclePath_circleParam him⟩⟩

/-- A complex number lies on `TauCeti.lowerSemicirclePath` iff it lies on the unit circle with
nonpositive imaginary part. -/
theorem mem_range_lowerSemicirclePath_iff {z : ℂ} :
    z ∈ range lowerSemicirclePath ↔ z ∈ sphere (0 : ℂ) 1 ∧ z.im ≤ 0 :=
  ⟨fun ⟨t, ht⟩ ↦ ht ▸ ⟨lowerSemicirclePath_mem_sphere t, lowerSemicirclePath_im_nonpos t⟩,
   fun ⟨hz, him⟩ ↦ ⟨circleParam ⟨z, hz⟩, lowerSemicirclePath_circleParam him⟩⟩

theorem circleParam_eq_zero_of_coe_eq_one {u : sphere (0 : ℂ) 1} (hu : (u : ℂ) = 1) :
    circleParam u = 0 := by
  apply Subtype.ext
  simp [coe_circleParam, hu]

theorem circleParam_eq_one_of_coe_eq_neg_one {u : sphere (0 : ℂ) 1} (hu : (u : ℂ) = -1) :
    circleParam u = 1 := by
  apply Subtype.ext
  simp [coe_circleParam, hu]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {θ r : E → ℝ}
  {θ' r' : E →L[ℝ] ℝ} {x : E}

/-- **The differential of a map in polar form.** If the angle `θ` and the radius `r` are
differentiable at `x`, then `f = e^{iθ} r` is differentiable at `x`, with differential
`df_x v = dr_x v • e^{iθ(x)} + dθ_x v • (r(x) i e^{iθ(x)})`. -/
theorem hasFDerivAt_circleExp_mul_ofReal (hθ : HasFDerivAt θ θ' x) (hr : HasFDerivAt r r' x) :
    HasFDerivAt (fun y ↦ (Circle.exp (θ y) : ℂ) * (r y : ℂ))
      (r'.smulRight (Circle.exp (θ x) : ℂ) +
        θ'.smulRight ((r x : ℂ) * I * Circle.exp (θ x))) x := by
  refine ((((ofRealCLM.hasFDerivAt.comp x hθ).mul_const' I).cexp.mul
      (ofRealCLM.hasFDerivAt.comp x hr)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ by simp [Circle.coe_exp])).congr_fderiv ?_
  ext v
  simp [Circle.coe_exp]
  ring

/-- The value of the differential of a map `e^{iθ} r` in polar form:
`df_x v = e^{iθ(x)} (dr_x v + i r(x) dθ_x v)`. -/
theorem fderiv_circleExp_mul_ofReal_apply (hθ : HasFDerivAt θ θ' x) (hr : HasFDerivAt r r' x)
    (v : E) :
    fderiv ℝ (fun y ↦ (Circle.exp (θ y) : ℂ) * (r y : ℂ)) x v =
      (Circle.exp (θ x) : ℂ) * ((r' v : ℂ) + (r x * θ' v : ℝ) * I) := by
  rw [(hasFDerivAt_circleExp_mul_ofReal hθ hr).fderiv]
  simp
  ring

end TauCeti
