/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.ContinuousMap.Star

/-!
# The unit circle: the unit sphere of `ℂ`, the exponential and the coordinate function

Mathlib's unit circle `Circle` is a type synonym for the unit sphere `sphere (0 : ℂ) 1`, carrying
its group structure.  This file records the identification as a homeomorphism, so that results
stated for unit spheres of real normed spaces (such as their CW structures) apply to `Circle`
without unfolding the synonym.

It also packages the exponential `t ↦ exp (i t)` as a continuous homomorphism from the real line,
and records that the coordinate function `z ↦ z` is a unitary element of `C(S¹, ℂ)`.

## Main declarations

* `Circle.homeomorphSphere`: `Circle ≃ₜ sphere (0 : ℂ) 1`, the identity on underlying complex
  numbers.
* `Circle.expContinuousMonoidHom`: `t ↦ exp (i t)` as a continuous homomorphism
  `Multiplicative ℝ →ₜ* Circle`.
* `Circle.coordinate`: the coordinate function `z ↦ z` in `C(S¹, ℂ)`, and
  `Circle.coordinate_mem_unitary`.
* `Circle.re_sq_add_im_sq` and `Circle.coe_add_inv_coe`: `Re z ^ 2 + Im z ^ 2 = 1` and
  `z + z⁻¹ = 2 Re z` on the circle.
* `Circle.exp_pow_eq_neg_one` and `Circle.mixed_power_rotation_factor`: power identities for
  complex exponentials on the circle.
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

end Circle
