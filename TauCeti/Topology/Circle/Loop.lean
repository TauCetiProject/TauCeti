/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Topology.Circle.AddCircle
import TauCeti.Algebra.Group.Pow

/-!
# Loops as maps out of the circle

The standard quotient `TauCeti.unitToCircle : C(I, Circle)`, `t ↦ exp (2πit)`, collapses the
endpoints `0` and `1` of the unit interval to `1 ∈ Circle` and maps `(0, 1)` bijectively onto
`Circle \ {1}`. A loop `γ : Path x x` closes up, so it factors through `unitToCircle`. The
factorization is `Path.toCircle γ : C(Circle, X)`: it sends `unitToCircle t = exp (2πit)` to `γ t`,
and the point `1` to `x`.

Maps out of a wedge of circles are assembled from maps out of the circles, so this is how loops
in a space give maps out of a wedge of circles.

In the other direction, the `(p, q)` curve `t ↦ (exp (2πipt), exp (2πiqt))` is the standard loop
on the torus `S¹ × S¹` winding `p` times around the first circle and `q` times around the second.

## Main definitions

* `TauCeti.unitToCircle`: the standard quotient `C(I, Circle)`, `t ↦ Circle.exp (2 * π * t)`.
* `Path.toCircle`: a loop, read as a map from the unit circle.
* `TauCeti.torusCurve p q`: the `(p, q)` curve on `S¹ × S¹`, a loop at `(1, 1)`.
* `TauCeti.torusGluing`: a torus homeomorphism given by a determinant-one integer matrix.

## Main results

* `TauCeti.unitToCircle_surjective`, `TauCeti.unitToCircle_eq_one_iff`,
  `TauCeti.eq_or_of_unitToCircle_eq`: quotient properties of `unitToCircle`.
* `Path.toCircle_unitToCircle`, `Path.toCircle_exp`: `unitToCircle t = exp (2πit)` goes to `γ t`.
* `Path.toCircle_one`: the point `1` goes to the base point.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

/-- The standard quotient `I → Circle`, `t ↦ exp(2πit)`, collapsing the endpoints `0` and `1` to
`1 ∈ Circle` and mapping `(0, 1)` bijectively onto `Circle \ {1}`. -/
def unitToCircle : C(I, Circle) where
  toFun t := Circle.exp (2 * Real.pi * t)
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)

theorem unitToCircle_apply (t : I) : unitToCircle t = Circle.exp (2 * Real.pi * t) :=
  (rfl)

@[simp]
theorem unitToCircle_zero : unitToCircle 0 = 1 := by
  simp [unitToCircle_apply]

@[simp]
theorem unitToCircle_one : unitToCircle 1 = 1 := by
  simp [unitToCircle_apply]

/-- `unitToCircle` is surjective: every `z : Circle` is `exp (angleDiff 1 z)` for
`angleDiff 1 z ∈ [0, 2π)`. -/
theorem unitToCircle_surjective : Function.Surjective unitToCircle := fun z ↦ by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⟨Circle.angleDiff 1 z / (2 * Real.pi),
    div_nonneg (Circle.angleDiff_nonneg 1 z) hp.le,
    (div_le_one hp).2 (Circle.angleDiff_lt_two_pi 1 z).le⟩, ?_⟩
  rw [unitToCircle_apply, mul_div_cancel₀ _ hp.ne']
  simpa using Circle.exp_angleDiff_mul (x := 1) (y := z)

/-- `unitToCircle` sends exactly the endpoints `0` and `1` to `1 ∈ Circle`. -/
@[simp]
theorem unitToCircle_eq_one_iff (t : I) : unitToCircle t = 1 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    rw [unitToCircle_apply, Circle.exp_eq_one] at h
    obtain ⟨n, hn⟩ := h
    have hp : (2 * Real.pi) ≠ 0 := by positivity
    have htn : (t : ℝ) = n := mul_left_cancel₀ hp (by linarith)
    have h0 : 0 ≤ n := by exact_mod_cast (htn ▸ t.2.1 : (0 : ℝ) ≤ n)
    have h1 : n ≤ 1 := by exact_mod_cast (htn ▸ t.2.2 : (n : ℝ) ≤ 1)
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa using htn))
    · exact Or.inr (Subtype.ext (by simpa using htn))
  · rintro (rfl | rfl) <;> simp

/-- Two points of `I` with the same image under `unitToCircle` are equal or opposite endpoints. -/
theorem eq_or_of_unitToCircle_eq {s t : I} (h : unitToCircle s = unitToCircle t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  rw [unitToCircle_apply, unitToCircle_apply, Circle.exp_eq_exp] at h
  obtain ⟨m, hm⟩ := h
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  have hst : (s : ℝ) = t + m := mul_left_cancel₀ hp (by linarith)
  have hm1 : (-1 : ℝ) ≤ m := by linarith [s.2.1, t.2.2]
  have hm2 : (m : ℝ) ≤ 1 := by linarith [s.2.2, t.2.1]
  have hm1' : -1 ≤ m := by exact_mod_cast hm1
  have hm2' : m ≤ 1 := by exact_mod_cast hm2
  have hcases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · right; left
    push_cast at hst
    exact ⟨Subtype.ext (by simpa using (by linarith [s.2.1, t.2.2] : (s : ℝ) = 0)),
      Subtype.ext (by simpa using (by linarith [s.2.1, t.2.2] : (t : ℝ) = 1))⟩
  · left
    push_cast at hst
    exact Subtype.ext (by linarith)
  · right; right
    push_cast at hst
    exact ⟨Subtype.ext (by simpa using (by linarith [s.2.2, t.2.1] : (s : ℝ) = 1)),
      Subtype.ext (by simpa using (by linarith [s.2.2, t.2.1] : (t : ℝ) = 0))⟩

end TauCeti

namespace Path

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- A loop `γ` at `x`, read as a map from the unit circle: `unitToCircle t = exp (2πit)` goes to
`γ t`. It is `γ` extended to `ℝ` and descended to `AddCircle 1`, which is identified with the
circle by `AddCircle.homeomorphCircle`. -/
def toCircle (γ : Path x x) : C(Circle, X) :=
  ⟨AddCircle.liftIco 1 0 γ.extend ∘ (AddCircle.homeomorphCircle one_ne_zero).symm,
    (AddCircle.liftIco_zero_continuous (by simp) γ.continuous_extend.continuousOn).comp
      (AddCircle.homeomorphCircle one_ne_zero).symm.continuous⟩

/-- The point `unitToCircle t` of the circle goes to `γ t`. -/
@[simp]
theorem toCircle_unitToCircle (γ : Path x x) (t : I) :
    γ.toCircle (TauCeti.unitToCircle t) = γ t := by
  have h : (AddCircle.homeomorphCircle one_ne_zero).symm (TauCeti.unitToCircle t) =
      ((t : ℝ) : AddCircle (1 : ℝ)) := by
    rw [TauCeti.unitToCircle_apply, Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk, div_one]
  rw [toCircle, ContinuousMap.coe_mk, Function.comp_apply, h]
  rcases eq_or_lt_of_le t.2.2 with ht | ht
  · have ht' : t = 1 := Subtype.ext ht
    rw [ht, AddCircle.coe_period, ← AddCircle.coe_zero (p := (1 : ℝ)),
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, zero_lt_one⟩, γ.extend_zero, ht', γ.target]
  · rw [AddCircle.liftIco_zero_coe_apply ⟨t.2.1, ht⟩, γ.extend_extends']

/-- The point `exp (2πit)` of the circle goes to `γ t`. -/
theorem toCircle_exp (γ : Path x x) (t : I) :
    γ.toCircle (Circle.exp (2 * Real.pi * t)) = γ t := by
  rw [← TauCeti.unitToCircle_apply, γ.toCircle_unitToCircle]

/-- The point `1` of the circle goes to the base point of the loop. -/
@[simp]
theorem toCircle_one (γ : Path x x) : γ.toCircle 1 = x := by
  simpa using γ.toCircle_unitToCircle 0

end Path

namespace TauCeti

/-- The `(p, q)` curve `t ↦ (exp (2πipt), exp (2πiqt))` on the torus `S¹ × S¹`, a loop at
`(1, 1)` winding `p` times around the first circle and `q` times around the second. -/
def torusCurve (p q : ℤ) : Path ((1 : Circle), (1 : Circle)) (1, 1) where
  toFun t := (Circle.exp (2 * Real.pi * (p * t)), Circle.exp (2 * Real.pi * (q * t)))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one, mul_one]
    exact Prod.ext (Circle.exp_two_pi_mul_int p) (Circle.exp_two_pi_mul_int q)

@[simp]
theorem torusCurve_apply (p q : ℤ) (t : unitInterval) :
    torusCurve p q t = (Circle.exp (2 * Real.pi * (p * t)), Circle.exp (2 * Real.pi * (q * t))) :=
  (rfl)

/-! ### The gluing of the boundary tori -/

/-- The homeomorphism `(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)` of the torus `S¹ × S¹` given by the
matrix `[[p, -t], [q, s]]` of determinant `s p + t q = 1`. -/
def torusGluing (p q s t : ℤ) (h : s * p + t * q = 1) :
    Circle × Circle ≃ₜ Circle × Circle where
  toFun x := (x.1 ^ p * x.2 ^ (-t), x.1 ^ q * x.2 ^ s)
  invFun y := (y.1 ^ s * y.2 ^ t, y.1 ^ (-q) * y.2 ^ p)
  left_inv x := by
    ext1 <;> dsimp only
    · rw [mul_zpow_mul_mul_zpow, show p * s + q * t = 1 by linear_combination h,
        show -t * s + s * t = 0 by ring, zpow_one, zpow_zero, mul_one]
    · rw [mul_zpow_mul_mul_zpow, show p * -q + q * p = 0 by ring,
        show -t * -q + s * p = 1 by linear_combination h, zpow_one, zpow_zero, one_mul]
  right_inv y := by
    ext1 <;> dsimp only
    · rw [mul_zpow_mul_mul_zpow,
        show s * p + -q * -t = 1 by linear_combination h, show t * p + p * -t = 0 by ring, zpow_one,
        zpow_zero, mul_one]
    · rw [mul_zpow_mul_mul_zpow, show s * q + -q * s = 0 by ring,
        show t * q + p * s = 1 by linear_combination h, zpow_one, zpow_zero, one_mul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The value of the determinant-one torus map. -/
@[simp]
theorem torusGluing_apply (p q s t : ℤ) (h : s * p + t * q = 1) (x : Circle × Circle) :
    torusGluing p q s t h x = (x.1 ^ p * x.2 ^ (-t), x.1 ^ q * x.2 ^ s) :=
  (rfl)

/-- The inverse of the determinant-one torus map. -/
@[simp]
theorem torusGluing_symm_apply (p q s t : ℤ) (h : s * p + t * q = 1) (x : Circle × Circle) :
    (torusGluing p q s t h).symm x = (x.1 ^ s * x.2 ^ t, x.1 ^ (-q) * x.2 ^ p) :=
  (rfl)

/-- The gluing carries the meridian `(a, 1)` to the `(p, q)` curve. -/
theorem torusGluing_torusCurve (p q s t : ℤ) (h : s * p + t * q = 1)
    (τ : unitInterval) : torusGluing p q s t h (torusCurve 1 0 τ) = torusCurve p q τ := by
  simp only [torusGluing_apply, torusCurve_apply, Int.cast_one, one_mul, Int.cast_zero, zero_mul,
    mul_zero, Circle.exp_zero, one_zpow, mul_one]
  refine Prod.ext ?_ ?_ <;>
    · simp only
      rw [← Circle.exp_intCast_mul]
      ring_nf

end TauCeti
