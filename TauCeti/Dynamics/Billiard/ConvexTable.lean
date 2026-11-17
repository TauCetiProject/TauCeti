/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Dynamics.Billiard.NextCollision
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Convex billiard tables

A *convex billiard table* of class `C^k` and perimeter `ℓ > 0` is an `ℓ`-periodic arclength
parametrisation `γ : ℝ → ℂ` of class `C^k`, `k ≥ 1`, such that every other point of the curve lies
strictly to the left of each tangent line: `τ(s) × (γ(t) - γ(s)) > 0` whenever `t - s ∉ ℓℤ`, where
`τ = γ'` is the unit tangent and `a × b = Im(conj a · b)` is the cross product of `ℂ`. The condition
combines the strict convexity of the region bounded by the curve with the positive
(counterclockwise) orientation of its boundary. The curvature is allowed to vanish.

This file defines the carrier `TauCeti.ConvexTable k ℓ` and its first properties:

* `γ(s) = γ(t)` exactly when `t - s ∈ ℓℤ` (`ConvexTable.apply_eq_apply_iff`), so `γ` is injective on
  every half-open interval of length `ℓ` (`ConvexTable.injOn_Ico`): injectivity is a consequence of
  the definition, not an axiom;
* a table is a `TauCeti.StrictConvexBilliardTable` for the orientation `Complex.orientation` of `ℂ`
  (`ConvexTable.toStrictConvexBilliardTable`), so the next-collision map, its inverse and its
  generating function, constructed there for an oriented Euclidean plane, apply to every table;
* a table of class `C^k` is a table of class `C^j` for `1 ≤ j ≤ k` (`ConvexTable.ofLE`), a shift of
  the parameter is a table (`ConvexTable.shift`), and so is the image under a rigid motion
  `z ↦ az + b` with `|a| = 1` (`ConvexTable.rigidMotion`), while the reversed parametrisation
  `s ↦ γ(-s)` never is (`ConvexTable.coe_ne_comp_neg`): the orientation is part of the carrier;
* the circle `s ↦ R exp(is/R)` of radius `R > 0` is a table of class `C^∞` and perimeter `2πR`
  (`ConvexTable.circle`), with `τ(s) × (γ(t) - γ(s)) = R(1 - cos((t - s)/R))`.

## References

* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
* Anatole Katok and Boris Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Section 9.2.
-/

public section

noncomputable section

open Function Set Complex
open scoped ComplexConjugate Real

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

/-- A convex billiard table of class `C^k` and perimeter `ℓ`: an `ℓ`-periodic unit-speed map
`γ : ℝ → ℂ` of class `C^k`, `k ≥ 1`, such that `τ(s) × (γ(t) - γ(s)) > 0` whenever `t - s ∉ ℓℤ`,
where `τ = γ'` and `a × b = Im(conj a · b)`. Every other point of the curve lies strictly to the
left of each tangent line, which combines strict convexity with positive orientation. -/
structure ConvexTable (k : ℕ∞) (ℓ : ℝ) [Fact (0 < ℓ)] where
  /-- The arclength parametrisation of the boundary. -/
  toFun : ℝ → ℂ
  /-- The regularity is at least `C¹`. -/
  one_le : 1 ≤ k
  /-- The parametrisation is of class `C^k`. -/
  contDiff : ContDiff ℝ k toFun
  /-- The parametrisation is `ℓ`-periodic. -/
  periodic : Periodic toFun ℓ
  /-- The parametrisation has unit speed. -/
  norm_deriv : ∀ s, ‖deriv toFun s‖ = 1
  /-- Every other point of the curve lies strictly to the left of each tangent line. -/
  left_of_tangent : ∀ s t : ℝ, (∀ m : ℤ, t - s ≠ m * ℓ) →
    0 < (conj (deriv toFun s) * (toFun t - toFun s)).im

namespace ConvexTable

variable {k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (γ : ConvexTable k ℓ)

instance : CoeFun (ConvexTable k ℓ) fun _ ↦ ℝ → ℂ :=
  ⟨toFun⟩

theorem differentiable : Differentiable ℝ γ :=
  γ.contDiff.differentiable <| by
    have := γ.one_le
    exact_mod_cast (zero_lt_one.trans_le this).ne'

theorem continuous : Continuous γ :=
  γ.differentiable.continuous

@[simp]
theorem apply_add_period (s : ℝ) : γ (s + ℓ) = γ s :=
  γ.periodic s

@[simp]
theorem deriv_add_period (s : ℝ) : deriv γ (s + ℓ) = deriv γ s :=
  γ.periodic.deriv s

/-- Two parameters give the same point of the table exactly when they differ by a multiple of the
period. -/
theorem apply_eq_apply_iff {s t : ℝ} : γ t = γ s ↔ ∃ m : ℤ, t - s = m * ℓ := by
  refine ⟨fun h ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · by_contra! hne
    simpa [h] using γ.left_of_tangent s t hne
  · rw [show t = s + m * ℓ by linarith]
    exact (γ.periodic.int_mul m) s

/-- The parametrisation is injective on every half-open interval of length `ℓ`. -/
theorem injOn_Ico (s : ℝ) : InjOn γ (Ico s (s + ℓ)) := by
  intro a ha b hb hab
  obtain ⟨m, hm⟩ := γ.apply_eq_apply_iff.1 hab.symm
  have hℓ : 0 < ℓ := Fact.out
  have h1 : (m : ℝ) * ℓ < 1 * ℓ := by linarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : (-1 : ℝ) * ℓ < m * ℓ := by linarith [ha.1, ha.2, hb.1, hb.2]
  have hm0 : m = 0 := by
    have := lt_of_mul_lt_mul_right h1 hℓ.le
    have := lt_of_mul_lt_mul_right h2 hℓ.le
    norm_cast at *
    omega
  simp only [hm0, Int.cast_zero, zero_mul] at hm
  linarith

/-- The defining inequality in terms of points: every point of the table other than `γ(s)` lies
strictly to the left of the tangent line at `γ(s)`. -/
theorem cross_pos_of_ne {s t : ℝ} (h : γ t ≠ γ s) :
    0 < (conj (deriv γ s) * (γ t - γ s)).im :=
  γ.left_of_tangent s t fun m hm ↦ h (γ.apply_eq_apply_iff.2 ⟨m, hm⟩)

/-! ### Comparison with `StrictConvexBilliardTable` -/

/-- A convex table is a strictly convex billiard table in `ℂ`, oriented by `Complex.orientation`,
whose period is `ℓ`. -/
def toStrictConvexBilliardTable : StrictConvexBilliardTable Complex.orientation where
  toFun := γ
  period := ℓ
  period_pos := Fact.out
  periodic := γ.periodic
  norm_deriv := γ.norm_deriv
  injOn := by simpa using γ.injOn_Ico 0
  areaForm_pos s t h := by
    rw [Complex.areaForm]
    exact γ.cross_pos_of_ne h

@[simp]
theorem coe_toStrictConvexBilliardTable : ⇑γ.toStrictConvexBilliardTable = γ :=
  (rfl)

@[simp]
theorem period_toStrictConvexBilliardTable : γ.toStrictConvexBilliardTable.period = ℓ :=
  (rfl)

/-! ### Changing the regularity, the parameter and the position -/

/-- A table of class `C^k` is a table of class `C^j` for `1 ≤ j ≤ k`. -/
def ofLE {j : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) : ConvexTable j ℓ where
  toFun := γ
  one_le := hj
  contDiff := γ.contDiff.of_le (mod_cast hjk)
  periodic := γ.periodic
  norm_deriv := γ.norm_deriv
  left_of_tangent := γ.left_of_tangent

@[simp]
theorem coe_ofLE {j : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) : ⇑(γ.ofLE hj hjk) = γ :=
  (rfl)

/-- Starting the parametrisation at `γ(c)`: the table `s ↦ γ(s + c)`. -/
def shift (c : ℝ) : ConvexTable k ℓ where
  toFun s := γ (s + c)
  one_le := γ.one_le
  contDiff := γ.contDiff.comp (contDiff_id.add contDiff_const)
  periodic s := by simp [add_right_comm s ℓ c]
  norm_deriv s := by simpa [deriv_comp_add_const] using γ.norm_deriv (s + c)
  left_of_tangent s t h := by
    simpa [deriv_comp_add_const] using γ.left_of_tangent (s + c) (t + c) (by simpa using h)

@[simp]
theorem shift_apply (c s : ℝ) : γ.shift c s = γ (s + c) :=
  (rfl)

/-- The image of a table under the rigid motion `z ↦ a z + b`, a rotation by `a` with `|a| = 1`
followed by a translation by `b`. -/
def rigidMotion (a : Circle) (b : ℂ) : ConvexTable k ℓ where
  toFun s := a * γ s + b
  one_le := γ.one_le
  contDiff := (contDiff_const.mul γ.contDiff).add contDiff_const
  periodic s := by simp
  norm_deriv s := by
    rw [deriv_add_const, deriv_const_mul _ (γ.differentiable s), norm_mul, Circle.norm_coe,
      γ.norm_deriv, one_mul]
  left_of_tangent s t h := by
    have hd : deriv (fun s ↦ (a : ℂ) * γ s + b) s = a * deriv γ s := by
      rw [deriv_add_const, deriv_const_mul _ (γ.differentiable s)]
    have ha : conj (a : ℂ) * a = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Circle.norm_coe]
      simp
    rw [hd, map_mul, add_sub_add_right_eq_sub, ← mul_sub,
      show conj (a : ℂ) * conj (deriv γ s) * (a * (γ t - γ s)) =
        conj (a : ℂ) * a * (conj (deriv γ s) * (γ t - γ s)) by ring, ha, one_mul]
    exact γ.left_of_tangent s t h

@[simp]
theorem rigidMotion_apply (a : Circle) (b : ℂ) (s : ℝ) : γ.rigidMotion a b s = a * γ s + b :=
  (rfl)

/-- Reversing the orientation never gives a table: no table, of any class, is parametrised by
`s ↦ γ(-s)`. At `s = 0`, `t = ℓ / 2` the defining quantities of the two have opposite signs. -/
theorem coe_ne_comp_neg {j : ℕ∞} (δ : ConvexTable j ℓ) : ⇑δ ≠ γ ∘ Neg.neg := by
  intro hδ
  have hℓ : 0 < ℓ := Fact.out
  have hm : ∀ m : ℤ, ℓ / 2 - 0 ≠ m * ℓ := fun m hm ↦ by
    have h1 : (2 * m : ℝ) * ℓ = 1 * ℓ := by linarith
    have h2 : (2 * m : ℝ) = 1 := mul_right_cancel₀ hℓ.ne' h1
    have : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  have hm' : ∀ m : ℤ, -(ℓ / 2) - -0 ≠ m * ℓ := fun m h ↦
    hm (-m) (by push_cast; linarith)
  have hd : deriv (⇑δ) 0 = -deriv γ 0 := by
    rw [hδ, show γ ∘ Neg.neg = fun s ↦ γ (-s) from rfl, deriv_comp_neg, neg_zero]
  have h1 := δ.left_of_tangent 0 (ℓ / 2) hm
  have h2 := γ.left_of_tangent (-0) (-(ℓ / 2)) hm'
  rw [hd] at h1
  simp only [hδ, comp_apply, map_neg, neg_mul, neg_im, neg_zero] at h1 h2
  linarith

/-! ### The circle -/

private theorem hasDerivAt_circle {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (R : ℂ) * exp (↑(s / R) * I)) (I * exp (↑(s / R) * I)) s := by
  have h := ((((hasDerivAt_id s).div_const R).ofReal_comp).mul_const I).cexp.const_mul (R : ℂ)
  simp only [id] at h
  refine h.congr_deriv ?_
  have : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR
  push_cast
  field_simp

private theorem circle_cross_aux (R s t : ℝ) :
    (conj (I * exp (↑(s / R) * I)) * (R * exp (↑(t / R) * I) - R * exp (↑(s / R) * I))).im =
      R * (1 - Real.cos ((t - s) / R)) := by
  simp only [map_mul, conj_I, ← exp_conj, conj_ofReal, mul_neg, ← neg_mul, ← ofReal_neg, mul_im,
    mul_re, sub_im, sub_re, neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  rw [sub_div, Real.cos_sub, Real.cos_neg, Real.sin_neg]
  linear_combination R * Real.sin_sq_add_cos_sq (s / R)

private theorem pos_of_two_pi_mul_pos {R : ℝ} (h : 0 < 2 * π * R) : 0 < R :=
  pos_of_mul_pos_right h Real.two_pi_pos.le

/-- The positively oriented circle `s ↦ R exp(is/R)` of radius `R > 0`, of perimeter `2πR`, is a
table of class `C^∞`: its unit tangent is `τ(s) = i exp(is/R)` (`ConvexTable.deriv_circle`) and
`τ(s) × (γ(t) - γ(s)) = R(1 - cos((t - s)/R))` (`ConvexTable.circle_cross`). -/
def circle (R : ℝ) [Fact (0 < 2 * π * R)] : ConvexTable ⊤ (2 * π * R) where
  toFun s := R * exp (↑(s / R) * I)
  one_le := le_top
  contDiff := contDiff_const.mul <| contDiff_exp.comp <|
    (ofRealCLM.contDiff.comp (contDiff_id.div_const R)).mul contDiff_const
  periodic s := by
    have hR := (pos_of_two_pi_mul_pos (Fact.out : 0 < 2 * π * R)).ne'
    simp only
    rw [show ((s + 2 * π * R) / R : ℝ) = s / R + 2 * π by field_simp, ofReal_add, add_mul,
      exp_add, ofReal_mul, ofReal_ofNat, exp_two_pi_mul_I, mul_one]
  norm_deriv s := by
    have hR := (pos_of_two_pi_mul_pos (Fact.out : 0 < 2 * π * R)).ne'
    rw [(hasDerivAt_circle hR s).deriv, norm_mul, norm_I, one_mul, norm_exp_ofReal_mul_I]
  left_of_tangent s t h := by
    have hR := pos_of_two_pi_mul_pos (Fact.out : 0 < 2 * π * R)
    rw [(hasDerivAt_circle hR.ne' s).deriv, circle_cross_aux]
    refine mul_pos hR (sub_pos.2 (lt_of_le_of_ne (Real.cos_le_one _) fun h1 ↦ ?_))
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1
    exact h n (by field_simp at hn; linarith)

variable (R : ℝ) [Fact (0 < 2 * π * R)]

theorem circle_apply (s : ℝ) : circle R s = R * exp (↑(s / R) * I) :=
  (rfl)

theorem deriv_circle (s : ℝ) : deriv (circle R) s = I * exp (↑(s / R) * I) :=
  (hasDerivAt_circle (pos_of_two_pi_mul_pos Fact.out).ne' s).deriv

/-- On the circle of radius `R` the defining quantity of a table is `R(1 - cos((t - s)/R))`, equal
to `2R` at `t - s = πR`. -/
theorem circle_cross (s t : ℝ) :
    (conj (deriv (circle R) s) * (circle R t - circle R s)).im =
      R * (1 - Real.cos ((t - s) / R)) := by
  rw [deriv_circle, circle_apply, circle_apply, circle_cross_aux]

end ConvexTable

end TauCeti
