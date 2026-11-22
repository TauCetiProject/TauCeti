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
public import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.MeasureTheory.Integral.CircleIntegral
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
* the circle `s ↦ R exp(is/R)` of radius `R > 0`, Mathlib's `circleMap 0 R` parametrized by
  arclength, is a table of class `C^∞` and perimeter `2πR` (`ConvexTable.circle`), with
  `τ(s) × (γ(t) - γ(s)) = R(1 - cos((t - s)/R))`.

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

instance instCoeFun : CoeFun (ConvexTable k ℓ) fun _ ↦ ℝ → ℂ :=
  ⟨toFun⟩

/-- A table is determined by its parametrisation. -/
theorem coe_injective : Injective fun γ : ConvexTable k ℓ ↦ (γ : ℝ → ℂ) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

/-- Two tables with the same parametrisation are equal. -/
@[ext]
theorem ext {γ₁ γ₂ : ConvexTable k ℓ} (h : ∀ s, γ₁ s = γ₂ s) : γ₁ = γ₂ :=
  coe_injective (funext h)

attribute [simp, grind =] norm_deriv

theorem differentiable : Differentiable ℝ γ :=
  γ.contDiff.differentiable <| by
    have := γ.one_le
    exact_mod_cast (zero_lt_one.trans_le this).ne'

theorem continuous : Continuous γ :=
  γ.differentiable.continuous

@[simp, grind =]
theorem apply_add_period (s : ℝ) : γ (s + ℓ) = γ s :=
  γ.periodic s

@[simp, grind =]
theorem deriv_add_period (s : ℝ) : deriv γ (s + ℓ) = deriv γ s :=
  γ.periodic.deriv s

/-- Two parameters give the same point of the table exactly when they differ by a multiple of the
period. -/
theorem apply_eq_apply_iff {s t : ℝ} : γ t = γ s ↔ ∃ m : ℤ, t - s = m * ℓ := by
  refine ⟨fun h ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · by_contra! hne
    simpa [h] using γ.left_of_tangent s t hne
  · rw [eq_add_of_sub_eq' hm]
    exact (γ.periodic.int_mul m) s

/-- The parametrisation is injective on every half-open interval of length `ℓ`. -/
theorem injOn_Ico (s : ℝ) : InjOn γ (Ico s (s + ℓ)) := by
  intro a ha b hb hab
  have hℓ : 0 < ℓ := Fact.out
  have h : toIcoMod hℓ s a = toIcoMod hℓ s b :=
    (toIcoMod_eq_toIcoMod hℓ).2 (by simpa only [zsmul_eq_mul] using γ.apply_eq_apply_iff.1 hab.symm)
  rwa [(toIcoMod_eq_self hℓ).2 ha, (toIcoMod_eq_self hℓ).2 hb] at h

/-- The defining inequality in terms of points: every point of the table other than `γ(s)` lies
strictly to the left of the tangent line at `γ(s)`. -/
theorem im_conj_deriv_mul_sub_pos_of_ne {s t : ℝ} (h : γ t ≠ γ s) :
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
    exact γ.im_conj_deriv_mul_sub_pos_of_ne h

@[simp, grind =]
theorem coe_toStrictConvexBilliardTable : ⇑γ.toStrictConvexBilliardTable = γ :=
  (rfl)

@[simp, grind =]
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

@[simp, grind =]
theorem coe_ofLE {j : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) : ⇑(γ.ofLE hj hjk) = γ :=
  (rfl)

/-- Changing the regularity to itself does nothing. -/
@[simp, grind =]
theorem ofLE_self : γ.ofLE γ.one_le le_rfl = γ :=
  ext fun _ ↦ rfl

/-- Changing the regularity twice is changing it once. -/
@[simp, grind =]
theorem ofLE_ofLE {j i : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) (hi : 1 ≤ i) (hij : i ≤ j) :
    (γ.ofLE hj hjk).ofLE hi hij = γ.ofLE hi (hij.trans hjk) :=
  ext fun _ ↦ rfl

/-- Changing the regularity does not change the underlying strictly convex billiard table. -/
@[simp, grind =]
theorem toStrictConvexBilliardTable_ofLE {j : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) :
    (γ.ofLE hj hjk).toStrictConvexBilliardTable = γ.toStrictConvexBilliardTable :=
  (rfl)

/-- Starting the parametrisation at `γ(c)`: the table `s ↦ γ(s + c)`. -/
def shift (c : ℝ) : ConvexTable k ℓ where
  toFun s := γ (s + c)
  one_le := γ.one_le
  contDiff := γ.contDiff.comp (contDiff_id.add contDiff_const)
  periodic s := by simp [add_right_comm s ℓ c]
  norm_deriv s := by simp [deriv_comp_add_const]
  left_of_tangent s t h := by
    simpa [deriv_comp_add_const] using γ.left_of_tangent (s + c) (t + c) (by simpa using h)

@[simp, grind =]
theorem shift_apply (c s : ℝ) : γ.shift c s = γ (s + c) :=
  (rfl)

theorem coe_shift (c : ℝ) : ⇑(γ.shift c) = fun s ↦ γ (s + c) :=
  (rfl)

/-- The unit tangent of the shifted table is the shifted unit tangent. -/
@[simp, grind =]
theorem deriv_shift (c s : ℝ) : deriv (γ.shift c) s = deriv γ (s + c) := by
  rw [coe_shift, deriv_comp_add_const]

/-- Shifting by `0` does nothing. -/
@[simp, grind =]
theorem shift_zero : γ.shift 0 = γ :=
  ext fun s ↦ by rw [shift_apply, add_zero]

/-- Shifting twice is shifting by the sum. -/
@[simp, grind =]
theorem shift_shift (c d : ℝ) : (γ.shift c).shift d = γ.shift (c + d) :=
  ext fun s ↦ by rw [shift_apply, shift_apply, shift_apply, add_assoc, add_comm d c]

/-- Shifting by a period does nothing. -/
@[simp, grind =]
theorem shift_period : γ.shift ℓ = γ :=
  ext fun s ↦ by rw [shift_apply, apply_add_period]

/-- Shifts differing by a period agree. -/
@[simp, grind =]
theorem shift_add_period (c : ℝ) : γ.shift (c + ℓ) = γ.shift c :=
  ext fun s ↦ by rw [shift_apply, shift_apply, ← add_assoc, apply_add_period]

theorem shift_ofLE {j : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) (c : ℝ) :
    (γ.ofLE hj hjk).shift c = (γ.shift c).ofLE hj hjk :=
  ext fun _ ↦ rfl

private theorem deriv_mul_add (a b : ℂ) (s : ℝ) :
    deriv (fun s ↦ a * γ s + b) s = a * deriv γ s := by
  rw [deriv_add_const, deriv_const_mul_field]

/-- The image of a table under the rigid motion `z ↦ a z + b`, a rotation by `a` with `|a| = 1`
followed by a translation by `b`. -/
def rigidMotion (a : Circle) (b : ℂ) : ConvexTable k ℓ where
  toFun s := a * γ s + b
  one_le := γ.one_le
  contDiff := (contDiff_const.mul γ.contDiff).add contDiff_const
  periodic s := by simp
  norm_deriv s := by simp [γ.deriv_mul_add]
  left_of_tangent s t h := by
    have ha : conj (a : ℂ) * a = 1 := by simp [← Complex.normSq_eq_conj_mul_self]
    have hprod : conj ((a : ℂ) * deriv γ s) * ((a : ℂ) * γ t + b - ((a : ℂ) * γ s + b)) =
        conj (deriv γ s) * (γ t - γ s) := by
      rw [map_mul]
      linear_combination (conj (deriv γ s) * (γ t - γ s)) * ha
    rw [γ.deriv_mul_add, hprod]
    exact γ.left_of_tangent s t h

@[simp, grind =]
theorem rigidMotion_apply (a : Circle) (b : ℂ) (s : ℝ) : γ.rigidMotion a b s = a * γ s + b :=
  (rfl)

theorem coe_rigidMotion (a : Circle) (b : ℂ) : ⇑(γ.rigidMotion a b) = fun s ↦ a * γ s + b :=
  (rfl)

/-- The unit tangent of the moved table is the rotated unit tangent. -/
@[simp, grind =]
theorem deriv_rigidMotion (a : Circle) (b : ℂ) (s : ℝ) :
    deriv (γ.rigidMotion a b) s = a * deriv γ s := by
  rw [coe_rigidMotion, γ.deriv_mul_add]

/-- The identity motion does nothing. -/
@[simp, grind =]
theorem rigidMotion_one_zero : γ.rigidMotion 1 0 = γ :=
  ext fun s ↦ by simp

/-- Moving twice is moving by the composite motion. -/
@[simp, grind =]
theorem rigidMotion_rigidMotion (a a' : Circle) (b b' : ℂ) :
    (γ.rigidMotion a b).rigidMotion a' b' = γ.rigidMotion (a' * a) (a' * b + b') :=
  ext fun s ↦ by simp only [rigidMotion_apply, Circle.coe_mul]; ring

theorem rigidMotion_ofLE {j : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) (a : Circle) (b : ℂ) :
    (γ.ofLE hj hjk).rigidMotion a b = (γ.rigidMotion a b).ofLE hj hjk :=
  ext fun _ ↦ rfl

theorem rigidMotion_shift (a : Circle) (b : ℂ) (c : ℝ) :
    (γ.shift c).rigidMotion a b = (γ.rigidMotion a b).shift c :=
  ext fun _ ↦ rfl

/-- Reversing the orientation never gives a table: `γ` is not `s ↦ δ(-s)` for any table `δ`, of
any class and perimeter (`StrictConvexBilliardTable.coe_ne_comp_neg`). -/
theorem coe_ne_comp_neg {j : ℕ∞} {ℓ' : ℝ} [Fact (0 < ℓ')] (δ : ConvexTable j ℓ') :
    ⇑γ ≠ δ ∘ Neg.neg :=
  γ.toStrictConvexBilliardTable.coe_ne_comp_neg δ.toStrictConvexBilliardTable

/-! ### The circle -/

private theorem pos_of_two_pi_mul_pos {R : ℝ} (h : 0 < 2 * π * R) : 0 < R :=
  pos_of_mul_pos_right h Real.two_pi_pos.le

/-- The positively oriented circle `s ↦ R exp(is/R)` of radius `R > 0`, of perimeter `2πR`, is a
table of class `C^∞`: it is Mathlib's `circleMap 0 R` parametrized by arclength, its unit tangent
is `τ(s) = i exp(is/R)` (`ConvexTable.deriv_circle`), and
`τ(s) × (γ(t) - γ(s)) = R(1 - cos((t - s)/R))` (`ConvexTable.im_conj_deriv_circle_mul_sub`). -/
def circle (R : ℝ) [Fact (0 < 2 * π * R)] : ConvexTable ⊤ (2 * π * R) where
  toFun s := circleMap 0 R (s / R)
  one_le := le_top
  contDiff := (contDiff_circleMap 0 R).comp (contDiff_id.div_const R)
  periodic := (periodic_circleMap 0 R).div_const R
  norm_deriv s := by
    have hR := (pos_of_two_pi_mul_pos (Fact.out : 0 < 2 * π * R)).ne'
    simp [(hasDerivAt_circleMap_div 0 hR s).deriv]
  left_of_tangent s t h := by
    have hR := pos_of_two_pi_mul_pos (Fact.out : 0 < 2 * π * R)
    rw [(hasDerivAt_circleMap_div 0 hR.ne' s).deriv, im_conj_mul_I_mul_circleMap_div_sub]
    refine mul_pos hR (sub_pos.2 (lt_of_le_of_ne (Real.cos_le_one _) fun h1 ↦ ?_))
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1
    exact h n (by field_simp at hn; linarith)

variable (R : ℝ) [Fact (0 < 2 * π * R)]

@[simp, grind =]
theorem circle_apply (s : ℝ) : circle R s = circleMap 0 R (s / R) :=
  (rfl)

/-- The circle `s ↦ R exp(is/R)` has unit velocity `exp(is/R) i`. -/
theorem hasDerivAt_circle (s : ℝ) : HasDerivAt (circle R) (circleMap 0 1 (s / R) * I) s :=
  hasDerivAt_circleMap_div 0 (pos_of_two_pi_mul_pos Fact.out).ne' s

@[simp, grind =]
theorem deriv_circle (s : ℝ) : deriv (circle R) s = circleMap 0 1 (s / R) * I :=
  (hasDerivAt_circle R s).deriv

/-- On the circle of radius `R` the defining quantity of a table is `R(1 - cos((t - s)/R))`, equal
to `2R` at `t - s = πR`. -/
theorem im_conj_deriv_circle_mul_sub (s t : ℝ) :
    (conj (deriv (circle R) s) * (circle R t - circle R s)).im =
      R * (1 - Real.cos ((t - s) / R)) := by
  rw [deriv_circle, circle_apply, circle_apply, im_conj_mul_I_mul_circleMap_div_sub]

end ConvexTable

end TauCeti
