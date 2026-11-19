/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.Irrational
public import TauCeti.NumberTheory.BinaryQuadraticForm.IndefiniteReduction.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Real roots of indefinite binary quadratic forms

An integral binary quadratic form `f = a x² + b x y + c y²` of positive discriminant
`D = b² - 4 a c` and nonzero leading coefficient has two distinct real roots of `a x² + b x + c`:
the **first root** `(-b + √D) / (2 a)` (`TauCeti.BinaryQuadraticForm.firstRoot`) and the **second
root** `(-b - √D) / (2 a)` (`TauCeti.BinaryQuadraticForm.secondRoot`), distinguished by
`2 a x + b = +√D` and `2 a x + b = -√D`.

When `D > 0` is not a square, both roots are quadratic irrationals, so no nontrivial integral
linear form `r x + s` vanishes at either root. Under the left action `γ • f = f ∘ γ⁻¹` of
`SL(2, ℤ)` on forms, both roots transform by the Möbius action
`x ↦ (p x + q) / (r x + s)` of `γ = !![p, q; r, s]` without ever interchanging (`firstRoot_smul`
and `secondRoot_smul`), because `det γ = 1` preserves the sign of `2 a x + b = ±√D`. Since `2 a`
and `b` are recovered from `2 a · firstRoot + b = √D` by irrationality, `firstRoot` is injective
on forms of a fixed nonsquare discriminant `D > 0` (`firstRoot_injOn`) and identifies the proper
stabiliser of `f` with the Möbius stabiliser of `f.firstRoot`.

Finally, `f` is Gauss reduced if and only if its two roots have opposite signs and separate the
unit circle: `f.firstRoot * f.secondRoot < 0`, `|f.firstRoot| < 1` and `1 < |f.secondRoot|`
(`isGaussReduced_iff_firstRoot_secondRoot`). Depending on the sign of `a`, this puts `f.firstRoot`
in `(0, 1)` with `f.secondRoot < -1` (`a > 0`), or `f.firstRoot` in `(-1, 0)` with
`1 < f.secondRoot` (`a < 0`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.firstRoot`: the first real root `(-b + √D) / (2 a)`.
* `TauCeti.BinaryQuadraticForm.secondRoot`: the second real root `(-b - √D) / (2 a)`.

## Main results

* `TauCeti.BinaryQuadraticForm.irrational_firstRoot` and
  `TauCeti.BinaryQuadraticForm.irrational_secondRoot`: both roots are irrational for nonsquare
  `D ≥ 0`.
* `TauCeti.BinaryQuadraticForm.firstRoot_injOn` and
  `TauCeti.BinaryQuadraticForm.secondRoot_injOn`: for fixed nonsquare `D ≥ 0`, a form is
  determined by either of its roots.
* `TauCeti.BinaryQuadraticForm.firstRoot_smul` and
  `TauCeti.BinaryQuadraticForm.secondRoot_smul`: `SL(2, ℤ)`-equivariance for the Möbius action.
* `TauCeti.BinaryQuadraticForm.smul_a_eq_mul_denom`: `(γ • f).a = a (r ω₁ + s) (r ω₂ + s)`.
* `TauCeti.BinaryQuadraticForm.isGaussReduced_iff_firstRoot_secondRoot`: root characterisation of
  Gauss reducedness.

## References

* J. Buchmann and U. Vollmer, *Binary Quadratic Forms: An Algorithmic Approach*, Springer, 2007,
  Chapter 6.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.6.
* D. Zagier, *Zetafunktionen und quadratische Körper*, Springer, 1981, §13.
-/

public section

open MulAction
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- The **first root** `(-b + √D) / (2 a)` of an integral binary quadratic form
`f = a x² + b x y + c y²` of discriminant `D = b² - 4 a c`, characterised for `a ≠ 0` by
`2 a x + b = √D` (`two_mul_a_mul_firstRoot_add_b`). -/
noncomputable def firstRoot (f : BinaryQuadraticForm ℤ) : ℝ :=
  (-(f.b : ℝ) + √(f.discrim : ℝ)) / (2 * f.a)

/-- Definitional expansion of `firstRoot`. -/
theorem firstRoot_def (f : BinaryQuadraticForm ℤ) :
    f.firstRoot = (-(f.b : ℝ) + √(f.discrim : ℝ)) / (2 * f.a) :=
  (rfl)

/-- The **second root** `(-b - √D) / (2 a)` of an integral binary quadratic form
`f = a x² + b x y + c y²` of discriminant `D = b² - 4 a c`, characterised for `a ≠ 0` by
`2 a x + b = -√D` (`two_mul_a_mul_secondRoot_add_b`). -/
noncomputable def secondRoot (f : BinaryQuadraticForm ℤ) : ℝ :=
  (-(f.b : ℝ) - √(f.discrim : ℝ)) / (2 * f.a)

/-- Definitional expansion of `secondRoot`. -/
theorem secondRoot_def (f : BinaryQuadraticForm ℤ) :
    f.secondRoot = (-(f.b : ℝ) - √(f.discrim : ℝ)) / (2 * f.a) :=
  (rfl)

/-! ### Algebraic identities -/

/-- For `a ≠ 0`, the first root satisfies `2 a · firstRoot + b = √D`. -/
theorem two_mul_a_mul_firstRoot_add_b {f : BinaryQuadraticForm ℤ} (ha : f.a ≠ 0) :
    2 * (f.a : ℝ) * f.firstRoot + f.b = √(f.discrim : ℝ) := by
  have ha' : (2 : ℝ) * f.a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr ha)
  rw [firstRoot_def, mul_div_cancel₀ _ ha']
  ring

/-- For `a ≠ 0`, the second root satisfies `2 a · secondRoot + b = -√D`. -/
theorem two_mul_a_mul_secondRoot_add_b {f : BinaryQuadraticForm ℤ} (ha : f.a ≠ 0) :
    2 * (f.a : ℝ) * f.secondRoot + f.b = -√(f.discrim : ℝ) := by
  have ha' : (2 : ℝ) * f.a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr ha)
  rw [secondRoot_def, mul_div_cancel₀ _ ha']
  ring

/-- Vieta's sum formula: `firstRoot + secondRoot = -b / a`. -/
theorem firstRoot_add_secondRoot (f : BinaryQuadraticForm ℤ) :
    f.firstRoot + f.secondRoot = -(f.b : ℝ) / f.a := by
  rw [firstRoot_def, secondRoot_def, ← add_div]
  have h : -(f.b : ℝ) + √(f.discrim : ℝ) + (-(f.b : ℝ) - √(f.discrim : ℝ)) = 2 * -(f.b : ℝ) := by
    ring
  rw [h, mul_div_mul_left _ _ two_ne_zero]

/-- The difference of the two roots is `√D / a`. -/
theorem firstRoot_sub_secondRoot (f : BinaryQuadraticForm ℤ) :
    f.firstRoot - f.secondRoot = √(f.discrim : ℝ) / f.a := by
  rw [firstRoot_def, secondRoot_def, ← sub_div]
  have h : -(f.b : ℝ) + √(f.discrim : ℝ) - (-(f.b : ℝ) - √(f.discrim : ℝ)) =
      2 * √(f.discrim : ℝ) := by
    ring
  rw [h, mul_div_mul_left _ _ two_ne_zero]

/-- Vieta's product formula: for `0 ≤ f.discrim`, `firstRoot * secondRoot = c / a`. -/
theorem firstRoot_mul_secondRoot {f : BinaryQuadraticForm ℤ} (hD : 0 ≤ f.discrim) :
    f.firstRoot * f.secondRoot = (f.c : ℝ) / f.a := by
  by_cases ha : f.a = 0
  · simp [firstRoot_def, ha]
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hD' : (0 : ℝ) ≤ f.discrim := by exact_mod_cast hD
  have hsq : √(f.discrim : ℝ) * √(f.discrim : ℝ) = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
    rw [Real.mul_self_sqrt hD']
    simp [discrim_def, discrim]
  rw [firstRoot_def, secondRoot_def]
  field_simp
  linear_combination -hsq

/-- For `0 ≤ f.discrim` and `a ≠ 0`, the dehomogenised polynomial `a x² + b x + c` vanishes at
`firstRoot`. -/
theorem eval_firstRoot_one {f : BinaryQuadraticForm ℤ} (hD : 0 ≤ f.discrim) (ha : f.a ≠ 0) :
    (f.a : ℝ) * f.firstRoot ^ 2 + f.b * f.firstRoot + f.c = 0 := by
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hD' : (0 : ℝ) ≤ f.discrim := by exact_mod_cast hD
  have hlin := two_mul_a_mul_firstRoot_add_b ha
  have hsq : √(f.discrim : ℝ) ^ 2 = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
    rw [Real.sq_sqrt hD']
    simp [discrim_def, discrim]
  apply mul_left_cancel₀ (mul_ne_zero four_ne_zero ha')
  rw [mul_zero]
  linear_combination (2 * (f.a : ℝ) * f.firstRoot + f.b + √(f.discrim : ℝ)) * hlin + hsq

/-- For `0 ≤ f.discrim` and `a ≠ 0`, the dehomogenised polynomial `a x² + b x + c` vanishes at
`secondRoot`. -/
theorem eval_secondRoot_one {f : BinaryQuadraticForm ℤ} (hD : 0 ≤ f.discrim) (ha : f.a ≠ 0) :
    (f.a : ℝ) * f.secondRoot ^ 2 + f.b * f.secondRoot + f.c = 0 := by
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hD' : (0 : ℝ) ≤ f.discrim := by exact_mod_cast hD
  have hlin := two_mul_a_mul_secondRoot_add_b ha
  have hsq : √(f.discrim : ℝ) ^ 2 = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
    rw [Real.sq_sqrt hD']
    simp [discrim_def, discrim]
  apply mul_left_cancel₀ (mul_ne_zero four_ne_zero ha')
  rw [mul_zero]
  linear_combination (2 * (f.a : ℝ) * f.secondRoot + f.b - √(f.discrim : ℝ)) * hlin + hsq

/-! ### Irrationality and injectivity -/

/-- A nontrivial integral linear form does not vanish at an irrational real number. -/
private theorem intCast_mul_add_ne_zero_of_irrational {x : ℝ} (hx : Irrational x) {r s : ℤ}
    (hrs : r ≠ 0 ∨ s ≠ 0) : (r : ℝ) * x + s ≠ 0 := by
  intro h
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h
    exact hrs.resolve_left (not_not.mpr rfl) h
  · have hr' : (r : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hr
    refine hx ⟨(-s : ℚ) / r, ?_⟩
    push_cast
    rw [div_eq_iff hr']
    linarith

/-- For a nonnegative nonsquare discriminant, `firstRoot` is irrational. -/
theorem irrational_firstRoot {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) : Irrational f.firstRoot := by
  have hs : Irrational √(f.discrim : ℝ) :=
    (irrational_sqrt_intCast_iff_of_nonneg hpos).mpr hD
  have hlin := two_mul_a_mul_firstRoot_add_b (a_ne_zero_of_not_isSquare_discrim hD)
  rintro ⟨q, hq⟩
  refine hs ⟨2 * f.a * q + f.b, ?_⟩
  push_cast
  rw [hq, hlin]

/-- For a nonnegative nonsquare discriminant, `secondRoot` is irrational. -/
theorem irrational_secondRoot {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) : Irrational f.secondRoot := by
  have hs : Irrational √(f.discrim : ℝ) :=
    (irrational_sqrt_intCast_iff_of_nonneg hpos).mpr hD
  have hlin := two_mul_a_mul_secondRoot_add_b (a_ne_zero_of_not_isSquare_discrim hD)
  rintro ⟨q, hq⟩
  refine hs ⟨-(2 * f.a * q + f.b), ?_⟩
  push_cast
  rw [hq, hlin, neg_neg]

/-- No nontrivial integral linear form vanishes at `firstRoot`. -/
theorem mul_firstRoot_add_ne_zero {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) {r s : ℤ} (hrs : r ≠ 0 ∨ s ≠ 0) :
    (r : ℝ) * f.firstRoot + s ≠ 0 :=
  intCast_mul_add_ne_zero_of_irrational (irrational_firstRoot hpos hD) hrs

/-- No nontrivial integral linear form vanishes at `secondRoot`. -/
theorem mul_secondRoot_add_ne_zero {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) {r s : ℤ} (hrs : r ≠ 0 ∨ s ≠ 0) :
    (r : ℝ) * f.secondRoot + s ≠ 0 :=
  intCast_mul_add_ne_zero_of_irrational (irrational_secondRoot hpos hD) hrs

/-- The Möbius denominator `(γ 1 0) · firstRoot + γ 1 1` of `γ ∈ SL(2, ℤ)` is nonzero. -/
theorem denom_firstRoot_ne_zero (γ : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hD : ¬ IsSquare f.discrim) :
    (γ 1 0 : ℝ) * f.firstRoot + γ 1 1 ≠ 0 := by
  refine mul_firstRoot_add_ne_zero hpos hD ?_
  by_contra! h
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  simp [h.1, h.2] at hdet

/-- The Möbius denominator `(γ 1 0) · secondRoot + γ 1 1` of `γ ∈ SL(2, ℤ)` is nonzero. -/
theorem denom_secondRoot_ne_zero (γ : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hD : ¬ IsSquare f.discrim) :
    (γ 1 0 : ℝ) * f.secondRoot + γ 1 1 ≠ 0 := by
  refine mul_secondRoot_add_ne_zero hpos hD ?_
  by_contra! h
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  simp [h.1, h.2] at hdet

/-- Two forms of the same nonnegative nonsquare discriminant have equal `firstRoot` exactly when
they are equal. Note that `f` and `-f` do not share `firstRoot`: `(-f).firstRoot = f.secondRoot`. -/
theorem firstRoot_eq_firstRoot_iff {f g : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (hfg : f.discrim = g.discrim) :
    f.firstRoot = g.firstRoot ↔ f = g := by
  refine ⟨fun h ↦ ?_, congrArg firstRoot⟩
  have haf := a_ne_zero_of_not_isSquare_discrim hD
  have hag := a_ne_zero_of_not_isSquare_discrim (hfg ▸ hD)
  have hg' := two_mul_a_mul_firstRoot_add_b hag
  rw [← h, ← hfg] at hg'
  have hlin : ((2 * (f.a - g.a) : ℤ) : ℝ) * f.firstRoot + (f.b - g.b : ℤ) = 0 := by
    push_cast
    linear_combination two_mul_a_mul_firstRoot_add_b haf - hg'
  have hab : 2 * (f.a - g.a) = 0 ∧ f.b - g.b = 0 := by
    by_contra! hne
    exact mul_firstRoot_add_ne_zero hpos hD (by tauto) hlin
  have ha : f.a = g.a := by lia
  have hb : f.b = g.b := by lia
  have hc : f.c = g.c := by
    simp only [discrim_def, discrim, ha, hb] at hfg
    have : 4 * g.a * (f.c - g.c) = 0 := by linarith
    simpa [hag, sub_eq_zero] using this
  exact BinaryQuadraticForm.ext ha hb hc

/-- For a fixed nonnegative nonsquare discriminant `D`, a form is determined by its `firstRoot`. -/
theorem firstRoot_injOn {D : ℤ} (hpos : 0 ≤ D) (hD : ¬ IsSquare D) :
    Set.InjOn firstRoot {f : BinaryQuadraticForm ℤ | f.discrim = D} :=
  fun _ hf _ hg h ↦
    (firstRoot_eq_firstRoot_iff (hf.symm ▸ hpos) (hf.symm ▸ hD) (hf.trans hg.symm)).mp h

/-- For a fixed nonnegative nonsquare discriminant `D`, a form is determined by its `secondRoot`. -/
theorem secondRoot_injOn {D : ℤ} (hpos : 0 ≤ D) (hD : ¬ IsSquare D) :
    Set.InjOn secondRoot {f : BinaryQuadraticForm ℤ | f.discrim = D} := by
  intro f hf g hg h
  have hfg : f.discrim = g.discrim := hf.trans hg.symm
  have haf := a_ne_zero_of_not_isSquare_discrim (hf.symm ▸ hD)
  have hag := a_ne_zero_of_not_isSquare_discrim (hg.symm ▸ hD)
  have hg' := two_mul_a_mul_secondRoot_add_b hag
  rw [← h, ← hfg] at hg'
  have hlin : ((2 * (f.a - g.a) : ℤ) : ℝ) * f.secondRoot + (f.b - g.b : ℤ) = 0 := by
    push_cast
    linear_combination two_mul_a_mul_secondRoot_add_b haf - hg'
  have hab : 2 * (f.a - g.a) = 0 ∧ f.b - g.b = 0 := by
    by_contra! hne
    exact mul_secondRoot_add_ne_zero (hf.symm ▸ hpos) (hf.symm ▸ hD) (by tauto) hlin
  have ha : f.a = g.a := by lia
  have hb : f.b = g.b := by lia
  have hc : f.c = g.c := by
    simp only [discrim_def, discrim, ha, hb] at hfg
    have : 4 * g.a * (f.c - g.c) = 0 := by linarith
    simpa [hag, sub_eq_zero] using this
  exact BinaryQuadraticForm.ext ha hb hc

/-! ### Equivariance under `SL(2, ℤ)` -/

/-- The leading coefficient `(γ • f).a = f(s, -r)` factors over `ℝ` through the two Möbius
denominators: `(γ • f).a = a (r · firstRoot + s) (r · secondRoot + s)`. -/
theorem smul_a_eq_mul_denom (γ : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (ha : f.a ≠ 0) :
    ((γ • f).a : ℝ) =
      f.a * ((γ 1 0 : ℝ) * f.firstRoot + γ 1 1) * ((γ 1 0 : ℝ) * f.secondRoot + γ 1 1) := by
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hsum : (f.a : ℝ) * (f.firstRoot + f.secondRoot) = -f.b := by
    rw [firstRoot_add_secondRoot, mul_div_cancel₀ _ ha']
  have hprod : (f.a : ℝ) * (f.firstRoot * f.secondRoot) = f.c := by
    rw [firstRoot_mul_secondRoot hpos, mul_div_cancel₀ _ ha']
  rw [smul_a]
  push_cast
  linear_combination -((γ 1 0 : ℝ) * (γ 1 1 : ℝ)) * hsum - (γ 1 0 : ℝ) ^ 2 * hprod

/-- Derivative identity transporting `2 a x + b = s` along `γ ∈ SL(2, ℤ)` at a root `x` of
`a x² + b x + c = 0`. -/
private theorem two_mul_smul_a_mul_moebius_add_smul_b (γ : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ}
    {x s : ℝ} (heval : (f.a : ℝ) * x ^ 2 + f.b * x + f.c = 0)
    (hlin : 2 * (f.a : ℝ) * x + f.b = s) (hden : (γ 1 0 : ℝ) * x + γ 1 1 ≠ 0) :
    2 * ((γ • f).a : ℝ) * (((γ 0 0 : ℝ) * x + γ 0 1) / ((γ 1 0 : ℝ) * x + γ 1 1)) +
      (γ • f).b = s := by
  have hdet : ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 :=
    γ.intCast_fin_two_mul_sub_mul_eq_one
  refine mul_right_cancel₀ hden ?_
  have hdiv : 2 * ((γ • f).a : ℝ) * (((γ 0 0 : ℝ) * x + γ 0 1) / ((γ 1 0 : ℝ) * x + γ 1 1)) *
      ((γ 1 0 : ℝ) * x + γ 1 1) = 2 * ((γ • f).a : ℝ) * ((γ 0 0 : ℝ) * x + γ 0 1) := by
    rw [mul_assoc, div_mul_cancel₀ _ hden]
  rw [add_mul, hdiv, smul_a, smul_b]
  push_cast
  linear_combination
    ((γ 0 0 : ℝ) * γ 1 1 - γ 0 1 * γ 1 0) * ((γ 1 0 : ℝ) * x + γ 1 1) * hlin +
      s * ((γ 1 0 : ℝ) * x + γ 1 1) * hdet -
      2 * (γ 1 0 : ℝ) * ((γ 0 0 : ℝ) * γ 1 1 - γ 0 1 * γ 1 0) * heval

/-- **Möbius equivariance of `firstRoot`**: for `γ ∈ SL(2, ℤ)` and nonsquare `f.discrim ≥ 0`,
`(γ • f).firstRoot = (p · f.firstRoot + q) / (r · f.firstRoot + s)` where `γ = !![p, q; r, s]`. -/
theorem firstRoot_smul (γ : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) :
    (γ • f).firstRoot =
      ((γ 0 0 : ℝ) * f.firstRoot + γ 0 1) / ((γ 1 0 : ℝ) * f.firstRoot + γ 1 1) := by
  have ha := a_ne_zero_of_not_isSquare_discrim hD
  have hγa := a_ne_zero_of_not_isSquare_discrim (by rwa [discrim_smul])
  have h₁ := two_mul_a_mul_firstRoot_add_b hγa
  rw [discrim_smul] at h₁
  have h₂ := two_mul_smul_a_mul_moebius_add_smul_b γ (eval_firstRoot_one hpos ha)
    (two_mul_a_mul_firstRoot_add_b ha) (denom_firstRoot_ne_zero γ hpos hD)
  have h2a : (2 : ℝ) * (γ • f).a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hγa)
  exact mul_left_cancel₀ h2a (by linarith)

/-- **Möbius equivariance of `secondRoot`**: for `γ ∈ SL(2, ℤ)` and nonsquare `f.discrim ≥ 0`,
`(γ • f).secondRoot = (p · f.secondRoot + q) / (r · f.secondRoot + s)` where
`γ = !![p, q; r, s]`. -/
theorem secondRoot_smul (γ : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) :
    (γ • f).secondRoot =
      ((γ 0 0 : ℝ) * f.secondRoot + γ 0 1) / ((γ 1 0 : ℝ) * f.secondRoot + γ 1 1) := by
  have ha := a_ne_zero_of_not_isSquare_discrim hD
  have hγa := a_ne_zero_of_not_isSquare_discrim (by rwa [discrim_smul])
  have h₁ := two_mul_a_mul_secondRoot_add_b hγa
  rw [discrim_smul] at h₁
  have h₂ := two_mul_smul_a_mul_moebius_add_smul_b γ (eval_secondRoot_one hpos ha)
    (two_mul_a_mul_secondRoot_add_b ha) (denom_secondRoot_ne_zero γ hpos hD)
  have h2a : (2 : ℝ) * (γ • f).a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hγa)
  exact mul_left_cancel₀ h2a (by linarith)

/-- The rotation `S` sends `firstRoot` to `-firstRoot⁻¹`. -/
theorem firstRoot_S_smul {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) :
    (ModularGroup.S • f).firstRoot = -f.firstRoot⁻¹ := by
  rw [firstRoot_smul ModularGroup.S hpos hD]
  simp [ModularGroup.coe_S, neg_div, one_div]

/-- The rotation `S` sends `secondRoot` to `-secondRoot⁻¹`. -/
theorem secondRoot_S_smul {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) :
    (ModularGroup.S • f).secondRoot = -f.secondRoot⁻¹ := by
  rw [secondRoot_smul ModularGroup.S hpos hD]
  simp [ModularGroup.coe_S, neg_div, one_div]

/-- For `a ≠ 0`, the translation `T ^ k` adds `k` to `firstRoot`. -/
theorem firstRoot_T_zpow_smul (k : ℤ) {f : BinaryQuadraticForm ℤ} (ha : f.a ≠ 0) :
    (ModularGroup.T ^ k • f).firstRoot = f.firstRoot + k := by
  have ha' : (2 : ℝ) * f.a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr ha)
  rw [firstRoot_def, firstRoot_def, discrim_smul, T_zpow_smul]
  dsimp only
  push_cast
  field_simp [ha']
  ring

/-- For `a ≠ 0`, the translation `T ^ k` adds `k` to `secondRoot`. -/
theorem secondRoot_T_zpow_smul (k : ℤ) {f : BinaryQuadraticForm ℤ} (ha : f.a ≠ 0) :
    (ModularGroup.T ^ k • f).secondRoot = f.secondRoot + k := by
  have ha' : (2 : ℝ) * f.a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr ha)
  rw [secondRoot_def, secondRoot_def, discrim_smul, T_zpow_smul]
  dsimp only
  push_cast
  field_simp [ha']
  ring

/-- Explicit matrix formula for `reductionStep`: `f.reductionStep = (T ^ k * S) • f` with
`k = -((Int.sqrt f.discrim + f.b) / (2 * f.c))`. -/
theorem reductionStep_eq_smul (f : BinaryQuadraticForm ℤ) :
    f.reductionStep =
      (ModularGroup.T ^ (-((Int.sqrt f.discrim + f.b) / (2 * f.c))) * ModularGroup.S) • f := by
  ext
  · rw [reductionStep_a, mul_smul, S_smul, T_zpow_smul]
  · rw [reductionStep_b, mul_smul, S_smul, T_zpow_smul]
    dsimp only
    linear_combination -Int.mul_ediv_add_emod (Int.sqrt f.discrim + f.b) (2 * f.c)
  · rw [reductionStep_c, mul_smul, S_smul, T_zpow_smul]
    dsimp only
    ring

/-- On `firstRoot`, the Gauss reduction step acts by `x ↦ -x⁻¹ - ((s + b) / (2 c))` with
`s = Int.sqrt f.discrim`. -/
theorem firstRoot_reductionStep {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) :
    f.reductionStep.firstRoot =
      -f.firstRoot⁻¹ - (((Int.sqrt f.discrim + f.b) / (2 * f.c) : ℤ) : ℝ) := by
  rw [reductionStep_eq_smul, mul_smul,
    firstRoot_T_zpow_smul _ (by rw [S_smul]; exact c_ne_zero_of_not_isSquare_discrim hD),
    firstRoot_S_smul hpos hD, Int.cast_neg, ← sub_eq_add_neg]

/-- On `secondRoot`, the Gauss reduction step acts by `x ↦ -x⁻¹ - ((s + b) / (2 c))` with
`s = Int.sqrt f.discrim`. -/
theorem secondRoot_reductionStep {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) :
    f.reductionStep.secondRoot =
      -f.secondRoot⁻¹ - (((Int.sqrt f.discrim + f.b) / (2 * f.c) : ℤ) : ℝ) := by
  rw [reductionStep_eq_smul, mul_smul,
    secondRoot_T_zpow_smul _ (by rw [S_smul]; exact c_ne_zero_of_not_isSquare_discrim hD),
    secondRoot_S_smul hpos hD, Int.cast_neg, ← sub_eq_add_neg]

/-- An element `γ ∈ SL(2, ℤ)` fixes a form `f` of nonnegative nonsquare discriminant if and only
if its Möbius transformation fixes `f.firstRoot`. -/
theorem mem_stabilizer_iff_firstRoot {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    γ ∈ stabilizer SL(2, ℤ) f ↔
      ((γ 0 0 : ℝ) * f.firstRoot + γ 0 1) / ((γ 1 0 : ℝ) * f.firstRoot + γ 1 1) = f.firstRoot := by
  rw [mem_stabilizer_iff,
    ← firstRoot_eq_firstRoot_iff (by rwa [discrim_smul]) (by rwa [discrim_smul])
      (discrim_smul γ f),
    firstRoot_smul γ hpos hD]

/-! ### Characterisation of Gauss reduced forms by their roots -/

private theorem isGaussReduced_imp_root_bounds {f : BinaryQuadraticForm ℤ}
    (hf : f.IsGaussReduced) :
    f.firstRoot * f.secondRoot < 0 ∧ |f.firstRoot| < 1 ∧ 1 < |f.secondRoot| := by
  have hD : 0 ≤ f.discrim := hf.discrim_pos.le
  have hac : f.a * f.c < 0 := (isGaussReduced_iff.mp hf).1
  have ha : f.a ≠ 0 := left_ne_zero_of_mul hac.ne
  have : 0 < |(f.a : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr ha)
  obtain ⟨h₁, h₂⟩ := isGaussReduced_iff_abs_sqrt_sub_lt.mp hf
  have hb : (0 : ℝ) < f.b := by exact_mod_cast hf.b_pos
  obtain ⟨hl, hu⟩ := abs_lt.mp h₁
  have hprod : f.firstRoot * f.secondRoot < 0 := by
    rw [firstRoot_mul_secondRoot hD, div_neg_iff]
    rcases lt_or_gt_of_ne ha with haneg | hapos
    · exact Or.inl ⟨by exact_mod_cast (by nlinarith : 0 < f.c), by exact_mod_cast haneg⟩
    · exact Or.inr ⟨by exact_mod_cast (by nlinarith : f.c < 0), by exact_mod_cast hapos⟩
  have hf_abs : |f.firstRoot| < 1 := by
    rw [firstRoot_def, abs_div, abs_mul, abs_two,
      abs_of_pos (a := -(f.b : ℝ) + √(f.discrim : ℝ)) (by linarith), div_lt_one (by positivity)]
    linarith
  have hs_abs : 1 < |f.secondRoot| := by
    rw [secondRoot_def, abs_div, abs_mul, abs_two,
      abs_of_neg (a := -(f.b : ℝ) - √(f.discrim : ℝ)) (by linarith), one_lt_div (by positivity)]
    linarith
  exact ⟨hprod, hf_abs, hs_abs⟩

private theorem isGaussReduced_of_root_bounds {f : BinaryQuadraticForm ℤ}
    (hprod : f.firstRoot * f.secondRoot < 0) (hf_abs : |f.firstRoot| < 1)
    (hs_abs : 1 < |f.secondRoot|) : f.IsGaussReduced := by
  have ha : f.a ≠ 0 := by
    rintro ha
    simp [firstRoot_def, ha] at hprod
  have hDpos : (0 : ℝ) < f.discrim := by
    by_contra! hle
    rw [firstRoot_def, secondRoot_def, Real.sqrt_eq_zero_of_nonpos hle, add_zero, sub_zero] at hprod
    exact hprod.not_ge (mul_self_nonneg _)
  have hspos : 0 < √(f.discrim : ℝ) := Real.sqrt_pos.mpr hDpos
  have : 0 < |(f.a : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr ha)
  have hsq_lt : f.firstRoot ^ 2 < f.secondRoot ^ 2 := by
    rw [← sq_abs f.firstRoot, ← sq_abs f.secondRoot]
    nlinarith [abs_nonneg f.firstRoot]
  have hb : (0 : ℝ) < f.b := by
    rw [firstRoot_def, secondRoot_def, div_pow, div_pow,
      div_lt_div_iff_of_pos_right (sq_pos_of_ne_zero (mul_ne_zero two_ne_zero
        (Int.cast_ne_zero.mpr ha)))] at hsq_lt
    have : 4 * (f.b : ℝ) * √(f.discrim : ℝ) > 0 := by linarith
    nlinarith
  have hac : f.a * f.c < 0 := by
    rw [firstRoot_mul_secondRoot (by exact_mod_cast hDpos.le), div_neg_iff] at hprod
    rcases hprod with ⟨hc, ha0⟩ | ⟨hc, ha0⟩
    · have hc' : 0 < f.c := by exact_mod_cast hc
      have ha0' : f.a < 0 := by exact_mod_cast ha0
      nlinarith
    · have hc' : f.c < 0 := by exact_mod_cast hc
      have ha0' : 0 < f.a := by exact_mod_cast ha0
      nlinarith
  have hbs : (f.b : ℝ) < √(f.discrim : ℝ) := by
    have hbd : f.b ^ 2 < f.discrim := by rw [discrim_def, discrim]; nlinarith
    have hbd' : (f.b : ℝ) ^ 2 < √(f.discrim : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hDpos.le]
      exact_mod_cast hbd
    nlinarith
  rw [firstRoot_def, abs_div, abs_mul, abs_two,
    abs_of_pos (a := -(f.b : ℝ) + √(f.discrim : ℝ)) (by linarith), div_lt_one (by positivity)]
    at hf_abs
  rw [secondRoot_def, abs_div, abs_mul, abs_two,
    abs_of_neg (a := -(f.b : ℝ) - √(f.discrim : ℝ)) (by linarith), one_lt_div (by positivity)]
    at hs_abs
  rw [isGaussReduced_iff_abs_sqrt_sub_lt]
  refine ⟨abs_lt.mpr ⟨?_, ?_⟩, hbs⟩ <;> linarith

/-- **Root characterisation of Gauss reduced forms**: an integral binary quadratic form `f` is
Gauss reduced if and only if `f.firstRoot * f.secondRoot < 0`, `|f.firstRoot| < 1` and
`1 < |f.secondRoot|` (Buchmann–Vollmer, Chapter 6; Zagier, §13). -/
theorem isGaussReduced_iff_firstRoot_secondRoot {f : BinaryQuadraticForm ℤ} :
    f.IsGaussReduced ↔
      f.firstRoot * f.secondRoot < 0 ∧ |f.firstRoot| < 1 ∧ 1 < |f.secondRoot| :=
  ⟨isGaussReduced_imp_root_bounds, fun ⟨h₁, h₂, h₃⟩ ↦ isGaussReduced_of_root_bounds h₁ h₂ h₃⟩

namespace IsGaussReduced

variable {f : BinaryQuadraticForm ℤ}

/-- A Gauss reduced form with `0 < a` has `firstRoot ∈ (0, 1)`. -/
theorem firstRoot_mem_Ioo_of_a_pos (hf : f.IsGaussReduced) (ha : 0 < f.a) :
    f.firstRoot ∈ Set.Ioo 0 1 := by
  obtain ⟨_, h₁, _⟩ := isGaussReduced_iff_firstRoot_secondRoot.mp hf
  obtain ⟨_, hbs⟩ := isGaussReduced_iff_abs_sqrt_sub_lt.mp hf
  have ha' : (0 : ℝ) < 2 * f.a := by exact_mod_cast mul_pos two_pos ha
  exact ⟨by rw [firstRoot_def]; exact div_pos (by linarith) ha', (abs_lt.mp h₁).2⟩

/-- A Gauss reduced form with `0 < a` has `secondRoot < -1`. -/
theorem secondRoot_lt_neg_one_of_a_pos (hf : f.IsGaussReduced) (ha : 0 < f.a) :
    f.secondRoot < -1 := by
  obtain ⟨_, _, h₂⟩ := isGaussReduced_iff_firstRoot_secondRoot.mp hf
  have hb : (0 : ℝ) < f.b := by exact_mod_cast hf.b_pos
  have hs : 0 ≤ √(f.discrim : ℝ) := Real.sqrt_nonneg _
  have ha' : (0 : ℝ) < 2 * f.a := by exact_mod_cast mul_pos two_pos ha
  have hneg : f.secondRoot < 0 := by
    rw [secondRoot_def]
    exact div_neg_of_neg_of_pos (by linarith) ha'
  rw [abs_of_neg hneg] at h₂
  linarith

/-- A Gauss reduced form with `0 < a` has `secondRoot < firstRoot`. -/
theorem secondRoot_lt_firstRoot_of_a_pos (hf : f.IsGaussReduced) (ha : 0 < f.a) :
    f.secondRoot < f.firstRoot :=
  (hf.secondRoot_lt_neg_one_of_a_pos ha).trans <|
    (by norm_num : (-1 : ℝ) < 0).trans (hf.firstRoot_mem_Ioo_of_a_pos ha).1

/-- A Gauss reduced form with `a < 0` has `firstRoot ∈ (-1, 0)`. -/
theorem firstRoot_mem_Ioo_of_a_neg (hf : f.IsGaussReduced) (ha : f.a < 0) :
    f.firstRoot ∈ Set.Ioo (-1) 0 := by
  obtain ⟨_, h₁, _⟩ := isGaussReduced_iff_firstRoot_secondRoot.mp hf
  obtain ⟨_, hbs⟩ := isGaussReduced_iff_abs_sqrt_sub_lt.mp hf
  have ha' : (2 : ℝ) * f.a < 0 := by
    have : 2 * f.a < 0 := mul_neg_of_pos_of_neg two_pos ha
    exact_mod_cast this
  exact ⟨(abs_lt.mp h₁).1, by rw [firstRoot_def]; exact div_neg_of_pos_of_neg (by linarith) ha'⟩

/-- A Gauss reduced form with `a < 0` has `1 < secondRoot`. -/
theorem one_lt_secondRoot_of_a_neg (hf : f.IsGaussReduced) (ha : f.a < 0) :
    1 < f.secondRoot := by
  obtain ⟨_, _, h₂⟩ := isGaussReduced_iff_firstRoot_secondRoot.mp hf
  have hb : (0 : ℝ) < f.b := by exact_mod_cast hf.b_pos
  have hs : 0 ≤ √(f.discrim : ℝ) := Real.sqrt_nonneg _
  have ha' : (2 : ℝ) * f.a < 0 := by
    have : 2 * f.a < 0 := mul_neg_of_pos_of_neg two_pos ha
    exact_mod_cast this
  have hpos : 0 < f.secondRoot := by
    rw [secondRoot_def]
    exact div_pos_of_neg_of_neg (by linarith) ha'
  rwa [abs_of_pos hpos] at h₂

end IsGaussReduced

end TauCeti.BinaryQuadraticForm
