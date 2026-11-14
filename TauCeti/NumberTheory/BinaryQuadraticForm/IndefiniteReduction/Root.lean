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
`D = b² - 4 a c` has two distinct real roots for the inhomogeneous polynomial `a t² + b t + c`:
its **first root** `ω₁(f) = (-b + √D) / (2 a)` and its **second root** `ω₂(f) = (-b - √D) / (2 a)`.
Unlike positive definite forms, whose leading coefficient has a fixed sign, an indefinite form in a
proper equivalence class or in a cycle of Gauss reduced forms alternates the sign of `a`, so both
roots are real and neither lies in a half-plane. Nonetheless, because changes of variables in
`SL(2, ℤ)` have determinant `+1` rather than `-1`, the Möbius transformation
`t ↦ (p t + q) / (r t + s)` of `γ = !![p, q; r, s] ∈ SL(2, ℤ)` carries the first root of `f` to the
first root of `γ • f` and the second root of `f` to the second root of `γ • f`, regardless of the
signs of `a` and `(γ • f).a`.

When `D ≥ 0` is not a square, `√D` is irrational, so `ω₁(f)` and `ω₂(f)` are irrational
(`irrational_firstRoot`, `irrational_secondRoot`) and `ω₁(f)` uniquely determines all three
coefficients `(a, b, c)` among forms of discriminant `D` (`firstRoot_injOn`): the `√D`-component
`1 / (2 a)` fixes `a`, the rational part `-b / (2 a)` fixes `b`, and the discriminant fixes `c`.

In terms of the two roots, Gauss reducedness of `f` is equivalent to the classical root separation
condition (`isGaussReduced_iff_roots`):
`ω₁(f) * ω₂(f) < 0`, `|ω₁(f)| < 1`, and `1 < |ω₂(f)|`.
One reduction step `f ↦ f.reductionStep` acts on `ω₁(f)` by the continued-fraction step
`ω₁(f.reductionStep) = -q - 1 / ω₁(f)` with `q = (⌊√D⌋ + b) / (2 c)`
(`firstRoot_mul_firstRoot_reductionStep`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.firstRoot`: the real number `(-b + √D) / (2 a)`.
* `TauCeti.BinaryQuadraticForm.secondRoot`: the real number `(-b - √D) / (2 a)`.

## Main results

* `TauCeti.BinaryQuadraticForm.isGaussReduced_iff_roots`: `f` is Gauss reduced if and only if
  `f.firstRoot * f.secondRoot < 0`, `|f.firstRoot| < 1`, and `1 < |f.secondRoot|`.
* `TauCeti.BinaryQuadraticForm.irrational_firstRoot` and
  `TauCeti.BinaryQuadraticForm.irrational_secondRoot`: for a nonnegative nonsquare discriminant,
  both roots are irrational.
* `TauCeti.BinaryQuadraticForm.firstRoot_injOn`: for a nonnegative nonsquare discriminant `D`, a
  form of discriminant `D` is determined by its first root.
* `TauCeti.BinaryQuadraticForm.firstRoot_smul` and `TauCeti.BinaryQuadraticForm.secondRoot_smul`:
  both roots transform by the Möbius action of `SL(2, ℤ)`.
* `TauCeti.BinaryQuadraticForm.denom_inv_mul_denom_firstRoot`: the Möbius automorphy-factor
  identity `((γ⁻¹ 1 0) ω₁(γ • f) + γ⁻¹ 1 1) ((γ 1 0) ω₁(f) + γ 1 1) = 1`.
* `TauCeti.BinaryQuadraticForm.reductionStep_eq_smul` and
  `TauCeti.BinaryQuadraticForm.firstRoot_mul_firstRoot_reductionStep`: explicit matrix action of
  `reductionStep` on forms and on `firstRoot`.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 183–193.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.6.
* J. Buchmann and U. Vollmer, *Binary Quadratic Forms: An Algorithmic Approach*, Springer, 2007,
  §6.1–6.3.
-/

public section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- The **first root** `(-b + √D) / (2 a)` of an integral binary quadratic form
`f = a x² + b x y + c y²` of discriminant `D = b² - 4 a c`. -/
noncomputable def firstRoot (f : BinaryQuadraticForm ℤ) : ℝ :=
  (-(f.b : ℝ) + √(f.discrim : ℝ)) / (2 * f.a)

/-- The **second root** `(-b - √D) / (2 a)` of an integral binary quadratic form
`f = a x² + b x y + c y²` of discriminant `D = b² - 4 a c`. -/
noncomputable def secondRoot (f : BinaryQuadraticForm ℤ) : ℝ :=
  (-(f.b : ℝ) - √(f.discrim : ℝ)) / (2 * f.a)

/-- Definitional expansion of `firstRoot`. -/
theorem firstRoot_def (f : BinaryQuadraticForm ℤ) :
    f.firstRoot = (-(f.b : ℝ) + √(f.discrim : ℝ)) / (2 * f.a) := by
  rfl

/-- Definitional expansion of `secondRoot`. -/
theorem secondRoot_def (f : BinaryQuadraticForm ℤ) :
    f.secondRoot = (-(f.b : ℝ) - √(f.discrim : ℝ)) / (2 * f.a) := by
  rfl

/-- Negating a form exchanges its first and second roots. -/
@[simp] theorem firstRoot_neg (f : BinaryQuadraticForm ℤ) :
    (-f).firstRoot = f.secondRoot := by
  have hd : (-f).discrim = f.discrim := by simp [discrim_def, _root_.discrim]
  rw [firstRoot_def, secondRoot_def, hd, neg_a, neg_b]
  push_cast
  ring

/-- Negating a form exchanges its second and first roots. -/
@[simp] theorem secondRoot_neg (f : BinaryQuadraticForm ℤ) :
    (-f).secondRoot = f.firstRoot := by
  rw [← firstRoot_neg, neg_neg]

/-- Vieta's sum formula `ω₁(f) + ω₂(f) = -b / a`. -/
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
      2 * √(f.discrim : ℝ) := by ring
  rw [h, mul_div_mul_left _ _ two_ne_zero]

/-- Vieta's product formula `ω₁(f) ω₂(f) = c / a` for nonnegative discriminant. -/
theorem firstRoot_mul_secondRoot {f : BinaryQuadraticForm ℤ} (hD : 0 ≤ f.discrim) :
    f.firstRoot * f.secondRoot = (f.c : ℝ) / f.a := by
  rcases eq_or_ne f.a 0 with ha | ha
  · simp [firstRoot_def, secondRoot_def, ha]
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hs : √(f.discrim : ℝ) ^ 2 = f.discrim := Real.sq_sqrt (by exact_mod_cast hD)
  have hd : (f.discrim : ℝ) = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
    simp [discrim_def, _root_.discrim]
  rw [firstRoot_def, secondRoot_def]
  field_simp
  linarith

/-- For nonnegative discriminant and nonzero leading coefficient, `firstRoot` is a root of
`a t² + b t + c = 0`. -/
theorem eval_firstRoot {f : BinaryQuadraticForm ℤ} (hD : 0 ≤ f.discrim) (ha : f.a ≠ 0) :
    (f.a : ℝ) * f.firstRoot ^ 2 + f.b * f.firstRoot + f.c = 0 := by
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hs : √(f.discrim : ℝ) ^ 2 = f.discrim := Real.sq_sqrt (by exact_mod_cast hD)
  have hd : (f.discrim : ℝ) = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
    simp [discrim_def, _root_.discrim]
  rw [firstRoot_def]
  field_simp
  linarith

/-- For nonnegative discriminant and nonzero leading coefficient, `secondRoot` is a root of
`a t² + b t + c = 0`. -/
theorem eval_secondRoot {f : BinaryQuadraticForm ℤ} (hD : 0 ≤ f.discrim) (ha : f.a ≠ 0) :
    (f.a : ℝ) * f.secondRoot ^ 2 + f.b * f.secondRoot + f.c = 0 := by
  have hd : 0 ≤ (-f).discrim := by
    have : (-f).discrim = f.discrim := by simp [discrim_def, _root_.discrim]
    rwa [this]
  have h := eval_firstRoot hd (by simpa only [neg_a, neg_ne_zero] using ha)
  rw [firstRoot_neg, neg_a, neg_b, neg_c] at h
  push_cast at h
  linarith

/-! ### Root characterization of Gauss reduced forms -/

/-- The two real root expressions have opposite signs if and only if `a * c < 0` (when
`f.discrim ≤ 0`, both sides are false because `√(f.discrim : ℝ) = 0` and `b² - 4 a c ≤ 0`). -/
@[simp] theorem firstRoot_mul_secondRoot_lt_zero_iff {f : BinaryQuadraticForm ℤ} :
    f.firstRoot * f.secondRoot < 0 ↔ f.a * f.c < 0 := by
  rcases le_or_gt f.discrim 0 with hD | hD
  · refine iff_of_false ?_ ?_
    · rw [firstRoot_def, secondRoot_def, Real.sqrt_eq_zero_of_nonpos (by exact_mod_cast hD)]
      simp only [add_zero, sub_zero]
      exact (mul_self_nonneg _).not_gt
    · rw [discrim_def, _root_.discrim] at hD
      nlinarith [sq_nonneg f.b]
  rcases eq_or_ne f.a 0 with ha | ha
  · simp [firstRoot_def, ha]
  rw [firstRoot_mul_secondRoot hD.le]
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have ha2 : (0 : ℝ) < (f.a : ℝ) ^ 2 := by positivity
  have hcancel : (f.a : ℝ) ^ 2 * ((f.c : ℝ) / f.a) = (f.a : ℝ) * f.c := by field_simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : (f.a : ℝ) * f.c < 0 := by nlinarith [mul_lt_mul_of_pos_left h ha2]
    exact_mod_cast h'
  · have h' : (f.a : ℝ) * f.c < 0 := by exact_mod_cast h
    nlinarith

/-- **Root characterization of Gauss reduced forms**: an integral binary quadratic form `f` is
Gauss reduced if and only if its two roots have opposite signs (`ω₁(f) ω₂(f) < 0`), `|ω₁(f)| < 1`,
and `1 < |ω₂(f)|`. No sign or nonsquare assumption on `f` is required: when `a = 0` or `D ≤ 0`,
both sides are false. -/
theorem isGaussReduced_iff_roots {f : BinaryQuadraticForm ℤ} :
    f.IsGaussReduced ↔
      f.firstRoot * f.secondRoot < 0 ∧ |f.firstRoot| < 1 ∧ 1 < |f.secondRoot| := by
  rcases eq_or_ne f.a 0 with ha | ha
  · simp [isGaussReduced_iff, ha]
  rcases le_or_gt f.discrim 0 with hD | hD
  · refine iff_of_false (fun hf ↦ hf.discrim_pos.not_ge hD) fun ⟨hac, _⟩ ↦ ?_
    rw [firstRoot_mul_secondRoot_lt_zero_iff] at hac
    rw [discrim_def, _root_.discrim] at hD
    nlinarith [sq_nonneg f.b]
  have ha_pos : (0 : ℝ) < 2 * |(f.a : ℝ)| := by
    have : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
    positivity
  have habs₁ : |f.firstRoot| < 1 ↔ |-(f.b : ℝ) + √(f.discrim : ℝ)| < 2 * |(f.a : ℝ)| := by
    rw [firstRoot_def, abs_div, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), div_lt_one ha_pos]
  have habs₂ : 1 < |f.secondRoot| ↔ 2 * |(f.a : ℝ)| < |-(f.b : ℝ) - √(f.discrim : ℝ)| := by
    rw [secondRoot_def, abs_div, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), one_lt_div ha_pos]
  rw [isGaussReduced_iff_abs_sqrt_sub_lt, firstRoot_mul_secondRoot_lt_zero_iff, habs₁, habs₂]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hb : (0 : ℝ) < f.b := (abs_nonneg _).trans_lt h₁
    have hs := Real.sq_sqrt (by exact_mod_cast hD.le : (0 : ℝ) ≤ f.discrim)
    have hd : (f.discrim : ℝ) = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
      simp [discrim_def, _root_.discrim]
    have hac : (f.a : ℝ) * f.c < 0 := by nlinarith
    obtain ⟨h₃, h₄⟩ := abs_lt.mp h₁
    refine ⟨by exact_mod_cast hac, abs_lt.mpr ⟨by linarith, by linarith⟩, ?_⟩
    rw [abs_of_neg (a := -(f.b : ℝ) - √(f.discrim : ℝ)) (by linarith)]
    linarith
  · rintro ⟨hac, h₁, h₂⟩
    have hd : (f.discrim : ℝ) = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
      simp [discrim_def, _root_.discrim]
    have hac' : (f.a : ℝ) * f.c < 0 := by exact_mod_cast hac
    have hsq : (f.b : ℝ) ^ 2 < √(f.discrim : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by exact_mod_cast hD.le)]
      linarith
    obtain ⟨hb₁, hb₂⟩ := abs_lt.mp
      (by simpa only [Real.sqrt_nonneg, abs_of_nonneg] using sq_lt_sq.mp hsq)
    rw [abs_of_pos (a := -(f.b : ℝ) + √(f.discrim : ℝ)) (by linarith)] at h₁
    rw [abs_of_neg (a := -(f.b : ℝ) - √(f.discrim : ℝ)) (by linarith)] at h₂
    exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, hb₂⟩

/-! ### Irrationality and injectivity for nonsquare discriminant -/

/-- For a form `f` of nonnegative nonsquare discriminant, `f.firstRoot` is irrational. -/
theorem irrational_firstRoot {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) : Irrational f.firstRoot := by
  have h2a : (2 * f.a : ℤ) ≠ 0 := mul_ne_zero two_ne_zero (a_ne_zero_of_not_isSquare_discrim hD)
  have hrew : f.firstRoot = ((-f.b : ℤ) + √(f.discrim : ℝ)) / ((2 * f.a : ℤ) : ℝ) := by
    rw [firstRoot_def]; push_cast; rfl
  rw [hrew]
  exact (((irrational_sqrt_intCast_iff_of_nonneg hpos).mpr hD).intCast_add (-f.b)).div_intCast h2a

/-- For a form `f` of nonnegative nonsquare discriminant, `f.secondRoot` is irrational. -/
theorem irrational_secondRoot {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) : Irrational f.secondRoot := by
  have hd : (-f).discrim = f.discrim := by simp [discrim_def, _root_.discrim]
  rw [← firstRoot_neg]
  exact irrational_firstRoot (hd.symm ▸ hpos) (hd.symm ▸ hD)

/-- For a form `f` of nonnegative nonsquare discriminant, `1` and `f.firstRoot` are `ℤ`-linearly
independent in `ℝ`. -/
@[simp] theorem intCast_mul_firstRoot_add_intCast_eq_zero_iff {f : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hD : ¬ IsSquare f.discrim) (r s : ℤ) :
    (r : ℝ) * f.firstRoot + s = 0 ↔ r = 0 ∧ s = 0 := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; simp⟩
  rcases eq_or_ne r 0 with rfl | hr
  · exact ⟨rfl, by simpa using h⟩
  have hs' : (r : ℝ) * f.firstRoot = ((-s : ℤ) : ℝ) := by push_cast; linarith
  exact absurd hs' (((irrational_firstRoot hpos hD).intCast_mul hr).ne_int (-s))

/-- For a form `f` of nonnegative nonsquare discriminant, `|r * f.firstRoot + s| = 1` with
`r, s : ℤ` holds only when `r = 0` and `s = ±1`. -/
theorem abs_intCast_mul_firstRoot_add_intCast_eq_one_iff {f : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hD : ¬ IsSquare f.discrim) (r s : ℤ) :
    |(r : ℝ) * f.firstRoot + s| = 1 ↔ r = 0 ∧ (s = 1 ∨ s = -1) := by
  rw [abs_eq (zero_le_one' ℝ)]
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl | rfl⟩ <;> simp⟩
  rcases h with h | h
  · have h0 : (r : ℝ) * f.firstRoot + ((s - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    obtain ⟨hr, hs⟩ := (intCast_mul_firstRoot_add_intCast_eq_zero_iff hpos hD r (s - 1)).mp h0
    exact ⟨hr, Or.inl (sub_eq_zero.mp hs)⟩
  · have h0 : (r : ℝ) * f.firstRoot + ((s + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    obtain ⟨hr, hs⟩ := (intCast_mul_firstRoot_add_intCast_eq_zero_iff hpos hD r (s + 1)).mp h0
    exact ⟨hr, Or.inr (eq_neg_of_add_eq_zero_left hs)⟩

/-- **A form of nonnegative nonsquare discriminant is determined by its first root**: on the set of
integral binary quadratic forms of fixed discriminant `D ≥ 0` with `¬ IsSquare D`, `firstRoot` is
injective. Primitivity is not needed. -/
theorem firstRoot_injOn {D : ℤ} (hpos : 0 ≤ D) (hD : ¬ IsSquare D) :
    Set.InjOn firstRoot {f : BinaryQuadraticForm ℤ | f.discrim = D} := by
  intro f hf g hg h
  have hfD : f.discrim = D := hf
  have hgD : g.discrim = D := hg
  have hfa : f.a ≠ 0 := a_ne_zero_of_not_isSquare_discrim (hfD ▸ hD)
  have hga : g.a ≠ 0 := a_ne_zero_of_not_isSquare_discrim (hgD ▸ hD)
  have hfa' : (2 : ℝ) * f.a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hfa)
  have hga' : (2 : ℝ) * g.a ≠ 0 := mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hga)
  rw [firstRoot_def, firstRoot_def, hfD, hgD, div_eq_div_iff hfa' hga'] at h
  have hlin : (((2 * (g.a - f.a)) : ℤ) : ℝ) * √(D : ℝ) =
      (((2 * (f.b * g.a - g.b * f.a)) : ℤ) : ℝ) := by
    push_cast
    linarith
  have ha0 : 2 * (g.a - f.a) = 0 := by
    by_contra hne
    exact (((irrational_sqrt_intCast_iff_of_nonneg hpos).mpr hD).intCast_mul hne).ne_int
      (2 * (f.b * g.a - g.b * f.a)) hlin
  have ha : f.a = g.a := by omega
  have hb : f.b = g.b := by
    rw [ha0, Int.cast_zero, zero_mul, eq_comm, Int.cast_eq_zero] at hlin
    rw [ha] at hlin
    have : 2 * g.a * (f.b - g.b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h2a | hsub
    · exact absurd h2a (mul_ne_zero two_ne_zero hga)
    · exact sub_eq_zero.mp hsub
  have hc : f.c = g.c := by
    have hdisc : f.discrim = g.discrim := hfD.trans hgD.symm
    simp only [discrim_def, _root_.discrim, ha, hb] at hdisc
    have : 4 * g.a * (f.c - g.c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h4a | hsub
    · exact absurd h4a (mul_ne_zero (by decide) hga)
    · exact sub_eq_zero.mp hsub
  exact BinaryQuadraticForm.ext ha hb hc

/-! ### Möbius covariance under `SL(2, ℤ)` -/

/-- Auxiliary root expression `(-b + t) / (2 a)` used to prove Möbius covariance uniformly for
`t = √D` (`firstRoot`) and `t = -√D` (`secondRoot`). -/
private noncomputable def rootAux (t : ℝ) (f : BinaryQuadraticForm ℤ) : ℝ :=
  (-(f.b : ℝ) + t) / (2 * f.a)

/-- Polynomial Möbius identity for `rootAux t` whenever `t² = f.discrim` and both `f` and `γ • f`
have nonzero leading coefficients. -/
private theorem mul_rootAux_smul {f : BinaryQuadraticForm ℤ} {t : ℝ} (ht : t ^ 2 = f.discrim)
    (γ : SL(2, ℤ)) (ha : f.a ≠ 0) (hγa : (γ • f).a ≠ 0) :
    ((γ 1 0 : ℝ) * rootAux t f + γ 1 1) * rootAux t (γ • f) =
      (γ 0 0 : ℝ) * rootAux t f + γ 0 1 := by
  have ha' : (f.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hγa' : ((γ • f).a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hγa
  have hdet := γ.intCast_fin_two_mul_sub_mul_eq_one (R := ℝ)
  have ht' : t ^ 2 = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
    rw [ht, discrim_def, _root_.discrim]
    push_cast
    rfl
  have hγa_eq : ((γ • f).a : ℝ) =
      f.a * (γ 1 1 : ℝ) ^ 2 - f.b * γ 1 0 * γ 1 1 + f.c * (γ 1 0 : ℝ) ^ 2 := by
    rw [smul_a]
    push_cast
    rfl
  rw [rootAux, rootAux, smul_b]
  field_simp
  push_cast
  rw [hγa_eq]
  linear_combination
    (γ 1 0 : ℝ) * ht' +
    ((f.b * γ 1 0 - 2 * f.a * γ 1 1) * t - ((f.b : ℝ) ^ 2 - 4 * f.a * f.c) * γ 1 0) * hdet

/-- For a form of nonnegative nonsquare discriminant, the Möbius denominator `γ₁₀ ω₁(f) + γ₁₁` is
nonzero for every `γ ∈ SL(2, ℤ)`. -/
theorem denom_firstRoot_ne_zero {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    (γ 1 0 : ℝ) * f.firstRoot + γ 1 1 ≠ 0 := by
  intro h
  obtain ⟨hr, hs⟩ := (intCast_mul_firstRoot_add_intCast_eq_zero_iff hpos hD _ _).mp h
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  simp [hr, hs] at hdet

/-- For a form of nonnegative nonsquare discriminant, the Möbius denominator `γ₁₀ ω₂(f) + γ₁₁` is
nonzero for every `γ ∈ SL(2, ℤ)`. -/
theorem denom_secondRoot_ne_zero {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    (γ 1 0 : ℝ) * f.secondRoot + γ 1 1 ≠ 0 := by
  have hd : (-f).discrim = f.discrim := by simp [discrim_def, _root_.discrim]
  rw [← firstRoot_neg]
  exact denom_firstRoot_ne_zero (hd.symm ▸ hpos) (hd.symm ▸ hD) γ

/-- Cleared-denominator Möbius covariance of `firstRoot` under `SL(2, ℤ)`. -/
theorem denom_mul_firstRoot_smul {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    ((γ 1 0 : ℝ) * f.firstRoot + γ 1 1) * (γ • f).firstRoot =
      (γ 0 0 : ℝ) * f.firstRoot + γ 0 1 := by
  have ht : √(f.discrim : ℝ) ^ 2 = f.discrim := Real.sq_sqrt (by exact_mod_cast hpos)
  have h := mul_rootAux_smul ht γ (a_ne_zero_of_not_isSquare_discrim hD)
    (a_ne_zero_of_not_isSquare_discrim (by rwa [discrim_smul]))
  simpa only [rootAux, discrim_smul, firstRoot_def] using h

/-- Cleared-denominator Möbius covariance of `secondRoot` under `SL(2, ℤ)`. -/
theorem denom_mul_secondRoot_smul {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    ((γ 1 0 : ℝ) * f.secondRoot + γ 1 1) * (γ • f).secondRoot =
      (γ 0 0 : ℝ) * f.secondRoot + γ 0 1 := by
  have ht : (-√(f.discrim : ℝ)) ^ 2 = f.discrim := by
    rw [neg_sq, Real.sq_sqrt (by exact_mod_cast hpos)]
  have h := mul_rootAux_smul ht γ (a_ne_zero_of_not_isSquare_discrim hD)
    (a_ne_zero_of_not_isSquare_discrim (by rwa [discrim_smul]))
  simpa only [rootAux, sub_eq_add_neg, discrim_smul, secondRoot_def] using h

/-- **Möbius equivariance of `firstRoot`**: for `γ ∈ SL(2, ℤ)` and a form `f` of nonnegative
nonsquare discriminant, `ω₁(γ • f) = (γ₀₀ ω₁(f) + γ₀₁) / (γ₁₀ ω₁(f) + γ₁₁)`. -/
theorem firstRoot_smul {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    (γ • f).firstRoot =
      ((γ 0 0 : ℝ) * f.firstRoot + γ 0 1) / ((γ 1 0 : ℝ) * f.firstRoot + γ 1 1) :=
  (eq_div_iff_mul_eq (denom_firstRoot_ne_zero hpos hD γ)).mpr
    (by rw [mul_comm]; exact denom_mul_firstRoot_smul hpos hD γ)

/-- **Möbius equivariance of `secondRoot`**: for `γ ∈ SL(2, ℤ)` and a form `f` of nonnegative
nonsquare discriminant, `ω₂(γ • f) = (γ₀₀ ω₂(f) + γ₀₁) / (γ₁₀ ω₂(f) + γ₁₁)`. -/
theorem secondRoot_smul {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    (γ • f).secondRoot =
      ((γ 0 0 : ℝ) * f.secondRoot + γ 0 1) / ((γ 1 0 : ℝ) * f.secondRoot + γ 1 1) :=
  (eq_div_iff_mul_eq (denom_secondRoot_ne_zero hpos hD γ)).mpr
    (by rw [mul_comm]; exact denom_mul_secondRoot_smul hpos hD γ)

/-- **Automorphy-factor product identity**: the Möbius denominators of `γ` at `f.firstRoot` and of
`γ⁻¹` at `(γ • f).firstRoot` multiply to `1`. -/
theorem denom_inv_mul_denom_firstRoot {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) (γ : SL(2, ℤ)) :
    ((γ⁻¹ 1 0 : ℝ) * (γ • f).firstRoot + γ⁻¹ 1 1) * ((γ 1 0 : ℝ) * f.firstRoot + γ 1 1) = 1 := by
  have hdet := γ.intCast_fin_two_mul_sub_mul_eq_one (R := ℝ)
  have hm := denom_mul_firstRoot_smul hpos hD γ
  have hinv₀ : (γ⁻¹ 1 0 : ℝ) = -(γ 1 0 : ℝ) := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have hinv₁ : (γ⁻¹ 1 1 : ℝ) = (γ 0 0 : ℝ) := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rw [hinv₀, hinv₁]
  linear_combination -(γ 1 0 : ℝ) * hm + hdet

/-- Explicit change-of-variables formula for `reductionStep`:
`f.reductionStep = (T ^ (-((Int.sqrt f.discrim + f.b) / (2 * f.c))) * S) • f`. -/
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

/-- **Action of `reductionStep` on `firstRoot`**: for `f` of nonnegative nonsquare discriminant,
`ω₁(f) ω₁(f.reductionStep) = -q ω₁(f) - 1` where `q = (⌊√D⌋ + b) / (2 c)`. -/
theorem firstRoot_mul_firstRoot_reductionStep {f : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) :
    f.firstRoot * f.reductionStep.firstRoot =
      -(((Int.sqrt f.discrim + f.b) / (2 * f.c) : ℤ) : ℝ) * f.firstRoot - 1 := by
  set q : ℤ := (Int.sqrt f.discrim + f.b) / (2 * f.c)
  set γ : SL(2, ℤ) := ModularGroup.T ^ (-q) * ModularGroup.S
  have h := denom_mul_firstRoot_smul hpos hD γ
  have hγ₀₀ : (γ 0 0 : ℝ) = -(q : ℝ) := by
    simp [γ, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  have hγ₀₁ : (γ 0 1 : ℝ) = -1 := by
    simp [γ, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  have hγ₁₀ : (γ 1 0 : ℝ) = 1 := by
    simp [γ, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  have hγ₁₁ : (γ 1 1 : ℝ) = 0 := by
    simp [γ, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  rw [hγ₀₀, hγ₀₁, hγ₁₀, hγ₁₁, one_mul, add_zero] at h
  rw [reductionStep_eq_smul]
  simpa only [q, γ, sub_eq_add_neg] using h

end TauCeti.BinaryQuadraticForm
