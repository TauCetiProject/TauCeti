/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Int.Sqrt
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.NumberTheory.BinaryQuadraticForm.LagrangeReduction
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Int.Sqrt

/-!
# Gauss reduction of indefinite binary quadratic forms, and its cycles

An integral binary quadratic form `f = a x² + b x y + c y²` of positive discriminant
`D = b² - 4 a c` is **reduced** in the sense of Gauss when `|√D - 2 |a|| < b < √D`. In terms of
the coefficients alone this says `a c < 0` and `|a + c| < b`, and that is the definition used
here (`TauCeti.BinaryQuadraticForm.IsGaussReduced`); `isGaussReduced_iff_abs_sqrt_sub_lt` proves
it agrees with the classical inequalities. A reduced form has `0 < b < √D` and
`|a| + |c| < √D`, so there are only finitely many reduced forms of a given discriminant, collected
in the explicit finite set `gaussReducedForms D`.

For a nonsquare `D > 0` the reduction step `f ↦ f.reductionStep` replaces `(a, b, c)` by the
properly equivalent form `(c, b', c')`, where `b'` is the integer congruent to `-b` modulo `2 c`
in the window `√D - 2 |c| < b' < √D` and `c'` is forced by the discriminant. Writing
`s = ⌊√D⌋ = Int.sqrt D`, this is `b' = s - (s + b) % (2 c)`, and in Lean
`f.reductionStep = (T ^ k * S) • f` for an explicit `k`. Then:

* every form of positive nonsquare discriminant is properly equivalent to a reduced form
  (`exists_smul_isGaussReduced`): a Lagrange reduced representative has `4 a² < D`, and one
  reduction step applied to its rotation `S • f` lands on a reduced form;
* the reduction step sends reduced forms to reduced forms (`IsGaussReduced.reductionStep`) and is
  injective on them (`reductionStep_injOn`), because a reduced form is recovered from its image:
  its last coefficient is the image's first one, and its middle coefficient is the unique
  representative of `-b'` modulo `2 c` in the window `(s - 2 |c|, s]`.

Hence the reduction step permutes the finite set of reduced forms of discriminant `D`
(`reductionPerm D`). Its cycles are the **cycles of reduced forms**. Each cycle lies in a single
proper equivalence class (`exists_smul_eq_of_sameCycle`), and each proper class contains a
reduced form, so the proper classes of discriminant `D` are the images of the finitely many
cycles. That two different cycles always give different classes is the classical theorem of
Gauss that completes the count of classes by cycles, and is not proved here.

On reduced forms the step agrees with the reduction operator `ρ` of Cohen and of
Buchmann–Vollmer: a reduced form has `|c| < √D`, which is the case in which their operator uses
the window `(√D - 2 |c|, √D)`. Off the reduced forms the definition here always uses this
window; this suffices for the existence of reduced representatives, which needs one step only.

## Main definitions

* `TauCeti.BinaryQuadraticForm.IsGaussReduced`: `a c < 0` and `|a + c| < b`.
* `TauCeti.BinaryQuadraticForm.gaussReducedForms D`: the finite set of reduced forms of
  discriminant `D`.
* `TauCeti.BinaryQuadraticForm.reductionStep`: the reduction step `(a, b, c) ↦ (c, b', c')`.
* `TauCeti.BinaryQuadraticForm.reductionPerm D`: for nonsquare `D`, the reduction step as a
  permutation of `gaussReducedForms D`.

## Main results

* `TauCeti.BinaryQuadraticForm.isGaussReduced_iff_abs_sqrt_sub_lt`: the classical inequalities
  `|√D - 2 |a|| < b < √D`.
* `TauCeti.BinaryQuadraticForm.isGaussReduced_iff_le_sqrt`: for nonsquare `D`, the equivalent
  integer conditions `b ≤ s`, `s < b + 2 |a|` and `2 |a| ≤ s + b`, with `s = Int.sqrt D`.
* `TauCeti.BinaryQuadraticForm.exists_smul_isGaussReduced`: every form of positive nonsquare
  discriminant is properly equivalent to a reduced form.
* `TauCeti.BinaryQuadraticForm.IsGaussReduced.reductionStep` and
  `TauCeti.BinaryQuadraticForm.reductionStep_injOn`: the reduction step preserves reducedness and
  is injective on reduced forms.
* `TauCeti.BinaryQuadraticForm.exists_smul_eq_of_sameCycle`: the forms of one cycle are properly
  equivalent.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 183–187.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.6, Definitions 5.6.2 and 5.6.4 and Proposition 5.6.6.
* J. Buchmann and U. Vollmer, *Binary Quadratic Forms: An Algorithmic Approach*, Springer, 2007,
  Chapter 6.
-/

public section

open Finset MulAction
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- The integral binary quadratic form `f = a x² + b x y + c y²` is **reduced** in the sense of
Gauss: `a c < 0` and `|a + c| < b`.

Such a form has positive discriminant `D`, and the condition is equivalent to the classical
`|√D - 2 |a|| < b < √D` (`isGaussReduced_iff_abs_sqrt_sub_lt`). It is symmetric in `a` and `c`
(`isGaussReduced_swap`). -/
def IsGaussReduced (f : BinaryQuadraticForm ℤ) : Prop :=
  f.a * f.c < 0 ∧ |f.a + f.c| < f.b
deriving Decidable

/-- The form `a x² + b x y + c y²` is Gauss reduced exactly when `a c < 0` and `|a + c| < b`. -/
theorem isGaussReduced_iff {f : BinaryQuadraticForm ℤ} :
    f.IsGaussReduced ↔ f.a * f.c < 0 ∧ |f.a + f.c| < f.b :=
  Iff.rfl

/-- Exchanging the outer coefficients preserves Gauss reducedness. -/
theorem isGaussReduced_swap {f : BinaryQuadraticForm ℤ} :
    (⟨f.c, f.b, f.a⟩ : BinaryQuadraticForm ℤ).IsGaussReduced ↔ f.IsGaussReduced := by
  simp only [isGaussReduced_iff, mul_comm f.c, add_comm f.c]

/-- Reducedness through squares: `a x² + b x y + c y²` of discriminant `D` is Gauss reduced
exactly when `0 < b`, `b² < D` and `(2 |a| - b)² < D < (2 |a| + b)²`. -/
theorem isGaussReduced_iff_sq_lt {f : BinaryQuadraticForm ℤ} :
    f.IsGaussReduced ↔ 0 < f.b ∧ f.b ^ 2 < f.discrim ∧ (2 * |f.a| - f.b) ^ 2 < f.discrim ∧
      f.discrim < (2 * |f.a| + f.b) ^ 2 := by
  obtain ⟨a, b, c⟩ := f
  simp only [isGaussReduced_iff, discrim_def, discrim]
  -- negating the outer coefficients `(a, b, c) ↦ (-a, b, -c)` preserves both sides
  wlog ha : 0 ≤ a generalizing a c with H
  · simpa only [mul_neg, neg_mul, neg_neg, ← neg_add, abs_neg] using H (-a) (-c) (by linarith)
  rcases ha.eq_or_lt with rfl | ha
  · simp
  rw [abs_of_pos ha]
  constructor
  · rintro ⟨hac, habs⟩
    have hc : c < 0 := by nlinarith
    obtain ⟨h₁, h₂⟩ := abs_lt.mp habs
    refine ⟨by linarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨hb, h₁, h₂, h₃⟩
    have hc : c < 0 := by nlinarith
    exact ⟨by nlinarith, abs_lt.mpr ⟨by nlinarith, by nlinarith⟩⟩

/-- **Gauss's reduction condition**: `a x² + b x y + c y²` of discriminant `D` is reduced exactly
when `|√D - 2 |a|| < b < √D`. -/
theorem isGaussReduced_iff_abs_sqrt_sub_lt {f : BinaryQuadraticForm ℤ} :
    f.IsGaussReduced ↔
      |√(f.discrim : ℝ) - 2 * (|f.a| : ℝ)| < f.b ∧ (f.b : ℝ) < √(f.discrim : ℝ) := by
  rw [isGaussReduced_iff_sq_lt]
  set D := f.discrim
  have hA := abs_nonneg (f.a : ℝ)
  constructor
  · rintro ⟨hb, h₁, h₂, h₃⟩
    have hD : (0 : ℝ) < D := by exact_mod_cast (sq_nonneg f.b).trans_lt h₁
    have hb' : (0 : ℝ) < f.b := by exact_mod_cast hb
    have h₁' : ((f.b : ℝ)) ^ 2 < D := by exact_mod_cast h₁
    have h₂' : (2 * |(f.a : ℝ)| - f.b) ^ 2 < D := by exact_mod_cast h₂
    have h₃' : (D : ℝ) < (2 * |(f.a : ℝ)| + f.b) ^ 2 := by exact_mod_cast h₃
    have hs := Real.sq_sqrt hD.le
    have hs₀ := Real.sqrt_nonneg (D : ℝ)
    refine ⟨abs_lt.mpr ⟨?_, ?_⟩, ?_⟩ <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    have hb : (0 : ℝ) < f.b := (abs_nonneg _).trans_lt h₁
    have hs₀ : 0 < √(D : ℝ) := hb.trans h₂
    have hD : (0 : ℝ) < D := Real.sqrt_pos.mp hs₀
    have hs := Real.sq_sqrt hD.le
    obtain ⟨h₃, h₄⟩ := abs_lt.mp h₁
    have key₁ : ((f.b : ℝ)) ^ 2 < D := by nlinarith
    have key₂ : (2 * |(f.a : ℝ)| - f.b) ^ 2 < D := by nlinarith
    have key₃ : (D : ℝ) < (2 * |(f.a : ℝ)| + f.b) ^ 2 := by nlinarith
    exact ⟨by exact_mod_cast hb, by exact_mod_cast key₁, by exact_mod_cast key₂,
      by exact_mod_cast key₃⟩

/-- For a nonsquare discriminant `D`, the form `a x² + b x y + c y²` is Gauss reduced exactly when
`b ≤ s`, `s < b + 2 |a|` and `2 |a| ≤ s + b`, where `s = Int.sqrt D = ⌊√D⌋`. -/
theorem isGaussReduced_iff_le_sqrt {f : BinaryQuadraticForm ℤ} (hD : ¬ IsSquare f.discrim) :
    f.IsGaussReduced ↔ f.b ≤ Int.sqrt f.discrim ∧ Int.sqrt f.discrim < f.b + 2 * |f.a| ∧
      2 * |f.a| ≤ Int.sqrt f.discrim + f.b := by
  rw [isGaussReduced_iff_sq_lt]
  set D := f.discrim
  set s := Int.sqrt D
  have hA := abs_nonneg f.a
  have hs₀ : 0 ≤ s := Int.sqrt_nonneg D
  have hs₂ := Int.lt_sqrt_add_one_mul_sqrt_add_one D
  constructor
  · rintro ⟨hb, h₁, h₂, h₃⟩
    have hs₁ : s * s ≤ D := (Int.abs_le_sqrt (by nlinarith)).1 (abs_of_nonneg hs₀).le
    refine ⟨?_, ?_, ?_⟩
    · by_contra! h
      nlinarith
    · by_contra! h
      nlinarith
    · by_contra! h
      nlinarith
  · rintro ⟨h₁, h₂, h₃⟩
    have hb : 0 < f.b := by linarith
    have hD₀ : 0 ≤ D := by
      by_contra! h
      have : s = 0 := Int.sqrt_eq_zero_of_nonpos h.le
      linarith
    have hs₁ := Int.sqrt_mul_sqrt_lt hD hD₀
    refine ⟨hb, by nlinarith, by nlinarith, by nlinarith⟩

namespace IsGaussReduced

variable {f : BinaryQuadraticForm ℤ}

/-- A Gauss reduced form has positive middle coefficient. -/
theorem b_pos (hf : f.IsGaussReduced) : 0 < f.b :=
  (isGaussReduced_iff_sq_lt.mp hf).1

/-- A Gauss reduced form has positive discriminant. -/
theorem discrim_pos (hf : f.IsGaussReduced) : 0 < f.discrim :=
  (sq_nonneg _).trans_lt (isGaussReduced_iff_sq_lt.mp hf).2.1

/-- A Gauss reduced form of discriminant `D` has `(|a| + |c|)² < D`, that is `|a| + |c| < √D`. -/
theorem sq_abs_add_abs_lt (hf : f.IsGaussReduced) : (|f.a| + |f.c|) ^ 2 < f.discrim := by
  obtain ⟨hac, habs⟩ := hf
  obtain ⟨h₁, h₂⟩ := abs_lt.mp habs
  rw [discrim_def, discrim]
  rcases lt_or_gt_of_ne (left_ne_zero_of_mul hac.ne) with ha | ha
  · have hc : 0 < f.c := by nlinarith
    rw [abs_of_neg ha, abs_of_pos hc]
    nlinarith
  · have hc : f.c < 0 := by nlinarith
    rw [abs_of_pos ha, abs_of_neg hc]
    nlinarith

end IsGaussReduced

/-- The variant of `isGaussReduced_iff_le_sqrt` with `|c|` in place of `|a|`: for a nonsquare
discriminant, `f` is Gauss reduced exactly when `b ≤ s`, `s < b + 2 |c|` and `2 |c| ≤ s + b`. -/
private theorem isGaussReduced_iff_le_sqrt' {f : BinaryQuadraticForm ℤ}
    (hD : ¬ IsSquare f.discrim) :
    f.IsGaussReduced ↔ f.b ≤ Int.sqrt f.discrim ∧ Int.sqrt f.discrim < f.b + 2 * |f.c| ∧
      2 * |f.c| ≤ Int.sqrt f.discrim + f.b := by
  have h := isGaussReduced_iff_le_sqrt (f := ⟨f.c, f.b, f.a⟩) (by rwa [discrim_swap])
  rwa [discrim_swap, isGaussReduced_swap] at h

/-! ### The finite set of reduced forms -/

/-- The Gauss reduced forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = D`.

The definition searches the box `|a| ≤ s`, `1 ≤ b ≤ s`, `|c| ≤ s` with `s = Int.sqrt D`, which
makes it a finite, decidable set; `mem_gaussReducedForms` shows that the box loses nothing. -/
def gaussReducedForms (D : ℤ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ (Icc (-Int.sqrt D) (Int.sqrt D) ×ˢ Icc 1 (Int.sqrt D) ×ˢ
      Icc (-Int.sqrt D) (Int.sqrt D)).map equivProd.symm.toEmbedding |
    f.discrim = D ∧ f.IsGaussReduced}

/-- **The Gauss reduced forms of discriminant `D`**: `f ∈ gaussReducedForms D` exactly when
`f.discrim = D` and `f` is Gauss reduced. -/
@[simp] theorem mem_gaussReducedForms {D : ℤ} {f : BinaryQuadraticForm ℤ} :
    f ∈ gaussReducedForms D ↔ f.discrim = D ∧ f.IsGaussReduced := by
  refine mem_filter.trans <| and_iff_right_of_imp fun ⟨hd, hf⟩ ↦ mem_map_equiv.2 ?_
  subst hd
  have hb := hf.b_pos
  have hsq := hf.sq_abs_add_abs_lt
  have hb' := (isGaussReduced_iff_sq_lt.mp hf).2.1
  have hA := abs_nonneg f.a
  have hC := abs_nonneg f.c
  have hD₀ := hf.discrim_pos.le
  have ha : |f.a| ≤ Int.sqrt f.discrim :=
    (Int.abs_le_sqrt hD₀).2 (by rw [← abs_mul_abs_self]; nlinarith)
  have hc : |f.c| ≤ Int.sqrt f.discrim :=
    (Int.abs_le_sqrt hD₀).2 (by rw [← abs_mul_abs_self]; nlinarith)
  have hb'' : f.b ≤ Int.sqrt f.discrim :=
    (le_abs_self _).trans ((Int.abs_le_sqrt hD₀).2 (by nlinarith))
  simp only [Equiv.symm_symm, equivProd_apply, mem_product, mem_Icc, ← abs_le]
  exact ⟨ha, ⟨hb, hb''⟩, hc⟩

/-! ### The reduction step -/

/-- The **reduction step** `(a, b, c) ↦ (c, b', c')` on integral binary quadratic forms of
discriminant `D`: with `s = Int.sqrt D`, the new middle coefficient is
`b' = s - (s + b) % (2 c)`, the representative of `-b` modulo `2 c` with `s - 2 |c| < b' ≤ s`
(for `c ≠ 0`), and `c'` is forced by the discriminant.

It is the change of variables `(T ^ k * S) • f` for `k = -((s + b) / (2 c))`, so `f.reductionStep`
is properly equivalent to `f` (`reductionStep_mem_orbit`). For nonsquare `D` it permutes the Gauss
reduced forms (`reductionPerm`). -/
def reductionStep (f : BinaryQuadraticForm ℤ) : BinaryQuadraticForm ℤ :=
  (ModularGroup.T ^ (-((Int.sqrt f.discrim + f.b) / (2 * f.c))) * ModularGroup.S) • f

/-- The reduction step is a proper change of variables. -/
theorem reductionStep_mem_orbit (f : BinaryQuadraticForm ℤ) :
    f.reductionStep ∈ orbit SL(2, ℤ) f :=
  ⟨_, rfl⟩

/-- The reduction step preserves the discriminant. -/
@[simp] theorem discrim_reductionStep (f : BinaryQuadraticForm ℤ) :
    f.reductionStep.discrim = f.discrim :=
  discrim_smul _ f

/-- The first coefficient of `f.reductionStep` is the last coefficient of `f`. -/
@[simp] theorem reductionStep_a (f : BinaryQuadraticForm ℤ) : f.reductionStep.a = f.c := by
  rw [reductionStep, mul_smul, S_smul, T_zpow_smul]

/-- The middle coefficient of `f.reductionStep` is `s - (s + b) % (2 c)`, for
`s = Int.sqrt f.discrim`. -/
@[simp] theorem reductionStep_b (f : BinaryQuadraticForm ℤ) :
    f.reductionStep.b = Int.sqrt f.discrim - (Int.sqrt f.discrim + f.b) % (2 * f.c) := by
  rw [reductionStep, mul_smul, S_smul, T_zpow_smul]
  dsimp only
  linear_combination Int.mul_ediv_add_emod (Int.sqrt f.discrim + f.b) (2 * f.c)

/-- The last coefficient of `f.reductionStep` is `c q² - b q + a`, for `q = (s + b) / (2 c)` and
`s = Int.sqrt f.discrim`. -/
@[simp] theorem reductionStep_c (f : BinaryQuadraticForm ℤ) :
    f.reductionStep.c = f.c * ((Int.sqrt f.discrim + f.b) / (2 * f.c)) ^ 2 -
      f.b * ((Int.sqrt f.discrim + f.b) / (2 * f.c)) + f.a := by
  rw [reductionStep, mul_smul, S_smul, T_zpow_smul]
  dsimp only
  ring

/-- The last coefficient `c'` of `f.reductionStep = (c, b', c')` is forced by the discriminant:
`4 c c' = b'² - D`. -/
theorem four_mul_c_mul_reductionStep_c (f : BinaryQuadraticForm ℤ) :
    4 * f.c * f.reductionStep.c = f.reductionStep.b ^ 2 - f.discrim := by
  have h := discrim_reductionStep f
  rw [discrim_def, discrim, reductionStep_a] at h
  linarith

/-- For `c ≠ 0`, the middle coefficient of `f.reductionStep` lies in the window `(s - 2 |c|, s]`,
where `s = Int.sqrt f.discrim`. -/
theorem reductionStep_b_mem_Ioc {f : BinaryQuadraticForm ℤ} (hc : f.c ≠ 0) :
    f.reductionStep.b ∈ Set.Ioc (Int.sqrt f.discrim - 2 * |f.c|) (Int.sqrt f.discrim) := by
  have h₂c : 2 * f.c ≠ 0 := mul_ne_zero two_ne_zero hc
  have h₀ := Int.emod_nonneg (Int.sqrt f.discrim + f.b) h₂c
  have h₁ := Int.emod_lt_abs (Int.sqrt f.discrim + f.b) h₂c
  rw [abs_mul, abs_two] at h₁
  rw [reductionStep_b, Set.mem_Ioc]
  constructor <;> linarith

/-- For a nonsquare discriminant, `f.reductionStep` is Gauss reduced exactly when its middle
coefficient `b'` satisfies `2 |c| ≤ s + b'`, where `s = Int.sqrt f.discrim`; the other two
inequalities of `isGaussReduced_iff_le_sqrt` hold by construction. -/
theorem isGaussReduced_reductionStep_iff {f : BinaryQuadraticForm ℤ}
    (hD : ¬ IsSquare f.discrim) :
    f.reductionStep.IsGaussReduced ↔ 2 * |f.c| ≤ Int.sqrt f.discrim + f.reductionStep.b := by
  rw [isGaussReduced_iff_le_sqrt (by rwa [discrim_reductionStep]), discrim_reductionStep,
    reductionStep_a]
  have h := reductionStep_b_mem_Ioc (c_ne_zero_of_not_isSquare_discrim hD)
  exact ⟨fun h' ↦ h'.2.2, fun h' ↦ ⟨h.2, by linarith [h.1], h'⟩⟩

/-- A form `a x² + b x y + c y²` of nonsquare discriminant `D` with `4 c² < D` is sent to a Gauss
reduced form by one reduction step. -/
theorem isGaussReduced_reductionStep_of_four_mul_sq_lt {f : BinaryQuadraticForm ℤ}
    (hD : ¬ IsSquare f.discrim) (h : 4 * f.c ^ 2 < f.discrim) :
    f.reductionStep.IsGaussReduced := by
  rw [isGaussReduced_reductionStep_iff hD]
  have hc : 2 * |f.c| ≤ Int.sqrt f.discrim := by
    rw [← abs_two, ← abs_mul]
    exact (Int.abs_le_sqrt (by nlinarith [sq_nonneg f.c])).2 (by nlinarith)
  have := (reductionStep_b_mem_Ioc (c_ne_zero_of_not_isSquare_discrim hD)).1
  linarith

/-- **The reduction step preserves reducedness**: for a nonsquare discriminant, the reduction step
of a Gauss reduced form is Gauss reduced. -/
theorem IsGaussReduced.reductionStep {f : BinaryQuadraticForm ℤ} (hf : f.IsGaussReduced)
    (hD : ¬ IsSquare f.discrim) : f.reductionStep.IsGaussReduced := by
  rw [isGaussReduced_reductionStep_iff hD]
  have hc := c_ne_zero_of_not_isSquare_discrim hD
  obtain ⟨hb₁, hb₂, hb₃⟩ := (isGaussReduced_iff_le_sqrt' hD).mp hf
  obtain ⟨h₁, h₂⟩ := reductionStep_b_mem_Ioc hc
  by_contra! h
  -- `b' + b` is a multiple of `2 c` strictly between `0` and `2 |c|`
  have hdvd : 2 * |f.c| ∣ f.reductionStep.b + f.b := by
    rw [← abs_two, ← abs_mul, abs_dvd, reductionStep_b]
    exact ⟨(Int.sqrt f.discrim + f.b) / (2 * f.c), by
      linear_combination -Int.mul_ediv_add_emod (Int.sqrt f.discrim + f.b) (2 * f.c)⟩
  have hzero := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by linarith, by linarith⟩)
  linarith

/-- **The reduction step is injective on reduced forms**: a Gauss reduced form of nonsquare
discriminant is determined by its reduction step. -/
theorem reductionStep_injOn :
    Set.InjOn reductionStep
      {f : BinaryQuadraticForm ℤ | f.IsGaussReduced ∧ ¬ IsSquare f.discrim} := by
  rintro f ⟨hf, hD⟩ g ⟨hg, -⟩ h
  have hdisc : f.discrim = g.discrim := by
    rw [← discrim_reductionStep f, h, discrim_reductionStep]
  have hc : f.c = g.c := by rw [← reductionStep_a f, h, reductionStep_a]
  have hc₀ := c_ne_zero_of_not_isSquare_discrim hD
  -- the middle coefficients are congruent modulo `2 c` and lie in one window of length `2 |c|`
  have hb : f.b = g.b := by
    have hr := congrArg BinaryQuadraticForm.b h
    rw [reductionStep_b, reductionStep_b, ← hdisc, ← hc] at hr
    have hmod : Int.sqrt f.discrim + f.b ≡ Int.sqrt f.discrim + g.b [ZMOD 2 * f.c] := by
      rw [Int.ModEq]
      linarith
    have hdvd : 2 * |f.c| ∣ g.b - f.b := by
      rw [← abs_two, ← abs_mul, abs_dvd, ← add_sub_add_left_eq_sub _ _ (Int.sqrt f.discrim)]
      exact Int.modEq_iff_dvd.mp hmod
    obtain ⟨hf₁, hf₂, -⟩ := (isGaussReduced_iff_le_sqrt' hD).mp hf
    obtain ⟨hg₁, hg₂, -⟩ := (isGaussReduced_iff_le_sqrt' (hdisc ▸ hD)).mp hg
    rw [← hdisc] at hg₁ hg₂
    rw [← hc] at hg₂
    have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by linarith, by linarith⟩)
    linarith
  -- the first coefficient is then forced by the discriminant
  have ha : f.a = g.a := by
    simp only [discrim_def, discrim, hb, hc] at hdisc
    have : 4 * g.c * (f.a - g.a) = 0 := by linarith
    simpa [hc₀, hc ▸ hc₀, sub_eq_zero] using this
  exact BinaryQuadraticForm.ext ha hb hc

/-! ### Existence of reduced representatives -/

/-- **Gauss reduction**: every integral binary quadratic form of positive nonsquare discriminant is
properly equivalent to a Gauss reduced form. -/
theorem exists_smul_isGaussReduced (f : BinaryQuadraticForm ℤ) (hpos : 0 < f.discrim)
    (hD : ¬ IsSquare f.discrim) : ∃ γ : SL(2, ℤ), (γ • f).IsGaussReduced := by
  obtain ⟨γ, hγ⟩ := exists_smul_isLagrangeReduced f hD
  -- the rotation `S • γ • f = ⟨c, -b, a⟩` has last coefficient `a` with `4 a² < D`
  have h4 := hγ.four_mul_sq_a_lt_discrim (by rwa [discrim_smul]) (by rwa [discrim_smul])
  obtain ⟨δ, hδ⟩ := mem_orbit_iff.mp (reductionStep_mem_orbit (ModularGroup.S • γ • f))
  refine ⟨δ * ModularGroup.S * γ, ?_⟩
  rw [mul_smul, mul_smul, hδ]
  refine isGaussReduced_reductionStep_of_four_mul_sq_lt (by rwa [discrim_smul, discrim_smul]) ?_
  have hc : (ModularGroup.S • γ • f).c = (γ • f).a := by rw [S_smul]
  rwa [hc, discrim_smul]

/-- Every form of positive nonsquare discriminant `D` is properly equivalent to a member of the
finite set `gaussReducedForms D`. -/
theorem exists_smul_mem_gaussReducedForms (f : BinaryQuadraticForm ℤ) (hpos : 0 < f.discrim)
    (hD : ¬ IsSquare f.discrim) : ∃ γ : SL(2, ℤ), γ • f ∈ gaussReducedForms f.discrim := by
  obtain ⟨γ, hγ⟩ := exists_smul_isGaussReduced f hpos hD
  exact ⟨γ, mem_gaussReducedForms.2 ⟨discrim_smul γ f, hγ⟩⟩

/-! ### Cycles of reduced forms -/

/-- For a nonsquare discriminant `D`, the reduction step as a permutation of the finite set of
Gauss reduced forms of discriminant `D`. Its cycles are the cycles of reduced forms. -/
noncomputable def reductionPerm (D : ℤ) [Fact (¬ IsSquare D)] :
    Equiv.Perm (gaussReducedForms D) :=
  Equiv.ofBijective
    (fun f ↦ ⟨f.1.reductionStep, by
      obtain ⟨hD, hf⟩ := mem_gaussReducedForms.mp f.2
      exact mem_gaussReducedForms.mpr ⟨by rw [discrim_reductionStep, hD],
        hf.reductionStep (by rw [hD]; exact Fact.out)⟩⟩)
    (Finite.injective_iff_bijective.mp fun f g h ↦ by
      obtain ⟨hDf, hf⟩ := mem_gaussReducedForms.mp f.2
      obtain ⟨hDg, hg⟩ := mem_gaussReducedForms.mp g.2
      exact Subtype.ext <| reductionStep_injOn ⟨hf, by rw [hDf]; exact Fact.out⟩
        ⟨hg, by rw [hDg]; exact Fact.out⟩ (congrArg Subtype.val h))

variable {D : ℤ} [Fact (¬ IsSquare D)]

/-- The permutation `reductionPerm D` is the reduction step. -/
@[simp] theorem coe_reductionPerm_apply (f : gaussReducedForms D) :
    (reductionPerm D f : BinaryQuadraticForm ℤ) = (f : BinaryQuadraticForm ℤ).reductionStep := by
  simp only [reductionPerm, Equiv.ofBijective_apply]

/-- **A cycle of reduced forms lies in one proper class**: two Gauss reduced forms in the same
cycle of the reduction step are properly equivalent. -/
theorem exists_smul_eq_of_sameCycle {f g : gaussReducedForms D}
    (h : (reductionPerm D).SameCycle f g) :
    ∃ γ : SL(2, ℤ), γ • (f : BinaryQuadraticForm ℤ) = g := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨γ, hγ⟩ := ih
    obtain ⟨δ, hδ⟩ :=
      mem_orbit_iff.mp (reductionStep_mem_orbit ((reductionPerm D ^ n) f : BinaryQuadraticForm ℤ))
    refine ⟨δ * γ, ?_⟩
    rw [pow_succ', Equiv.Perm.mul_apply, coe_reductionPerm_apply, mul_smul, hγ]
    exact hδ

/-! The Gauss reduced forms of discriminant `12` are `(1, 2, -2)`, `(-2, 2, 1)`, `(-1, 2, 2)` and
`(2, 2, -1)`. The reduction step exchanges the first two (and likewise the last two), so they form
two cycles of length two, matching the two proper classes of `x² - 3 y²` and `-x² + 3 y²`. -/

example : (⟨1, 2, -2⟩ : BinaryQuadraticForm ℤ).IsGaussReduced ∧
    (⟨-2, 2, 1⟩ : BinaryQuadraticForm ℤ).IsGaussReduced ∧
    (⟨-1, 2, 2⟩ : BinaryQuadraticForm ℤ).IsGaussReduced ∧
    (⟨2, 2, -1⟩ : BinaryQuadraticForm ℤ).IsGaussReduced := by
  decide

example : reductionStep ⟨1, 2, -2⟩ = ⟨-2, 2, 1⟩ ∧ reductionStep ⟨-2, 2, 1⟩ = ⟨1, 2, -2⟩ := by
  have hs : Nat.sqrt 12 = 3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
  constructor <;> ext <;> simp [discrim_def, discrim, hs]

end TauCeti.BinaryQuadraticForm
