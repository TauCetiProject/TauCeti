/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.IndefiniteReduction.Root
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Gauss's theorem on cycles of reduced indefinite binary quadratic forms

For a nonsquare discriminant `D > 0`, the Gauss reduction step permutes the finite set
`gaussReducedForms D` of reduced forms of discriminant `D` (`reductionPerm D`), and every form in a
single cycle lies in the same `SL(2, ℤ)`-orbit (`exists_smul_eq_of_sameCycle`). This file proves the
converse, **Gauss's theorem**: two Gauss reduced forms of nonsquare discriminant `D` are properly
equivalent if and only if they lie in the same cycle of `reductionPerm D`
(`sameCycle_reductionPerm_iff`). Together with `exists_smul_mem_gaussReducedForms`, the cycles of
`reductionPerm D` are in canonical bijection with the `SL(2, ℤ)`-classes of forms of discriminant
`D` (`cycleEquivProperClass`), and restricting to primitive forms identifies the cycles of
`primitiveReductionPerm D` on `primitiveGaussReducedForms D` with the proper equivalence classes of
primitive forms of discriminant `D` (`primitiveCycleEquivProperClass`).

## Proof sketch

Suppose `f` and `g` are Gauss reduced of nonsquare discriminant `D` and `γ • f = g` for
`γ ∈ SL(2, ℤ)`. Let `ω₁` and `ω₂` be the first and second real roots (`|ω₁| < 1 < |ω₂|` and
`ω₁ ω₂ < 0`).

1. If `γ 1 0 = 0`, then `γ = ±T ^ k`, so `ω₁(g) = ω₁(f) + k` and `ω₂(g) = ω₂(f) + k`. The bounds
   `|ω₁(f)| < 1`, `|ω₁(g)| < 1` together with `ω₁ ω₂ < 0` force `k = 0`, hence `f = g` by
   `firstRoot_injOn`.
2. If `γ 1 1 = 0`, replacing `(f, γ)` by `(f.reductionStep, γ * γ_f⁻¹)` produces a matrix with
   bottom-left entry `-γ 1 1 = 0`, reducing to step 1 and giving `g = f.reductionStep`.
3. In general, the automorphy-factor relation
   `((γ⁻¹ 1 0) ω₁(g) + γ⁻¹ 1 1) ((γ 1 0) ω₁(f) + γ 1 1) = 1`
   allows us (after swapping `f` and `g` via `γ⁻¹` if needed, since `SameCycle` is symmetric) to
   assume `|(γ 1 0) ω₁(f) + γ 1 1| < 1`. Whenever `γ 1 1 ≠ 0`, one reduction step transforms
   `(f, γ)` to `(f', γ') = (f.reductionStep, γ * γ_f⁻¹)`, dividing the denominator magnitude by
   `|ω₁(f)| < 1` while keeping `|(γ' 1 0) ω₁(f') + γ' 1 1| < 1` (if it exceeded `1`, its inverse
   denominator on `g` would have magnitude `< 1`, forcing `|(γ 1 1) ω₂(g) - γ 0 1| > 1` and
   `|(γ 1 0) ω₂(f) + γ 1 1| > |ω₂(f)|`, contradicting their product `|ω₂(f)|`). Since
   `gaussReducedForms D` is finite, `|ω₁|` is bounded away from `1` on it, so only finitely many
   steps can occur before `γ_n 1 1 = 0`, landing on `g` in the cycle of `f`.

## Main definitions

* `TauCeti.BinaryQuadraticForm.formsOfDiscrim D`: all integral forms of discriminant `D` as a
  `SubMulAction` of `SL(2, ℤ)`.
* `TauCeti.BinaryQuadraticForm.cycleEquivProperClass`: bijection between cycles of `reductionPerm D`
  and proper classes of forms of positive nonsquare discriminant `D`.
* `TauCeti.BinaryQuadraticForm.primitiveGaussReducedForms D`: the finite set of primitive Gauss
  reduced forms of discriminant `D`.
* `TauCeti.BinaryQuadraticForm.primitiveReductionPerm D`: `reductionPerm D` restricted to primitive
  Gauss reduced forms.
* `TauCeti.BinaryQuadraticForm.primitiveCycleEquivProperClass`: bijection between cycles of
  `primitiveReductionPerm D` and proper classes of primitive forms of positive nonsquare
  discriminant `D`.

## Main results

* `TauCeti.BinaryQuadraticForm.sameCycle_reductionPerm_iff`: two Gauss reduced forms of nonsquare
  discriminant `D` lie in the same cycle of `reductionPerm D` if and only if they are properly
  equivalent.
* `TauCeti.BinaryQuadraticForm.sameCycle_primitiveReductionPerm_iff`: the corresponding criterion
  for `primitiveReductionPerm D`.
* `TauCeti.BinaryQuadraticForm.nat_card_formsOfDiscrim_quotient` and
  `TauCeti.BinaryQuadraticForm.nat_card_primitiveForms_quotient`: class counts from cycle counts.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 188–195.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.6, Proposition 5.6.6 and Theorem 5.6.11.
* J. Buchmann and U. Vollmer, *Binary Quadratic Forms: An Algorithmic Approach*, Springer, 2007,
  §6.3, Theorem 6.3.4.
-/

public section

open Finset MulAction
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-! ### Matrix step helpers for Gauss's theorem -/

/-- The change-of-variables matrix `T ^ (-((⌊√D⌋ + b) / (2 c))) * S` for `f.reductionStep`. -/
private def reductionStepMatrix (f : BinaryQuadraticForm ℤ) : SL(2, ℤ) :=
  ModularGroup.T ^ (-((Int.sqrt f.discrim + f.b) / (2 * f.c))) * ModularGroup.S

private theorem reductionStepMatrix_smul (f : BinaryQuadraticForm ℤ) :
    reductionStepMatrix f • f = f.reductionStep :=
  (reductionStep_eq_smul f).symm

private theorem mul_inv_reductionStepMatrix_smul (γ : SL(2, ℤ)) (f : BinaryQuadraticForm ℤ) :
    (γ * (reductionStepMatrix f)⁻¹) • f.reductionStep = γ • f := by
  rw [← reductionStepMatrix_smul, mul_smul, inv_smul_smul]

private theorem reductionStepMatrix_zero_zero (f : BinaryQuadraticForm ℤ) :
    reductionStepMatrix f 0 0 = -((Int.sqrt f.discrim + f.b) / (2 * f.c)) :=
  Int.cast_injective (α := ℝ) (by
    simp [reductionStepMatrix, ModularGroup.coe_T_zpow, ModularGroup.coe_S])

private theorem reductionStepMatrix_zero_one (f : BinaryQuadraticForm ℤ) :
    reductionStepMatrix f 0 1 = -1 :=
  Int.cast_injective (α := ℝ) (by
    simp [reductionStepMatrix, ModularGroup.coe_T_zpow, ModularGroup.coe_S])

private theorem reductionStepMatrix_one_zero (f : BinaryQuadraticForm ℤ) :
    reductionStepMatrix f 1 0 = 1 :=
  Int.cast_injective (α := ℝ) (by
    simp [reductionStepMatrix, ModularGroup.coe_T_zpow, ModularGroup.coe_S])

private theorem reductionStepMatrix_one_one (f : BinaryQuadraticForm ℤ) :
    reductionStepMatrix f 1 1 = 0 :=
  Int.cast_injective (α := ℝ) (by
    simp [reductionStepMatrix, ModularGroup.coe_T_zpow, ModularGroup.coe_S])

private theorem mul_inv_reductionStepMatrix_zero_zero (γ : SL(2, ℤ)) (f : BinaryQuadraticForm ℤ) :
    (γ * (reductionStepMatrix f)⁻¹) 0 0 = -γ 0 1 := by
  have h := congrFun₂ (Matrix.SpecialLinearGroup.coe_mul γ (reductionStepMatrix f)⁻¹) 0 0
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h
  have h₀ : (reductionStepMatrix f)⁻¹ 0 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, reductionStepMatrix_one_one]
  have h₁ : (reductionStepMatrix f)⁻¹ 1 0 = -1 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, reductionStepMatrix_one_zero]
  exact h.trans (by rw [h₀, h₁]; ring)

private theorem mul_inv_reductionStepMatrix_one_zero (γ : SL(2, ℤ)) (f : BinaryQuadraticForm ℤ) :
    (γ * (reductionStepMatrix f)⁻¹) 1 0 = -γ 1 1 := by
  have h := congrFun₂ (Matrix.SpecialLinearGroup.coe_mul γ (reductionStepMatrix f)⁻¹) 1 0
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h
  have h₀ : (reductionStepMatrix f)⁻¹ 0 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, reductionStepMatrix_one_one]
  have h₁ : (reductionStepMatrix f)⁻¹ 1 0 = -1 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, reductionStepMatrix_one_zero]
  exact h.trans (by rw [h₀, h₁]; ring)

private theorem mul_inv_reductionStepMatrix_one_one (γ : SL(2, ℤ)) (f : BinaryQuadraticForm ℤ) :
    (γ * (reductionStepMatrix f)⁻¹) 1 1 =
      γ 1 0 - ((Int.sqrt f.discrim + f.b) / (2 * f.c)) * γ 1 1 := by
  have h := congrFun₂ (Matrix.SpecialLinearGroup.coe_mul γ (reductionStepMatrix f)⁻¹) 1 1
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h
  have h₀ : (reductionStepMatrix f)⁻¹ 0 1 = 1 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, reductionStepMatrix_zero_one]
  have h₁ : (reductionStepMatrix f)⁻¹ 1 1 = -((Int.sqrt f.discrim + f.b) / (2 * f.c)) := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, reductionStepMatrix_zero_zero]
  exact h.trans (by rw [h₀, h₁]; ring)

/-- Base case `γ 1 0 = 0`: an upper-triangular proper equivalence between two Gauss reduced forms of
nonsquare discriminant must be trivial on forms (`f = g`). -/
private theorem eq_of_smul_eq_of_apply_one_zero_eq_zero {f g : BinaryQuadraticForm ℤ}
    (hf : f.IsGaussReduced) (hg : g.IsGaussReduced) (hD : ¬ IsSquare f.discrim)
    {γ : SL(2, ℤ)} (hγ : γ • f = g) (hr : γ 1 0 = 0) : f = g := by
  have hpos : 0 < f.discrim := hf.discrim_pos
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h := γ.fin_two_mul_sub_mul_eq_one
    rwa [hr, mul_zero, sub_zero] at h
  have hp2 : (γ 0 0 : ℝ) ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with hp | hp <;> simp [hp]
  have hdetR : (γ 0 0 : ℝ) * γ 1 1 = 1 := by exact_mod_cast hdet
  have hr₁ := denom_mul_firstRoot_smul hpos.le hD γ
  have hr₂ := denom_mul_secondRoot_smul hpos.le hD γ
  rw [hγ, hr, Int.cast_zero, zero_mul, zero_add] at hr₁ hr₂
  set k : ℤ := γ 0 0 * γ 0 1
  have hk₁ : g.firstRoot = f.firstRoot + (k : ℝ) := by
    have h : (γ 0 0 : ℝ) * ((γ 1 1 : ℝ) * g.firstRoot) =
        (γ 0 0 : ℝ) * ((γ 0 0 : ℝ) * f.firstRoot + γ 0 1) := congrArg ((γ 0 0 : ℝ) * ·) hr₁
    push_cast [k]
    linear_combination h - g.firstRoot * hdetR + f.firstRoot * hp2
  have hk₂ : g.secondRoot = f.secondRoot + (k : ℝ) := by
    have h : (γ 0 0 : ℝ) * ((γ 1 1 : ℝ) * g.secondRoot) =
        (γ 0 0 : ℝ) * ((γ 0 0 : ℝ) * f.secondRoot + γ 0 1) := congrArg ((γ 0 0 : ℝ) * ·) hr₂
    push_cast [k]
    linear_combination h - g.secondRoot * hdetR + f.secondRoot * hp2
  obtain ⟨hfm, hf₁, -⟩ := isGaussReduced_iff_roots.mp hf
  obtain ⟨hgm, hg₁, -⟩ := isGaussReduced_iff_roots.mp hg
  obtain ⟨hf₁', hf₁''⟩ := abs_lt.mp hf₁
  obtain ⟨hg₁', hg₁''⟩ := abs_lt.mp hg₁
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
      have : 0 < f.firstRoot := by linarith
      have : g.firstRoot < 0 := by linarith
      have : f.secondRoot < 0 := by nlinarith
      have : g.secondRoot < 0 := by linarith
      nlinarith
    · exact hk
    · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : f.firstRoot < 0 := by linarith
      have : 0 < g.firstRoot := by linarith
      have : 0 < f.secondRoot := by nlinarith
      have : 0 < g.secondRoot := by linarith
      nlinarith
  rw [hk0, Int.cast_zero, add_zero] at hk₁
  exact firstRoot_injOn hpos.le hD rfl (hγ ▸ discrim_smul γ f) hk₁.symm

/-- Base case `γ 1 1 = 0`: if `γ • f = g` has `γ 1 1 = 0` for Gauss reduced `f, g` of nonsquare
discriminant, then `g = f.reductionStep`. -/
private theorem eq_reductionStep_of_smul_eq_of_apply_one_one_eq_zero {f g : BinaryQuadraticForm ℤ}
    (hf : f.IsGaussReduced) (hg : g.IsGaussReduced) (hD : ¬ IsSquare f.discrim)
    {γ : SL(2, ℤ)} (hγ : γ • f = g) (hs : γ 1 1 = 0) : f.reductionStep = g :=
  eq_of_smul_eq_of_apply_one_zero_eq_zero (hf.reductionStep hD) hg
    (by rwa [discrim_reductionStep])
    ((mul_inv_reductionStepMatrix_smul γ f).trans hγ)
    (by rw [mul_inv_reductionStepMatrix_one_zero, hs, neg_zero])

/-- Root separation bound: if `f` is Gauss reduced, `m ≠ 0`, and `|m ω₁(f) + n| < 1`, then
`m ω₂(f)` and `n` cannot have opposite signs, so `1 < |m ω₂(f) + n|` (and
`|ω₂(f)| < |m ω₂(f) + n|` whenever `n ≠ 0`). -/
private theorem one_lt_abs_secondRoot_linear {f : BinaryQuadraticForm ℤ} (hf : f.IsGaussReduced)
    {m n : ℤ} (hm : m ≠ 0) (h : |(m : ℝ) * f.firstRoot + n| < 1) :
    1 < |(m : ℝ) * f.secondRoot + n| ∧ (n ≠ 0 → |f.secondRoot| < |(m : ℝ) * f.secondRoot + n|) := by
  obtain ⟨hmul, _, h₂⟩ := isGaussReduced_iff_roots.mp hf
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
  have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [sq_abs (m : ℝ)]
  have hω2 : 1 < f.secondRoot ^ 2 := by nlinarith [sq_abs f.secondRoot, abs_nonneg f.secondRoot]
  have hsign : 0 ≤ (m : ℝ) * f.secondRoot * n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
    obtain ⟨ha, hb⟩ := abs_lt.mp h
    have hlt1 : ((m : ℝ) * f.firstRoot + n) ^ 2 < 1 := by nlinarith
    have hneg1 : (m : ℝ) * f.firstRoot * n < 0 := by
      nlinarith [sq_nonneg ((m : ℝ) * f.firstRoot)]
    have hmn_pos : 0 < (m : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      have : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
      have : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
      positivity
    have : ((m : ℝ) * f.firstRoot * n) * ((m : ℝ) * f.secondRoot * n) < 0 := by
      have hid : ((m : ℝ) * f.firstRoot * n) * ((m : ℝ) * f.secondRoot * n) =
          (m : ℝ) ^ 2 * (n : ℝ) ^ 2 * (f.firstRoot * f.secondRoot) := by ring
      rw [hid]
      exact mul_neg_of_pos_of_neg hmn_pos hmul
    nlinarith
  have hsq1 : (1 : ℝ) ^ 2 < ((m : ℝ) * f.secondRoot + n) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  refine ⟨by simpa using sq_lt_sq.mp hsq1, fun hn ↦ ?_⟩
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hn2 : (1 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
  have hsq2 : f.secondRoot ^ 2 < ((m : ℝ) * f.secondRoot + n) ^ 2 := by nlinarith
  exact sq_lt_sq.mp hsq2

/-- Under a single reduction step `(f, γ) ↦ (f.reductionStep, γ * γ_f⁻¹)`, the Möbius denominator at
`firstRoot` divides by `f.firstRoot`. -/
private theorem firstRoot_mul_denom_reductionStep (γ : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hD : ¬ IsSquare f.discrim) :
    f.firstRoot * (((γ * (reductionStepMatrix f)⁻¹) 1 0 : ℝ) * f.reductionStep.firstRoot +
      (γ * (reductionStepMatrix f)⁻¹) 1 1) = (γ 1 0 : ℝ) * f.firstRoot + γ 1 1 := by
  have hstep := firstRoot_mul_firstRoot_reductionStep hpos hD
  rw [mul_inv_reductionStepMatrix_one_zero, mul_inv_reductionStepMatrix_one_one]
  push_cast
  linear_combination -(γ 1 1 : ℝ) * hstep

/-- Auxiliary product identity on `secondRoot` used in `abs_denom_reductionStep_lt_one`. -/
private theorem secondRoot_denom_mul_eq {f g : BinaryQuadraticForm ℤ} (hpos : 0 ≤ f.discrim)
    (hD : ¬ IsSquare f.discrim) {γ : SL(2, ℤ)} (hγ : γ • f = g) :
    ((γ 1 1 : ℝ) * g.secondRoot + ((-γ 0 1 : ℤ) : ℝ)) *
      ((γ 1 0 : ℝ) * f.secondRoot + γ 1 1) = f.secondRoot := by
  have hm := denom_mul_secondRoot_smul hpos hD γ
  rw [hγ] at hm
  have hdet := γ.intCast_fin_two_mul_sub_mul_eq_one (R := ℝ)
  push_cast
  linear_combination (γ 1 1 : ℝ) * hm + f.secondRoot * hdet

/-- Key invariant step: if `γ • f = g` for Gauss reduced `f, g` of nonsquare discriminant,
`|(γ 1 0) ω₁(f) + γ 1 1| < 1`, and `γ 1 1 ≠ 0`, then after one reduction step on `f` the new
denominator magnitude `|(γ' 1 0) ω₁(f.reductionStep) + γ' 1 1|` remains strictly less than `1`. -/
private theorem abs_denom_reductionStep_lt_one {f g : BinaryQuadraticForm ℤ}
    (hf : f.IsGaussReduced) (hg : g.IsGaussReduced) (hD : ¬ IsSquare f.discrim)
    {γ : SL(2, ℤ)} (hγ : γ • f = g)
    (hlt : |(γ 1 0 : ℝ) * f.firstRoot + γ 1 1| < 1) (hs : γ 1 1 ≠ 0) :
    |((γ * (reductionStepMatrix f)⁻¹) 1 0 : ℝ) * f.reductionStep.firstRoot +
      (γ * (reductionStepMatrix f)⁻¹) 1 1| < 1 := by
  set f' := f.reductionStep
  set γ' := γ * (reductionStepMatrix f)⁻¹
  have hf' : f'.IsGaussReduced := hf.reductionStep hD
  have hD' : ¬ IsSquare f'.discrim := by rwa [discrim_reductionStep]
  have hγ' : γ' • f' = g := (mul_inv_reductionStepMatrix_smul γ f).trans hγ
  by_contra! hge
  have hne1 : |(γ' 1 0 : ℝ) * f'.firstRoot + γ' 1 1| ≠ 1 := fun heq ↦ hs <| by
    obtain ⟨hr', -⟩ :=
      (abs_intCast_mul_firstRoot_add_intCast_eq_one_iff hf'.discrim_pos.le hD' _ _).mp heq
    rwa [mul_inv_reductionStepMatrix_one_zero, neg_eq_zero] at hr'
  have hgt1 : 1 < |(γ' 1 0 : ℝ) * f'.firstRoot + γ' 1 1| := lt_of_le_of_ne hge hne1.symm
  have hprod1 : |((γ'⁻¹ 1 0 : ℝ) * g.firstRoot + γ'⁻¹ 1 1)| *
      |(γ' 1 0 : ℝ) * f'.firstRoot + γ' 1 1| = 1 := by
    have h := congrArg abs (denom_inv_mul_denom_firstRoot hf'.discrim_pos.le hD' γ')
    rwa [hγ', abs_mul, abs_one] at h
  have hinv_lt : |(γ 1 1 : ℝ) * g.firstRoot + ((-γ 0 1 : ℤ) : ℝ)| < 1 := by
    have h₀ : γ'⁻¹ 1 0 = γ 1 1 := by
      have hinv : γ'⁻¹ 1 0 = -γ' 1 0 := by simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
      rw [hinv, mul_inv_reductionStepMatrix_one_zero, neg_neg]
    have h₁ : γ'⁻¹ 1 1 = -γ 0 1 := by
      have hinv : γ'⁻¹ 1 1 = γ' 0 0 := by simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
      rw [hinv, mul_inv_reductionStepMatrix_zero_zero]
    rw [← h₀, ← h₁]
    nlinarith [abs_nonneg ((γ'⁻¹ 1 0 : ℝ) * g.firstRoot + γ'⁻¹ 1 1)]
  have hr : γ 1 0 ≠ 0 := fun hr0 ↦ by
    rw [hr0, Int.cast_zero, zero_mul, zero_add] at hlt
    have : (1 : ℝ) ≤ |(γ 1 1 : ℝ)| := by exact_mod_cast Int.one_le_abs hs
    linarith
  have hgB := (one_lt_abs_secondRoot_linear hg hs hinv_lt).1
  have hfB := (one_lt_abs_secondRoot_linear hf hr hlt).2 hs
  have habs_prod := congrArg abs (secondRoot_denom_mul_eq hf.discrim_pos.le hD hγ)
  rw [abs_mul] at habs_prod
  nlinarith [abs_nonneg f.secondRoot]

private theorem not_isSquare_of_discrim_eq {D : ℤ} [Fact (¬ IsSquare D)]
    {f : BinaryQuadraticForm ℤ} (hf : f.discrim = D) : ¬ IsSquare f.discrim := by
  rw [hf]
  exact Fact.out

section Descent

variable {D : ℤ} [Fact (¬ IsSquare D)]

/-- Sequence of matrices `γ_n` satisfying `γ_n • ((reductionPerm D ^ n) f) = γ₀ • f`. -/
private noncomputable def iterMatrix (f : gaussReducedForms D) (γ₀ : SL(2, ℤ)) : ℕ → SL(2, ℤ)
  | 0 => γ₀
  | n + 1 =>
      iterMatrix f γ₀ n *
        (reductionStepMatrix ((reductionPerm D ^ n) f : gaussReducedForms D))⁻¹

private theorem iterMatrix_smul (f : gaussReducedForms D) (γ₀ : SL(2, ℤ)) (n : ℕ) :
    iterMatrix f γ₀ n • (((reductionPerm D ^ n) f : gaussReducedForms D) : BinaryQuadraticForm ℤ) =
      γ₀ • (f : BinaryQuadraticForm ℤ) := by
  induction n with
  | zero => simp [iterMatrix]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coe_reductionPerm_apply, iterMatrix,
      mul_inv_reductionStepMatrix_smul, ih]

/-- Magnitude of the `n`-th Möbius denominator along the reduction orbit of `f`. -/
private noncomputable def iterDenomAbs (f : gaussReducedForms D) (γ₀ : SL(2, ℤ)) (n : ℕ) : ℝ :=
  |(iterMatrix f γ₀ n 1 0 : ℝ) * (((reductionPerm D ^ n) f).1).firstRoot + iterMatrix f γ₀ n 1 1|

/-- If `iterMatrix f γ₀ n 1 1` never vanishes, `iterDenomAbs f γ₀ n` stays `< 1` while growing at
least geometrically relative to `μ = sup |firstRoot|`. -/
private theorem iterDenomAbs_lt_one_and_le {f g : gaussReducedForms D} {γ₀ : SL(2, ℤ)}
    (hγ₀ : γ₀ • (f : BinaryQuadraticForm ℤ) = g) (hlt₀ : iterDenomAbs f γ₀ 0 < 1)
    (hne : ∀ n : ℕ, iterMatrix f γ₀ n 1 1 ≠ 0) (n : ℕ) :
    iterDenomAbs f γ₀ n < 1 ∧
      iterDenomAbs f γ₀ 0 ≤
        iterDenomAbs f γ₀ n *
          (univ.sup' ⟨f, mem_univ f⟩ fun h : gaussReducedForms D ↦ |h.1.firstRoot|) ^ n := by
  set μ : ℝ := univ.sup' ⟨f, mem_univ f⟩ fun h : gaussReducedForms D ↦ |h.1.firstRoot|
  obtain ⟨-, hg_red⟩ := mem_gaussReducedForms.mp g.2
  induction n with
  | zero => simpa using hlt₀
  | succ n ih =>
    set fn : gaussReducedForms D := (reductionPerm D ^ n) f
    obtain ⟨hDfn, hfn⟩ := mem_gaussReducedForms.mp fn.2
    have hlt_next : iterDenomAbs f γ₀ (n + 1) < 1 := by
      simpa only [iterDenomAbs, iterMatrix, pow_succ', Equiv.Perm.mul_apply,
        coe_reductionPerm_apply] using abs_denom_reductionStep_lt_one hfn hg_red
          (not_isSquare_of_discrim_eq hDfn) ((iterMatrix_smul f γ₀ n).trans hγ₀) ih.1 (hne n)
    have hmul_step : |fn.1.firstRoot| * iterDenomAbs f γ₀ (n + 1) = iterDenomAbs f γ₀ n := by
      have h := congrArg abs (firstRoot_mul_denom_reductionStep (iterMatrix f γ₀ n)
        hfn.discrim_pos.le (not_isSquare_of_discrim_eq hDfn))
      rw [abs_mul] at h
      simpa only [iterDenomAbs, iterMatrix, pow_succ', Equiv.Perm.mul_apply,
        coe_reductionPerm_apply, fn] using h
    have hfn_le_μ : |fn.1.firstRoot| ≤ μ :=
      Finset.le_sup' (fun h : gaussReducedForms D ↦ |h.1.firstRoot|) (mem_univ fn)
    have hμ_nonneg : 0 ≤ μ ^ n :=
      pow_nonneg ((abs_nonneg _).trans (Finset.le_sup'
        (fun h : gaussReducedForms D ↦ |h.1.firstRoot|) (mem_univ f))) n
    refine ⟨hlt_next, ?_⟩
    calc
      iterDenomAbs f γ₀ 0 ≤ iterDenomAbs f γ₀ n * μ ^ n := ih.2
      _ = (|fn.1.firstRoot| * iterDenomAbs f γ₀ (n + 1)) * μ ^ n := by rw [hmul_step]
      _ ≤ (μ * iterDenomAbs f γ₀ (n + 1)) * μ ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfn_le_μ (abs_nonneg _)) hμ_nonneg
      _ = iterDenomAbs f γ₀ (n + 1) * μ ^ (n + 1) := by rw [pow_succ]; ring

/-- Archimedean cycle descent: if `f, g : gaussReducedForms D` satisfy `γ₀ • f = g` with
`|(γ₀ 1 0) ω₁(f) + γ₀ 1 1| < 1`, then `f` and `g` lie in the same cycle of `reductionPerm D`. -/
private theorem sameCycle_of_abs_denom_lt_one {f g : gaussReducedForms D} {γ₀ : SL(2, ℤ)}
    (hγ₀ : γ₀ • (f : BinaryQuadraticForm ℤ) = g)
    (hlt₀ : |(γ₀ 1 0 : ℝ) * (f : BinaryQuadraticForm ℤ).firstRoot + γ₀ 1 1| < 1) :
    (reductionPerm D).SameCycle f g := by
  classical
  by_cases hex : ∃ n : ℕ, iterMatrix f γ₀ n 1 1 = 0
  · obtain ⟨n, hn⟩ := hex
    set fn : gaussReducedForms D := (reductionPerm D ^ n) f
    obtain ⟨hDfn, hfn⟩ := mem_gaussReducedForms.mp fn.2
    obtain ⟨-, hg_red⟩ := mem_gaussReducedForms.mp g.2
    have hstep : fn.1.reductionStep = g.1 :=
      eq_reductionStep_of_smul_eq_of_apply_one_one_eq_zero hfn hg_red
        (not_isSquare_of_discrim_eq hDfn) ((iterMatrix_smul f γ₀ n).trans hγ₀) hn
    have hg_eq : reductionPerm D fn = g := Subtype.ext ((coe_reductionPerm_apply fn).trans hstep)
    exact ⟨(n + 1 : ℕ), by rw [zpow_natCast, pow_succ', Equiv.Perm.mul_apply, hg_eq]⟩
  · push Not at hex
    exfalso
    set μ : ℝ := univ.sup' ⟨f, mem_univ f⟩ fun h : gaussReducedForms D ↦ |h.1.firstRoot|
    have hμ_lt : μ < 1 := (Finset.sup'_lt_iff _).mpr fun h _ ↦
      (isGaussReduced_iff_roots.mp (mem_gaussReducedForms.mp h.2).2).2.1
    obtain ⟨hDf, hf_red⟩ := mem_gaussReducedForms.mp f.2
    have hx₀_pos : 0 < iterDenomAbs f γ₀ 0 :=
      abs_pos.mpr (denom_firstRoot_ne_zero hf_red.discrim_pos.le
        (not_isSquare_of_discrim_eq hDf) γ₀)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx₀_pos hμ_lt
    obtain ⟨hxn_lt, hx0_le⟩ :=
      iterDenomAbs_lt_one_and_le hγ₀ (by simpa [iterDenomAbs, iterMatrix] using hlt₀) hex n
    have hμn_nonneg : 0 ≤ μ ^ n :=
      pow_nonneg ((abs_nonneg _).trans (Finset.le_sup'
        (fun h : gaussReducedForms D ↦ |h.1.firstRoot|) (mem_univ f))) n
    nlinarith

/-- **Gauss's theorem on reduced cycles**: if two Gauss reduced forms of nonsquare discriminant `D`
are properly equivalent (`γ • f = g`), then they lie in the same cycle of `reductionPerm D`. -/
theorem sameCycle_reductionPerm_of_smul_eq {f g : gaussReducedForms D} {γ : SL(2, ℤ)}
    (hγ : γ • (f : BinaryQuadraticForm ℤ) = g) :
    (reductionPerm D).SameCycle f g := by
  obtain ⟨hDf, hf_red⟩ := mem_gaussReducedForms.mp f.2
  obtain ⟨-, hg_red⟩ := mem_gaussReducedForms.mp g.2
  have hD : ¬ IsSquare f.1.discrim := not_isSquare_of_discrim_eq hDf
  set d₁ : ℝ := |(γ 1 0 : ℝ) * f.1.firstRoot + γ 1 1|
  set d₂ : ℝ := |(γ⁻¹ 1 0 : ℝ) * g.1.firstRoot + γ⁻¹ 1 1|
  have hprod : d₂ * d₁ = 1 := by
    have h := congrArg abs (denom_inv_mul_denom_firstRoot hf_red.discrim_pos.le hD γ)
    rwa [hγ, abs_mul, abs_one] at h
  rcases lt_trichotomy d₁ 1 with hlt | heq | hgt
  · exact sameCycle_of_abs_denom_lt_one hγ hlt
  · obtain ⟨hr, -⟩ :=
      (abs_intCast_mul_firstRoot_add_intCast_eq_one_iff hf_red.discrim_pos.le hD _ _).mp heq
    have hfg : f = g := Subtype.ext
      (eq_of_smul_eq_of_apply_one_zero_eq_zero hf_red hg_red hD hγ hr)
    exact hfg.sameCycle _
  · have hd₂_lt : d₂ < 1 := by nlinarith [abs_nonneg ((γ⁻¹ 1 0 : ℝ) * g.1.firstRoot + γ⁻¹ 1 1)]
    have hγ_inv : γ⁻¹ • (g : BinaryQuadraticForm ℤ) = f := by rw [← hγ, inv_smul_smul]
    exact (sameCycle_of_abs_denom_lt_one hγ_inv hd₂_lt).symm

/-- **Gauss's theorem**: two Gauss reduced forms of nonsquare discriminant `D` lie in the same cycle
of `reductionPerm D` if and only if they are properly equivalent. -/
theorem sameCycle_reductionPerm_iff {f g : gaussReducedForms D} :
    (reductionPerm D).SameCycle f g ↔ ∃ γ : SL(2, ℤ), γ • (f : BinaryQuadraticForm ℤ) = g :=
  ⟨exists_smul_eq_of_sameCycle, fun ⟨_, hγ⟩ ↦ sameCycle_reductionPerm_of_smul_eq hγ⟩

end Descent

/-! ### Cycle classification of all forms of discriminant `D` -/

/-- All integral binary quadratic forms of fixed discriminant `D`, as a `SubMulAction` of
`SL(2, ℤ)`. -/
def formsOfDiscrim (D : ℤ) : SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ) where
  carrier := {f | f.discrim = D}
  smul_mem' γ f hf := (discrim_smul γ f).trans hf

/-- Membership in `formsOfDiscrim D` is having discriminant `D`. -/
@[simp] theorem mem_formsOfDiscrim {D : ℤ} {f : BinaryQuadraticForm ℤ} :
    f ∈ formsOfDiscrim D ↔ f.discrim = D := by
  rfl

section AllClasses

variable (D : ℤ) [Fact (¬ IsSquare D)]

/-- Send a cycle of `reductionPerm D` to its proper equivalence class in `formsOfDiscrim D`. -/
noncomputable def cycleToProperClass :
    Quotient (Equiv.Perm.SameCycle.setoid (reductionPerm D)) →
      orbitRel.Quotient SL(2, ℤ) (formsOfDiscrim D) :=
  Quotient.map'
    (fun f : gaussReducedForms D ↦ ⟨f.1, mem_formsOfDiscrim.mpr (mem_gaussReducedForms.mp f.2).1⟩)
    fun f g h ↦ by
      obtain ⟨γ, hγ⟩ := exists_smul_eq_of_sameCycle h.symm
      exact ⟨γ, Subtype.ext (by simpa only [SubMulAction.val_smul] using hγ)⟩

/-- On a Gauss reduced representative, `cycleToProperClass` gives its `SL(2, ℤ)`-orbit class. -/
@[simp] theorem cycleToProperClass_mk (f : gaussReducedForms D) :
    cycleToProperClass D (Quotient.mk'' f) =
      Quotient.mk'' ⟨f.1, mem_formsOfDiscrim.mpr (mem_gaussReducedForms.mp f.2).1⟩ := by
  rfl

/-- Distinct cycles of `reductionPerm D` give distinct proper equivalence classes. -/
theorem cycleToProperClass_injective : Function.Injective (cycleToProperClass D) := by
  refine fun c₁ c₂ ↦ Quotient.inductionOn₂' c₁ c₂ fun f g h ↦ ?_
  rw [cycleToProperClass_mk, cycleToProperClass_mk] at h
  obtain ⟨γ, hγ⟩ := Quotient.exact' h
  exact Quotient.sound' ((sameCycle_reductionPerm_of_smul_eq (D := D)
    (by simpa only [SubMulAction.val_smul] using congrArg Subtype.val hγ)).symm)

/-- For positive nonsquare `D`, every proper class of discriminant `D` comes from a cycle of
`reductionPerm D`. -/
theorem cycleToProperClass_surjective (hpos : 0 < D) :
    Function.Surjective (cycleToProperClass D) := by
  refine Quotient.ind' fun f ↦ ?_
  have hfD : f.1.discrim = D := mem_formsOfDiscrim.mp f.2
  obtain ⟨γ, hγ⟩ := exists_smul_mem_gaussReducedForms f.1 (by rwa [hfD])
    (not_isSquare_of_discrim_eq hfD)
  rw [hfD] at hγ
  refine ⟨Quotient.mk'' ⟨γ • f.1, hγ⟩, ?_⟩
  rw [cycleToProperClass_mk]
  exact Quotient.sound' ⟨γ, Subtype.ext rfl⟩

/-- **Cycles of reduced forms classify proper classes**: for positive nonsquare `D`, the cycles of
`reductionPerm D` are in bijection with the `SL(2, ℤ)`-orbits on `formsOfDiscrim D`. -/
noncomputable def cycleEquivProperClass (hpos : 0 < D) :
    Quotient (Equiv.Perm.SameCycle.setoid (reductionPerm D)) ≃
      orbitRel.Quotient SL(2, ℤ) (formsOfDiscrim D) :=
  Equiv.ofBijective (cycleToProperClass D)
    ⟨cycleToProperClass_injective D, cycleToProperClass_surjective D hpos⟩

/-- The forward map of `cycleEquivProperClass` is `cycleToProperClass`. -/
@[simp] theorem cycleEquivProperClass_apply (hpos : 0 < D)
    (c : Quotient (Equiv.Perm.SameCycle.setoid (reductionPerm D))) :
    cycleEquivProperClass D hpos c = cycleToProperClass D c := by
  rfl

/-- **The number of proper equivalence classes of forms of discriminant `D > 0`** (nonsquare) is the
number of cycles of `reductionPerm D`. -/
theorem nat_card_formsOfDiscrim_quotient (hpos : 0 < D) :
    Nat.card (orbitRel.Quotient SL(2, ℤ) (formsOfDiscrim D)) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (reductionPerm D))) :=
  Nat.card_congr (cycleEquivProperClass D hpos).symm

end AllClasses

/-! ### Primitive Gauss reduced forms and primitive cycles -/

/-- The **primitive Gauss reduced forms** of discriminant `D`: the Gauss reduced forms of
discriminant `D` whose coefficients have gcd `1`. -/
def primitiveGaussReducedForms (D : ℤ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ gaussReducedForms D | Int.gcd f.a (Int.gcd f.b f.c) = 1}

/-- **Membership in `primitiveGaussReducedForms D`**: `f ∈ primitiveGaussReducedForms D` if and only
if `f.discrim = D`, `f` is Gauss reduced, and `f` is primitive. -/
@[simp] theorem mem_primitiveGaussReducedForms {D : ℤ} {f : BinaryQuadraticForm ℤ} :
    f ∈ primitiveGaussReducedForms D ↔ f.discrim = D ∧ f.IsGaussReduced ∧ f.IsPrimitive := by
  rw [primitiveGaussReducedForms, mem_filter, mem_gaussReducedForms, isPrimitive_iff,
    content_def, and_assoc]

/-- `primitiveGaussReducedForms D` is a subset of `gaussReducedForms D`. -/
theorem primitiveGaussReducedForms_subset_gaussReducedForms (D : ℤ) :
    primitiveGaussReducedForms D ⊆ gaussReducedForms D :=
  filter_subset _ _

/-- The reduction step preserves the content of a form. -/
@[simp] theorem content_reductionStep (f : BinaryQuadraticForm ℤ) :
    f.reductionStep.content = f.content := by
  rw [reductionStep_eq_smul, content_smul]

/-- The reduction step preserves primitivity. -/
@[simp] theorem isPrimitive_reductionStep (f : BinaryQuadraticForm ℤ) :
    f.reductionStep.IsPrimitive ↔ f.IsPrimitive := by
  rw [reductionStep_eq_smul, isPrimitive_smul_iff]

/-- Every primitive form of positive nonsquare discriminant `D` is properly equivalent to a member
of `primitiveGaussReducedForms D`. -/
theorem exists_smul_mem_primitiveGaussReducedForms {f : BinaryQuadraticForm ℤ}
    (hpos : 0 < f.discrim) (hD : ¬ IsSquare f.discrim) (hp : f.IsPrimitive) :
    ∃ γ : SL(2, ℤ), γ • f ∈ primitiveGaussReducedForms f.discrim := by
  obtain ⟨γ, hγ⟩ := exists_smul_isGaussReduced f hpos hD
  exact ⟨γ, mem_primitiveGaussReducedForms.mpr
    ⟨discrim_smul γ f, hγ, (isPrimitive_smul_iff f γ).mpr hp⟩⟩

section PrimitiveCycles

variable (D : ℤ) [Fact (¬ IsSquare D)]

/-- For nonsquare `D`, the reduction step as a permutation of `primitiveGaussReducedForms D`. -/
noncomputable def primitiveReductionPerm : Equiv.Perm (primitiveGaussReducedForms D) :=
  Equiv.ofBijective
    (fun f ↦ ⟨f.1.reductionStep, by
      obtain ⟨hD, hf, hp⟩ := mem_primitiveGaussReducedForms.mp f.2
      exact mem_primitiveGaussReducedForms.mpr
        ⟨by rw [discrim_reductionStep, hD], hf.reductionStep (not_isSquare_of_discrim_eq hD),
          (isPrimitive_reductionStep f.1).mpr hp⟩⟩)
    (Finite.injective_iff_bijective.mp fun f g h ↦ by
      obtain ⟨hDf, hf, -⟩ := mem_primitiveGaussReducedForms.mp f.2
      obtain ⟨hDg, hg, -⟩ := mem_primitiveGaussReducedForms.mp g.2
      exact Subtype.ext <| reductionStep_injOn ⟨hf, not_isSquare_of_discrim_eq hDf⟩
        ⟨hg, not_isSquare_of_discrim_eq hDg⟩ (congrArg Subtype.val h))

variable {D}

/-- `primitiveReductionPerm D` acts as `reductionStep`. -/
@[simp] theorem coe_primitiveReductionPerm_apply (f : primitiveGaussReducedForms D) :
    (primitiveReductionPerm D f : BinaryQuadraticForm ℤ) =
      (f : BinaryQuadraticForm ℤ).reductionStep := by
  simp only [primitiveReductionPerm, Equiv.ofBijective_apply]

/-- Iterates of `primitiveReductionPerm D` agree with iterates of `reductionPerm D` on the
underlying form. -/
private theorem coe_primitiveReductionPerm_pow (f : primitiveGaussReducedForms D) (n : ℕ) :
    (((primitiveReductionPerm D ^ n) f : primitiveGaussReducedForms D) : BinaryQuadraticForm ℤ) =
      (((reductionPerm D ^ n)
        ⟨f.1, primitiveGaussReducedForms_subset_gaussReducedForms D f.2⟩ : gaussReducedForms D) :
          BinaryQuadraticForm ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coe_primitiveReductionPerm_apply,
      pow_succ', Equiv.Perm.mul_apply, coe_reductionPerm_apply, ih]

/-- Inclusion into `gaussReducedForms D` preserves and reflects cycles of `primitiveReductionPerm D`
and `reductionPerm D`. -/
theorem sameCycle_primitiveReductionPerm_iff_sameCycle_reductionPerm
    {f g : primitiveGaussReducedForms D} :
    (primitiveReductionPerm D).SameCycle f g ↔
      (reductionPerm D).SameCycle
        ⟨f.1, primitiveGaussReducedForms_subset_gaussReducedForms D f.2⟩
        ⟨g.1, primitiveGaussReducedForms_subset_gaussReducedForms D g.2⟩ := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext ((coe_primitiveReductionPerm_pow f n).symm.trans (congrArg Subtype.val hn))
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext ((coe_primitiveReductionPerm_pow f n).trans (congrArg Subtype.val hn))

/-- **Gauss's theorem for primitive reduced forms**: two primitive Gauss reduced forms of nonsquare
discriminant `D` lie in the same cycle of `primitiveReductionPerm D` if and only if they are
properly equivalent. -/
theorem sameCycle_primitiveReductionPerm_iff {f g : primitiveGaussReducedForms D} :
    (primitiveReductionPerm D).SameCycle f g ↔
      ∃ γ : SL(2, ℤ), γ • (f : BinaryQuadraticForm ℤ) = g :=
  sameCycle_primitiveReductionPerm_iff_sameCycle_reductionPerm.trans sameCycle_reductionPerm_iff

variable (D)

/-- Send a cycle of `primitiveReductionPerm D` to its proper equivalence class in
`primitiveForms D`. -/
noncomputable def primitiveCycleToProperClass :
    Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D)) →
      orbitRel.Quotient SL(2, ℤ) (primitiveForms D) :=
  Quotient.map'
    (fun f : primitiveGaussReducedForms D ↦
      ⟨f.1, by
        obtain ⟨hd, -, hp⟩ := mem_primitiveGaussReducedForms.mp f.2
        exact (mem_primitiveForms D f.1).mpr ⟨hd, hp⟩⟩)
    fun f g h ↦ by
      obtain ⟨γ, hγ⟩ := sameCycle_primitiveReductionPerm_iff.mp h.symm
      exact ⟨γ, Subtype.ext (by simpa only [SubMulAction.val_smul] using hγ)⟩

/-- On a primitive Gauss reduced representative, `primitiveCycleToProperClass` gives its proper
class in `primitiveForms D`. -/
@[simp] theorem primitiveCycleToProperClass_mk (f : primitiveGaussReducedForms D) :
    primitiveCycleToProperClass D (Quotient.mk'' f) =
      Quotient.mk'' ⟨f.1, (mem_primitiveForms D f.1).mpr
        ⟨(mem_primitiveGaussReducedForms.mp f.2).1,
          (mem_primitiveGaussReducedForms.mp f.2).2.2⟩⟩ := by
  rfl

/-- Distinct cycles of `primitiveReductionPerm D` give distinct proper classes in
`primitiveForms D`. -/
theorem primitiveCycleToProperClass_injective :
    Function.Injective (primitiveCycleToProperClass D) := by
  refine fun c₁ c₂ ↦ Quotient.inductionOn₂' c₁ c₂ fun f g h ↦ ?_
  rw [primitiveCycleToProperClass_mk, primitiveCycleToProperClass_mk] at h
  obtain ⟨γ, hγ⟩ := Quotient.exact' h
  exact Quotient.sound' ((sameCycle_primitiveReductionPerm_iff.mpr
    ⟨γ, by simpa only [SubMulAction.val_smul] using congrArg Subtype.val hγ⟩).symm)

/-- For positive nonsquare `D`, every proper class of primitive forms of discriminant `D` comes from
a cycle of `primitiveReductionPerm D`. -/
theorem primitiveCycleToProperClass_surjective (hpos : 0 < D) :
    Function.Surjective (primitiveCycleToProperClass D) := by
  refine Quotient.ind' fun f ↦ ?_
  obtain ⟨hfD, hfp⟩ := (mem_primitiveForms D f.1).mp f.2
  obtain ⟨γ, hγ⟩ := exists_smul_mem_primitiveGaussReducedForms (by rwa [hfD])
    (not_isSquare_of_discrim_eq hfD) hfp
  rw [hfD] at hγ
  refine ⟨Quotient.mk'' ⟨γ • f.1, hγ⟩, ?_⟩
  rw [primitiveCycleToProperClass_mk]
  exact Quotient.sound' ⟨γ, Subtype.ext rfl⟩

/-- **Cycles of primitive reduced forms classify primitive proper classes**: for positive nonsquare
`D`, the cycles of `primitiveReductionPerm D` are in bijection with the proper equivalence classes
of primitive forms of discriminant `D`. -/
noncomputable def primitiveCycleEquivProperClass (hpos : 0 < D) :
    Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D)) ≃
      orbitRel.Quotient SL(2, ℤ) (primitiveForms D) :=
  Equiv.ofBijective (primitiveCycleToProperClass D)
    ⟨primitiveCycleToProperClass_injective D, primitiveCycleToProperClass_surjective D hpos⟩

/-- The forward map of `primitiveCycleEquivProperClass` is `primitiveCycleToProperClass`. -/
@[simp] theorem primitiveCycleEquivProperClass_apply (hpos : 0 < D)
    (c : Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D))) :
    primitiveCycleEquivProperClass D hpos c = primitiveCycleToProperClass D c := by
  rfl

/-- **The number of proper classes of primitive forms of discriminant `D > 0`** (nonsquare) is the
number of cycles of `primitiveReductionPerm D`. -/
theorem nat_card_primitiveForms_quotient (hpos : 0 < D) :
    Nat.card (orbitRel.Quotient SL(2, ℤ) (primitiveForms D)) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D))) :=
  Nat.card_congr (primitiveCycleEquivProperClass D hpos).symm

end PrimitiveCycles

end TauCeti.BinaryQuadraticForm
