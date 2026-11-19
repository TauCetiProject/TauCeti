/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.NumberTheory.BinaryQuadraticForm.IndefiniteReduction.Root
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Gauss's cycle theorem and classification of indefinite proper classes

For a positive nonsquare discriminant `D`, the Gauss reduction step `reductionStep` permutes the
finite set `gaussReducedForms D` of Gauss reduced forms (`reductionPerm D`). Unlike in the positive
definite case, a proper equivalence class of indefinite forms generally contains several reduced
forms: all forms in a single cycle of `reductionPerm D` are properly equivalent
(`exists_smul_eq_of_sameCycle`).

This file proves the converse, **Gauss's cycle theorem**
(`sameCycle_reductionPerm_iff_exists_smul_eq`): two Gauss reduced forms of discriminant `D` are
properly equivalent under `SL(2, ℤ)` if and only if they lie in the same cycle of
`reductionPerm D`. Consequently, the quotient `GaussReducedCycle D` of `gaussReducedForms D` by
`(reductionPerm D).SameCycle` is in canonical bijection with the `SL(2, ℤ)` orbits of integral
forms of discriminant `D` (`gaussReducedCyclesEquivProperClasses`).

Because proper equivalence and `reductionStep` preserve content, the permutation restricts to the
finite set `primitiveGaussReducedForms D` of primitive Gauss reduced forms
(`primitiveReductionPerm D`), and its cycle quotient `PrimitiveGaussReducedCycle D` is in canonical
bijection with the proper classes `orbitRel.Quotient SL(2, ℤ) (primitiveForms D)`
(`primitiveGaussReducedCyclesEquivProperClasses`).

## Proof outline

Every cycle contains a form with positive leading coefficient (`a > 0`), since `a c < 0` flips the
sign of the leading coefficient at each step. For two reduced forms `f` and `g` with `f.a > 0` and
`g.a > 0` related by `γ • f = g` (normalised via `SL2_neg_smul` so that the Möbius denominator at
`f.firstRoot` is positive), the root bounds `firstRoot ∈ (0, 1)` and `secondRoot < -1` force
`1 ≤ γ 0 0`, `1 ≤ γ 1 1` and either `f = g`, `0 < γ 0 1 ∧ 0 < γ 1 0`, or `γ 0 1 < 0 ∧ γ 1 0 < 0`.
Passing to `γ⁻¹` reduces the positive off-diagonal case to the negative off-diagonal case, where
two applications of `reductionPerm D` strictly decrease `γ 0 0` while preserving all invariants.

## Main definitions

* `TauCeti.BinaryQuadraticForm.discrimForms D`: the `SL(2, ℤ)` sub-action of integral binary
  quadratic forms of discriminant `D`.
* `TauCeti.BinaryQuadraticForm.GaussReducedCycle D`: cycles of `reductionPerm D` on
  `gaussReducedForms D`.
* `TauCeti.BinaryQuadraticForm.gaussReducedCyclesEquivProperClasses`: for `0 < D` nonsquare, the
  bijection between `GaussReducedCycle D` and `orbitRel.Quotient SL(2, ℤ) (discrimForms D)`.
* `TauCeti.BinaryQuadraticForm.primitiveGaussReducedForms D`: the finite set of primitive Gauss
  reduced forms of discriminant `D`.
* `TauCeti.BinaryQuadraticForm.primitiveReductionPerm D`: restriction of `reductionPerm D` to
  `primitiveGaussReducedForms D`.
* `TauCeti.BinaryQuadraticForm.PrimitiveGaussReducedCycle D`: cycles of `primitiveReductionPerm D`.
* `TauCeti.BinaryQuadraticForm.primitiveGaussReducedCyclesEquivProperClasses`: for `0 < D`
  nonsquare, the bijection between `PrimitiveGaussReducedCycle D` and
  `orbitRel.Quotient SL(2, ℤ) (primitiveForms D)`.

## Main results

* `TauCeti.BinaryQuadraticForm.sameCycle_reductionPerm_iff_exists_smul_eq`: **Gauss's cycle
  theorem**: two Gauss reduced forms are properly equivalent iff they lie in the same cycle.
* `TauCeti.BinaryQuadraticForm.nat_card_properClasses_discrimForms` and
  `TauCeti.BinaryQuadraticForm.nat_card_properClasses_primitiveForms`: proper class counts equal
  the cardinalities of `GaussReducedCycle D` and `PrimitiveGaussReducedCycle D`.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 183–193.
* J. Buchmann and U. Vollmer, *Binary Quadratic Forms: An Algorithmic Approach*, Springer, 2007,
  Chapter 6, Theorem 6.6.4.
* D. Zagier, *Zetafunktionen und quadratische Körper*, Springer, 1981, §13.
-/

public section

open Finset Matrix MulAction
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-! ### Negation in `SL(2, R)` and the fixed-discriminant sub-action -/

/-- Negating a matrix in `SL(2, R)` acts trivially on binary quadratic forms, since `(-x)² = x²`
and `(-x)(-y) = x y`. -/
@[simp] theorem SL2_neg_smul {R : Type*} [CommRing R] (γ : SL(2, R))
    (f : BinaryQuadraticForm R) : (-γ) • f = γ • f := by
  ext <;> simp

/-- The central element `-1 ∈ SL(2, R)` acts trivially on binary quadratic forms. -/
theorem SL2_neg_one_smul {R : Type*} [CommRing R] (f : BinaryQuadraticForm R) :
    (-1 : SL(2, R)) • f = f := by
  rw [SL2_neg_smul, one_smul]

/-- Integral binary quadratic forms of fixed discriminant `D`, as a sub-action of `SL(2, ℤ)`. -/
def discrimForms (D : ℤ) : SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ) where
  carrier := {f | f.discrim = D}
  smul_mem' γ f hf := (discrim_smul γ f).trans hf

/-- A form lies in `discrimForms D` exactly when its discriminant is `D`. -/
@[simp] theorem mem_discrimForms {D : ℤ} {f : BinaryQuadraticForm ℤ} :
    f ∈ discrimForms D ↔ f.discrim = D :=
  Iff.rfl

/-! ### Sign analysis and two-step descent for Gauss's cycle theorem -/

private theorem denom_firstRoot_mul (α β : SL(2, ℤ)) {f : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hD : ¬ IsSquare f.discrim) :
    (((α * β) 1 0 : ℝ) * f.firstRoot + (α * β) 1 1) =
      ((α 1 0 : ℝ) * (β • f).firstRoot + α 1 1) * ((β 1 0 : ℝ) * f.firstRoot + β 1 1) := by
  have hβ := denom_firstRoot_ne_zero β hpos hD
  rw [firstRoot_smul β hpos hD]
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
    Int.cast_mul]
  field_simp
  ring

private theorem coe_T_zpow_mul_S (k : ℤ) :
    ((ModularGroup.T ^ k * ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![k, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, ModularGroup.coe_S]

private theorem coe_T_zpow_mul_S_inv (k : ℤ) :
    (((ModularGroup.T ^ k * ModularGroup.S)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, 1; -1, k] := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, ModularGroup.coe_S]

private theorem exists_sameCycle_a_pos {D : ℤ} [Fact (¬ IsSquare D)]
    (f : gaussReducedForms D) :
    ∃ f' : gaussReducedForms D, (reductionPerm D).SameCycle f f' ∧ 0 < f'.1.a := by
  obtain ⟨_, hf⟩ := mem_gaussReducedForms.mp f.2
  have hac : f.1.a * f.1.c < 0 := (isGaussReduced_iff.mp hf).1
  rcases lt_or_gt_of_ne (left_ne_zero_of_mul hac.ne) with ha | ha
  · refine ⟨reductionPerm D f, ⟨1, by simp⟩, ?_⟩
    rw [coe_reductionPerm_apply, reductionStep_a]
    nlinarith
  · exact ⟨f, Equiv.Perm.SameCycle.refl _ _, ha⟩

private theorem exists_smul_eq_and_denom_pos {f g : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hD : ¬ IsSquare f.discrim)
    (h : ∃ γ : SL(2, ℤ), γ • f = g) :
    ∃ γ : SL(2, ℤ), γ • f = g ∧ 0 < (γ 1 0 : ℝ) * f.firstRoot + γ 1 1 := by
  obtain ⟨γ, rfl⟩ := h
  rcases lt_or_gt_of_ne (denom_firstRoot_ne_zero γ hpos hD) with hneg | hpos'
  · refine ⟨-γ, SL2_neg_smul γ f, ?_⟩
    simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    linarith
  · exact ⟨γ, rfl, hpos'⟩

private theorem eq_of_mul_offDiag_eq_zero {D : ℤ} [Fact (¬ IsSquare D)]
    {f g : gaussReducedForms D} (hf_a : 0 < f.1.a) (hg_a : 0 < g.1.a)
    {γ : SL(2, ℤ)} (hγ : γ • f.1 = g.1)
    (hden₁ : 0 < (γ 1 0 : ℝ) * f.1.firstRoot + γ 1 1)
    (hden₂ : 0 < (γ 1 0 : ℝ) * f.1.secondRoot + γ 1 1)
    (hp : 1 ≤ γ 0 0) (hs : 1 ≤ γ 1 1) (hqr : γ 0 1 * γ 1 0 = 0) : f = g := by
  obtain ⟨hDf, hf⟩ := mem_gaussReducedForms.mp f.2
  obtain ⟨hDg, hg⟩ := mem_gaussReducedForms.mp g.2
  have hDpos : 0 ≤ f.1.discrim := hf.discrim_pos.le
  have hDns : ¬ IsSquare f.1.discrim := by rw [hDf]; exact Fact.out
  have hx₁ := hf.firstRoot_mem_Ioo_of_a_pos hf_a
  have hx₂ := hf.secondRoot_lt_neg_one_of_a_pos hf_a
  have hy₁ := hγ ▸ hg.firstRoot_mem_Ioo_of_a_pos hg_a
  have hy₂ := hγ ▸ hg.secondRoot_lt_neg_one_of_a_pos hg_a
  rw [firstRoot_smul γ hDpos hDns, Set.mem_Ioo, div_pos_iff_of_pos_right hden₁,
    div_lt_one hden₁] at hy₁
  rw [secondRoot_smul γ hDpos hDns, div_lt_iff₀ hden₂] at hy₂
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  have hp1 : γ 0 0 = 1 := by nlinarith
  have hs1 : γ 1 1 = 1 := by nlinarith
  have hr0 : γ 1 0 = 0 := by
    by_contra hr0
    have hq0 : γ 0 1 = 0 := (mul_eq_zero.mp hqr).resolve_right hr0
    simp only [hp1, hq0, hs1, Int.cast_one, Int.cast_zero, one_mul, add_zero] at hy₂ hden₂
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · have : (γ 1 0 : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hrneg
      nlinarith
    · have : (1 : ℝ) ≤ γ 1 0 := by exact_mod_cast hrpos
      nlinarith
  simp only [hp1, hs1, hr0, Int.cast_one, Int.cast_zero, one_mul, zero_mul, zero_add] at hy₁
  have hq0 : γ 0 1 = 0 := by
    have h1 : -1 < γ 0 1 := by exact_mod_cast (by linarith [hx₁.2, hy₁.1] : (-1 : ℝ) < γ 0 1)
    have h2 : γ 0 1 < 1 := by exact_mod_cast (by linarith [hx₁.1, hy₁.2] : (γ 0 1 : ℝ) < 1)
    omega
  apply Subtype.ext
  rw [← firstRoot_eq_firstRoot_iff hDpos hDns (hDf.trans hDg.symm), ← hγ,
    firstRoot_smul γ hDpos hDns]
  simp [hp1, hs1, hr0, hq0]

private theorem entries_of_smul_eq_of_a_pos {D : ℤ} [Fact (¬ IsSquare D)]
    {f g : gaussReducedForms D} (hf_a : 0 < f.1.a) (hg_a : 0 < g.1.a)
    {γ : SL(2, ℤ)} (hγ : γ • f.1 = g.1)
    (hden₁ : 0 < (γ 1 0 : ℝ) * f.1.firstRoot + γ 1 1) :
    1 ≤ γ 0 0 ∧ 1 ≤ γ 1 1 ∧
      (f = g ∨ (0 < γ 0 1 ∧ 0 < γ 1 0) ∨ (γ 0 1 < 0 ∧ γ 1 0 < 0)) := by
  obtain ⟨hDf, hf⟩ := mem_gaussReducedForms.mp f.2
  obtain ⟨_, hg⟩ := mem_gaussReducedForms.mp g.2
  have hDpos : 0 ≤ f.1.discrim := hf.discrim_pos.le
  have hDns : ¬ IsSquare f.1.discrim := by rw [hDf]; exact Fact.out
  have hx₁ := hf.firstRoot_mem_Ioo_of_a_pos hf_a
  have hx₂ := hf.secondRoot_lt_neg_one_of_a_pos hf_a
  have hden₂ : 0 < (γ 1 0 : ℝ) * f.1.secondRoot + γ 1 1 := by
    have hmul := smul_a_eq_mul_denom γ hDpos hf_a.ne'
    rw [hγ] at hmul
    have hga : (0 : ℝ) < g.1.a := by exact_mod_cast hg_a
    have hfa : (0 : ℝ) < f.1.a := by exact_mod_cast hf_a
    exact pos_of_mul_pos_right (hmul ▸ hga) (mul_pos hfa hden₁).le
  have hy₁ := hγ ▸ hg.firstRoot_mem_Ioo_of_a_pos hg_a
  have hy₂ := hγ ▸ hg.secondRoot_lt_neg_one_of_a_pos hg_a
  rw [firstRoot_smul γ hDpos hDns, Set.mem_Ioo, div_pos_iff_of_pos_right hden₁,
    div_lt_one hden₁] at hy₁
  rw [secondRoot_smul γ hDpos hDns, div_lt_iff₀ hden₂] at hy₂
  have hp : 1 ≤ γ 0 0 := by
    have : (0 : ℝ) < γ 0 0 := by nlinarith [hx₁.1, hx₂, hy₁.1, hy₂, hden₂]
    exact Int.lt_iff_add_one_le.mp (by exact_mod_cast this)
  have hs : 1 ≤ γ 1 1 := by
    have : (0 : ℝ) < γ 1 1 := by nlinarith [hx₁.1, hx₂, hden₁, hden₂]
    exact Int.lt_iff_add_one_le.mp (by exact_mod_cast this)
  have hqr : 0 ≤ γ 0 1 * γ 1 0 := by nlinarith [γ.fin_two_mul_sub_mul_eq_one]
  refine ⟨hp, hs, ?_⟩
  rcases eq_or_lt_of_le hqr with hqr0 | hqr_pos
  · exact Or.inl (eq_of_mul_offDiag_eq_zero hf_a hg_a hγ hden₁ hden₂ hp hs hqr0.symm)
  · exact Or.inr (mul_pos_iff.mp hqr_pos)

private theorem eq_step_two_of_add_mul_eq_zero {D : ℤ} [Fact (¬ IsSquare D)]
    {f g : gaussReducedForms D} (hf_a : 0 < f.1.a) (hg_a : 0 < g.1.a)
    {γ₁ : SL(2, ℤ)} {q : ℤ}
    (hγ₁ : γ₁ • (reductionPerm D f).1 = g.1)
    (h00 : γ₁ 0 0 = -q) (h01 : γ₁ 0 1 = 1) (h10 : γ₁ 1 0 = -1) (h11 : γ₁ 1 1 = 0) :
    g = reductionPerm D (reductionPerm D f) := by
  set f₁ := reductionPerm D f
  set f₂ := reductionPerm D f₁
  obtain ⟨_, hf⟩ := mem_gaussReducedForms.mp f.2
  obtain ⟨hDf₁, hf₁⟩ := mem_gaussReducedForms.mp f₁.2
  obtain ⟨hDf₂, hf₂⟩ := mem_gaussReducedForms.mp f₂.2
  obtain ⟨hDg, hg⟩ := mem_gaussReducedForms.mp g.2
  have hf₁_a : f₁.1.a < 0 := by
    rw [coe_reductionPerm_apply, reductionStep_a]
    nlinarith [(isGaussReduced_iff.mp hf).1]
  have hf₂_a : 0 < f₂.1.a := by
    rw [coe_reductionPerm_apply, reductionStep_a]
    nlinarith [(isGaussReduced_iff.mp hf₁).1]
  have hmat : γ₁ = -(ModularGroup.T ^ q * ModularGroup.S) := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_neg, coe_T_zpow_mul_S]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  rw [hmat, SL2_neg_smul] at hγ₁
  have hpos₁ : 0 ≤ f₁.1.discrim := hf₁.discrim_pos.le
  have hns₁ : ¬ IsSquare f₁.1.discrim := by rw [hDf₁]; exact Fact.out
  have hns_g : ¬ IsSquare g.1.discrim := by rw [hDg]; exact Fact.out
  have hgr : g.1.firstRoot = -f₁.1.firstRoot⁻¹ + q := by
    rw [← hγ₁, mul_smul,
      firstRoot_T_zpow_smul _ (by rw [S_smul]; exact c_ne_zero_of_not_isSquare_discrim hns₁),
      firstRoot_S_smul hpos₁ hns₁]
  set k₁ : ℤ := -((Int.sqrt f₁.1.discrim + f₁.1.b) / (2 * f₁.1.c))
  have hf₂r : f₂.1.firstRoot = -f₁.1.firstRoot⁻¹ + k₁ := by
    rw [coe_reductionPerm_apply, firstRoot_reductionStep hpos₁ hns₁]
    simp [k₁, sub_eq_add_neg]
  have hy := hg.firstRoot_mem_Ioo_of_a_pos hg_a
  have hz := hf₂.firstRoot_mem_Ioo_of_a_pos hf₂_a
  have hqk : q = k₁ := by
    have h1 : (-1 : ℝ) < (q - k₁ : ℤ) := by push_cast; linarith [hy.1, hz.2, hgr, hf₂r]
    have h2 : ((q - k₁ : ℤ) : ℝ) < 1 := by push_cast; linarith [hy.2, hz.1, hgr, hf₂r]
    have h1' : -1 < q - k₁ := by exact_mod_cast h1
    have h2' : q - k₁ < 1 := by exact_mod_cast h2
    omega
  apply Subtype.ext
  rw [← firstRoot_eq_firstRoot_iff hg.discrim_pos.le hns_g (hDg.trans hDf₂.symm), hgr, hf₂r, hqk]

private theorem step_one_bounds {D : ℤ} [Fact (¬ IsSquare D)]
    {f g : gaussReducedForms D} (hf_a : 0 < f.1.a) (hg_a : 0 < g.1.a)
    {γ : SL(2, ℤ)} (hγ : γ • f.1 = g.1)
    (hden : 0 < (γ 1 0 : ℝ) * f.1.firstRoot + γ 1 1)
    (hs : 1 ≤ γ 1 1) (hq : γ 0 1 < 0) :
    1 ≤ -((Int.sqrt f.1.discrim + f.1.b) / (2 * f.1.c)) ∧
      1 ≤ γ 0 0 + (-((Int.sqrt f.1.discrim + f.1.b) / (2 * f.1.c))) * γ 0 1 ∧
      γ 0 0 + (-((Int.sqrt f.1.discrim + f.1.b) / (2 * f.1.c))) * γ 0 1 < γ 0 0 ∧
      γ 1 0 + (-((Int.sqrt f.1.discrim + f.1.b) / (2 * f.1.c))) * γ 1 1 ≤ 0 := by
  obtain ⟨hDf, hf⟩ := mem_gaussReducedForms.mp f.2
  obtain ⟨_, hg⟩ := mem_gaussReducedForms.mp g.2
  have hDns : ¬ IsSquare f.1.discrim := by rw [hDf]; exact Fact.out
  set f₁ := reductionPerm D f
  obtain ⟨_, hf₁⟩ := mem_gaussReducedForms.mp f₁.2
  set k : ℤ := -((Int.sqrt f.1.discrim + f.1.b) / (2 * f.1.c))
  have hx₁ := hf.firstRoot_mem_Ioo_of_a_pos hf_a
  have hf₁_a : f₁.1.a < 0 := by
    rw [coe_reductionPerm_apply, reductionStep_a]
    nlinarith [(isGaussReduced_iff.mp hf).1]
  have hx₁' := hf₁.firstRoot_mem_Ioo_of_a_neg hf₁_a
  have hr₁ : f₁.1.firstRoot = -f.1.firstRoot⁻¹ + k := by
    rw [coe_reductionPerm_apply, firstRoot_reductionStep hf.discrim_pos.le hDns]
    simp [k, sub_eq_add_neg]
  have hinv_gt : 1 < f.1.firstRoot⁻¹ := (one_lt_inv₀ hx₁.1).mpr hx₁.2
  have hk_pos : 1 ≤ k := by
    have : (0 : ℝ) < k := by linarith [hx₁'.1, hr₁, hinv_gt]
    exact Int.lt_iff_add_one_le.mp (by exact_mod_cast this)
  have hy₁ := hγ ▸ hg.firstRoot_mem_Ioo_of_a_pos hg_a
  rw [firstRoot_smul γ hf.discrim_pos.le hDns, Set.mem_Ioo,
    div_pos_iff_of_pos_right hden] at hy₁
  have hp'_pos : 1 ≤ γ 0 0 + k * γ 0 1 := by
    have h1 : (-(γ 0 1 : ℝ)) * f.1.firstRoot⁻¹ < γ 0 0 := by
      rw [← div_eq_mul_inv, div_lt_iff₀ hx₁.1]
      linarith [hy₁.1]
    have hq' : 0 < -(γ 0 1 : ℝ) := by exact_mod_cast neg_pos.mpr hq
    have hk_lt : (k : ℝ) < f.1.firstRoot⁻¹ := by linarith [hx₁'.2, hr₁]
    have h2 : (0 : ℝ) < (γ 0 0 + k * γ 0 1 : ℤ) := by push_cast; nlinarith
    exact Int.lt_iff_add_one_le.mp (by exact_mod_cast h2)
  have hrs : γ 1 0 + k * γ 1 1 ≤ 0 := by
    have hdet := γ.fin_two_mul_sub_mul_eq_one
    have : 0 ≤ γ 0 1 * (γ 1 0 + k * γ 1 1) := by nlinarith
    nlinarith
  exact ⟨hk_pos, hp'_pos, by nlinarith, hrs⟩

private theorem mul_T_zpow_mul_S_inv_entries (δ : SL(2, ℤ)) (m : ℤ) :
    (δ * (ModularGroup.T ^ m * ModularGroup.S)⁻¹) 0 0 = -δ 0 1 ∧
      (δ * (ModularGroup.T ^ m * ModularGroup.S)⁻¹) 0 1 = δ 0 0 + m * δ 0 1 ∧
      (δ * (ModularGroup.T ^ m * ModularGroup.S)⁻¹) 1 0 = -δ 1 1 ∧
      (δ * (ModularGroup.T ^ m * ModularGroup.S)⁻¹) 1 1 = δ 1 0 + m * δ 1 1 := by
  have h : (((ModularGroup.T ^ m * ModularGroup.S)⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, m] := coe_T_zpow_mul_S_inv m
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [SpecialLinearGroup.coe_mul, h, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

private theorem denom_firstRoot_step_two_pos {f f₁ f₂ : BinaryQuadraticForm ℤ}
    (hpos : 0 ≤ f.discrim) (hDns : ¬ IsSquare f.discrim)
    (h₀ : 0 < f.firstRoot) (h₁ : f₁.firstRoot < 0)
    {k k₁ : ℤ} {γ : SL(2, ℤ)}
    (hf₁ : f₁ = (ModularGroup.T ^ k * ModularGroup.S) • f)
    (hf₂ : f₂ = (ModularGroup.T ^ k₁ * ModularGroup.S) • f₁)
    (hden : 0 < (γ 1 0 : ℝ) * f.firstRoot + γ 1 1) :
    0 < ((-(γ * (ModularGroup.T ^ k * ModularGroup.S)⁻¹ *
      (ModularGroup.T ^ k₁ * ModularGroup.S)⁻¹) 1 0 : ℤ) : ℝ) * f₂.firstRoot +
      (-(γ * (ModularGroup.T ^ k * ModularGroup.S)⁻¹ *
        (ModularGroup.T ^ k₁ * ModularGroup.S)⁻¹) 1 1 : ℤ) := by
  set σ₀ : SL(2, ℤ) := ModularGroup.T ^ k * ModularGroup.S
  set σ₁ : SL(2, ℤ) := ModularGroup.T ^ k₁ * ModularGroup.S
  have hcoc := denom_firstRoot_mul (γ * σ₀⁻¹ * σ₁⁻¹) (σ₁ * σ₀) hpos hDns
  have hmul_eq : (γ * σ₀⁻¹ * σ₁⁻¹) * (σ₁ * σ₀) = γ := by simp [mul_assoc]
  have hcoc₁ := denom_firstRoot_mul σ₁ σ₀ hpos hDns
  rw [hmul_eq, hcoc₁, ← hf₁, mul_smul, ← hf₁, ← hf₂] at hcoc
  have hσ₀ : 0 < (σ₀ 1 0 : ℝ) * f.firstRoot + σ₀ 1 1 := by simpa [σ₀, coe_T_zpow_mul_S] using h₀
  have hσ₁ : (σ₁ 1 0 : ℝ) * f₁.firstRoot + σ₁ 1 1 < 0 := by simpa [σ₁, coe_T_zpow_mul_S] using h₁
  have hneg : ((γ * σ₀⁻¹ * σ₁⁻¹) 1 0 : ℝ) * f₂.firstRoot + (γ * σ₀⁻¹ * σ₁⁻¹) 1 1 < 0 := by
    nlinarith [mul_neg_of_neg_of_pos hσ₁ hσ₀]
  push_cast
  linarith

private theorem step_two_of_neg_entries {D : ℤ} [Fact (¬ IsSquare D)]
    {f g : gaussReducedForms D} (hf_a : 0 < f.1.a) (hg_a : 0 < g.1.a)
    {γ : SL(2, ℤ)} (hγ : γ • f.1 = g.1)
    (hden : 0 < (γ 1 0 : ℝ) * f.1.firstRoot + γ 1 1)
    (hs : 1 ≤ γ 1 1) (hq : γ 0 1 < 0) :
    (reductionPerm D).SameCycle f g ∨
      ∃ (f₂ : gaussReducedForms D) (γ₂ : SL(2, ℤ)),
        (reductionPerm D).SameCycle f f₂ ∧ 0 < f₂.1.a ∧ γ₂ • f₂.1 = g.1 ∧
          0 < (γ₂ 1 0 : ℝ) * f₂.1.firstRoot + γ₂ 1 1 ∧
          1 ≤ γ₂ 0 0 ∧ γ₂ 0 0 < γ 0 0 ∧ γ₂ 1 0 < 0 := by
  obtain ⟨hDf, hf⟩ := mem_gaussReducedForms.mp f.2
  have hDns : ¬ IsSquare f.1.discrim := by rw [hDf]; exact Fact.out
  obtain ⟨_, hp'_pos, hp'_lt, hrs⟩ := step_one_bounds hf_a hg_a hγ hden hs hq
  set k : ℤ := -((Int.sqrt f.1.discrim + f.1.b) / (2 * f.1.c))
  set σ₀ : SL(2, ℤ) := ModularGroup.T ^ k * ModularGroup.S
  set f₁ := reductionPerm D f
  obtain ⟨_, hf₁⟩ := mem_gaussReducedForms.mp f₁.2
  have hf₁_eq : f₁.1 = σ₀ • f.1 :=
    (coe_reductionPerm_apply f).trans (reductionStep_eq_smul f.1)
  set γ₁ : SL(2, ℤ) := γ * σ₀⁻¹
  have hγ₁ : γ₁ • f₁.1 = g.1 := by rw [hf₁_eq, mul_smul, inv_smul_smul, hγ]
  obtain ⟨hγ₁00, hγ₁01, hγ₁10, hγ₁11⟩ := mul_T_zpow_mul_S_inv_entries γ k
  rcases eq_or_lt_of_le hrs with hrs0 | hrs_lt
  · have hdet₁ := γ₁.fin_two_mul_sub_mul_eq_one
    rw [hγ₁00, hγ₁01, hγ₁10, hγ₁11, hrs0] at hdet₁
    have hp1 : γ 0 0 + k * γ 0 1 = 1 := by nlinarith
    have hgeq := eq_step_two_of_add_mul_eq_zero hf_a hg_a hγ₁ hγ₁00 (hγ₁01.trans hp1)
      (hγ₁10.trans (by nlinarith)) (hγ₁11.trans hrs0)
    exact Or.inl (hgeq ▸ ⟨2, by simp [sq]⟩)
  · set f₂ := reductionPerm D f₁
    have hf₁_a : f₁.1.a < 0 := by
      rw [coe_reductionPerm_apply, reductionStep_a]; nlinarith [(isGaussReduced_iff.mp hf).1]
    have hf₂_a : 0 < f₂.1.a := by
      rw [coe_reductionPerm_apply, reductionStep_a]; nlinarith [(isGaussReduced_iff.mp hf₁).1]
    set k₁ : ℤ := -((Int.sqrt f₁.1.discrim + f₁.1.b) / (2 * f₁.1.c))
    set σ₁ : SL(2, ℤ) := ModularGroup.T ^ k₁ * ModularGroup.S
    have hf₂_eq : f₂.1 = σ₁ • f₁.1 :=
      (coe_reductionPerm_apply f₁).trans (reductionStep_eq_smul f₁.1)
    set γ₂ : SL(2, ℤ) := -(γ₁ * σ₁⁻¹)
    have hγ₂ : γ₂ • f₂.1 = g.1 := by rw [SL2_neg_smul, hf₂_eq, mul_smul, inv_smul_smul, hγ₁]
    have hden₂ : 0 < (γ₂ 1 0 : ℝ) * f₂.1.firstRoot + γ₂ 1 1 := by
      simpa only [γ₂, γ₁, σ₁, σ₀, SpecialLinearGroup.coe_neg, Matrix.neg_apply] using
        denom_firstRoot_step_two_pos hf.discrim_pos.le hDns
          (hf.firstRoot_mem_Ioo_of_a_pos hf_a).1 (hf₁.firstRoot_mem_Ioo_of_a_neg hf₁_a).2
          hf₁_eq hf₂_eq hden
    obtain ⟨h₂00, _, h₂10, _⟩ := mul_T_zpow_mul_S_inv_entries γ₁ k₁
    have hγ₂00 : γ₂ 0 0 = γ 0 0 + k * γ 0 1 :=
      (by simp only [γ₂, σ₁, SpecialLinearGroup.coe_neg, Matrix.neg_apply, h₂00, neg_neg] :
        γ₂ 0 0 = γ₁ 0 1).trans hγ₁01
    have hγ₂10 : γ₂ 1 0 = γ 1 0 + k * γ 1 1 :=
      (by simp only [γ₂, σ₁, SpecialLinearGroup.coe_neg, Matrix.neg_apply, h₂10, neg_neg] :
        γ₂ 1 0 = γ₁ 1 1).trans hγ₁11
    exact Or.inr ⟨f₂, γ₂, ⟨2, by simp [f₂, f₁, sq]⟩, hf₂_a, hγ₂, hden₂,
      hγ₂00 ▸ hp'_pos, hγ₂00 ▸ hp'_lt, hγ₂10 ▸ hrs_lt⟩

private theorem sameCycle_of_smul_eq_of_neg_entries {D : ℤ} [Fact (¬ IsSquare D)] :
    ∀ (n : ℕ) {f g : gaussReducedForms D} (_hf_a : 0 < f.1.a) (_hg_a : 0 < g.1.a)
      (γ : SL(2, ℤ)) (_hn : (γ 0 0).natAbs = n) (_hγ : γ • f.1 = g.1)
      (_hden : 0 < (γ 1 0 : ℝ) * f.1.firstRoot + γ 1 1)
      (_hq : γ 0 1 < 0) (_hr : γ 1 0 < 0),
      (reductionPerm D).SameCycle f g := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro f g hf_a hg_a γ hn hγ hden hq _
    obtain ⟨_, hs, _⟩ := entries_of_smul_eq_of_a_pos hf_a hg_a hγ hden
    rcases step_two_of_neg_entries hf_a hg_a hγ hden hs hq with hsc |
      ⟨f₂, γ₂, hsc, hf₂_a, hγ₂, hden₂, hp₂_pos, hp₂_lt, hr₂⟩
    · exact hsc
    · obtain ⟨_, _, hcases⟩ := entries_of_smul_eq_of_a_pos hf₂_a hg_a hγ₂ hden₂
      rcases hcases with rfl | ⟨_, hr₂_pos⟩ | ⟨hq₂, _⟩
      · exact hsc
      · omega
      · have hlt : (γ₂ 0 0).natAbs < n := by omega
        exact hsc.trans (ih _ hlt hf₂_a hg_a γ₂ rfl hγ₂ hden₂ hq₂ hr₂)

private theorem sameCycle_of_smul_eq_of_a_pos {D : ℤ} [Fact (¬ IsSquare D)]
    {f g : gaussReducedForms D} (hf_a : 0 < f.1.a) (hg_a : 0 < g.1.a)
    (h : ∃ γ : SL(2, ℤ), γ • f.1 = g.1) :
    (reductionPerm D).SameCycle f g := by
  obtain ⟨hDf, hf⟩ := mem_gaussReducedForms.mp f.2
  have hDns : ¬ IsSquare f.1.discrim := by rw [hDf]; exact Fact.out
  obtain ⟨γ, hγ, hden⟩ := exists_smul_eq_and_denom_pos hf.discrim_pos.le hDns h
  obtain ⟨_, _, hcases⟩ := entries_of_smul_eq_of_a_pos hf_a hg_a hγ hden
  rcases hcases with rfl | ⟨hq, hr⟩ | ⟨hq, hr⟩
  · exact Equiv.Perm.SameCycle.refl _ _
  · have hγ_inv : γ⁻¹ • g.1 = f.1 := by rw [← hγ, inv_smul_smul]
    have hden_inv : 0 < (γ⁻¹ 1 0 : ℝ) * g.1.firstRoot + γ⁻¹ 1 1 := by
      have hcoc := denom_firstRoot_mul γ⁻¹ γ hf.discrim_pos.le hDns
      rw [inv_mul_cancel, hγ] at hcoc
      have h1 : (1 : ℝ) = ((γ⁻¹ 1 0 : ℝ) * g.1.firstRoot + γ⁻¹ 1 1) *
          ((γ 1 0 : ℝ) * f.1.firstRoot + γ 1 1) := by simpa using hcoc
      exact pos_of_mul_pos_left (h1 ▸ one_pos) hden.le
    have hq_inv : γ⁻¹ 0 1 < 0 := by
      rw [SpecialLinearGroup.SL2_inv_expl]; exact neg_neg_of_pos hq
    have hr_inv : γ⁻¹ 1 0 < 0 := by
      rw [SpecialLinearGroup.SL2_inv_expl]; exact neg_neg_of_pos hr
    exact (sameCycle_of_smul_eq_of_neg_entries _ hg_a hf_a γ⁻¹ rfl hγ_inv hden_inv
      hq_inv hr_inv).symm
  · exact sameCycle_of_smul_eq_of_neg_entries _ hf_a hg_a γ rfl hγ hden hq hr

/-! ### Gauss's cycle theorem and cycles of reduced forms -/

/-- **Gauss's cycle theorem**: two Gauss reduced forms of nonsquare discriminant `D` lie in the
same cycle of `reductionPerm D` if and only if they are properly equivalent under `SL(2, ℤ)`
(Gauss, *Disquisitiones Arithmeticae*, art. 183–193; Buchmann–Vollmer, Theorem 6.6.4). -/
theorem sameCycle_reductionPerm_iff_exists_smul_eq {D : ℤ} [Fact (¬ IsSquare D)]
    {f g : gaussReducedForms D} :
    (reductionPerm D).SameCycle f g ↔ ∃ γ : SL(2, ℤ), γ • (f : BinaryQuadraticForm ℤ) = g := by
  refine ⟨exists_smul_eq_of_sameCycle, fun ⟨γ, hγ⟩ ↦ ?_⟩
  obtain ⟨f', hff', hf'_a⟩ := exists_sameCycle_a_pos f
  obtain ⟨g', hgg', hg'_a⟩ := exists_sameCycle_a_pos g
  obtain ⟨δ₁, hδ₁⟩ := exists_smul_eq_of_sameCycle hff'.symm
  obtain ⟨δ₂, hδ₂⟩ := exists_smul_eq_of_sameCycle hgg'
  have hfg' : ∃ τ : SL(2, ℤ), τ • f'.1 = g'.1 :=
    ⟨δ₂ * γ * δ₁, by rw [mul_smul, mul_smul, hδ₁, hγ, hδ₂]⟩
  exact hff'.trans ((sameCycle_of_smul_eq_of_a_pos hf'_a hg'_a hfg').trans hgg'.symm)

/-- The **cycles of Gauss reduced forms** of nonsquare discriminant `D`: the quotient of
`gaussReducedForms D` by `(reductionPerm D).SameCycle`. -/
abbrev GaussReducedCycle (D : ℤ) [Fact (¬ IsSquare D)] : Type :=
  Quotient (Equiv.Perm.SameCycle.setoid (reductionPerm D))

/-- There are finitely many cycles of Gauss reduced forms of nonsquare discriminant `D`. -/
noncomputable instance instFintypeGaussReducedCycle (D : ℤ) [Fact (¬ IsSquare D)] :
    Fintype (GaussReducedCycle D) :=
  Fintype.ofFinite _

/-- Map sending a cycle of Gauss reduced forms of discriminant `D` to its proper equivalence class
in `orbitRel.Quotient SL(2, ℤ) (discrimForms D)`. -/
noncomputable def gaussReducedCycleToProperClass (D : ℤ) [Fact (¬ IsSquare D)] :
    GaussReducedCycle D → orbitRel.Quotient SL(2, ℤ) (discrimForms D) :=
  Quotient.lift
    (fun f : gaussReducedForms D ↦
      Quotient.mk'' (⟨f.1, mem_discrimForms.mpr (mem_gaussReducedForms.mp f.2).1⟩ :
        discrimForms D))
    fun f g h ↦ by
      obtain ⟨γ, hγ⟩ := exists_smul_eq_of_sameCycle h
      exact Quotient.sound' ⟨γ⁻¹, Subtype.ext (by simpa using (inv_smul_eq_iff.mpr hγ.symm))⟩

/-- On a cycle representative `f`, `gaussReducedCycleToProperClass` gives the orbit of `f`. -/
@[simp] theorem gaussReducedCycleToProperClass_mk {D : ℤ} [Fact (¬ IsSquare D)]
    (f : gaussReducedForms D) :
    gaussReducedCycleToProperClass D (Quotient.mk _ f) =
      Quotient.mk'' (⟨f.1, mem_discrimForms.mpr (mem_gaussReducedForms.mp f.2).1⟩ :
        discrimForms D) := by
  unfold gaussReducedCycleToProperClass
  rfl

/-- Distinct cycles of Gauss reduced forms give distinct proper equivalence classes. -/
theorem gaussReducedCycleToProperClass_injective (D : ℤ) [Fact (¬ IsSquare D)] :
    Function.Injective (gaussReducedCycleToProperClass D) := by
  intro c₁ c₂
  refine Quotient.inductionOn₂ c₁ c₂ fun f g h ↦ Quotient.sound ?_
  obtain ⟨γ, hγ⟩ := Quotient.exact' h
  exact sameCycle_reductionPerm_iff_exists_smul_eq.mpr
    ⟨γ⁻¹, inv_smul_eq_iff.mpr (by simpa using (congrArg Subtype.val hγ).symm)⟩

/-- Every proper equivalence class of forms of positive nonsquare discriminant `D` contains a cycle
of Gauss reduced forms. -/
theorem gaussReducedCycleToProperClass_surjective {D : ℤ} [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    Function.Surjective (gaussReducedCycleToProperClass D) := by
  refine Quotient.ind' fun f ↦ ?_
  have hfD : f.1.discrim = D := mem_discrimForms.mp f.2
  have hDns : ¬ IsSquare f.1.discrim := by rw [hfD]; exact Fact.out
  obtain ⟨γ, hγ⟩ := exists_smul_mem_gaussReducedForms f.1 (hfD.symm ▸ hpos) hDns
  rw [hfD] at hγ
  refine ⟨Quotient.mk _ ⟨γ • f.1, hγ⟩, ?_⟩
  rw [gaussReducedCycleToProperClass_mk]
  exact Quotient.sound' ⟨γ, rfl⟩

/-- **Classification of indefinite proper classes by Gauss cycles**: for a positive nonsquare
discriminant `D`, the cycles of `reductionPerm D` are in canonical bijection with the `SL(2, ℤ)`
equivalence classes of integral binary quadratic forms of discriminant `D`. -/
noncomputable def gaussReducedCyclesEquivProperClasses (D : ℤ) [Fact (¬ IsSquare D)]
    (hpos : 0 < D) :
    GaussReducedCycle D ≃ orbitRel.Quotient SL(2, ℤ) (discrimForms D) :=
  Equiv.ofBijective (gaussReducedCycleToProperClass D)
    ⟨gaussReducedCycleToProperClass_injective D,
      gaussReducedCycleToProperClass_surjective hpos⟩

/-- Applying `gaussReducedCyclesEquivProperClasses` evaluates `gaussReducedCycleToProperClass`. -/
@[simp] theorem gaussReducedCyclesEquivProperClasses_apply (D : ℤ) [Fact (¬ IsSquare D)]
    (hpos : 0 < D) (c : GaussReducedCycle D) :
    gaussReducedCyclesEquivProperClasses D hpos c = gaussReducedCycleToProperClass D c := by
  unfold gaussReducedCyclesEquivProperClasses
  rfl

/-- For a positive nonsquare discriminant `D`, the number of proper equivalence classes of forms of
discriminant `D` equals the number of cycles of `reductionPerm D`. -/
theorem nat_card_properClasses_discrimForms {D : ℤ} [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    Nat.card (orbitRel.Quotient SL(2, ℤ) (discrimForms D)) =
      Fintype.card (GaussReducedCycle D) := by
  rw [← Nat.card_congr (gaussReducedCyclesEquivProperClasses D hpos), Nat.card_eq_fintype_card]

/-! ### Primitive Gauss reduced forms and primitive cycles -/

/-- The primitive Gauss reduced forms `a x² + b x y + c y²` of discriminant `D`: the Gauss reduced
forms whose coefficients have gcd one. -/
def primitiveGaussReducedForms (D : ℤ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ gaussReducedForms D | Int.gcd f.a (Int.gcd f.b f.c) = 1}

/-- The underlying filter definition of `primitiveGaussReducedForms`. -/
theorem primitiveGaussReducedForms_def (D : ℤ) :
    primitiveGaussReducedForms D =
      {f ∈ gaussReducedForms D | Int.gcd f.a (Int.gcd f.b f.c) = 1} := by
  unfold primitiveGaussReducedForms
  rfl

/-- A form lies in `primitiveGaussReducedForms D` exactly when it has discriminant `D`, is Gauss
reduced, and is primitive. -/
@[simp] theorem mem_primitiveGaussReducedForms {D : ℤ} {f : BinaryQuadraticForm ℤ} :
    f ∈ primitiveGaussReducedForms D ↔
      f.discrim = D ∧ f.IsGaussReduced ∧ f.IsPrimitive := by
  rw [primitiveGaussReducedForms, mem_filter, mem_gaussReducedForms, isPrimitive_iff,
    content_def, and_assoc]

/-- Every primitive Gauss reduced form of discriminant `D` is a Gauss reduced form of discriminant
`D`. -/
theorem primitiveGaussReducedForms_subset_gaussReducedForms (D : ℤ) :
    primitiveGaussReducedForms D ⊆ gaussReducedForms D :=
  filter_subset _ _

/-- The Gauss reduction step preserves content. -/
@[simp] theorem content_reductionStep (f : BinaryQuadraticForm ℤ) :
    f.reductionStep.content = f.content := by
  rw [reductionStep_eq_smul, content_smul]

/-- The Gauss reduction step preserves primitivity. -/
@[simp] theorem isPrimitive_reductionStep_iff (f : BinaryQuadraticForm ℤ) :
    f.reductionStep.IsPrimitive ↔ f.IsPrimitive := by
  rw [reductionStep_eq_smul, isPrimitive_smul_iff]

/-- Every form in `primitiveForms D` for a positive nonsquare discriminant `D` is properly
equivalent to a member of `primitiveGaussReducedForms D`. -/
theorem exists_smul_mem_primitiveGaussReducedForms {f : BinaryQuadraticForm ℤ}
    (hpos : 0 < f.discrim) (hD : ¬ IsSquare f.discrim) (hp : f.IsPrimitive) :
    ∃ γ : SL(2, ℤ), γ • f ∈ primitiveGaussReducedForms f.discrim := by
  obtain ⟨γ, hγ⟩ := exists_smul_isGaussReduced f hpos hD
  exact ⟨γ, mem_primitiveGaussReducedForms.mpr
    ⟨discrim_smul γ f, hγ, (isPrimitive_smul_iff f γ).mpr hp⟩⟩

/-- Restriction of `reductionPerm D` to the finite set `primitiveGaussReducedForms D` of primitive
Gauss reduced forms of nonsquare discriminant `D`. -/
noncomputable def primitiveReductionPerm (D : ℤ) [Fact (¬ IsSquare D)] :
    Equiv.Perm (primitiveGaussReducedForms D) :=
  Equiv.ofBijective
    (fun f ↦ ⟨f.1.reductionStep, by
      obtain ⟨hD, hf, hp⟩ := mem_primitiveGaussReducedForms.mp f.2
      have hDns : ¬ IsSquare f.1.discrim := by rw [hD]; exact Fact.out
      exact mem_primitiveGaussReducedForms.mpr
        ⟨(discrim_reductionStep f.1).trans hD, hf.reductionStep hDns,
          (isPrimitive_reductionStep_iff f.1).mpr hp⟩⟩)
    (Finite.injective_iff_bijective.mp fun f g h ↦ by
      obtain ⟨hDf, hf, _⟩ := mem_primitiveGaussReducedForms.mp f.2
      obtain ⟨hDg, hg, _⟩ := mem_primitiveGaussReducedForms.mp g.2
      have hDns_f : ¬ IsSquare f.1.discrim := by rw [hDf]; exact Fact.out
      have hDns_g : ¬ IsSquare g.1.discrim := by rw [hDg]; exact Fact.out
      exact Subtype.ext <| reductionStep_injOn ⟨hf, hDns_f⟩ ⟨hg, hDns_g⟩ (congrArg Subtype.val h))

/-- Applying `primitiveReductionPerm D` performs `reductionStep` on the underlying form. -/
@[simp] theorem coe_primitiveReductionPerm_apply {D : ℤ} [Fact (¬ IsSquare D)]
    (f : primitiveGaussReducedForms D) :
    (primitiveReductionPerm D f : BinaryQuadraticForm ℤ) =
      (f : BinaryQuadraticForm ℤ).reductionStep := by
  simp only [primitiveReductionPerm, Equiv.ofBijective_apply]

/-- Inclusion of `primitiveGaussReducedForms D` into `gaussReducedForms D` intertwines
`primitiveReductionPerm D` with `reductionPerm D`. -/
theorem pow_primitiveReductionPerm_coe {D : ℤ} [Fact (¬ IsSquare D)]
    (n : ℕ) (f : primitiveGaussReducedForms D) :
    (((primitiveReductionPerm D ^ n) f : primitiveGaussReducedForms D) :
      BinaryQuadraticForm ℤ) =
      ((reductionPerm D ^ n) ⟨f.1, primitiveGaussReducedForms_subset_gaussReducedForms D f.2⟩ :
        BinaryQuadraticForm ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coe_primitiveReductionPerm_apply,
      pow_succ', Equiv.Perm.mul_apply, coe_reductionPerm_apply, ih]

/-- Two primitive Gauss reduced forms lie in the same cycle of `primitiveReductionPerm D` if and
only if they lie in the same cycle of `reductionPerm D`. -/
theorem sameCycle_primitiveReductionPerm_iff_sameCycle_reductionPerm
    {D : ℤ} [Fact (¬ IsSquare D)] {f g : primitiveGaussReducedForms D} :
    (primitiveReductionPerm D).SameCycle f g ↔
      (reductionPerm D).SameCycle
        ⟨f.1, primitiveGaussReducedForms_subset_gaussReducedForms D f.2⟩
        ⟨g.1, primitiveGaussReducedForms_subset_gaussReducedForms D g.2⟩ := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    exact ⟨n, Subtype.ext (pow_primitiveReductionPerm_coe n f).symm⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, Subtype.ext ((pow_primitiveReductionPerm_coe n f).trans (congrArg Subtype.val hn))⟩

/-- **Gauss's cycle theorem for primitive forms**: two primitive Gauss reduced forms of nonsquare
discriminant `D` lie in the same cycle of `primitiveReductionPerm D` if and only if they are
properly equivalent under `SL(2, ℤ)`. -/
theorem sameCycle_primitiveReductionPerm_iff_exists_smul_eq
    {D : ℤ} [Fact (¬ IsSquare D)] {f g : primitiveGaussReducedForms D} :
    (primitiveReductionPerm D).SameCycle f g ↔
      ∃ γ : SL(2, ℤ), γ • (f : BinaryQuadraticForm ℤ) = g := by
  rw [sameCycle_primitiveReductionPerm_iff_sameCycle_reductionPerm,
    sameCycle_reductionPerm_iff_exists_smul_eq]

/-- The **cycles of primitive Gauss reduced forms** of nonsquare discriminant `D`: the quotient of
`primitiveGaussReducedForms D` by `(primitiveReductionPerm D).SameCycle`. -/
abbrev PrimitiveGaussReducedCycle (D : ℤ) [Fact (¬ IsSquare D)] : Type :=
  Quotient (Equiv.Perm.SameCycle.setoid (primitiveReductionPerm D))

/-- There are finitely many cycles of primitive Gauss reduced forms of nonsquare discriminant
`D`. -/
noncomputable instance instFintypePrimitiveGaussReducedCycle (D : ℤ) [Fact (¬ IsSquare D)] :
    Fintype (PrimitiveGaussReducedCycle D) :=
  Fintype.ofFinite _

/-- Map sending a cycle of primitive Gauss reduced forms of discriminant `D` to its proper
equivalence class in `orbitRel.Quotient SL(2, ℤ) (primitiveForms D)`. -/
noncomputable def primitiveGaussReducedCycleToProperClass (D : ℤ) [Fact (¬ IsSquare D)] :
    PrimitiveGaussReducedCycle D → orbitRel.Quotient SL(2, ℤ) (primitiveForms D) :=
  Quotient.lift
    (fun f : primitiveGaussReducedForms D ↦
      Quotient.mk'' (⟨f.1, (mem_primitiveForms D f.1).mpr
        ⟨(mem_primitiveGaussReducedForms.mp f.2).1,
          (mem_primitiveGaussReducedForms.mp f.2).2.2⟩⟩ : primitiveForms D))
    fun f g h ↦ by
      obtain ⟨γ, hγ⟩ := sameCycle_primitiveReductionPerm_iff_exists_smul_eq.mp h
      exact Quotient.sound' ⟨γ⁻¹, Subtype.ext (by simpa using (inv_smul_eq_iff.mpr hγ.symm))⟩

/-- On a primitive cycle representative `f`, `primitiveGaussReducedCycleToProperClass` gives the
orbit of `f`. -/
@[simp] theorem primitiveGaussReducedCycleToProperClass_mk {D : ℤ} [Fact (¬ IsSquare D)]
    (f : primitiveGaussReducedForms D) :
    primitiveGaussReducedCycleToProperClass D (Quotient.mk _ f) =
      Quotient.mk'' (⟨f.1, (mem_primitiveForms D f.1).mpr
        ⟨(mem_primitiveGaussReducedForms.mp f.2).1,
          (mem_primitiveGaussReducedForms.mp f.2).2.2⟩⟩ : primitiveForms D) := by
  unfold primitiveGaussReducedCycleToProperClass
  rfl

/-- Distinct cycles of primitive Gauss reduced forms give distinct proper equivalence classes. -/
theorem primitiveGaussReducedCycleToProperClass_injective (D : ℤ) [Fact (¬ IsSquare D)] :
    Function.Injective (primitiveGaussReducedCycleToProperClass D) := by
  intro c₁ c₂
  refine Quotient.inductionOn₂ c₁ c₂ fun f g h ↦ Quotient.sound ?_
  obtain ⟨γ, hγ⟩ := Quotient.exact' h
  exact sameCycle_primitiveReductionPerm_iff_exists_smul_eq.mpr
    ⟨γ⁻¹, inv_smul_eq_iff.mpr (by simpa using (congrArg Subtype.val hγ).symm)⟩

/-- Every proper equivalence class of primitive forms of positive nonsquare discriminant `D`
contains a cycle of primitive Gauss reduced forms. -/
theorem primitiveGaussReducedCycleToProperClass_surjective {D : ℤ} [Fact (¬ IsSquare D)]
    (hpos : 0 < D) :
    Function.Surjective (primitiveGaussReducedCycleToProperClass D) := by
  refine Quotient.ind' fun f ↦ ?_
  obtain ⟨hfD, hfp⟩ := (mem_primitiveForms D f.1).mp f.2
  have hDns : ¬ IsSquare f.1.discrim := by rw [hfD]; exact Fact.out
  obtain ⟨γ, hγ⟩ := exists_smul_mem_primitiveGaussReducedForms (hfD.symm ▸ hpos) hDns hfp
  rw [hfD] at hγ
  refine ⟨Quotient.mk _ ⟨γ • f.1, hγ⟩, ?_⟩
  rw [primitiveGaussReducedCycleToProperClass_mk]
  exact Quotient.sound' ⟨γ, rfl⟩

/-- **Classification of primitive indefinite proper classes by Gauss cycles**: for a positive
nonsquare discriminant `D`, the cycles of `primitiveReductionPerm D` are in canonical bijection
with the proper equivalence classes of primitive forms of discriminant `D`. -/
noncomputable def primitiveGaussReducedCyclesEquivProperClasses (D : ℤ) [Fact (¬ IsSquare D)]
    (hpos : 0 < D) :
    PrimitiveGaussReducedCycle D ≃ orbitRel.Quotient SL(2, ℤ) (primitiveForms D) :=
  Equiv.ofBijective (primitiveGaussReducedCycleToProperClass D)
    ⟨primitiveGaussReducedCycleToProperClass_injective D,
      primitiveGaussReducedCycleToProperClass_surjective hpos⟩

/-- Applying `primitiveGaussReducedCyclesEquivProperClasses` evaluates
`primitiveGaussReducedCycleToProperClass`. -/
@[simp] theorem primitiveGaussReducedCyclesEquivProperClasses_apply (D : ℤ) [Fact (¬ IsSquare D)]
    (hpos : 0 < D) (c : PrimitiveGaussReducedCycle D) :
    primitiveGaussReducedCyclesEquivProperClasses D hpos c =
      primitiveGaussReducedCycleToProperClass D c := by
  unfold primitiveGaussReducedCyclesEquivProperClasses
  rfl

/-- For a positive nonsquare discriminant `D`, the number of proper equivalence classes of
primitive forms of discriminant `D` equals the number of cycles of `primitiveReductionPerm D`. -/
theorem nat_card_properClasses_primitiveForms {D : ℤ} [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    Nat.card (orbitRel.Quotient SL(2, ℤ) (primitiveForms D)) =
      Fintype.card (PrimitiveGaussReducedCycle D) := by
  rw [← Nat.card_congr (primitiveGaussReducedCyclesEquivProperClasses D hpos),
    Nat.card_eq_fintype_card]

end TauCeti.BinaryQuadraticForm
