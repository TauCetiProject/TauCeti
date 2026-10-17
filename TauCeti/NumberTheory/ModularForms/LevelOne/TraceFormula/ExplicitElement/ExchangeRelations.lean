/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExchangeRelations
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.End.OrderTwoThree

/-!
# Exchange relations for Popa–Zagier's explicit element

Popa–Zagier's explicit element satisfies the exchange relations: its right symmetrization by
`1 + S` is invariant under left multiplication by `U = T S`, and its right symmetrization by
`1 + U + U²` is invariant under left multiplication by `S`. The finite order projection
identities identify these fixed spaces with the ranges in the exchange relations.

The proof uses the integer weights of the explicit element, including the boundary fractions.
Its auxiliary weights are twelve times the coefficients of Popa–Zagier's `F` and `G`; their
factorizations in eq. (16) make the two invariances finite algebraic identities.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4, Theorem 4(a),
  eqs. (15)–(16).
-/

public section

open MonoidAlgebra Representation ModularGroup
open scoped MatrixGroups RightActions

namespace TauCeti.TraceFormulaMatrixModule

open PopaZagier

private def symWeight (a b c d : ℤ) :=
  weight !![a, b; c, d] + weight !![-a, -b; -c, -d]

namespace FirstExchange

-- Twelve times the coefficient of the auxiliary F in Popa–Zagier's eq. (16).
-- The two upper equalities overlap, so their common boundary has weight 4 rather than 3.
private def f0 (a b c d : ℤ) : ℤ :=
  if d ≤ b ∧ b < 0 ∧ 0 < c ∧ 0 ≤ a - d ∧ a - d ≤ c ∧ a - d ≤ -b then
    if a - d = c ∧ a - d = -b then 4
    else if a = d ∨ a - d = c ∨ a - d = -b then 6 else 12
  else 0
private def f (a b c d : ℤ) := f0 a b c d + f0 (-a) (-b) (-c) (-d)
private def t (a b c d : ℤ) := weight₁ a b c d + weight₁ (-a) (-b) (-c) (-d)

-- Resolve the support conditions before the boundary equalities. Keeping these as two
-- simplification stages avoids exploring equality cases outside the support.
private theorem factor_of_d_le_b (a b c d : ℤ) (hb : b < 0) (hc : 0 < c) (hd : d ≤ b) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  simp (disch := omega) only [symWeight, weight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, f, f0, t, weight₁, weight₂, weight₃, weight₄,
    ite_eq_left, ite_eq_right]
  simp (disch := omega) only [chainWeight₃, chainWeight₄, ite_eq_right]
  omega

private theorem factor_of_pos_d (a b c d : ℤ) (hb : b < 0) (hc : 0 < c) (hd : 0 < d) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  simp (disch := omega) only [symWeight, weight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, f, f0, t, weight₁, weight₂, weight₃, weight₄,
    ite_eq_left, ite_eq_right]
  simp (disch := omega) only [chainWeight₃, chainWeight₄, ite_eq_left, ite_eq_right]
  omega

private theorem factor_of_middle_nonpos (a b c d : ℤ) (hb : b < 0) (hc : 0 < c)
    (hbd : b < d) (hd : d ≤ 0) (ha : a ≤ 0) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  simp (disch := omega) only [symWeight, weight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, f, f0, t, weight₁, weight₂, weight₃, weight₄,
    ite_eq_left, ite_eq_right]
  simp (disch := omega) only [chainWeight₃, chainWeight₄, ite_eq_right]
  omega

private theorem factor_of_middle_pos (a b c d : ℤ) (hb : b < 0) (hc : 0 < c)
    (hbd : b < d) (hd : d ≤ 0) (ha : 0 < a) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  -- The remaining boundaries compare a with b + c, and a - d with -b and c.
  rcases lt_trichotomy a (b + c) with hsum | hsum | hsum
  all_goals rcases lt_trichotomy (a - d) (-b) with hu | hu | hu
  all_goals rcases lt_trichotomy (-b) c with hv | hv | hv
  all_goals simp (disch := omega) only [symWeight, weight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, f, f0, t, weight₁, weight₂, weight₃, weight₄,
    ite_eq_left, ite_eq_right]
  all_goals simp (disch := omega) only [chainWeight₃, chainWeight₄, ite_eq_left, ite_eq_right]
  all_goals omega

private theorem factor_of_nonneg_b_nonneg_c (a b c d : ℤ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  simp (disch := omega) only [symWeight, weight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, f, f0, t, weight₁, weight₂, weight₃, weight₄,
    ite_eq_left, ite_eq_right]
  simp (disch := omega) only [chainWeight₃, chainWeight₄, ite_eq_left, ite_eq_right]
  omega

private theorem factor_of_zero_c (a b c d : ℤ) (hc : c = 0) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  simp (disch := omega) only [symWeight, weight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, f, f0, t, weight₁, weight₂, weight₃, weight₄,
    ite_eq_left, ite_eq_right]
  simp (disch := omega) only [chainWeight₃, chainWeight₄, ite_eq_left, ite_eq_right]
  omega

private theorem w_neg (a b c d : ℤ) : symWeight (-a) (-b) (-c) (-d) = symWeight a b c d := by
  simp only [symWeight, neg_neg]
  omega
private theorem f_neg (a b c d : ℤ) : f (-a) (-b) (-c) (-d) = f a b c d := by
  simp only [f, neg_neg]
  omega
private theorem t_neg (a b c d : ℤ) : t (-a) (-b) (-c) (-d) = t a b c d := by
  simp only [t, neg_neg]
  omega

private theorem factor_of_neg_b_pos_c (a b c d : ℤ) (hb : b < 0) (hc : 0 < c) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  by_cases hd : d ≤ b
  · exact factor_of_d_le_b a b c d hb hc hd
  by_cases hd0 : 0 < d
  · exact factor_of_pos_d a b c d hb hc hd0
  by_cases ha : a ≤ 0
  · exact factor_of_middle_nonpos a b c d hb hc (by omega) (by omega) ha
  · exact factor_of_middle_pos a b c d hb hc (by omega) (by omega) (by omega)

private theorem factorization (a b c d : ℤ) :
    symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
      t a b c d - t (-b) a (-d) c := by
  have pos (a b c d : ℤ) (hc : 0 < c) :
      symWeight a b c d = -f a b c d - f (-d) c (b - d) (c - a) - f (c - a) (d - b) (-a) (-b) +
        t a b c d - t (-b) a (-d) c := by
    by_cases hb : b < 0
    · exact factor_of_neg_b_pos_c a b c d hb hc
    · exact factor_of_nonneg_b_nonneg_c a b c d (by omega) hc.le
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hn := pos (-a) (-b) (-c) (-d) (by omega)
    simp only [neg_neg, neg_sub_neg, w_neg, f_neg, t_neg] at hn
    have hf₁ := f_neg (-d) c (b - d) (c - a)
    have hf₂ := f_neg (c - a) (d - b) (-a) (-b)
    have ht := t_neg (-b) a (-d) c
    simp only [neg_sub, neg_neg] at hf₁ hf₂ ht
    rw [hf₁, hf₂, ht] at hn
    exact hn
  · exact factor_of_zero_c a b c d hc
  · exact pos a b c d hc

private theorem weight_relation (a b c d : ℤ) :
    symWeight c d (c - a) (d - b) + symWeight (-d) c (b - d) (c - a) =
      symWeight a b c d + symWeight (-b) a (-d) c := by
  rw [factorization, factorization, factorization, factorization]
  simp only [f, t]
  ring_nf

end FirstExchange

namespace SecondExchange

-- The remaining two summands of the explicit element decompose using the auxiliary G
-- and the boundary correction B of eq. (16). The values 3, 6 and 12 retain its corner weights.
private def p (a b c d : ℤ) := weight₃ a b c d + weight₄ a b c d
private def g (a b c d : ℤ) : ℤ :=
  if a ≤ 0 ∧ b < 0 ∧ 0 < c ∧ 0 ≤ a - d ∧ a - d ≤ c ∧ a - d ≤ -b ∧ a ≤ -b - c then
    if (a - d = c ∧ c = -b) ∨ (a = d ∧ d = -b - c) then 3
    else if a = d ∨ a - d = c ∨ a - d = -b ∨ a = -b - c then 6 else 12
  else 0
private def h (a b c d : ℤ) : ℤ :=
  if d ≤ 0 ∧ b < 0 ∧ -c < d ∧ 0 ≤ a - d ∧ a - d ≤ -b ∧ -b ≤ c ∧ -b - c ≤ a then
    if (a - d = c ∧ c = -b) ∨ (a = d ∧ d = -b - c) then 3
    else if a = d ∨ a - d = -b ∨ c = -b ∨ a = -b - c then 6 else 12
  else 0
private def β (a b c d : ℤ) : ℤ :=
  if a - d = c ∧ c = -b ∧ d ≤ 0 ∧ 0 < a then 1 else 0
private def β' (a b c d : ℤ) : ℤ :=
  if a - d = c ∧ c = -b ∧ a ≤ 0 ∧ 0 < c then 1 else 0
private theorem factor_of_c_lt_neg_b (a b c d : ℤ) (ha : a ≤ 0) (hcb : c < -b) :
    p a b c d = g a b c d + h a b c d + β' a b c d - β a b c d := by
  unfold p g h β β'
  simp (disch := omega) [weight₃, weight₄, chainWeight₄, ite_eq_left, ite_eq_right]
  omega
private theorem factor_of_c_eq_neg_b (a b c d : ℤ) (ha : a ≤ 0) (hcb : c = -b) :
    p a b c d = g a b c d + h a b c d + β' a b c d - β a b c d := by
  unfold p g h β β'
  simp (disch := omega) [weight₃, weight₄, chainWeight₄, ite_eq_left, ite_eq_right]
  omega
private theorem factor_of_neg_b_lt_c (a b c d : ℤ) (ha : a ≤ 0) (hcb : -b < c) :
    p a b c d = g a b c d + h a b c d + β' a b c d - β a b c d := by
  unfold p g h β β'
  simp (disch := omega) [weight₃, weight₄, chainWeight₄, ite_eq_left, ite_eq_right]
  omega
private theorem factor_of_pos_a (a b c d : ℤ) (ha : 0 < a) :
    p a b c d = g a b c d + h a b c d + β' a b c d - β a b c d := by
  unfold p g h β β'
  simp (disch := omega) [weight₃, weight₄, chainWeight₄, ite_eq_left, ite_eq_right]
  omega

private theorem factor (a b c d : ℤ) :
    p a b c d = g a b c d + g d (-c - d) (-b) (a + b) +
      β (-b) (a + b) (-d) (c + d) - β a b c d := by
  have hsg : h a b c d = g d (-c - d) (-b) (a + b) := by
    unfold g h
    grind
  have hb : β' a b c d = β (-b) (a + b) (-d) (c + d) := by
    unfold β β'
    grind
  rw [← hsg, ← hb]
  by_cases ha : a ≤ 0
  · rcases lt_trichotomy c (-b) with hc | hc | hc
    · exact factor_of_c_lt_neg_b a b c d ha hc
    · exact factor_of_c_eq_neg_b a b c d ha hc
    · exact factor_of_neg_b_lt_c a b c d ha hc
  · exact factor_of_pos_a a b c d (by omega)

private def gg (a b c d : ℤ) := g a b c d + g (-a) (-b) (-c) (-d)
private def r0 (a b c d : ℤ) := weight₁ a b c d + β a b c d
private def rr (a b c d : ℤ) := r0 a b c d + r0 (-a) (-b) (-c) (-d)
private theorem sym_factor (a b c d : ℤ) :
    symWeight a b c d = -gg a b c d - gg (-d) (c + d) b (-a - b) +
      rr a b c d - rr (-b) (a + b) (-d) (c + d) := by
  have h1 := factor a b c d
  have h2 := factor (-a) (-b) (-c) (-d)
  simp only [p] at h1 h2
  simp only [symWeight, weight, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, gg, rr, r0]
  rw [weight₂_eq_weight₁, weight₂_eq_weight₁]
  ring_nf at h1 h2 ⊢
  linear_combination -h1 - h2

private theorem weight_relation (a b c d : ℤ) :
    symWeight c d (-a) (-b) + symWeight (-d) (c + d) b (-a - b) +
        symWeight (-c - d) c (a + b) (-a) =
      symWeight a b c d + symWeight (-b) (a + b) (-d) (c + d) +
        symWeight (-a - b) a (-c - d) c := by
  rw [sym_factor, sym_factor, sym_factor, sym_factor, sym_factor, sym_factor]
  simp only [gg, rr]
  ring_nf

end SecondExchange

variable {k : Type*} [DivisionRing k] {n : ℤ}

local notation "ℳ" => TraceFormulaMatrixModule
local notation "ρL" => ofMulAction k SL(2, ℤ) (ℳ n)
local notation "ρR" => ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (ℳ n)

private theorem popaZagierElement_one_add_S_fixed :
    ρL (T * S) ((1 + ρR (.op ↑S)) (popaZagierElement k n)) =
      (1 + ρR (.op ↑S)) (popaZagierElement k n) := by
  ext x
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  simp only [LinearMap.add_apply, Module.End.one_apply, map_add, coeff_add,
    Finsupp.add_apply, coeff_ofMulAction]
  simp only [smul_mk, inv_op_smul_mk, coeff_popaZagierElement_mk,
    FixedDetMatrices.smul_coe, val_traceFormulaMatrixRight]
  rw [Matrix.eta_fin_two A.1]
  suffices hcoeff :
      (symWeight (A.1 1 0) (A.1 1 1) (-A.1 0 0 + A.1 1 0) (-A.1 0 1 + A.1 1 1) : k) / 12 +
          (symWeight (-A.1 1 1) (A.1 1 0) (-A.1 1 1 + A.1 0 1)
            (-A.1 0 0 + A.1 1 0) : k) / 12 =
        (symWeight (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1) : k) / 12 +
          (symWeight (-A.1 0 1) (A.1 0 0) (-A.1 1 1) (A.1 1 0) : k) / 12 by
    simpa [symWeight, Int.cast_add, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T, ModularGroup.coe_S,
      Matrix.adjugate_fin_two] using hcoeff
  have hi := congrArg (fun z : ℤ ↦ (z : k) / 12)
    (FirstExchange.weight_relation (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1))
  simp only [symWeight] at hi
  simp only [Int.cast_add, add_div, sub_eq_add_neg, neg_add_rev, neg_neg] at hi
  simp only [symWeight, Int.cast_add, add_div, neg_add_rev, neg_neg]
  convert hi using 1; congr 2 <;> ring_nf

private theorem popaZagierElement_one_add_U_add_U_sq_fixed :
    ρL S ((1 + ρR (.op ((T : PSL(2, ℤ)) * S)) +
        ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 : Module.End k k[ℳ n]) (popaZagierElement k n)) =
      (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) +
        ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 : Module.End k k[ℳ n]) (popaZagierElement k n) := by
  ext x
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  simp only [LinearMap.add_apply, Module.End.one_apply, map_add, coeff_add,
    Finsupp.add_apply, sq, Module.End.mul_apply, coeff_ofMulAction]
  simp only [← QuotientGroup.mk_mul, smul_mk, inv_op_smul_mk, coeff_popaZagierElement_mk,
    FixedDetMatrices.smul_coe, val_traceFormulaMatrixRight]
  rw [Matrix.eta_fin_two A.1]
  suffices hcoeff :
      (symWeight (A.1 1 0) (A.1 1 1) (-A.1 0 0) (-A.1 0 1) : k) / 12 +
          (symWeight (-A.1 1 1) (A.1 1 0 + A.1 1 1) (A.1 0 1)
            (-A.1 0 0 + -A.1 0 1) : k) / 12 +
          (symWeight (-A.1 1 1 + -A.1 1 0) (A.1 1 0) (A.1 0 1 + A.1 0 0)
            (-A.1 0 0) : k) / 12 =
        (symWeight (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1) : k) / 12 +
          (symWeight (-A.1 0 1) (A.1 0 0 + A.1 0 1) (-A.1 1 1)
            (A.1 1 0 + A.1 1 1) : k) / 12 +
          (symWeight (-A.1 0 1 + -A.1 0 0) (A.1 0 0) (-A.1 1 1 + -A.1 1 0)
            (A.1 1 0) : k) / 12 by
    simpa [symWeight, Int.cast_add, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T, ModularGroup.coe_S,
      Matrix.adjugate_fin_two] using hcoeff
  have hi := congrArg (fun z : ℤ ↦ (z : k) / 12)
    (SecondExchange.weight_relation (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1))
  simp only [symWeight] at hi
  simp only [Int.cast_add, add_div, sub_eq_add_neg, neg_add_rev, neg_neg] at hi
  simp only [symWeight, Int.cast_add, add_div, neg_add_rev, neg_neg]
  convert hi using 1 <;> congr 2 <;> ring_nf

variable (k n) in
/-- **Popa–Zagier's explicit element satisfies the exchange relations**
(Theorem 4(a) of their paper). This holds over every coefficient division ring; when `12 = 0`,
the element defined by the totalized inverse is zero. -/
theorem exchangeRelations_popaZagierElement :
    ExchangeRelations k n (popaZagierElement k n) := by
  by_cases h12 : (12 : k) = 0
  · rw [popaZagierElement_eq_inv_smul_ofWeight, h12, inv_zero, zero_smul]
    constructor <;> simp
  · have h2 : (2 : k) ≠ 0 := by
      intro h2
      apply h12
      calc
        (12 : k) = 6 * 2 := by norm_num
        _ = 0 := by rw [h2, mul_zero]
    have h3 : (3 : k) ≠ 0 := by
      intro h3
      apply h12
      calc
        (12 : k) = 4 * 3 := by norm_num
        _ = 0 := by rw [h3, mul_zero]
    let : Invertible (2 : k) := invertibleOfNonzero h2
    let : Invertible (3 : k) := invertibleOfNonzero h3
    constructor
    · rw [End.range_one_add_add_sq_eq_ker_one_sub (by simp)]
      exact LinearMap.mem_ker.mpr (by
        simpa [sub_eq_zero] using
          (popaZagierElement_one_add_S_fixed (k := k) (n := n)).symm)
    · rw [End.range_one_add_eq_ker_one_sub (by simp)]
      exact LinearMap.mem_ker.mpr (by
        simpa [sub_eq_zero] using
          (popaZagierElement_one_add_U_add_U_sq_fixed (k := k) (n := n)).symm)

end TauCeti.TraceFormulaMatrixModule
