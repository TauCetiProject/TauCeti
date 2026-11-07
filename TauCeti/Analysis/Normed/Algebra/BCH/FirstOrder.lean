/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Lemmas
public import TauCeti.Analysis.Normed.Algebra.Basic
public import TauCeti.Analysis.Normed.Algebra.BCH.Local
public import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# The first-order term of the local Baker--Campbell--Hausdorff germ

The local Baker--Campbell--Hausdorff germ of `TauCeti/Analysis/Normed/Algebra/BCH/Local.lean` is
represented by `fun p ↦ log (exp p.1 * exp p.2)`.  This file proves the law that fixes
its expansion at the origin:

`log (exp x * exp y) = x + y + 2⁻¹ • (x * y - y * x) + O(‖(x, y)‖ ^ 3)`.

The second-order term `x * y - y * x` is the commutator `⁅x, y⁆` of the Lie ring underlying the
associative ring, so this is the familiar `x + y + ½⁅x, y⁆` of the Baker--Campbell--Hausdorff
series.  It is written as a difference of products rather than as a bracket because
`LieRing.ofAssociativeRing` is not an instance.

The proof is the classical formal computation, carried out with the two quadratic Taylor
estimates that the ingredients satisfy, `NormedSpace.isBigO_exp_sub_quadratic` and
`NormedSpace.isBigO_log_one_add_sub_quadratic`.  Writing `u = exp x * exp y - 1` and `q = x + y`:

* multiplying the two quadratic truncations gives `u = q + 2⁻¹ • q ^ 2 + 2⁻¹ • (x * y - y * x)`
  to third order, the three leftover monomials `x * y ^ 2`, `x ^ 2 * y` and `x ^ 2 * y ^ 2` being
  of order at least three;
* hence `u - q` is of order two, so `u ^ 2` and `q ^ 2` agree to third order;
* and `log (1 + u) = u - 2⁻¹ • u ^ 2` to third order, with `‖u‖` of order one, so the two
  quadratic terms cancel and only `q + 2⁻¹ • (x * y - y * x)` survives.

Only the germ at the origin is involved, so the statement transfers to any representative of
`NormedSpace.localBCH`.

## Main results

* `NormedSpace.isBigO_exp_mul_exp_sub_one_sub_quadratic`: the quadratic Taylor estimate for
  `exp x * exp y - 1`.
* `NormedSpace.isBigO_log_exp_mul_exp_sub_firstOrder`: **the first-order law**, that
  the representative of the local Baker--Campbell--Hausdorff germ is
  `x + y + 2⁻¹ • (x * y - y * x)` up to `O(‖(x, y)‖ ^ 3)`.
* `NormedSpace.isBigO_sub_firstOrder_of_coe_eq_localBCH`: the same for an arbitrary representative
  of `NormedSpace.localBCH`.
-/

public section

open Asymptotics Filter Topology

noncomputable section

namespace NormedSpace

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-! ### The quadratic Taylor estimate for a product of two exponentials -/

/-- The exponential is continuous at `0`, with value `1`. -/
private lemma tendsto_exp_nhds_zero : Tendsto (exp : A → A) (𝓝 (0 : A)) (𝓝 (1 : A)) := by
  simpa only [exp_zero] using (exp_analytic (𝕂 := ℝ) (0 : A)).continuousAt.tendsto

omit [CompleteSpace A] in
/-- The product of the two quadratic truncations of the exponential, minus the quadratic
truncation of the product, leaves only monomials of degree at least three. -/
private lemma exp_mul_exp_sub_quadratic_eq (x y : A) :
    exp x * exp y - 1 - (x + y) - ((2⁻¹ : ℝ) • x ^ 2 + x * y + (2⁻¹ : ℝ) • y ^ 2) =
      (exp x - (1 + x + (2⁻¹ : ℝ) • x ^ 2)) * exp y +
          (1 + x + (2⁻¹ : ℝ) • x ^ 2) * (exp y - (1 + y + (2⁻¹ : ℝ) • y ^ 2)) +
        ((2⁻¹ : ℝ) • (x * y ^ 2) + (2⁻¹ : ℝ) • (x ^ 2 * y) +
          (2⁻¹ : ℝ) • ((2⁻¹ : ℝ) • (x ^ 2 * y ^ 2))) := by
  have hcancel : ∀ a b c d : A, (a - c) * b + c * (b - d) = a * b - c * d := by
    intro a b c d
    simp only [sub_mul, mul_sub]
    abel
  have hquad : (1 + x + (2⁻¹ : ℝ) • x ^ 2) * (1 + y + (2⁻¹ : ℝ) • y ^ 2) - 1 - (x + y) -
          ((2⁻¹ : ℝ) • x ^ 2 + x * y + (2⁻¹ : ℝ) • y ^ 2) =
        (2⁻¹ : ℝ) • (x * y ^ 2) + (2⁻¹ : ℝ) • (x ^ 2 * y) +
          (2⁻¹ : ℝ) • ((2⁻¹ : ℝ) • (x ^ 2 * y ^ 2)) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  rw [hcancel, ← hquad]
  abel

omit [CompleteSpace A] in
/-- The three cubic monomials left over by `exp_mul_exp_sub_quadratic_eq` are of order three. -/
private lemma isBigO_cubic_remainder :
    (fun p : A × A ↦ (2⁻¹ : ℝ) • (p.1 * p.2 ^ 2) + (2⁻¹ : ℝ) • (p.1 ^ 2 * p.2) +
        (2⁻¹ : ℝ) • ((2⁻¹ : ℝ) • (p.1 ^ 2 * p.2 ^ 2)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  have hfst : (fun p : A × A ↦ p.1) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_fst_prod'.norm_right
  have hsnd : (fun p : A × A ↦ p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_snd_prod'.norm_right
  have hfst2 : (fun p : A × A ↦ p.1 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 := hfst.pow 2
  have hsnd2 : (fun p : A × A ↦ p.2 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 := hsnd.pow 2
  have hcube₁ : (fun p : A × A ↦ p.1 * p.2 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    (hfst.mul hsnd2).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
  have hcube₂ : (fun p : A × A ↦ p.1 ^ 2 * p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    (hfst2.mul hsnd).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
  have hcube₃ : (fun p : A × A ↦ p.1 ^ 2 * p.2 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    ((hfst2.mul hsnd2).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)).trans
      (isBigO_norm_pow_norm_pow_nhds_zero_of_le (E := A × A) (show 3 ≤ 4 by norm_num))
  have h := ((hcube₁.const_smul_left (2⁻¹ : ℝ)).add (hcube₂.const_smul_left (2⁻¹ : ℝ))).add
    ((hcube₃.const_smul_left (2⁻¹ : ℝ)).const_smul_left (2⁻¹ : ℝ))
  simpa using h

/-- The two terms of `exp_mul_exp_sub_quadratic_eq` that come from the Taylor remainders of
`exp x` and `exp y` are of order three. -/
private lemma isBigO_exp_remainder_mul :
    (fun p : A × A ↦ (exp p.1 - (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2)) * exp p.2 +
        (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2) * (exp p.2 - (1 + p.2 + (2⁻¹ : ℝ) • p.2 ^ 2)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  have hfst : (fun p : A × A ↦ p.1) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_fst_prod'.norm_right
  have hsnd : (fun p : A × A ↦ p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_snd_prod'.norm_right
  have htfst : Tendsto (fun p : A × A ↦ p.1) (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) :=
    continuous_fst.tendsto' _ _ rfl
  have htsnd : Tendsto (fun p : A × A ↦ p.2) (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) :=
    continuous_snd.tendsto' _ _ rfl
  have hexpFst : (fun p : A × A ↦ exp p.1 - (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    ((isBigO_exp_sub_quadratic ℝ (A := A)).comp_tendsto htfst).trans (hfst.norm_left.pow 3)
  have hexpSnd : (fun p : A × A ↦ exp p.2 - (1 + p.2 + (2⁻¹ : ℝ) • p.2 ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    ((isBigO_exp_sub_quadratic ℝ (A := A)).comp_tendsto htsnd).trans (hsnd.norm_left.pow 3)
  have hbddExp : (fun p : A × A ↦ exp p.2) =O[𝓝 ((0, 0) : A × A)] fun _ ↦ (1 : ℝ) := by
    exact ((tendsto_exp_nhds_zero A).comp htsnd).isBigO_one ℝ
  have hbddTrunc : (fun p : A × A ↦ 1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2)
      =O[𝓝 ((0, 0) : A × A)] fun _ ↦ (1 : ℝ) := by
    refine Tendsto.isBigO_one ℝ (c := (1 : A)) ?_
    have hc : Continuous fun p : A × A ↦ 1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2 := by fun_prop
    simpa using hc.tendsto' ((0, 0) : A × A) 1 (by simp)
  have hleft : (fun p : A × A ↦ (exp p.1 - (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2)) * exp p.2)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    simpa using hexpFst.mul hbddExp
  have hright : (fun p : A × A ↦ (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2) *
        (exp p.2 - (1 + p.2 + (2⁻¹ : ℝ) • p.2 ^ 2)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    simpa using hbddTrunc.mul hexpSnd
  exact hleft.add hright

/-- **The quadratic Taylor estimate for `exp x * exp y - 1`.**  Multiplying the two quadratic
truncations of the exponential leaves monomials of degree at least three. -/
theorem isBigO_exp_mul_exp_sub_one_sub_quadratic :
    (fun p : A × A ↦ exp p.1 * exp p.2 - 1 - (p.1 + p.2) -
        ((2⁻¹ : ℝ) • p.1 ^ 2 + p.1 * p.2 + (2⁻¹ : ℝ) • p.2 ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
  ((isBigO_exp_remainder_mul A).add (isBigO_cubic_remainder A)).congr'
    (.of_forall fun p ↦ (exp_mul_exp_sub_quadratic_eq A p.1 p.2).symm) EventuallyEq.rfl

/-! ### The first-order law -/

omit [CompleteSpace A] in
/-- The quadratic truncation of `exp x * exp y` is of order two. -/
private lemma isBigO_quadratic_truncation :
    (fun p : A × A ↦ (2⁻¹ : ℝ) • p.1 ^ 2 + p.1 * p.2 + (2⁻¹ : ℝ) • p.2 ^ 2)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 := by
  have hfst : (fun p : A × A ↦ p.1) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_fst_prod'.norm_right
  have hsnd : (fun p : A × A ↦ p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_snd_prod'.norm_right
  have hmix : (fun p : A × A ↦ p.1 * p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 :=
    (hfst.mul hsnd).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
  have h := (((hfst.pow 2).const_smul_left (2⁻¹ : ℝ)).add hmix).add
    ((hsnd.pow 2).const_smul_left (2⁻¹ : ℝ))
  simpa using h

/-- The product of the exponentials differs from `x + y` by a term of order two. -/
private lemma isBigO_exp_mul_exp_sub_one_sub_add :
    (fun p : A × A ↦ exp p.1 * exp p.2 - 1 - (p.1 + p.2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 := by
  refine (((isBigO_exp_mul_exp_sub_one_sub_quadratic A).trans
    (isBigO_norm_pow_norm_pow_nhds_zero_of_le (E := A × A)
      (show 2 ≤ 3 by norm_num))).add (isBigO_quadratic_truncation A)).congr'
    (.of_forall fun p ↦ ?_) EventuallyEq.rfl
  abel_nf

/-- The product of the exponentials is of order one. -/
private lemma isBigO_exp_mul_exp_sub_one :
    (fun p : A × A ↦ exp p.1 * exp p.2 - 1) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ := by
  have hsum : (fun p : A × A ↦ p.1 + p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_fst_prod'.norm_right.add isBigO_snd_prod'.norm_right
  have hnorm2 : (fun p : A × A ↦ ‖p‖ ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    (isBigO_norm_pow_norm_pow_nhds_zero_of_le (E := A × A) (show 1 ≤ 2 by norm_num)).congr'
      EventuallyEq.rfl (.of_forall fun _ ↦ pow_one _)
  refine (((isBigO_exp_mul_exp_sub_one_sub_add A).trans hnorm2).add hsum).congr'
    (.of_forall fun p ↦ ?_) EventuallyEq.rfl
  abel_nf

/-- The squares of `exp x * exp y - 1` and `x + y` agree to third order. -/
private lemma isBigO_exp_mul_exp_sub_one_sq_sub_add_sq :
    (fun p : A × A ↦ (exp p.1 * exp p.2 - 1) ^ 2 - (p.1 + p.2) ^ 2)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  have hsum : (fun p : A × A ↦ p.1 + p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    isBigO_fst_prod'.norm_right.add isBigO_snd_prod'.norm_right
  have h₁ : (fun p : A × A ↦ (exp p.1 * exp p.2 - 1 - (p.1 + p.2)) * (exp p.1 * exp p.2 - 1))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    ((isBigO_exp_mul_exp_sub_one_sub_add A).mul (isBigO_exp_mul_exp_sub_one A)).congr'
      EventuallyEq.rfl (.of_forall fun p ↦ by ring)
  have h₂ : (fun p : A × A ↦ (p.1 + p.2) * (exp p.1 * exp p.2 - 1 - (p.1 + p.2)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    (hsum.mul (isBigO_exp_mul_exp_sub_one_sub_add A)).congr' EventuallyEq.rfl
      (.of_forall fun p ↦ by ring)
  refine (h₁.add h₂).congr' (.of_forall fun p ↦ ?_) EventuallyEq.rfl
  simp only [pow_two, sub_mul, mul_sub]
  abel

/-- The logarithm contributes its own quadratic estimate. -/
private lemma isBigO_log_exp_mul_exp_sub_quadratic :
    (fun p : A × A ↦ log (exp p.1 * exp p.2) -
        ((exp p.1 * exp p.2 - 1) - (2⁻¹ : ℝ) • (exp p.1 * exp p.2 - 1) ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  have htendsto : Tendsto (fun p : A × A ↦ exp p.1 * exp p.2 - 1)
      (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) := by
    have h := (((tendsto_exp_nhds_zero A).comp (continuous_fst.tendsto' ((0, 0) : A × A) 0 rfl)).mul
      ((tendsto_exp_nhds_zero A).comp
        (continuous_snd.tendsto' ((0, 0) : A × A) 0 rfl))).sub_const 1
    simpa using h
  have h : (fun p : A × A ↦ log (exp p.1 * exp p.2) -
        ((exp p.1 * exp p.2 - 1) - (2⁻¹ : ℝ) • (exp p.1 * exp p.2 - 1) ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p : A × A ↦ ‖exp p.1 * exp p.2 - 1‖ ^ 3 :=
    by simpa only [Function.comp_def, add_sub_cancel] using
      (isBigO_log_one_add_sub_quadratic ℝ A).comp_tendsto htendsto
  exact h.trans ((isBigO_exp_mul_exp_sub_one A).norm_left.pow 3)

/-- **The first-order law of the local Baker--Campbell--Hausdorff germ.**  Its defining
representative is `x + y + 2⁻¹ • (x * y - y * x)` up to third order at the origin; the
second-order term is half the commutator. -/
theorem isBigO_log_exp_mul_exp_sub_firstOrder :
    (fun p : A × A ↦ log (exp p.1 * exp p.2) -
        (p.1 + p.2 + (2⁻¹ : ℝ) • (p.1 * p.2 - p.2 * p.1)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  -- The quadratic terms cancel against half the square of `x + y`.
  have hcommutator : ∀ x y : A,
      (2⁻¹ : ℝ) • x ^ 2 + x * y + (2⁻¹ : ℝ) • y ^ 2 - (2⁻¹ : ℝ) • (x * y - y * x) =
        (2⁻¹ : ℝ) • (x + y) ^ 2 := by
    intro x y
    simp only [pow_two, add_mul, mul_add, smul_add, smul_sub]
    module
  have hcancel : (fun p : A × A ↦ (2⁻¹ : ℝ) • p.1 ^ 2 + p.1 * p.2 + (2⁻¹ : ℝ) • p.2 ^ 2 -
        (2⁻¹ : ℝ) • (p.1 * p.2 - p.2 * p.1) - (2⁻¹ : ℝ) • (exp p.1 * exp p.2 - 1) ^ 2)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    refine (((isBigO_exp_mul_exp_sub_one_sq_sub_add_sq A).const_smul_left
      (2⁻¹ : ℝ)).neg_left).congr' (.of_forall fun p ↦ ?_) EventuallyEq.rfl
    simp only [Pi.smul_apply]
    rw [hcommutator p.1 p.2]
    module
  refine (((isBigO_log_exp_mul_exp_sub_quadratic A).add
    (isBigO_exp_mul_exp_sub_one_sub_quadratic A)).add hcancel).congr'
    (.of_forall fun p ↦ ?_) EventuallyEq.rfl
  abel_nf

/-- The first-order law holds for every representative of the local Baker--Campbell--Hausdorff
germ, the estimate at the origin depending only on the germ. -/
theorem isBigO_sub_firstOrder_of_coe_eq_localBCH (f : A × A → A)
    (hf : (↑f : Germ (𝓝 ((0, 0) : A × A)) A) = localBCH A) :
    (fun p : A × A ↦ f p - (p.1 + p.2 + (2⁻¹ : ℝ) • (p.1 * p.2 - p.2 * p.1)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  rw [localBCH_def, Germ.coe_eq] at hf
  exact (isBigO_log_exp_mul_exp_sub_firstOrder A).congr'
    (hf.symm.sub EventuallyEq.rfl) EventuallyEq.rfl

end NormedSpace
