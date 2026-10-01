/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.BCH.Local
public import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# The first-order term of the local Baker--Campbell--Hausdorff germ

The local Baker--Campbell--Hausdorff germ of `TauCeti/Analysis/Normed/Algebra/BCH/Local.lean` is
represented by `fun p ↦ logOneAdd (exp p.1 * exp p.2 - 1)`.  Its endpoint laws, its exponential
law and its uniqueness are proved there; what is still missing, and is proved here, is the law
that fixes its expansion at the origin:

`logOneAdd (exp x * exp y - 1) = x + y + 2⁻¹ • (x * y - y * x) + O(‖(x, y)‖ ^ 3)`.

The second-order term `x * y - y * x` is the commutator `⁅x, y⁆` of the Lie ring underlying the
associative ring, so this is the familiar `x + y + ½⁅x, y⁆` of the Baker--Campbell--Hausdorff
series.  It is written as a difference of products rather than as a bracket because
`LieRing.ofAssociativeRing` is not an instance.

The proof is the classical formal computation, carried out with the two quadratic Taylor
estimates that the ingredients satisfy, `NormedSpace.isBigO_exp_sub_quadratic` and
`NormedSpace.isBigO_logOneAdd_sub_quadratic`.  Writing `u = exp x * exp y - 1` and `q = x + y`:

* multiplying the two quadratic truncations gives `u = q + 2⁻¹ • q ^ 2 + 2⁻¹ • (x * y - y * x)`
  to third order, the three leftover monomials `x * y ^ 2`, `x ^ 2 * y` and `x ^ 2 * y ^ 2` being
  of order at least three;
* hence `u - q` is of order two, so `u ^ 2` and `q ^ 2` agree to third order;
* and `logOneAdd u = u - 2⁻¹ • u ^ 2` to third order, with `‖u‖` of order one, so the two
  quadratic terms cancel and only `q + 2⁻¹ • (x * y - y * x)` survives.

Only the germ at the origin is involved, so the statement transfers to any representative of
`NormedSpace.localBCH`.

## Main results

* `NormedSpace.isBigO_exp_mul_exp_sub_one_sub_quadratic`: the quadratic Taylor estimate for
  `exp x * exp y - 1`.
* `NormedSpace.isBigO_logOneAdd_exp_mul_exp_sub_one_sub_firstOrder`: **the first-order law**, that
  the representative of the local Baker--Campbell--Hausdorff germ is
  `x + y + 2⁻¹ • (x * y - y * x)` up to `O(‖(x, y)‖ ^ 3)`.
* `NormedSpace.isBigO_sub_firstOrder_of_coe_eq_localBCH`: the same for an arbitrary representative
  of `NormedSpace.localBCH`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker--Campbell--Hausdorff", whose first-order law
  `bch x y - (x + y) - 2⁻¹ • ⁅x, y⁆ = O(‖(x, y)‖ ^ 3)` this file supplies.
-/

public section

open Asymptotics Filter Topology

noncomputable section

namespace NormedSpace

variable (A : Type*) [NormedRing A]

/-! ### Elementary estimates at the origin of `A × A` -/

private theorem eventually_norm_le_one : ∀ᶠ p in 𝓝 ((0, 0) : A × A), ‖p‖ ≤ 1 := by
  filter_upwards [Metric.closedBall_mem_nhds ((0, 0) : A × A) one_pos] with p hp
  simpa [Metric.mem_closedBall, dist_eq_norm, Prod.mk_zero_zero] using hp

private theorem isBigO_norm_pow_le {m n : ℕ} (h : n ≤ m) :
    (fun p : A × A ↦ ‖p‖ ^ m) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ n := by
  refine isBigO_iff.2 ⟨1, ?_⟩
  filter_upwards [eventually_norm_le_one A] with p hp
  simp only [one_mul, norm_pow, norm_norm]
  exact pow_le_pow_of_le_one (norm_nonneg p) hp h

private theorem isBigO_norm_pow_le_one {m : ℕ} (h : 1 ≤ m) :
    (fun p : A × A ↦ ‖p‖ ^ m) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
  (isBigO_norm_pow_le A h).congr' EventuallyEq.rfl (.of_forall fun _ ↦ pow_one _)

private theorem isBigO_fst : (fun p : A × A ↦ p.1) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
  isBigO_of_le _ fun p ↦ by simpa using norm_fst_le p

private theorem isBigO_snd : (fun p : A × A ↦ p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
  isBigO_of_le _ fun p ↦ by simpa using norm_snd_le p

private theorem tendsto_fst_zero :
    Tendsto (fun p : A × A ↦ p.1) (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) :=
  continuous_fst.tendsto' _ _ rfl

private theorem tendsto_snd_zero :
    Tendsto (fun p : A × A ↦ p.2) (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) :=
  continuous_snd.tendsto' _ _ rfl

variable [NormedAlgebra ℝ A] [CompleteSpace A]

private theorem tendsto_exp_zero : Tendsto (exp : A → A) (𝓝 (0 : A)) (𝓝 (1 : A)) := by
  simpa only [exp_zero] using (exp_analytic (𝕂 := ℝ) (0 : A)).continuousAt.tendsto

/-! ### The quadratic Taylor estimate for a product of two exponentials -/

/-- **The quadratic Taylor estimate for `exp x * exp y - 1`.**  Multiplying the two quadratic
truncations of the exponential leaves monomials of degree at least three. -/
theorem isBigO_exp_mul_exp_sub_one_sub_quadratic :
    (fun p : A × A ↦ exp p.1 * exp p.2 - 1 - (p.1 + p.2) -
        ((2⁻¹ : ℝ) • p.1 ^ 2 + p.1 * p.2 + (2⁻¹ : ℝ) • p.2 ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  -- Splitting off the two quadratic truncations, and then expanding their product.
  have hcancel : ∀ a b c d : A, (a - c) * b + c * (b - d) = a * b - c * d := by
    intro a b c d
    simp only [sub_mul, mul_sub]
    abel
  have hquad : ∀ x y : A,
      (1 + x + (2⁻¹ : ℝ) • x ^ 2) * (1 + y + (2⁻¹ : ℝ) • y ^ 2) - 1 - (x + y) -
          ((2⁻¹ : ℝ) • x ^ 2 + x * y + (2⁻¹ : ℝ) • y ^ 2) =
        (2⁻¹ : ℝ) • (x * y ^ 2) + (2⁻¹ : ℝ) • (x ^ 2 * y) +
          (2⁻¹ : ℝ) • ((2⁻¹ : ℝ) • (x ^ 2 * y ^ 2)) := by
    intro x y
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  have key : ∀ p : A × A,
      exp p.1 * exp p.2 - 1 - (p.1 + p.2) -
          ((2⁻¹ : ℝ) • p.1 ^ 2 + p.1 * p.2 + (2⁻¹ : ℝ) • p.2 ^ 2) =
        (exp p.1 - (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2)) * exp p.2 +
            (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2) *
              (exp p.2 - (1 + p.2 + (2⁻¹ : ℝ) • p.2 ^ 2)) +
          ((2⁻¹ : ℝ) • (p.1 * p.2 ^ 2) + (2⁻¹ : ℝ) • (p.1 ^ 2 * p.2) +
            (2⁻¹ : ℝ) • ((2⁻¹ : ℝ) • (p.1 ^ 2 * p.2 ^ 2))) := by
    intro p
    rw [hcancel, ← hquad p.1 p.2]
    abel
  have hexpFst : (fun p : A × A ↦ exp p.1 - (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    have h : (fun p : A × A ↦ exp p.1 - (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2))
        =O[𝓝 ((0, 0) : A × A)] fun p : A × A ↦ ‖p.1‖ ^ 3 :=
      (isBigO_exp_sub_quadratic ℝ (A := A)).comp_tendsto (tendsto_fst_zero A)
    exact h.trans ((isBigO_fst A).norm_left.pow 3)
  have hexpSnd : (fun p : A × A ↦ exp p.2 - (1 + p.2 + (2⁻¹ : ℝ) • p.2 ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    have h : (fun p : A × A ↦ exp p.2 - (1 + p.2 + (2⁻¹ : ℝ) • p.2 ^ 2))
        =O[𝓝 ((0, 0) : A × A)] fun p : A × A ↦ ‖p.2‖ ^ 3 :=
      (isBigO_exp_sub_quadratic ℝ (A := A)).comp_tendsto (tendsto_snd_zero A)
    exact h.trans ((isBigO_snd A).norm_left.pow 3)
  have hbddExp : (fun p : A × A ↦ exp p.2) =O[𝓝 ((0, 0) : A × A)] fun _ ↦ (1 : ℝ) :=
    ((tendsto_exp_zero A).comp (tendsto_snd_zero A)).isBigO_one ℝ
  have hbddTrunc : (fun p : A × A ↦ 1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2)
      =O[𝓝 ((0, 0) : A × A)] fun _ ↦ (1 : ℝ) := by
    refine Tendsto.isBigO_one ℝ (c := (1 : A)) ?_
    have hc : Continuous fun p : A × A ↦ 1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2 := by fun_prop
    simpa using hc.tendsto' ((0, 0) : A × A) 1 (by simp)
  have hfst2 : (fun p : A × A ↦ p.1 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 :=
    (isBigO_fst A).pow 2
  have hsnd2 : (fun p : A × A ↦ p.2 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 :=
    (isBigO_snd A).pow 2
  have hcube₁ : (fun p : A × A ↦ p.1 * p.2 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    ((isBigO_fst A).mul hsnd2).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
  have hcube₂ : (fun p : A × A ↦ p.1 ^ 2 * p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    (hfst2.mul (isBigO_snd A)).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
  have hcube₃ : (fun p : A × A ↦ p.1 ^ 2 * p.2 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
    ((hfst2.mul hsnd2).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)).trans
      (isBigO_norm_pow_le A (show 3 ≤ 4 by norm_num))
  have hleft : (fun p : A × A ↦ (exp p.1 - (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2)) * exp p.2)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    simpa using hexpFst.mul hbddExp
  have hright : (fun p : A × A ↦ (1 + p.1 + (2⁻¹ : ℝ) • p.1 ^ 2) *
        (exp p.2 - (1 + p.2 + (2⁻¹ : ℝ) • p.2 ^ 2)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    simpa using hbddTrunc.mul hexpSnd
  have hrest : (fun p : A × A ↦ (2⁻¹ : ℝ) • (p.1 * p.2 ^ 2) + (2⁻¹ : ℝ) • (p.1 ^ 2 * p.2) +
        (2⁻¹ : ℝ) • ((2⁻¹ : ℝ) • (p.1 ^ 2 * p.2 ^ 2)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    have h := ((hcube₁.const_smul_left (2⁻¹ : ℝ)).add (hcube₂.const_smul_left (2⁻¹ : ℝ))).add
      ((hcube₃.const_smul_left (2⁻¹ : ℝ)).const_smul_left (2⁻¹ : ℝ))
    simpa using h
  exact ((hleft.add hright).add hrest).congr' (.of_forall fun p ↦ (key p).symm) EventuallyEq.rfl

/-! ### The first-order law -/

/-- **The first-order law of the local Baker--Campbell--Hausdorff germ.**  Its defining
representative is `x + y + 2⁻¹ • (x * y - y * x)` up to third order at the origin; the
second-order term is half the commutator. -/
theorem isBigO_logOneAdd_exp_mul_exp_sub_one_sub_firstOrder :
    (fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1) -
        (p.1 + p.2 + (2⁻¹ : ℝ) • (p.1 * p.2 - p.2 * p.1)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  have hsum : (fun p : A × A ↦ p.1 + p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ :=
    (isBigO_fst A).add (isBigO_snd A)
  have hfst2 : (fun p : A × A ↦ p.1 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 :=
    (isBigO_fst A).pow 2
  have hsnd2 : (fun p : A × A ↦ p.2 ^ 2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 :=
    (isBigO_snd A).pow 2
  have hmix : (fun p : A × A ↦ p.1 * p.2) =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 :=
    ((isBigO_fst A).mul (isBigO_snd A)).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
  have hquadTerm : (fun p : A × A ↦ (2⁻¹ : ℝ) • p.1 ^ 2 + p.1 * p.2 + (2⁻¹ : ℝ) • p.2 ^ 2)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 := by
    have h := ((hfst2.const_smul_left (2⁻¹ : ℝ)).add hmix).add (hsnd2.const_smul_left (2⁻¹ : ℝ))
    simpa using h
  -- The product of the exponentials differs from `x + y` by a term of order two.
  have hord2 : (fun p : A × A ↦ exp p.1 * exp p.2 - 1 - (p.1 + p.2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 2 := by
    refine (((isBigO_exp_mul_exp_sub_one_sub_quadratic A).trans
      (isBigO_norm_pow_le A (show 2 ≤ 3 by norm_num))).add hquadTerm).congr'
      (.of_forall fun p ↦ ?_) EventuallyEq.rfl
    abel_nf
  have hord1 : (fun p : A × A ↦ exp p.1 * exp p.2 - 1)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ := by
    refine ((hord2.trans (isBigO_norm_pow_le_one A (show 1 ≤ 2 by norm_num))).add hsum).congr'
      (.of_forall fun p ↦ ?_) EventuallyEq.rfl
    abel_nf
  -- Hence the squares of the two agree to third order.
  have hsquares : (fun p : A × A ↦ (exp p.1 * exp p.2 - 1) ^ 2 - (p.1 + p.2) ^ 2)
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    have h₁ : (fun p : A × A ↦ (exp p.1 * exp p.2 - 1 - (p.1 + p.2)) * (exp p.1 * exp p.2 - 1))
        =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
      (hord2.mul hord1).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
    have h₂ : (fun p : A × A ↦ (p.1 + p.2) * (exp p.1 * exp p.2 - 1 - (p.1 + p.2)))
        =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 :=
      (hsum.mul hord2).congr' EventuallyEq.rfl (.of_forall fun p ↦ by ring)
    refine (h₁.add h₂).congr' (.of_forall fun p ↦ ?_) EventuallyEq.rfl
    simp only [pow_two, sub_mul, mul_sub]
    abel
  -- The logarithm contributes its own quadratic estimate.
  have htendsto : Tendsto (fun p : A × A ↦ exp p.1 * exp p.2 - 1)
      (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) := by
    have h := (((tendsto_exp_zero A).comp (tendsto_fst_zero A)).mul
      ((tendsto_exp_zero A).comp (tendsto_snd_zero A))).sub_const 1
    simpa using h
  have hlog : (fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1) -
        ((exp p.1 * exp p.2 - 1) - (2⁻¹ : ℝ) • (exp p.1 * exp p.2 - 1) ^ 2))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
    have h : (fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1) -
          ((exp p.1 * exp p.2 - 1) - (2⁻¹ : ℝ) • (exp p.1 * exp p.2 - 1) ^ 2))
        =O[𝓝 ((0, 0) : A × A)] fun p : A × A ↦ ‖exp p.1 * exp p.2 - 1‖ ^ 3 :=
      (isBigO_logOneAdd_sub_quadratic ℝ (A := A)).comp_tendsto htendsto
    exact h.trans (hord1.norm_left.pow 3)
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
    refine ((hsquares.const_smul_left (2⁻¹ : ℝ)).neg_left).congr'
      (.of_forall fun p ↦ ?_) EventuallyEq.rfl
    simp only [Pi.smul_apply]
    rw [hcommutator p.1 p.2]
    module
  refine ((hlog.add (isBigO_exp_mul_exp_sub_one_sub_quadratic A)).add hcancel).congr'
    (.of_forall fun p ↦ ?_) EventuallyEq.rfl
  abel_nf

/-- The first-order law holds for every representative of the local Baker--Campbell--Hausdorff
germ, the estimate at the origin depending only on the germ. -/
theorem isBigO_sub_firstOrder_of_coe_eq_localBCH (f : A × A → A)
    (hf : (↑f : Germ (𝓝 ((0, 0) : A × A)) A) = localBCH A) :
    (fun p : A × A ↦ f p - (p.1 + p.2 + (2⁻¹ : ℝ) • (p.1 * p.2 - p.2 * p.1)))
      =O[𝓝 ((0, 0) : A × A)] fun p ↦ ‖p‖ ^ 3 := by
  rw [localBCH_def, Germ.coe_eq] at hf
  exact (isBigO_logOneAdd_exp_mul_exp_sub_one_sub_firstOrder A).congr'
    (hf.symm.sub EventuallyEq.rfl) EventuallyEq.rfl

end NormedSpace
