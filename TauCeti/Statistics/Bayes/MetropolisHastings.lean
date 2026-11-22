/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import TauCeti.Probability.Kernel.Matrix.Invariance

/-!
# The Metropolis–Hastings kernel on a finite state space

Let `ι` be a finite state space, `π : ι → ℝ` a family of weights and `q` a proposal matrix.
The **Metropolis acceptance** of a move from `x` to `y` is `min 1 (π y q y x / (π x q x y))`,
and `1` when `π x q x y = 0`. The **Metropolis–Hastings kernel** moves from `x` to `y ≠ x` with
probability `q x y` times the acceptance, and stays at `x` with the remaining probability.

For nonnegative weights and a nonnegative proposal whose rows sum to at most `1`, the kernel is
Markov. For a nonnegative proposal it satisfies detailed balance with respect to the weight
measure `∑ x, ofReal (π x) • δ_x` of the positive parts of the weights, in Mathlib's form
`Kernel.IsReversible`. The key identity is that
for nonnegative weights the probability flux `π x q x y` times the acceptance is
`min (π x q x y) (π y q y x)`, which is symmetric in `x` and `y`. States of negative weight
have mass `0` in the weight measure and receive no flux from states of nonnegative weight.
Invariance of the weight measure then follows from Mathlib's `Kernel.IsReversible.invariant`.

## Main definitions

* `TauCeti.metropolisAcceptance π q x y`: the acceptance probability of a move from `x` to `y`.
* `TauCeti.metropolisHastingsMatrix π q`: the transition matrix of the chain.
* `TauCeti.metropolisHastingsKernel π q`: the kernel with that transition matrix (negative
  entries clipped to `0`).

## Main results

* `TauCeti.isSymm_diagonal_mul_metropolisHastingsMatrix`: detailed balance in matrix form.
* `TauCeti.isMarkovKernel_metropolisHastingsKernel`: the kernel is Markov.
* `TauCeti.isReversible_metropolisHastingsKernel`: the kernel is reversible for the weight
  measure.

The definitions and the matrix computations are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), files `CKSD/Bayes/Basic.lean` and
`CKSD/Bayes/MonteCarlo/MetropolisHastings.lean`.

## References

* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer (2004),
  Theorem 7.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {ι : Type*}

/-- The **Metropolis acceptance** probability `min 1 (π y q y x / (π x q x y))` of a move from
`x` to `y`, for weights `π` and a proposal `q`; it is `1` when `π x q x y = 0`. -/
def metropolisAcceptance (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) : ℝ :=
  if π x * q x y = 0 then 1 else min 1 (π y * q y x / (π x * q x y))

theorem metropolisAcceptance_def (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) :
    metropolisAcceptance π q x y =
      if π x * q x y = 0 then 1 else min 1 (π y * q y x / (π x * q x y)) := (rfl)

@[simp]
theorem metropolisAcceptance_of_mul_eq_zero {π : ι → ℝ} {q : Matrix ι ι ℝ} {x y : ι}
    (h : π x * q x y = 0) : metropolisAcceptance π q x y = 1 :=
  by simp [metropolisAcceptance_def, h]

theorem metropolisAcceptance_of_mul_ne_zero {π : ι → ℝ} {q : Matrix ι ι ℝ} {x y : ι}
    (h : π x * q x y ≠ 0) :
    metropolisAcceptance π q x y = min 1 (π y * q y x / (π x * q x y)) := by
  simp [metropolisAcceptance_def, h]

/-- For a proposal with `q y x = q x y ≠ 0` and `π x ≠ 0`, the acceptance is
`min 1 (π y / π x)`. -/
theorem metropolisAcceptance_of_eq {π : ι → ℝ} {q : Matrix ι ι ℝ} {x y : ι}
    (hq : q y x = q x y) (hqxy : q x y ≠ 0) (hπ : π x ≠ 0) :
    metropolisAcceptance π q x y = min 1 (π y / π x) := by
  rw [metropolisAcceptance_of_mul_ne_zero (mul_ne_zero hπ hqxy), hq,
    mul_div_mul_right _ _ hqxy]

/-- The acceptance is at most `1`. -/
theorem metropolisAcceptance_le_one (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) :
    metropolisAcceptance π q x y ≤ 1 := by
  rw [metropolisAcceptance_def]
  split_ifs
  exacts [le_rfl, min_le_left _ _]

/-- For nonnegative weights and proposal at `x` and `y`, the acceptance is nonnegative. -/
theorem metropolisAcceptance_nonneg {π : ι → ℝ} {q : Matrix ι ι ℝ} {x y : ι} (hx : 0 ≤ π x)
    (hy : 0 ≤ π y) (hxy : 0 ≤ q x y) (hyx : 0 ≤ q y x) : 0 ≤ metropolisAcceptance π q x y := by
  rw [metropolisAcceptance_def]
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (div_nonneg (mul_nonneg hy hyx) (mul_nonneg hx hxy))

/-- The accepted flux `π x q x y` times the acceptance is `min (π x q x y) (π y q y x)`, for
nonnegative weights and proposal. -/
theorem mul_mul_metropolisAcceptance_eq_min {π : ι → ℝ} {q : Matrix ι ι ℝ} {x y : ι}
    (hx : 0 ≤ π x) (hy : 0 ≤ π y) (hxy : 0 ≤ q x y) (hyx : 0 ≤ q y x) :
    π x * q x y * metropolisAcceptance π q x y = min (π x * q x y) (π y * q y x) := by
  by_cases h : π x * q x y = 0
  · rw [h, zero_mul, min_eq_left (mul_nonneg hy hyx)]
  · rw [metropolisAcceptance_of_mul_ne_zero h, mul_min_of_nonneg _ _ (mul_nonneg hx hxy),
      mul_one, mul_div_cancel₀ _ h]

/-- From a state of nonnegative weight, a move towards a state of negative weight has
nonpositive accepted flux `π x q x y` times the acceptance, for a nonnegative proposal. -/
theorem mul_mul_metropolisAcceptance_nonpos {π : ι → ℝ} {q : Matrix ι ι ℝ} {x y : ι}
    (hx : 0 ≤ π x) (hy : π y < 0) (hxy : 0 ≤ q x y) (hyx : 0 ≤ q y x) :
    π x * q x y * metropolisAcceptance π q x y ≤ 0 := by
  rcases (mul_nonneg hx hxy).eq_or_lt with h | h
  · rw [← h, zero_mul]
  · rw [metropolisAcceptance_of_mul_ne_zero h.ne', mul_min_of_nonneg _ _ h.le, mul_one,
      mul_div_cancel₀ _ h.ne']
    exact (min_le_right _ _).trans (mul_nonpos_of_nonpos_of_nonneg hy.le hyx)

variable [Fintype ι] [DecidableEq ι]

/-- The **Metropolis–Hastings transition matrix**: off the diagonal, `q x y` times the
acceptance; the diagonal also carries the probability `1 - ∑ z, q x z * a x z` of a rejected
proposal. -/
def metropolisHastingsMatrix (π : ι → ℝ) (q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun x y ↦ q x y * metropolisAcceptance π q x y +
    if x = y then 1 - ∑ z, q x z * metropolisAcceptance π q x z else 0

theorem metropolisHastingsMatrix_apply (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) :
    metropolisHastingsMatrix π q x y = q x y * metropolisAcceptance π q x y +
      if x = y then 1 - ∑ z, q x z * metropolisAcceptance π q x z else 0 := (rfl)

/-- The diagonal entry of the Metropolis–Hastings matrix: the accepted proposal to stay at `x`
plus the probability of a rejected proposal. -/
theorem metropolisHastingsMatrix_apply_self (π : ι → ℝ) (q : Matrix ι ι ℝ) (x : ι) :
    metropolisHastingsMatrix π q x x = q x x * metropolisAcceptance π q x x +
      (1 - ∑ z, q x z * metropolisAcceptance π q x z) := by
  simp [metropolisHastingsMatrix_apply]

@[simp]
theorem metropolisHastingsMatrix_apply_of_ne (π : ι → ℝ) (q : Matrix ι ι ℝ) {x y : ι}
    (h : x ≠ y) : metropolisHastingsMatrix π q x y = q x y * metropolisAcceptance π q x y := by
  simp [metropolisHastingsMatrix_apply, h]

/-- Every row of the Metropolis–Hastings matrix sums to `1`. -/
@[simp]
theorem sum_metropolisHastingsMatrix (π : ι → ℝ) (q : Matrix ι ι ℝ) (x : ι) :
    ∑ y, metropolisHastingsMatrix π q x y = 1 := by
  simp [metropolisHastingsMatrix_apply, Finset.sum_add_distrib]

/-- For nonnegative weights and a nonnegative proposal with rows summing to at most `1`, the
entries of the Metropolis–Hastings matrix are nonnegative. -/
theorem metropolisHastingsMatrix_nonneg {π : ι → ℝ} {q : Matrix ι ι ℝ} (hπ : 0 ≤ π)
    (hq : ∀ x y, 0 ≤ q x y) (hq₁ : ∀ x, ∑ y, q x y ≤ 1) (x y : ι) :
    0 ≤ metropolisHastingsMatrix π q x y := by
  have hrow : ∑ z, q x z * metropolisAcceptance π q x z ≤ 1 :=
    (Finset.sum_le_sum fun z _ ↦
      mul_le_of_le_one_right (hq x z) (metropolisAcceptance_le_one π q x z)).trans (hq₁ x)
  rw [metropolisHastingsMatrix_apply]
  refine add_nonneg
    (mul_nonneg (hq x y) (metropolisAcceptance_nonneg (hπ x) (hπ y) (hq x y) (hq y x))) ?_
  split_ifs
  exacts [sub_nonneg.mpr hrow, le_rfl]

/-- **Detailed balance** at a pair of states: for nonnegative weights and proposal at `x` and
`y`, `π x P x y = π y P y x`. -/
theorem mul_metropolisHastingsMatrix_comm {π : ι → ℝ} {q : Matrix ι ι ℝ} {x y : ι}
    (hx : 0 ≤ π x) (hy : 0 ≤ π y) (hxy : 0 ≤ q x y) (hyx : 0 ≤ q y x) :
    π x * metropolisHastingsMatrix π q x y = π y * metropolisHastingsMatrix π q y x := by
  rcases eq_or_ne x y with rfl | h
  · rfl
  rw [metropolisHastingsMatrix_apply_of_ne _ _ h, metropolisHastingsMatrix_apply_of_ne _ _ h.symm,
    ← mul_assoc, ← mul_assoc, mul_mul_metropolisAcceptance_eq_min hx hy hxy hyx,
    mul_mul_metropolisAcceptance_eq_min hy hx hyx hxy, min_comm]

/-- **Detailed balance**: for nonnegative weights and proposal,
`π x P x y = π y P y x`, that is, `diagonal π * P` is symmetric. -/
theorem isSymm_diagonal_mul_metropolisHastingsMatrix {π : ι → ℝ} {q : Matrix ι ι ℝ}
    (hπ : 0 ≤ π) (hq : ∀ x y, 0 ≤ q x y) :
    (Matrix.diagonal π * metropolisHastingsMatrix π q).IsSymm :=
  Matrix.IsSymm.ext fun x y ↦ by
    simpa only [Matrix.diagonal_mul] using
      mul_metropolisHastingsMatrix_comm (hπ y) (hπ x) (hq y x) (hq x y)

/-- Detailed balance for the positive parts of the weights and of the entries of the
Metropolis–Hastings matrix, for a nonnegative proposal. -/
theorem toNNReal_mul_toNNReal_metropolisHastingsMatrix_comm {π : ι → ℝ} {q : Matrix ι ι ℝ}
    (hq : ∀ x y, 0 ≤ q x y) (x y : ι) :
    (π x).toNNReal * (metropolisHastingsMatrix π q x y).toNNReal =
      (π y).toNNReal * (metropolisHastingsMatrix π q y x).toNNReal := by
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  -- A state of negative weight carries no flux in either direction.
  have hneg {a b : ι} (hab : a ≠ b) (hb : π b < 0) :
      (π a).toNNReal * (metropolisHastingsMatrix π q a b).toNNReal = 0 := by
    rcases le_or_gt (π a) 0 with ha | ha
    · rw [Real.toNNReal_of_nonpos ha, zero_mul]
    rw [← Real.toNNReal_mul ha.le, metropolisHastingsMatrix_apply_of_ne _ _ hab, ← mul_assoc]
    exact Real.toNNReal_of_nonpos (mul_mul_metropolisAcceptance_nonpos ha.le hb (hq a b) (hq b a))
  rcases lt_or_ge (π y) 0 with hy | hy
  · rw [hneg hxy hy, Real.toNNReal_of_nonpos hy.le, zero_mul]
  rcases lt_or_ge (π x) 0 with hx | hx
  · rw [hneg (Ne.symm hxy) hx, Real.toNNReal_of_nonpos hx.le, zero_mul]
  rw [← Real.toNNReal_mul hx, ← Real.toNNReal_mul hy,
    mul_metropolisHastingsMatrix_comm hx hy (hq x y) (hq y x)]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [DecidableEq ι] [MeasurableSingletonClass ι] in
/-- A finite sum of finitely weighted Dirac measures is a finite measure. -/
private theorem isFiniteMeasure_sum_smul_dirac (c : ι → ℝ≥0∞) (hc : ∀ y, c y ≠ ∞) :
    IsFiniteMeasure (∑ y, c y • Measure.dirac y) :=
  ⟨by simpa using fun y ↦ (hc y).lt_top⟩

/-- The positive part of a real number, through `ℝ≥0∞`, is `Real.toNNReal`. -/
private theorem toNNReal_ofReal (r : ℝ) : (ENNReal.ofReal r).toNNReal = r.toNNReal :=
  ENNReal.toNNReal_coe r.toNNReal

/-- The **Metropolis–Hastings kernel**, with transition matrix `metropolisHastingsMatrix π q`
(negative entries, which do not occur under the hypotheses of
`isMarkovKernel_metropolisHastingsKernel`, are replaced by `0`). -/
def metropolisHastingsKernel (π : ι → ℝ) (q : Matrix ι ι ℝ) : Kernel ι ι :=
  Kernel.ofFunOfCountable fun x ↦
    ∑ y, ENNReal.ofReal (metropolisHastingsMatrix π q x y) • Measure.dirac y

theorem metropolisHastingsKernel_apply (π : ι → ℝ) (q : Matrix ι ι ℝ) (x : ι) :
    metropolisHastingsKernel π q x =
      ∑ y, ENNReal.ofReal (metropolisHastingsMatrix π q x y) • Measure.dirac y := (rfl)

@[simp]
theorem metropolisHastingsKernel_apply_singleton (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) :
    metropolisHastingsKernel π q x {y} = ENNReal.ofReal (metropolisHastingsMatrix π q x y) := by
  rw [metropolisHastingsKernel_apply, ← Measure.sum_fintype, Measure.sum_smul_dirac_singleton]

/-- The transition matrix of the Metropolis–Hastings kernel is the positive part of the
Metropolis–Hastings matrix. -/
@[simp]
theorem toMatrix_metropolisHastingsKernel_apply (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) :
    (metropolisHastingsKernel π q).toMatrix x y = (metropolisHastingsMatrix π q x y).toNNReal := by
  rw [Kernel.toMatrix_apply, metropolisHastingsKernel_apply_singleton, toNNReal_ofReal]

instance (π : ι → ℝ) (q : Matrix ι ι ℝ) : IsFiniteKernel (metropolisHastingsKernel π q) := by
  have (x : ι) : IsFiniteMeasure (metropolisHastingsKernel π q x) :=
    isFiniteMeasure_sum_smul_dirac _ fun _ ↦ ENNReal.ofReal_ne_top
  exact ⟨⟨∑ x, metropolisHastingsKernel π q x Set.univ,
    ENNReal.sum_lt_top.2 fun _ _ ↦ measure_lt_top _ _,
    fun x ↦ Finset.single_le_sum (f := fun x ↦ metropolisHastingsKernel π q x Set.univ)
      (fun _ _ ↦ bot_le) (Finset.mem_univ x)⟩⟩

/-- For nonnegative weights and a nonnegative proposal whose rows sum to at most `1`, the
Metropolis–Hastings kernel is Markov. -/
theorem isMarkovKernel_metropolisHastingsKernel {π : ι → ℝ} {q : Matrix ι ι ℝ} (hπ : 0 ≤ π)
    (hq : ∀ x y, 0 ≤ q x y) (hq₁ : ∀ x, ∑ y, q x y ≤ 1) :
    IsMarkovKernel (metropolisHastingsKernel π q) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  simp only [metropolisHastingsKernel_apply, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ metropolisHastingsMatrix_nonneg hπ hq hq₁ x y,
    sum_metropolisHastingsMatrix, ENNReal.ofReal_one]

/-- **Reversibility** of the Metropolis–Hastings kernel: for a nonnegative proposal, the kernel
satisfies detailed balance with respect to the weight measure `∑ x, ofReal (π x) • δ_x` of the
positive parts of the weights. -/
theorem isReversible_metropolisHastingsKernel {π : ι → ℝ} {q : Matrix ι ι ℝ}
    (hq : ∀ x y, 0 ≤ q x y) :
    (metropolisHastingsKernel π q).IsReversible
      (∑ x, ENNReal.ofReal (π x) • Measure.dirac x) := by
  set w : Measure ι := ∑ x, ENNReal.ofReal (π x) • Measure.dirac x with hw_def
  have hw (a : ι) : w {a} = ENNReal.ofReal (π a) := by
    rw [hw_def, ← Measure.sum_fintype, Measure.sum_smul_dirac_singleton]
  have : IsFiniteMeasure w := isFiniteMeasure_sum_smul_dirac _ fun _ ↦ ENNReal.ofReal_ne_top
  rw [Kernel.isReversible_iff_isSymm_diagonal_mul]
  refine Matrix.IsSymm.ext fun a b ↦ ?_
  simp only [Matrix.diagonal_mul, toMatrix_metropolisHastingsKernel_apply, hw, toNNReal_ofReal]
  exact toNNReal_mul_toNNReal_metropolisHastingsMatrix_comm hq b a

end TauCeti
