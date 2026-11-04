/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic

/-!
# Positivity and Loewner order of diagonal operators on `ℓ²`

On `ℓ²(ι, 𝕜)` over `RCLike 𝕜`, the bounded diagonal operator `lp.diagonalCLM d` acts by
coordinatewise multiplication in the standard Hilbert-sum inner product `⟪x, y⟫ = ∑' i, ⟪x i, y i⟫`.
It is self-adjoint precisely when every coefficient `d i` is fixed by conjugation, positive
precisely when `0 ≤ d i` for every `i`, and monotone in the Loewner order with respect to the
pointwise order on `ℓ^∞(ι, 𝕜)`.

For nonnegative coefficients `0 ≤ d i`, the finite coordinate truncations
`lp.diagonalTruncation d s` form an increasing family of positive finite-rank operators bounded
above by `lp.diagonalCLM d`. On `ℓ²(ℕ, 𝕜)`, when `‖d n‖ → 0`, the truncations along
`Finset.range n` converge to `lp.diagonalCLM d` in operator norm and hence have `lp.diagonalCLM d`
as their least upper bound in the Loewner order.

## Main declarations

* `lp.isSelfAdjoint_diagonalCLM_iff`: `lp.diagonalCLM d` on `ℓ²` is self-adjoint iff
  `∀ i, star (d i) = d i`.
* `lp.isPositive_diagonalCLM_iff`, `lp.diagonalCLM_le_diagonalCLM_iff`: characterizations of
  positivity and the Loewner order on `ℓ²` diagonal operators.
* `lp.isPositive_diagonalTruncation_iff`, `lp.diagonalTruncation_mono`,
  `lp.diagonalTruncation_le_diagonalCLM`: positivity and monotonicity of finite coordinate
  truncations.
* `lp.isLUB_range_diagonalTruncation_range`: for `0 ≤ d n` with `‖d n‖ → 0`, `lp.diagonalCLM d` is
  the least upper bound in the Loewner order of its finite-rank truncations along `Finset.range n`.
-/

public section

open Filter
open scoped lp ENNReal NNReal Topology InnerProductSpace ComplexConjugate ComplexOrder

namespace lp

variable {ι 𝕜 : Type*} [RCLike 𝕜]

/-- A bounded diagonal operator on `ℓ²(ι, 𝕜)` is self-adjoint if and only if each diagonal entry is
fixed by conjugation. -/
@[simp]
theorem isSelfAdjoint_diagonalCLM_iff (d : ℓ^∞(ι, 𝕜)) :
    IsSelfAdjoint (diagonalCLM (p := 2) d) ↔ ∀ i, star (d i) = d i := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  refine ⟨fun h i ↦ ?_, fun h x y ↦ ?_⟩
  · classical
    simpa [lp.inner_single_left, lp.inner_single_right] using
      h (lp.single 2 i (1 : 𝕜)) (lp.single 2 i (1 : 𝕜))
  · simp only [ContinuousLinearMap.coe_coe, lp.inner_eq_tsum, diagonalCLM_apply]
    refine tsum_congr fun i ↦ ?_
    have hi : conj (d i) = d i := h i
    rw [← smul_eq_mul, ← smul_eq_mul, inner_smul_left, inner_smul_right, hi]

/-- A bounded diagonal operator on `ℓ²(ι, 𝕜)` is positive if and only if all of its coefficients
are nonnegative. -/
@[simp]
theorem isPositive_diagonalCLM_iff (d : ℓ^∞(ι, 𝕜)) :
    (diagonalCLM (p := 2) d).IsPositive ↔ ∀ i, 0 ≤ d i := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · classical
    simpa [lp.inner_single_left] using h.inner_nonneg_right (lp.single 2 i (1 : 𝕜))
  · refine ⟨(ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 <|
        (isSelfAdjoint_diagonalCLM_iff d).2 fun i ↦ (IsSelfAdjoint.of_nonneg (h i)).star_eq),
      fun x ↦ ?_⟩
    have hsum := RCLike.reCLM.map_tsum (lp.summable_inner (𝕜 := 𝕜) (diagonalCLM (p := 2) d x) x)
    simp_rw [RCLike.reCLM_apply] at hsum
    rw [← lp.inner_eq_tsum] at hsum
    rw [ContinuousLinearMap.reApplyInnerSelf, hsum]
    refine tsum_nonneg fun i ↦ ?_
    have hdi : 0 ≤ RCLike.re (d i) := (RCLike.nonneg_iff.1 (h i)).1
    have hconj : conj (d i) = d i := RCLike.conj_eq_iff_im.2 (RCLike.nonneg_iff.1 (h i)).2
    rw [diagonalCLM_apply, ← smul_eq_mul, inner_smul_left, hconj, inner_self_eq_norm_sq_to_K]
    have hmul : d i * ((‖x i‖ : 𝕜) ^ 2) = (‖x i‖ ^ 2 : ℝ) • d i := by
      simp [Algebra.smul_def, mul_comm]
    rw [hmul, RCLike.smul_re]
    positivity

/-- The Loewner order between diagonal operators on `ℓ²(ι, 𝕜)` is the pointwise order on their
coefficients. -/
@[simp]
theorem diagonalCLM_le_diagonalCLM_iff (d e : ℓ^∞(ι, 𝕜)) :
    diagonalCLM (p := 2) d ≤ diagonalCLM (p := 2) e ↔ ∀ i, d i ≤ e i := by
  have hsub {p : ℝ≥0∞} [Fact (1 ≤ p)] :
      diagonalCLM (p := p) e - diagonalCLM (p := p) d = diagonalCLM (p := p) (e - d) := by
    ext x i
    simp [sub_mul]
  simp [ContinuousLinearMap.le_def, hsub, sub_nonneg]

section Truncation

variable [DecidableEq ι]

private theorem inner_diagonalTruncation_left (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) (x y : ℓ^2(ι, 𝕜)) :
    ⟪diagonalTruncation (p := 2) d s x, y⟫_𝕜 = ∑ i ∈ s, conj (d i) * ⟪x i, y i⟫_𝕜 := by
  rw [lp.inner_eq_tsum, tsum_eq_sum (s := s) fun i hi ↦ by simp [hi]]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [diagonalTruncation_apply, ite_eq_left hi, ← smul_eq_mul, inner_smul_left]

private theorem inner_diagonalTruncation_right (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) (x y : ℓ^2(ι, 𝕜)) :
    ⟪x, diagonalTruncation (p := 2) d s y⟫_𝕜 = ∑ i ∈ s, d i * ⟪x i, y i⟫_𝕜 := by
  rw [lp.inner_eq_tsum, tsum_eq_sum (s := s) fun i hi ↦ by simp [hi]]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [diagonalTruncation_apply, ite_eq_left hi, ← smul_eq_mul, inner_smul_right]

/-- A finite coordinate truncation of a diagonal operator on `ℓ²(ι, 𝕜)` is positive if and only if
the retained coefficients are nonnegative. -/
@[simp]
theorem isPositive_diagonalTruncation_iff (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) :
    (diagonalTruncation (p := 2) d s).IsPositive ↔ ∀ i ∈ s, 0 ≤ d i := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ ⟨fun x y ↦ ?_, fun x ↦ ?_⟩⟩
  · simpa [lp.inner_single_left, hi] using h.inner_nonneg_right (lp.single 2 i (1 : 𝕜))
  · simp only [ContinuousLinearMap.coe_coe, inner_diagonalTruncation_left,
      inner_diagonalTruncation_right]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [RCLike.conj_eq_iff_im.2 (RCLike.nonneg_iff.1 (h i hi)).2]
  · rw [ContinuousLinearMap.reApplyInnerSelf, inner_diagonalTruncation_left, map_sum]
    refine Finset.sum_nonneg fun i hi ↦ ?_
    have hdi : 0 ≤ RCLike.re (d i) := (RCLike.nonneg_iff.1 (h i hi)).1
    have hconj : conj (d i) = d i := RCLike.conj_eq_iff_im.2 (RCLike.nonneg_iff.1 (h i hi)).2
    rw [hconj, inner_self_eq_norm_sq_to_K]
    have hmul : d i * ((‖x i‖ : 𝕜) ^ 2) = (‖x i‖ ^ 2 : ℝ) • d i := by
      simp [Algebra.smul_def, mul_comm]
    rw [hmul, RCLike.smul_re]
    positivity

/-- For nonnegative diagonal coefficients, finite coordinate truncations on `ℓ²(ι, 𝕜)` are monotone
in the retained set of coordinates. -/
theorem diagonalTruncation_mono {d : ℓ^∞(ι, 𝕜)} (hd : ∀ i, 0 ≤ d i) :
    Monotone (diagonalTruncation (p := 2) d) := by
  intro s t hst
  have hdiff : diagonalTruncation (p := 2) d t - diagonalTruncation (p := 2) d s =
      diagonalTruncation (p := 2) d (t \ s) := by
    ext x i
    by_cases hit : i ∈ t <;> by_cases his : i ∈ s
    · simp [hit, his]
    · simp [hit, his]
    · exact absurd (hst his) hit
    · simp [hit, his]
  rw [ContinuousLinearMap.le_def, hdiff, isPositive_diagonalTruncation_iff]
  exact fun i _ ↦ hd i

/-- For nonnegative diagonal coefficients, every finite coordinate truncation on `ℓ²(ι, 𝕜)` is
bounded above in the Loewner order by the full diagonal operator. -/
theorem diagonalTruncation_le_diagonalCLM {d : ℓ^∞(ι, 𝕜)} (hd : ∀ i, 0 ≤ d i) (s : Finset ι) :
    diagonalTruncation (p := 2) d s ≤ diagonalCLM (p := 2) d := by
  rw [ContinuousLinearMap.le_def]
  have hR {p : ℝ≥0∞} [Fact (1 ≤ p)] (x : ℓ^p(ι, 𝕜)) (i : ι) :
      ((diagonalCLM (p := p) d - diagonalTruncation (p := p) d s) x) i =
        if i ∈ s then 0 else d i * x i := by
    by_cases hi : i ∈ s <;> simp [hi]
  refine ⟨fun x y ↦ ?_, fun x ↦ ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, lp.inner_eq_tsum]
    refine tsum_congr fun i ↦ ?_
    rw [hR x i, hR y i]
    by_cases hi : i ∈ s
    · simp [hi]
    · have hconj : conj (d i) = d i := RCLike.conj_eq_iff_im.2 (RCLike.nonneg_iff.1 (hd i)).2
      rw [ite_eq_right hi, ite_eq_right hi, ← smul_eq_mul, ← smul_eq_mul, inner_smul_left,
        inner_smul_right, hconj]
  · have hsum := RCLike.reCLM.map_tsum
      (lp.summable_inner (𝕜 := 𝕜) ((diagonalCLM (p := 2) d - diagonalTruncation (p := 2) d s) x) x)
    simp_rw [RCLike.reCLM_apply] at hsum
    rw [← lp.inner_eq_tsum] at hsum
    rw [ContinuousLinearMap.reApplyInnerSelf, hsum]
    refine tsum_nonneg fun i ↦ ?_
    rw [hR x i]
    by_cases hi : i ∈ s
    · simp [hi]
    · have hdi : 0 ≤ RCLike.re (d i) := (RCLike.nonneg_iff.1 (hd i)).1
      have hconj : conj (d i) = d i := RCLike.conj_eq_iff_im.2 (RCLike.nonneg_iff.1 (hd i)).2
      rw [ite_eq_right hi, ← smul_eq_mul, inner_smul_left, hconj, inner_self_eq_norm_sq_to_K]
      have hmul : d i * ((‖x i‖ : 𝕜) ^ 2) = (‖x i‖ ^ 2 : ℝ) • d i := by
        simp [Algebra.smul_def, mul_comm]
      rw [hmul, RCLike.smul_re]
      positivity

end Truncation

/-- When `0 ≤ d n` for every `n` and `‖d n‖ → 0`, the full diagonal operator `lp.diagonalCLM d` on
`ℓ²(ℕ, 𝕜)` is the least upper bound in the Loewner order of its finite-rank truncations along
`Finset.range n`. -/
theorem isLUB_range_diagonalTruncation_range {d : ℓ^∞(ℕ, 𝕜)} (hd : ∀ n, 0 ≤ d n)
    (h0 : Tendsto (fun n ↦ ‖d n‖) atTop (𝓝 0)) :
    IsLUB (Set.range fun n ↦ diagonalTruncation (p := 2) d (Finset.range n))
      (diagonalCLM (p := 2) d) := by
  refine ⟨?_, fun B hB ↦ ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact diagonalTruncation_le_diagonalCLM hd (Finset.range n)
  · rw [ContinuousLinearMap.le_def]
    have htend : Tendsto (fun n ↦ B - diagonalTruncation (p := 2) d (Finset.range n)) atTop
        (𝓝 (B - diagonalCLM (p := 2) d)) :=
      tendsto_const_nhds.sub (tendsto_diagonalTruncation_range d h0)
    have hpos (n : ℕ) : (B - diagonalTruncation (p := 2) d (Finset.range n)).IsPositive :=
      ContinuousLinearMap.le_def.1 (hB ⟨n, rfl⟩)
    have heval (x : ℓ^2(ℕ, 𝕜)) :
        Tendsto (fun n ↦ (B - diagonalTruncation (p := 2) d (Finset.range n)) x) atTop
          (𝓝 ((B - diagonalCLM (p := 2) d) x)) :=
      ((ContinuousLinearMap.apply 𝕜 ℓ^2(ℕ, 𝕜) x).continuous.tendsto _).comp htend
    refine ⟨fun x y ↦ tendsto_nhds_unique ((heval x).inner (𝕜 := 𝕜) tendsto_const_nhds) ?_,
      fun x ↦ ge_of_tendsto (RCLike.continuous_re.tendsto _ |>.comp
        ((heval x).inner (𝕜 := 𝕜) tendsto_const_nhds)) (Eventually.of_forall fun n ↦ ?_)⟩
    · exact (tendsto_const_nhds.inner (𝕜 := 𝕜) (heval y)).congr fun n ↦
        ((hpos n).isSymmetric x y).symm
    · exact (hpos n).re_inner_nonneg_left x

end lp
