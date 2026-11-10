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
`lp.diagonalTruncation d s` form an increasing family of positive finite-rank operators converging
pointwise to `lp.diagonalCLM d`, so `lp.diagonalCLM d` is their least upper bound in the Loewner
order (`lp.isLUB_range_diagonalTruncation`, and along `Finset.range n` on `ℓ²(ℕ, 𝕜)`,
`lp.isLUB_range_diagonalTruncation_range`).

## Main declarations

* `lp.isSelfAdjoint_diagonalCLM_iff`: `lp.diagonalCLM d` on `ℓ²` is self-adjoint iff
  `∀ i, star (d i) = d i`.
* `lp.isPositive_diagonalCLM_iff`, `lp.diagonalCLM_le_diagonalCLM_iff`,
  `lp.isPositive_diagonalCLM_ofAntitone`: characterizations of positivity and the Loewner order on
  `ℓ²` diagonal operators, and positivity for antitone `ℝ≥0` sequences.
* `lp.isPositive_diagonalTruncation_iff`, `lp.diagonalTruncation_mono`,
  `lp.diagonalTruncation_le_diagonalCLM`: positivity and monotonicity of finite coordinate
  truncations.
* `lp.isLUB_range_diagonalTruncation`, `lp.isLUB_range_diagonalTruncation_range`: for `0 ≤ d i`,
  `lp.diagonalCLM d` is the least upper bound in the Loewner order of its finite-rank coordinate
  truncations (and of those along `Finset.range n` on `ℓ²(ℕ, 𝕜)`).
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
  refine ⟨fun h i ↦ ?_, fun h ↦ ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 <|
      (isSelfAdjoint_diagonalCLM_iff d).2 fun i ↦ (IsSelfAdjoint.of_nonneg (h i)).star_eq,
    fun x ↦ ?_⟩⟩
  · classical
    simpa [lp.inner_single_left] using h.inner_nonneg_right (lp.single 2 i (1 : 𝕜))
  · rw [ContinuousLinearMap.reApplyInnerSelf, lp.inner_eq_tsum, ← RCLike.reCLM_apply,
      RCLike.reCLM.map_tsum (lp.summable_inner (𝕜 := 𝕜) (diagonalCLM (p := 2) d x) x)]
    refine tsum_nonneg fun i ↦ ?_
    obtain ⟨hre, him⟩ := RCLike.nonneg_iff.1 (h i)
    have hmul : d i * ((‖x i‖ : 𝕜) ^ 2) = (‖x i‖ ^ 2 : ℝ) • d i := by
      simp [Algebra.smul_def, mul_comm]
    rw [RCLike.reCLM_apply, diagonalCLM_apply, ← smul_eq_mul, inner_smul_left,
      RCLike.conj_eq_iff_im.2 him, inner_self_eq_norm_sq_to_K, hmul, RCLike.smul_re]
    positivity

/-- For any antitone `ℝ≥0`-valued sequence `c`, the diagonal operator `lp.diagonalCLM` of
`lp.ofAntitone 𝕜 hc` on `ℓ²(ℕ, 𝕜)` is positive. -/
theorem isPositive_diagonalCLM_ofAntitone {c : ℕ → ℝ≥0} (hc : Antitone c) :
    (diagonalCLM (p := 2) (ofAntitone 𝕜 hc)).IsPositive :=
  (isPositive_diagonalCLM_iff _).2 (ofAntitone_apply_nonneg 𝕜 hc)

/-- The Loewner order between diagonal operators on `ℓ²(ι, 𝕜)` is the pointwise order on their
coefficients. -/
@[simp]
theorem diagonalCLM_le_diagonalCLM_iff (d e : ℓ^∞(ι, 𝕜)) :
    diagonalCLM (p := 2) d ≤ diagonalCLM (p := 2) e ↔ ∀ i, d i ≤ e i := by
  have hsub : diagonalCLM (p := 2) e - diagonalCLM (p := 2) d = diagonalCLM (p := 2) (e - d) := by
    ext x i; simp [sub_mul]
  simp [ContinuousLinearMap.le_def, hsub, sub_nonneg]

section Truncation

variable [DecidableEq ι]

/-- A finite coordinate truncation of a diagonal operator on `ℓ²(ι, 𝕜)` is positive if and only if
the retained coefficients are nonnegative. -/
@[simp]
theorem isPositive_diagonalTruncation_iff (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) :
    (diagonalTruncation (p := 2) d s).IsPositive ↔ ∀ i ∈ s, 0 ≤ d i := by
  rw [diagonalTruncation_eq_diagonalCLM, isPositive_diagonalCLM_iff]
  simp only [coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  exact ⟨fun h i hi ↦ by simpa [hi] using h i, fun h i ↦ by by_cases hi : i ∈ s <;> simp_all⟩

/-- For nonnegative diagonal coefficients, finite coordinate truncations on `ℓ²(ι, 𝕜)` are monotone
in the retained set of coordinates. -/
theorem diagonalTruncation_mono {d : ℓ^∞(ι, 𝕜)} (hd : ∀ i, 0 ≤ d i) :
    Monotone (diagonalTruncation (p := 2) d) := fun s t hst ↦ by
  rw [diagonalTruncation_eq_diagonalCLM, diagonalTruncation_eq_diagonalCLM,
    diagonalCLM_le_diagonalCLM_iff]; intro i
  simp only [coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  by_cases his : i ∈ s
  · simp [his, hst his]
  · by_cases hit : i ∈ t <;> simp [his, hit, hd i]

/-- For nonnegative diagonal coefficients, every finite coordinate truncation on `ℓ²(ι, 𝕜)` is
bounded above in the Loewner order by the full diagonal operator. -/
theorem diagonalTruncation_le_diagonalCLM {d : ℓ^∞(ι, 𝕜)} (hd : ∀ i, 0 ≤ d i) (s : Finset ι) :
    diagonalTruncation (p := 2) d s ≤ diagonalCLM (p := 2) d := by
  rw [diagonalTruncation_eq_diagonalCLM, diagonalCLM_le_diagonalCLM_iff]; intro i
  simp only [coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  by_cases hi : i ∈ s <;> simp [hi, hd i]

/-- When `0 ≤ d i` for every `i`, the full diagonal operator `lp.diagonalCLM d` on `ℓ²(ι, 𝕜)` is
the least upper bound in the Loewner order of its finite coordinate truncations. -/
theorem isLUB_range_diagonalTruncation {d : ℓ^∞(ι, 𝕜)} (hd : ∀ i, 0 ≤ d i) :
    IsLUB (Set.range (diagonalTruncation (p := 2) d)) (diagonalCLM (p := 2) d) := by
  refine ⟨Set.forall_mem_range.2 (diagonalTruncation_le_diagonalCLM hd), fun B hB ↦ ?_⟩
  rw [ContinuousLinearMap.le_def]
  have hpos (s : Finset ι) := ContinuousLinearMap.le_def.1 (hB ⟨s, rfl⟩)
  have heval (x : ℓ^2(ι, 𝕜)) : Tendsto (fun s ↦ (B - diagonalTruncation (p := 2) d s) x) atTop
      (𝓝 ((B - diagonalCLM (p := 2) d) x)) :=
    tendsto_const_nhds.sub (tendsto_diagonalTruncation_apply ENNReal.ofNat_ne_top d x)
  exact ⟨fun x y ↦ tendsto_nhds_unique ((heval x).inner (𝕜 := 𝕜) tendsto_const_nhds)
      ((tendsto_const_nhds.inner (𝕜 := 𝕜) (heval y)).congr fun s ↦ ((hpos s).isSymmetric x y).symm),
    fun x ↦ ge_of_tendsto (RCLike.continuous_re.tendsto _ |>.comp
      ((heval x).inner (𝕜 := 𝕜) tendsto_const_nhds))
      (Eventually.of_forall fun s ↦ (hpos s).re_inner_nonneg_left x)⟩

end Truncation

/-- When `0 ≤ d n` for every `n`, the full diagonal operator `lp.diagonalCLM d` on `ℓ²(ℕ, 𝕜)` is
the least upper bound in the Loewner order of its finite-rank truncations along
`Finset.range n`. -/
theorem isLUB_range_diagonalTruncation_range {d : ℓ^∞(ℕ, 𝕜)} (hd : ∀ n, 0 ≤ d n) :
    IsLUB (Set.range fun n ↦ diagonalTruncation (p := 2) d (Finset.range n))
      (diagonalCLM (p := 2) d) := by
  refine ⟨Set.forall_mem_range.2 fun n ↦ diagonalTruncation_le_diagonalCLM hd (Finset.range n),
    fun B hB ↦ (isLUB_range_diagonalTruncation hd).2 ?_⟩
  rintro _ ⟨s, rfl⟩
  obtain ⟨n, hn⟩ := (tendsto_finset_range.eventually (eventually_ge_atTop s)).exists
  exact (diagonalTruncation_mono hd hn).trans (hB ⟨n, rfl⟩)

end lp
