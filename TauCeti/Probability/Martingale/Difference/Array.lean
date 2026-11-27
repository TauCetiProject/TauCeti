/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Difference.Series
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# Martingale difference arrays

A martingale difference array on a measure space `(Ω, μ)` is a doubly indexed family of real
functions `X n j`, where row `n` has the finitely many entries `X n 0, …, X n (k n - 1)` and carries
its own filtration `ℱ n`. Entry `j` of row `n` is `ℱ n (j + 1)`-measurable, integrable, and has
conditional mean `0` given `ℱ n j`. Nothing relates the filtrations of different rows. This is the
setting of the central limit theorems for martingales, whose conclusions concern the row sums
`∑ j ∈ range (k n), X n j`.

This file defines the predicate and proves its basic stability and orthogonality properties: the
partial sums of a row form a martingale for the row's filtration, a martingale difference array
for `ℱ` stays one for any smaller filtration to which its entries are still adapted, multiplying
each entry by a factor measurable for the previous σ-algebra preserves the property (in
particular, stopping each row at a predictable time does), and square-integrable entries of one
row are orthogonal.

## Main definitions

* `TauCeti.MeasureTheory.IsMartingaleDiffArray μ ℱ k X`: `X` is a martingale difference array
  with row lengths `k` for the row filtrations `ℱ`.

## Main results

* `TauCeti.MeasureTheory.IsMartingaleDiffArray.martingale_sum_range`: the partial sums of row `n`,
  frozen after time `k n`, form a martingale for `ℱ n`.
* `TauCeti.MeasureTheory.IsMartingaleDiffArray.of_filtration_le`: passing to a smaller
  filtration for which the entries are still adapted.
* `TauCeti.MeasureTheory.IsMartingaleDiffArray.mul_left`,
  `TauCeti.MeasureTheory.IsMartingaleDiffArray.indicator`: multiplying entry `j` by an
  `ℱ n j`-measurable factor, for instance the indicator of the event `{j < τ n}` of a predictable
  time `τ n`.
* `TauCeti.MeasureTheory.IsMartingaleDiffArray.integral_sq_sum_range`: the second moment of a
  partial row sum of square-integrable entries is the sum of their second moments.

## References

* R. Durrett, *Probability: Theory and Examples*, fifth edition, §8.2 (martingale difference
  arrays, p. 397).
* D. L. McLeish, *Dependent central limit theorems and invariance principles*, Ann. Probab. 2
  (1974).
-/

public section

open MeasureTheory Finset

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ 𝒢 : ℕ → Filtration ℕ m₀}
  {k : ℕ → ℕ} {X : ℕ → ℕ → Ω → ℝ}

/-- `X` is a **martingale difference array** with row lengths `k` for the row filtrations `ℱ`:
for every row `n` and every index `j < k n`, the entry `X n j` is `ℱ n (j + 1)`-measurable,
integrable, and its conditional expectation given `ℱ n j` vanishes almost everywhere. Entries with
`j ≥ k n` are not constrained, and the filtrations of different rows are unrelated. -/
structure IsMartingaleDiffArray (μ : Measure Ω) (ℱ : ℕ → Filtration ℕ m₀) (k : ℕ → ℕ)
    (X : ℕ → ℕ → Ω → ℝ) : Prop where
  /-- Entry `j` of row `n` is measurable for the next σ-algebra `ℱ n (j + 1)`. -/
  stronglyMeasurable ⦃n j : ℕ⦄ : j < k n → StronglyMeasurable[ℱ n (j + 1)] (X n j)
  /-- Every entry is integrable. -/
  integrable ⦃n j : ℕ⦄ : j < k n → Integrable (X n j) μ
  /-- Entry `j` of row `n` has conditional mean `0` given the previous σ-algebra `ℱ n j`. -/
  condExp_eq_zero ⦃n j : ℕ⦄ : j < k n → μ[X n j | ℱ n j] =ᵐ[μ] 0

namespace IsMartingaleDiffArray

/-! ### Truncated rows

Replacing the entries of row `n` with index at least `c ≤ k n` by `0` gives a martingale difference
sequence indexed by all of `ℕ`, to which the results of
`TauCeti.Probability.Martingale.Difference.Series` apply. -/

private lemma stronglyMeasurable_truncate (hX : IsMartingaleDiffArray μ ℱ k X) {n c : ℕ}
    (hc : c ≤ k n) (j : ℕ) :
    StronglyMeasurable[ℱ n (j + 1)] (if j < c then X n j else 0) := by
  split_ifs with h
  · exact hX.stronglyMeasurable (h.trans_le hc)
  · exact stronglyMeasurable_zero

private lemma memLp_truncate {p : ENNReal} {n c : ℕ} (hX : ∀ j < c, MemLp (X n j) p μ) (j : ℕ) :
    MemLp (if j < c then X n j else 0) p μ := by
  split_ifs with h
  · exact hX j h
  · exact MemLp.zero

private lemma condExp_truncate (hX : IsMartingaleDiffArray μ ℱ k X) {n c : ℕ} (hc : c ≤ k n)
    (j : ℕ) : μ[if j < c then X n j else 0 | ℱ n j] =ᵐ[μ] 0 := by
  split_ifs with h
  · exact hX.condExp_eq_zero (h.trans_le hc)
  · rw [condExp_zero]

private lemma sum_range_truncate_apply (n c i : ℕ) (ω : Ω) :
    ∑ j ∈ range i, (if j < c then X n j else 0) ω = ∑ j ∈ range (min i c), X n j ω := by
  simp only [ite_apply, Pi.zero_apply, ← sum_filter]
  congr 1
  ext j
  simp [lt_min_iff]

/-- **Martingale property of the row sums.** The partial sums `∑_{j < min i (k n)} X n j` of row
`n`, which are constant from time `k n` on, form a martingale for the row filtration `ℱ n`. -/
theorem martingale_sum_range [IsFiniteMeasure μ] (hX : IsMartingaleDiffArray μ ℱ k X) (n : ℕ) :
    Martingale (fun i ω ↦ ∑ j ∈ range (min i (k n)), X n j ω) (ℱ n) μ := by
  have h := _root_.TauCeti.MeasureTheory.martingale_sum_range
    (hX.stronglyMeasurable_truncate (n := n) le_rfl)
    (fun j ↦ memLp_one_iff_integrable.1
      (memLp_truncate (n := n) (fun i hi ↦ memLp_one_iff_integrable.2 (hX.integrable hi)) j))
    (hX.condExp_truncate (n := n) le_rfl)
  simpa only [sum_range_truncate_apply] using h

/-- **Orthogonality of martingale differences.** For square-integrable entries, the second moment
of a partial row sum `∑_{j < i} X n j`, `i ≤ k n`, is the sum of the second moments of its
terms. -/
theorem integral_sq_sum_range [IsFiniteMeasure μ] (hX : IsMartingaleDiffArray μ ℱ k X)
    {n i : ℕ} (hi : i ≤ k n) (hL2 : ∀ j < i, MemLp (X n j) 2 μ) :
    ∫ ω, (∑ j ∈ range i, X n j ω) ^ 2 ∂μ = ∑ j ∈ range i, ∫ ω, X n j ω ^ 2 ∂μ := by
  have h := integral_sq_sum_range_of_condExp_eq_zero (hX.stronglyMeasurable_truncate hi)
    (memLp_truncate hL2)
    (hX.condExp_truncate hi) i
  simp only [sum_range_truncate_apply, min_self] at h
  rw [h]
  exact sum_congr rfl fun j hj ↦ by simp [mem_range.1 hj]

/-! ### Changing the filtration and the entries -/

/-- A martingale difference array for `ℱ` is one for any smaller filtration `𝒢 ≤ ℱ` for which
its entries are still adapted, for instance the filtration generated by the earlier entries of
each row. -/
theorem of_filtration_le (hX : IsMartingaleDiffArray μ ℱ k X) (h𝒢 : ∀ n, 𝒢 n ≤ ℱ n)
    (hX𝒢 : ∀ ⦃n j : ℕ⦄, j < k n → StronglyMeasurable[𝒢 n (j + 1)] (X n j)) :
    IsMartingaleDiffArray μ 𝒢 k X where
  stronglyMeasurable := hX𝒢
  integrable := hX.integrable
  condExp_eq_zero n j hj := by
    by_cases hσ : SigmaFinite (μ.trim ((ℱ n).le j))
    · -- By the tower property, `μ[X n j | 𝒢 n j] = μ[μ[X n j | ℱ n j] | 𝒢 n j] = μ[0 | 𝒢 n j]`.
      refine (condExp_condExp_of_le (h𝒢 n j) ((ℱ n).le j)).symm.trans ?_
      filter_upwards [condExp_congr_ae (m := 𝒢 n j) (hX.condExp_eq_zero hj)] with ω hω
      simp [hω]
    · -- Otherwise the trimmed measure on the smaller σ-algebra is not σ-finite either, and the
      -- conditional expectation is `0` by convention.
      have hσ𝒢 : ¬SigmaFinite (μ.trim ((𝒢 n).le j)) := fun h ↦
        hσ (sigmaFiniteTrim_mono ((ℱ n).le j) (h𝒢 n j))
      rw [condExp_of_not_sigmaFinite _ hσ𝒢]

/-- Multiplying entry `j` of row `n` by an `ℱ n j`-measurable factor `H n j` keeps a martingale
difference array one, provided the products stay integrable (for instance when the factors are
bounded). This covers martingale transforms. -/
theorem mul_left (hX : IsMartingaleDiffArray μ ℱ k X) {H : ℕ → ℕ → Ω → ℝ}
    (hH : ∀ ⦃n j : ℕ⦄, j < k n → StronglyMeasurable[ℱ n j] (H n j))
    (hHX : ∀ ⦃n j : ℕ⦄, j < k n → Integrable (H n j * X n j) μ) :
    IsMartingaleDiffArray μ ℱ k fun n j ↦ H n j * X n j where
  stronglyMeasurable n j hj :=
    ((hH hj).mono ((ℱ n).mono j.le_succ)).mul (hX.stronglyMeasurable hj)
  integrable n j hj := hHX hj
  condExp_eq_zero n j hj := by
    simpa only [smul_eq_mul] using condExp_smul_eq_zero_of_condExp_eq_zero
      (hH hj).aestronglyMeasurable (by simpa only [smul_eq_mul] using hHX hj) (hX.integrable hj)
      (hX.condExp_eq_zero hj)

/-- **Stopping at a predictable time.** Keeping entry `j` of row `n` only on an event `A n j`
of the previous σ-algebra `ℱ n j`, and replacing it by `0` elsewhere, keeps a martingale difference
array one. With `A n j = {j < τ n}` for a random index `τ n` whose events `{j < τ n}` lie in
`ℱ n j`, this stops each row at the predictable time `τ n`. -/
theorem indicator (hX : IsMartingaleDiffArray μ ℱ k X) {A : ℕ → ℕ → Set Ω}
    (hA : ∀ ⦃n j : ℕ⦄, j < k n → MeasurableSet[ℱ n j] (A n j)) :
    IsMartingaleDiffArray μ ℱ k fun n j ↦ (A n j).indicator (X n j) where
  stronglyMeasurable n j hj :=
    (hX.stronglyMeasurable hj).indicator ((ℱ n).mono j.le_succ _ (hA hj))
  integrable n j hj := (hX.integrable hj).indicator ((ℱ n).le j _ (hA hj))
  condExp_eq_zero n j hj := by
    filter_upwards [condExp_indicator (hX.integrable hj) (hA hj), hX.condExp_eq_zero hj]
      with ω h₁ h₂
    simp [h₁, h₂]

end IsMartingaleDiffArray

end MeasureTheory

end TauCeti
