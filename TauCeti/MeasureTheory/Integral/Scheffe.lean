/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Scheffé's lemma

Let `f i` be nonnegative integrable functions converging almost everywhere to an integrable
function `g`. Pointwise convergence alone does not give convergence in `L¹`: mass may escape to
infinity or concentrate on small sets. Scheffé's lemma says that this is the only obstruction:
if moreover the integrals converge, `∫ f i → ∫ g`, then `∫ ‖f i - g‖ → 0`
(`MeasureTheory.tendsto_integral_norm_sub_of_tendsto_integral`).

The proof writes `‖x - y‖ = (x - y) + 2 max (y - x) 0`. The integral of the first term tends to
zero by assumption. The second term tends to zero pointwise and, since `f i ≥ 0`, it is dominated
by `‖g‖`, so its integral tends to zero by dominated convergence.

## References

* H. Scheffé, *A useful convergence theorem for probability distributions*, Ann. Math. Statist.
  **18** (1947), 434–438.
-/

public section

open Filter Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Scheffé's lemma.** If nonnegative integrable functions `f i` converge almost everywhere to an
integrable function `g` and their integrals converge to the integral of `g`, then `f i` converges
to `g` in `L¹`: `∫ ‖f i - g‖ → 0`. -/
theorem tendsto_integral_norm_sub_of_tendsto_integral {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → α → ℝ} {g : α → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (hg : Integrable g μ) (hf₀ : ∀ i, 0 ≤ᵐ[μ] f i)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) l (𝓝 (g a)))
    (hint : Tendsto (fun i ↦ ∫ a, f i a ∂μ) l (𝓝 (∫ a, g a ∂μ))) :
    Tendsto (fun i ↦ ∫ a, ‖f i a - g a‖ ∂μ) l (𝓝 0) := by
  -- The negative part `max (g - f i) 0` of `f i - g` is dominated by `‖g‖`, as `f i ≥ 0`, and
  -- tends to zero almost everywhere.
  have hpos (i : ι) : Integrable (fun a ↦ max (g a - f i a) 0) μ := (hg.sub (hf i)).pos_part
  have hneg : Tendsto (fun i ↦ ∫ a, max (g a - f i a) 0 ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun a ↦ ‖g a‖)
      (Eventually.of_forall fun i ↦ (hpos i).aestronglyMeasurable)
      (Eventually.of_forall fun i ↦ (hf₀ i).mono fun a (ha : 0 ≤ f i a) ↦ by
        rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
        exact max_le (by linarith [le_abs_self (g a)]) (abs_nonneg _))
      hg.norm (hlim.mono fun a ha ↦ by
        simpa using (tendsto_const_nhds.sub ha).max (tendsto_const_nhds (x := (0 : ℝ))))
    simpa using h
  -- `‖f i - g‖ = (f i - g) + 2 max (g - f i) 0`.
  have hsplit (i : ι) : ∫ a, ‖f i a - g a‖ ∂μ =
      (∫ a, f i a ∂μ - ∫ a, g a ∂μ) + 2 * ∫ a, max (g a - f i a) 0 ∂μ := by
    have hsub : Integrable (fun a ↦ f i a - g a) μ := (hf i).sub hg
    rw [← integral_sub (hf i) hg, ← integral_const_mul, ← integral_add hsub ((hpos i).const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    simp only [Real.norm_eq_abs]
    rcases le_total (f i a) (g a) with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      ring
  simp_rw [hsplit]
  simpa using (hint.sub_const (∫ a, g a ∂μ)).add (hneg.const_mul 2)

end MeasureTheory
