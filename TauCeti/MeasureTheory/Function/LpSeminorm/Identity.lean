/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Global `Lᵖ` non-membership of the identity map

On a nontrivial proper real normed space equipped with a left-invariant, open-positive measure
finite on compact sets (in particular, any additive Haar measure on a nontrivial finite-dimensional
real normed space), the identity map `id : E → E` fails global `MemLp` for every nonzero exponent
`p : ℝ≥0∞`, including `p = ∞`:

* For `p = ∞`, any ball of radius `‖v‖` (`v ≠ 0`) centered far enough from the origin has positive
  measure and lies in `{x | C < ‖x‖}`, contradicting finite essential supremum.
* For `0 < p < ∞`, the complement of the unit ball has infinite measure (since the space is
  noncompact and left-invariant), contradicting Chebyshev–Markov finiteness of `{x | 1 ≤ ‖x‖}`.

## Main declarations

* `TauCeti.not_memLp_id`: `id : E → E` is not in `Lᵖ(μ)` for any `p ≠ 0`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- On a nontrivial proper real normed space with a left-invariant, open-positive measure finite on
compact sets (in particular any additive Haar measure on a nontrivial finite-dimensional real normed
space), the identity map fails global `MemLp` for every nonzero exponent `p ≤ ∞`. -/
theorem not_memLp_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsAddLeftInvariant]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    ¬ MemLp (id : E → E) p μ := by
  intro hid
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.2 hv
  rcases eq_or_ne p ∞ with rfl | hp
  · have hfin : eLpNormEssSup (id : E → E) μ < ∞ :=
      eLpNorm_exponent_top hid.aestronglyMeasurable ▸ hid.eLpNorm_lt_top
    set C : ℝ := (eLpNormEssSup (id : E → E) μ).toReal
    set c : E := ((max C 0 + 2 * ‖v‖) / ‖v‖) • v
    have hball_sub : ball c ‖v‖ ⊆ {x : E | C < ‖x‖} := by
      intro x hx
      have hdist : ‖x - c‖ < ‖v‖ := by simpa [dist_eq_norm] using hx
      have hc_norm : ‖c‖ = max C 0 + 2 * ‖v‖ := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by positivity) hv_pos.le),
          div_mul_cancel₀ _ hv_pos.ne']
      have htri : ‖c‖ - ‖x - c‖ ≤ ‖x‖ := by
        have := norm_sub_norm_le c (c - x)
        simpa [sub_sub_cancel, norm_sub_rev] using this
      have hC : C ≤ max C 0 := le_max_left C 0
      rw [Set.mem_ofPred_eq]
      linarith
    have hpos : 0 < μ (ball c ‖v‖) :=
      isOpen_ball.measure_pos μ (nonempty_ball.2 hv_pos)
    have hnull : μ {x : E | C < ‖x‖} = 0 := by
      refine measure_mono_null (fun x (hlt : C < ‖x‖) => ?_)
        (ae_iff.1 (eNorm_ae_le_eLpNormEssSup (id : E → E) μ))
      intro hx
      have hle : ‖x‖ ≤ C := by
        have hx' := ENNReal.toReal_mono hfin.ne hx
        simpa [C, toReal_eNorm] using hx'
      exact hle.not_gt hlt
    exact (hpos.trans_le (measure_mono hball_sub)).ne' hnull
  · have hcompl_top : μ (ball (0 : E) 1)ᶜ = ∞ := by
      by_contra hlt
      have huniv : μ univ < ∞ := by
        calc μ univ
            = μ (ball (0 : E) 1 ∪ (ball (0 : E) 1)ᶜ) := by rw [union_compl_self]
          _ ≤ μ (ball (0 : E) 1) + μ (ball (0 : E) 1)ᶜ := measure_union_le _ _
          _ < ∞ := ENNReal.add_lt_top.2 ⟨measure_ball_lt_top, Ne.lt_top hlt⟩
      exact (measure_univ_of_isAddLeftInvariant μ).symm.not_gt huniv
    have hge_lt : μ {x : E | (1 : ℝ≥0) ≤ ‖(id : E → E) x‖₊} < ∞ :=
      hid.meas_ge_lt_top hp0 hp one_ne_zero
    have hsub : (ball (0 : E) 1)ᶜ ⊆ {x : E | (1 : ℝ≥0) ≤ ‖(id : E → E) x‖₊} := fun x hx => by
      have hx' : 1 ≤ ‖x‖ := by simpa using hx
      exact hx'
    exact (hcompl_top ▸ measure_mono hsub).not_gt hge_lt

end TauCeti
