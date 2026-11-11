/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Nonseparability of `W^{1,∞}` on an interval

On every nonempty bounded open interval, the functions `x ↦ |x - t|`, with `t` in the
interval, give an uncountable family whose pairwise `W^{1,∞}` distances are at least two.
Their weak derivatives differ by two on the interval between the two corners. Thus the
full Sobolev norm, unlike the uniform norm of the continuous representatives, is not separable.

The construction uses the absolutely continuous characterization of interval Sobolev classes;
it imposes no boundary condition. In particular this concerns the full space, not the
closure-defined zero-boundary subspace.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3, for the distinction between
  finite and infinite exponents in separability and smooth approximation.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal

namespace TauCeti.W1p

/-- The corner functions `|x - t|` form a two-separated family in `W^{1,∞}(a,b)`.
The parameter ranges over the whole open interval. -/
theorem exists_pairwise_two_le_dist_Ioo_top (a b : ℝ) :
    ∃ u : Ioo a b → W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤,
      (∀ t, value (u t) =ᵐ[volume.restrict (Ioo a b)] fun x ↦ |x - t.val|) ∧
      Pairwise (fun s t ↦ 2 ≤ dist (u s) (u t)) := by
  have hex (t : Ioo a b) : ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤,
      value u =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ |x - t.val|) ∧
      gradient u =ᵐ[volume.restrict (Ioo a b)] deriv (fun x ↦ |x - t.val|) := by
    have hl : LipschitzWith 1 (fun x : ℝ ↦ |x - t.val|) := by
      simpa only [Function.comp_def, Real.norm_eq_abs, one_mul, sub_eq_add_neg] using
        (lipschitzWith_one_norm (E := ℝ)).comp (isometry_add_right (-t.val)).lipschitzWith
    exact hl.lipschitzOnWith.absolutelyContinuousOnInterval.exists_w1p_value_gradient_ae_eq
      (MemLp.of_bound (aestronglyMeasurable_deriv _ _) 1
        (Eventually.of_forall fun x ↦ norm_deriv_le_of_lipschitz hl))
  choose u hv hg using hex
  refine ⟨u, hv, ?_⟩
  have hsep {s t : Ioo a b} (hst : s.val < t.val) : 2 ≤ dist (u s) (u t) := by
    -- On the positive-measure interval between the corners, the gradients are `1` and `-1`.
    have hsub : Ioo s.val t.val ⊆ Ioo a b :=
      fun x hx ↦ ⟨s.property.1.trans hx.1, hx.2.trans t.property.2⟩
    have hbound : ∀ᵐ x ∂volume.restrict (Ioo a b),
        ‖gradient (u s) x - gradient (u t) x‖ ≤ dist (u s) (u t) := by
      filter_upwards [Lp.ae_norm_le_norm_top (gradient (u s) - gradient (u t)),
        Lp.coeFn_sub (gradient (u s)) (gradient (u t))] with x hx hsub
      have hn : ‖gradient (u s) - gradient (u t)‖ ≤ dist (u s) (u t) := by
        simpa only [dist_eq_norm, gradient_sub] using norm_gradient_le (u s - u t)
      simpa only [hsub, Pi.sub_apply] using hx.trans hn
    have : (ae (volume.restrict (Ioo s.val t.val))).NeBot :=
      ae_restrict_neBot.2 (by
        rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact sub_pos.2 hst)
    obtain ⟨x, hx, hs, ht, hnorm⟩ := ((ae_restrict_mem measurableSet_Ioo).and
      (ae_restrict_of_ae_restrict_of_subset hsub ((hg s).and ((hg t).and hbound)))).exists
    have hds : deriv (fun x : ℝ ↦ |x - s.val|) x = 1 := by
      simpa only [Function.comp_def, id_eq, mul_one] using
        ((hasDerivAt_abs_pos (sub_pos.2 hx.1)).comp x
          ((hasDerivAt_id x).sub_const s.val)).deriv
    have hdt : deriv (fun x : ℝ ↦ |x - t.val|) x = -1 := by
      simpa only [Function.comp_def, id_eq, mul_one] using
        ((hasDerivAt_abs_neg (sub_neg.2 hx.2)).comp x
          ((hasDerivAt_id x).sub_const t.val)).deriv
    norm_num [hs, ht, hds, hdt] at hnorm ⊢
    exact hnorm
  intro s t hst
  rcases lt_or_gt_of_ne (fun h ↦ hst (Subtype.ext h)) with h | h
  · exact hsep h
  · simpa only [dist_comm] using hsep h

/-- The full infinite-exponent Sobolev space on a nonempty bounded interval is not separable.
This does not assert nonseparability of the closure-defined zero-boundary space. -/
theorem not_separableSpace_Ioo_top {a b : ℝ} (hab : a < b) :
    ¬ SeparableSpace (W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤) := by
  intro hs
  obtain ⟨u, -, hsep⟩ := exists_pairwise_two_le_dist_Ioo_top a b
  have hdisj : Pairwise (fun s t ↦ Disjoint (Metric.ball (u s) 1) (Metric.ball (u t) 1)) := by
    intro s t hst
    exact Metric.ball_disjoint_ball (by norm_num; exact hsep hst)
  have hcount : Countable (Ioo a b) :=
    hdisj.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
      (fun t ↦ ⟨u t, Metric.mem_ball_self zero_lt_one⟩)
  exact (Cardinal.Real.Ioo_countable_iff.mp (Set.countable_coe_iff.mp hcount)).not_gt hab

end TauCeti.W1p
