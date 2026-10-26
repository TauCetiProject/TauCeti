/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement
-- Proof-only: Lebesgue measure, uniqueness of Haar measure and the Brunn–Minkowski inequality.
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic

/-!
# Schwarz rearrangement of Lipschitz functions

Schwarz rearrangement preserves Lipschitz bounds. For an additive Haar measure on a
finite-dimensional real inner product space, if `f : E → ℝ≥0∞` satisfies
`f x ≤ f y + K * edist x y` for all `x` and `y`, then so does its Schwarz rearrangement `f*`
(`TauCeti.schwarzRearrangement_le_add_mul_edist`).

The argument compares superlevel sets. If `f > s + K δ` at a point, then `f > s` on the closed
`δ`-ball around it, so `{f > s + K δ} + closedBall 0 δ ⊆ {f > s}`. The Brunn–Minkowski inequality
bounds the dimension root of the measure of the left side below by the sum of those of
`{f > s + K δ}` and of `closedBall 0 δ`. The dimension root of the measure of a centered ball is
linear in its radius. So if `{f > s + K δ}` has more measure than the centered ball of radius `r`,
then `{f > s}` has more measure than the centered ball of radius `r + δ`. In terms of `f*`, the
level `s + K δ` at radius `r` drops at most to `s` at radius `r + δ`.

For a real `K`-Lipschitz function `h`, the real value (`ENNReal.toReal`) of the rearrangement of
`x ↦ ENNReal.ofReal (h x)` is `K`-Lipschitz (`TauCeti.lipschitzWith_toReal_schwarzRearrangement`).
If some finite level has a superlevel set of finite measure, for instance when
`∫⁻ x, ENNReal.ofReal (h x) ∂μ < ∞`, the rearrangement is finite everywhere
(`TauCeti.schwarzRearrangement_ne_top`). It is then the extended-real coercion of that real
Lipschitz function at every point, which gives a Lipschitz representative of the rearrangement of a
nonnegative integrable Lipschitz function.

## Main results

* `TauCeti.schwarzRearrangement_le_add_mul_edist`: Lipschitz bounds pass to the rearrangement.
* `TauCeti.schwarzRearrangement_ne_top`: finiteness of the rearrangement.
* `TauCeti.lipschitzWith_toReal_schwarzRearrangement`: the real-valued form.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi and M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, arXiv:2206.09833, for Lipschitz functions under rearrangement at the
  `p = 1` endpoint of the Pólya–Szegő inequality.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {f : E → ℝ≥0∞} {K : ℝ≥0}

/-- The radial form of the Lipschitz bound, for Lebesgue measure: moving outward by `δ` lowers the
rearrangement by at most `K δ`. -/
private theorem schwarzRearrangement_volume_le_add (hf : ∀ x y, f x ≤ f y + K * edist x y)
    {x y : E} (hxy : ‖x‖ ≤ ‖y‖) :
    schwarzRearrangement volume f x ≤
      schwarzRearrangement volume f y + K * ENNReal.ofReal (‖y‖ - ‖x‖) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [Subsingleton.elim x y]
    exact le_self_add
  set δ := ‖y‖ - ‖x‖ with hδ
  have hδ₀ : 0 ≤ δ := sub_nonneg.2 hxy
  have hKδ : (K : ℝ≥0∞) * ENNReal.ofReal δ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  set p := ((Module.finrank ℝ E : ℝ))⁻¹
  have hp : 0 < p := inv_pos.2 (Nat.cast_pos.2 Module.finrank_pos)
  -- The dimension root of the volume of a centered ball is linear in the radius.
  have hball {r : ℝ} (hr : 0 ≤ r) :
      volume (ball (0 : E) r) ^ p = ENNReal.ofReal r * volume (ball (0 : E) 1) ^ p := by
    rw [Measure.addHaar_ball _ _ hr, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
      Real.pow_rpow_inv_natCast hr Module.finrank_pos.ne']
  refine le_of_forall_lt fun c hc ↦ ?_
  obtain ⟨t, hct, ht⟩ := exists_between hc
  rcases le_or_gt t (K * ENNReal.ofReal δ) with htK | htK
  · exact hct.trans_le (htK.trans le_add_self)
  -- Write the level `t` as `s + K δ` and show that `s` is below the rearrangement at `y`.
  obtain ⟨s, rfl⟩ : ∃ s, t = s + K * ENNReal.ofReal δ :=
    ⟨t - K * ENNReal.ofReal δ, (tsub_add_cancel_of_le htK.le).symm⟩
  refine hct.trans ((ENNReal.add_lt_add_iff_right hKδ).2 ?_)
  rw [lt_schwarzRearrangement_iff] at ht ⊢
  set A := {z | s + K * ENNReal.ofReal δ < f z}
  have hA : MeasurableSet A :=
    (isOpen_lt continuous_const (continuous_of_le_add_edist K ENNReal.coe_ne_top hf)).measurableSet
  have hAn : A.Nonempty := nonempty_of_measure_ne_zero (zero_le.trans_lt ht).ne'
  -- The closed `δ`-neighbourhood of the level set `A` lies in the lower level set.
  have hsub : A + closedBall 0 δ ⊆ {z | s < f z} := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have hab : edist a (a + b) ≤ ENNReal.ofReal δ := by
      rw [edist_dist, dist_self_add_right]
      exact ENNReal.ofReal_le_ofReal (mem_closedBall_zero_iff.1 hb)
    refine (ENNReal.add_lt_add_iff_right hKδ).1 (ha.trans_le ((hf a (a + b)).trans ?_))
    gcongr
  rw [← ENNReal.rpow_lt_rpow_iff hp]
  calc volume (ball (0 : E) ‖y‖) ^ p
      = volume (ball (0 : E) ‖x‖) ^ p + volume (closedBall (0 : E) δ) ^ p := by
        rw [Measure.addHaar_closedBall_eq_addHaar_ball, hball (norm_nonneg y),
          hball (norm_nonneg x), hball hδ₀, ← add_mul, ← ENNReal.ofReal_add (norm_nonneg x) hδ₀, hδ,
          add_sub_cancel]
    _ < volume A ^ p + volume (closedBall (0 : E) δ) ^ p :=
        (ENNReal.add_lt_add_iff_right (ENNReal.rpow_ne_top_of_nonneg hp.le
          measure_closedBall_lt_top.ne)).2 (ENNReal.rpow_lt_rpow ht hp)
    _ ≤ volume (A + closedBall (0 : E) δ) ^ p :=
        volume_rpow_add_volume_rpow_le Module.finrank_pos.ne' hAn hA.nullMeasurableSet
          (nonempty_closedBall.2 hδ₀) measurableSet_closedBall.nullMeasurableSet
    _ ≤ volume {z | s < f z} ^ p := ENNReal.rpow_le_rpow (measure_mono hsub) hp.le

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Schwarz rearrangement preserves Lipschitz bounds.** If `f x ≤ f y + K * edist x y` for all
`x` and `y`, then the Schwarz rearrangement of `f` with respect to an additive Haar measure
satisfies the same bound. -/
theorem schwarzRearrangement_le_add_mul_edist (hf : ∀ x y, f x ≤ f y + K * edist x y) (x y : E) :
    schwarzRearrangement μ f x ≤ schwarzRearrangement μ f y + K * edist x y := by
  rw [Measure.isAddLeftInvariant_eq_smul μ volume, ENNReal.smul_def,
    schwarzRearrangement_smul_measure volume
      (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne')
      ENNReal.coe_ne_top]
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · refine (schwarzRearrangement_volume_le_add hf hxy).trans ?_
    gcongr
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa [norm_sub_rev] using norm_sub_norm_le y x)
  · exact (schwarzRearrangement_le_of_norm_le volume f hyx).trans le_self_add

/-- **Finiteness of the rearrangement of a Lipschitz function.** If `f` satisfies the Lipschitz
bound `f x ≤ f y + K * edist x y` and some finite level `t` has a superlevel set of finite measure,
then the Schwarz rearrangement of `f` is finite everywhere. -/
theorem schwarzRearrangement_ne_top [Nontrivial E] (hf : ∀ x y, f x ≤ f y + K * edist x y)
    {t : ℝ≥0∞} (ht : t ≠ ∞) (hμt : μ {x | t < f x} ≠ ∞) (x : E) :
    schwarzRearrangement μ f x ≠ ∞ := by
  -- By equimeasurability, the level `t` is not exceeded somewhere.
  obtain ⟨y, hy⟩ : ∃ y, ¬t < schwarzRearrangement μ f y := by
    by_contra! h
    have huniv : {y | t < schwarzRearrangement μ f y} = univ := eq_univ_of_forall h
    have := addHaar_setOf_lt_schwarzRearrangement μ f t
    rw [huniv, measure_univ_of_isAddLeftInvariant] at this
    exact hμt this.symm
  refine ne_top_of_le_ne_top ?_ (schwarzRearrangement_le_add_mul_edist μ hf x y)
  exact ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ht (not_lt.1 hy),
    ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top x y)⟩

/-- **Schwarz rearrangement of a real Lipschitz function.** For a real `K`-Lipschitz function `h`,
the real value (`ENNReal.toReal`) of the Schwarz rearrangement of its positive part is
`K`-Lipschitz. -/
theorem lipschitzWith_toReal_schwarzRearrangement {h : E → ℝ} (hh : LipschitzWith K h) :
    LipschitzWith K fun x ↦ (schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) x).toReal := by
  set g := schwarzRearrangement μ fun y ↦ ENNReal.ofReal (h y)
  have hg : ∀ x y, g x ≤ g y + K * edist x y := by
    refine schwarzRearrangement_le_add_mul_edist μ fun x y ↦ ?_
    calc ENNReal.ofReal (h x) ≤ ENNReal.ofReal (h y + K * dist x y) :=
          ENNReal.ofReal_le_ofReal (hh.le_add_mul x y)
      _ ≤ ENNReal.ofReal (h y) + K * edist x y := by
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
        exact ENNReal.ofReal_add_le
  refine LipschitzWith.of_le_add_mul K fun x y ↦ ?_
  have hxy : K * edist x y ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top x y)
  rcases eq_or_ne (g y) ∞ with hgy | hgy
  · -- An infinite value forces the rearrangement to be infinite everywhere.
    have hgx : g x = ∞ := by
      by_contra hgx
      exact (ENNReal.add_ne_top.2 ⟨hgx, by rwa [edist_comm]⟩) (top_unique (hgy ▸ hg y x))
    rw [hgx, hgy, ENNReal.toReal_top]
    positivity
  · have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hgy, hxy⟩) (hg x y)
    rwa [ENNReal.toReal_add hgy hxy, ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at this

end TauCeti
