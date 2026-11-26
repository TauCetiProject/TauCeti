/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Lebesgue measure of intervals and centered interval differences

Replacing two subsets of the real line by open centered intervals of the same respective
volumes can only decrease the volume of their one-sided difference. The inequality uses
Mathlib's extended-radius balls and `Real.volume_eball`, and allows zero and infinite volumes.
It supplies the sectionwise contraction inequality for Steiner symmetrization. The annulus
between two concentric open intervals of radii `0 ≤ r ≤ R` has length `2 (R - r)`
(`TauCeti.volume_ball_sdiff_ball`), so that between radii `r` and `2r` has length `2r`
(`TauCeti.volume_ball_two_mul_sdiff_ball`).

An order-connected subset of the real line of positive finite volume agrees almost everywhere
with a nonempty bounded open interval (`Set.OrdConnected.exists_ae_eq_Ioo`): finite volume
bounds it, and it lies between the open and the closed interval spanned by its infimum and
supremum.

Pulling real Lebesgue measure on `(0,T]` back to `ℝ≥0` commutes with restriction,
and the resulting finite-horizon measure has total mass `T`.

On a finite coordinate space `ι → ℝ`, permuting the coordinates and changing their signs
preserves Lebesgue measure (`TauCeti.volume_preserving_signedPerm`). In particular the reflection
`(s, t) ↦ (-s, t)` of the plane preserves Lebesgue measure
(`LinearIsometryEquiv.measurePreserving_negFst`).

The Lebesgue measure of a finite union of pairwise disjoint intervals `Ι (a i) (b i)` is the sum of
their lengths (`TauCeti.volume_biUnion_uIoc_eq_ofReal_sum`).

Cutting a closed box `Set.Icc a b` in `ι → ℝ` along coordinate `k` at `t` produces two almost-
everywhere disjoint sub-boxes (`TauCeti.aeDisjoint_Icc_update`), as their intersection lies in a
coordinate hyperplane of measure zero.

Lebesgue measure on `[0, 1]` is a probability measure
(`TauCeti.isProbabilityMeasure_restrict_Icc_zero_one`).

A rectangle in `ℝ × ℝ` whose sides have lengths at least `ℓ ≤ r` and `ℓ' ≤ r` meets the ball of
radius `r` about each of its points, a square for the sup norm, in a set of area at least `ℓ ℓ'`
(`TauCeti.ofReal_mul_ofReal_le_volume_Ioo_prod_Ioo_inter_ball`), however long the rectangle is.
This is the uniform lower bound on the local measure of a domain under which Sobolev estimates on
rectangles of unbounded length have uniform constants.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace NNReal

/-- Pulling Lebesgue measure on `(0,T]` back to `ℝ≥0` is the restriction of its pullback. -/
theorem comap_volume_restrict_Ioc (T : ℝ≥0) :
    (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ) =
      (volume.comap ((↑) : ℝ≥0 → ℝ)).restrict (Ioc 0 T) := by
  rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_restrict]
  -- The preimage is definitionally `Ioc 0 T`: the order on `ℝ≥0` is inherited from `ℝ`.
  congr 1

/-- The pullback of Lebesgue measure on `(0,T]` to `ℝ≥0` has total mass `T`. -/
theorem comap_volume_restrict_Ioc_univ (T : ℝ≥0) :
    (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ) univ = T := by
  rw [comap_volume_restrict_Ioc, Measure.restrict_apply_univ,
    NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply]
  simp

end NNReal

namespace TauCeti

/-- Lebesgue measure on `[0, 1]` is a probability measure. -/
instance isProbabilityMeasure_restrict_Icc_zero_one :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Centering intervals can only decrease the length of a one-sided difference. -/
theorem volume_eball_sdiff_le (s u : Set ℝ) :
    volume (Metric.eball (0 : ℝ) (volume s / 2) \ Metric.eball 0 (volume u / 2)) ≤
      volume (s \ u) := by
  have hlength (a : ℝ≥0∞) : volume (Metric.eball (0 : ℝ) (a / 2)) = a := by
    rw [Real.volume_eball]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  rcases le_total (volume s) (volume u) with h | h
  · rw [sdiff_eq_empty.mpr (Metric.eball_subset_eball (ENNReal.div_le_div_right h 2)),
      measure_empty]
    exact bot_le
  · by_cases hu : volume u = ∞
    · have hs : volume s = ∞ := top_le_iff.mp (hu ▸ h)
      simp [hu, hs]
    · rw [measure_sdiff (Metric.eball_subset_eball (ENNReal.div_le_div_right h 2))
        Metric.isOpen_eball.measurableSet.nullMeasurableSet (by rwa [hlength]), hlength, hlength]
      exact le_measure_sdiff

/-- The annulus between two concentric open intervals of radii `0 ≤ r ≤ R` has length
`2 (R - r)`. -/
theorem volume_ball_sdiff_ball {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (x : ℝ) :
    volume (Metric.ball x R \ Metric.ball x r) = ENNReal.ofReal (2 * (R - r)) := by
  rw [measure_sdiff (Metric.ball_subset_ball hrR) measurableSet_ball.nullMeasurableSet
    measure_ball_lt_top.ne, Real.volume_ball, Real.volume_ball,
    ← ENNReal.ofReal_sub _ (by positivity), mul_sub]

/-- The annulus between the open intervals of radii `r` and `2r` about a point has length `2r`. -/
theorem volume_ball_two_mul_sdiff_ball (r x : ℝ) :
    volume (Metric.ball x (2 * r) \ Metric.ball x r) = ENNReal.ofReal (2 * r) := by
  rcases le_or_gt 0 r with hr | hr
  · rw [volume_ball_sdiff_ball hr (by linarith)]
    ring_nf
  · rw [Metric.ball_eq_empty.2 (by linarith), empty_sdiff, measure_empty,
      ENNReal.ofReal_of_nonpos (by linarith)]

/-- A permutation of the coordinates combined with sign changes, `x ↦ fun i => c i * x (e i)`
with `|c i| = 1`, preserves Lebesgue measure on `ι → ℝ`. -/
theorem volume_preserving_signedPerm {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) (c : ι → ℝ)
    (hc : ∀ i, |c i| = 1) :
    MeasurePreserving (fun (x : ι → ℝ) i => c i * x (e i)) := by
  have hmul : MeasurePreserving (fun (y : ι → ℝ) i => c i * y i) :=
    volume_preserving_pi fun i => ⟨measurable_const_mul _, by
      rw [Real.map_volume_mul_left fun h0 => by simpa [h0] using hc i,
        abs_inv, hc i, inv_one, ENNReal.ofReal_one, one_smul]⟩
  exact hmul.comp
    (volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))

/-- The reflection `(s, t) ↦ (-s, t)` of the plane preserves Lebesgue measure. -/
theorem _root_.LinearIsometryEquiv.measurePreserving_negFst :
    MeasurePreserving (LinearIsometryEquiv.negFst ℝ ℝ ℝ) := by
  rw [LinearIsometryEquiv.coe_negFst, Measure.volume_eq_prod]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure ℝ))

/-- The measure of a finite union of pairwise disjoint intervals `Ι (a i) (b i)` is the sum of their
lengths `max (a i) (b i) - min (a i) (b i)`. -/
theorem volume_biUnion_uIoc_eq_ofReal_sum {ι : Type*} (I : Finset ι) (a b : ι → ℝ)
    (h : (I : Set ι).PairwiseDisjoint fun i ↦ Ι (a i) (b i)) :
    volume (⋃ i ∈ I, Ι (a i) (b i)) =
      ENNReal.ofReal (∑ i ∈ I, (max (a i) (b i) - min (a i) (b i))) := by
  rw [measure_biUnion_finset h fun _ _ ↦ measurableSet_uIoc,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sub_nonneg.2 min_le_max]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.volume_uIoc, ← max_sub_min_eq_abs', max_comm, min_comm]

/-- The two sub-boxes obtained by splitting `Set.Icc a b` along coordinate `k` at `t` meet in the
hyperplane slice `x k = t` of Lebesgue measure zero, hence are almost-everywhere disjoint. -/
theorem aeDisjoint_Icc_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (k : ι) (t : ℝ) :
    AEDisjoint volume (Icc a (Function.update b k t)) (Icc (Function.update a k t) b) := by
  have hsub : Icc a (Function.update b k t) ∩ Icc (Function.update a k t) b ⊆
      Icc (Function.update a k t) (Function.update b k t) := by
    rintro x ⟨⟨_, hx₁⟩, ⟨hx₂, _⟩⟩
    exact ⟨hx₂, hx₁⟩
  have hzero : volume (Icc (Function.update a k t) (Function.update b k t)) = 0 := by
    rw [Real.volume_Icc_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  exact measure_mono_null hsub hzero

open Metric in
/-- If `ℓ ≤ r` and `ℓ ≤ b - a`, then the open interval `(a, b)` meets the interval of radius `r`
about each point of `[a, b]` in a set of length at least `ℓ`. -/
theorem ofReal_le_volume_Ioo_inter_ball {a b x r ℓ : ℝ} (hℓr : ℓ ≤ r) (hℓ : ℓ ≤ b - a)
    (hx : x ∈ Icc a b) : ENNReal.ofReal ℓ ≤ volume (Ioo a b ∩ ball x r) := by
  rcases le_or_gt ℓ 0 with h | h
  · simp [ENNReal.ofReal_of_nonpos h]
  rw [Real.ball_eq_Ioo, Ioo_inter_Ioo, Real.volume_Ioo]
  refine ENNReal.ofReal_le_ofReal (le_sub_iff_add_le'.2 (le_inf ?_ ?_))
  · exact (le_sub_iff_add_le.1 (sup_le (by linarith) (by linarith [hx.2])))
  · exact (le_sub_iff_add_le.1 (sup_le (by linarith [hx.1]) (by linarith)))

open Metric in
/-- If `ℓ, ℓ' ≤ r`, then a rectangle in `ℝ × ℝ` with sides of lengths at least `ℓ` and `ℓ'` meets
the ball of radius `r` about each point of its closure in a set of area at least `ℓ ℓ'`, whatever
the lengths of its sides. For the sup norm of `ℝ × ℝ` this ball is the square
`(x - r, x + r) × (y - r, y + r)`. -/
theorem ofReal_mul_ofReal_le_volume_Ioo_prod_Ioo_inter_ball {a b c d r ℓ ℓ' : ℝ} (hℓr : ℓ ≤ r)
    (hℓ : ℓ ≤ b - a) (hℓ'r : ℓ' ≤ r) (hℓ' : ℓ' ≤ d - c) {z : ℝ × ℝ}
    (hz : z ∈ Icc a b ×ˢ Icc c d) :
    ENNReal.ofReal ℓ * ENNReal.ofReal ℓ' ≤ volume (Ioo a b ×ˢ Ioo c d ∩ ball z r) := by
  obtain ⟨x, y⟩ := z
  rw [← ball_prod_same, prod_inter_prod, Measure.volume_eq_prod, Measure.prod_prod]
  exact mul_le_mul' (ofReal_le_volume_Ioo_inter_ball hℓr hℓ hz.1)
    (ofReal_le_volume_Ioo_inter_ball hℓ'r hℓ' hz.2)

end TauCeti

/-- An order-connected subset of `ℝ` of positive finite volume agrees almost everywhere with a
nonempty bounded open interval. -/
theorem Set.OrdConnected.exists_ae_eq_Ioo {I : Set ℝ} (hI : I.OrdConnected) (h0 : volume I ≠ 0)
    (hfin : volume I ≠ ∞) : ∃ a b, a < b ∧ I =ᵐ[volume] Ioo a b := by
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero h0
  -- An unbounded order-connected set contains a ray, of infinite volume.
  have hbdd : BddBelow I ∧ BddAbove I := by
    refine ⟨by_contra fun h => hfin ?_, by_contra fun h => hfin ?_⟩
    · refine measure_mono_top (s₁ := Iic y) (fun z hz => ?_) Real.volume_Iic
      obtain ⟨w, hwI, hwz⟩ := not_bddBelow_iff.1 h z
      exact hI.out hwI hy ⟨hwz.le, hz⟩
    · refine measure_mono_top (s₁ := Ici y) (fun z hz => ?_) Real.volume_Ici
      obtain ⟨w, hwI, hwz⟩ := not_bddAbove_iff.1 h z
      exact hI.out hy hwI ⟨hz, hwz.le⟩
  have hsub := IsConnected.Ioo_csInf_csSup_subset ⟨⟨y, hy⟩, hI.isPreconnected⟩ hbdd.1 hbdd.2
  have hae : I =ᵐ[volume] Ioo (sInf I) (sSup I) :=
    ((subset_Icc_csInf_csSup hbdd.1 hbdd.2).eventuallySubset.trans
        Ioo_ae_eq_Icc.symm.subset).antisymm
      hsub.eventuallySubset
  refine ⟨sInf I, sSup I, lt_of_not_ge fun hle => h0 ?_, hae⟩
  rw [measure_congr hae, Ioo_eq_empty_of_le hle, measure_empty]
