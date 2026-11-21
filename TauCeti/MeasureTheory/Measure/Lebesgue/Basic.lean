/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Prod

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
preserves Lebesgue measure (`TauCeti.volume_preserving_signedPerm`).

The Lebesgue measure of a finite union of pairwise disjoint intervals `Ι (a i) (b i)` is the sum of
their lengths (`TauCeti.volume_biUnion_uIoc_eq_ofReal_sum`).

Cutting a closed box `Set.Icc a b` in `ι → ℝ` along coordinate `k` at `t` produces two almost-
everywhere disjoint sub-boxes (`TauCeti.aeDisjoint_Icc_update`), as their intersection lies in a
coordinate hyperplane of measure zero.

On `ι → ℝ`, Lebesgue integrals split along the diagonal lines `u ↦ z - u·1`, weighted by the
indicator of the slab `{z | z i₀ ∈ [0, 1]}`, which cuts out a parameter interval of Lebesgue
measure one on each line (`TauCeti.lintegral_eq_lintegral_indicator_mul_lintegral_sub_const`, and
for a weighted Lebesgue measure
`TauCeti.lintegral_withDensity_eq_lintegral_indicator_mul_lintegral_sub_const`).
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

/-- **Decomposition of Lebesgue measure on `ι → ℝ` along the diagonal lines.** The lower
integral of an a.e. measurable `H` over `ι → ℝ` is the integral, against the indicator of
`z i₀ ∈ [0, 1]`, of the integrals of `H` along the lines `u ↦ z - u·1`, each taken with respect to
Lebesgue measure in the parameter `u`. The condition `z i₀ - u ∈ [0, 1]` cuts out a parameter
interval of Lebesgue measure one on each line (not a Euclidean segment of length one).

The proof is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Inference/Families.lean` (`lintegral_eq_lintegral_indicator_mul_lintegral_sub_const`, for
`ι = Fin n` and measurable `H`). -/
theorem lintegral_eq_lintegral_indicator_mul_lintegral_sub_const {ι : Type*} [Fintype ι]
    (i₀ : ι) {H : (ι → ℝ) → ℝ≥0∞} (hH : AEMeasurable H) :
    ∫⁻ x, H x =
      ∫⁻ z : ι → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) * ∫⁻ u : ℝ, H fun i ↦ z i - u := by
  set k : ℝ → ℝ≥0∞ := (Icc (0 : ℝ) 1).indicator 1 with hkdef
  have hk : Measurable k := measurable_one.indicator measurableSet_Icc
  have hk1 : ∀ t : ℝ, ∫⁻ u, k (t + u) = 1 := fun t ↦ by
    rw [lintegral_add_left_eq_self k t, hkdef, lintegral_indicator_one measurableSet_Icc,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  -- The shear `(u, z) ↦ z - u·1` is quasi-measure-preserving.
  have hsub : QuasiMeasurePreserving (fun p : ℝ × (ι → ℝ) ↦ fun i ↦ p.2 i - p.1)
      (volume.prod volume) volume :=
    .prod_of_right (by fun_prop) (ae_of_all _ fun u ↦
      (measurePreserving_sub_right volume fun _ : ι ↦ u).quasiMeasurePreserving)
  calc ∫⁻ x, H x = ∫⁻ x, ∫⁻ u : ℝ, k (x i₀ + u) * H x := by
        refine lintegral_congr fun x ↦ ?_
        rw [lintegral_mul_const (f := fun u ↦ k (x i₀ + u)) _ (hk.comp (measurable_const_add _)),
          hk1, one_mul]
    _ = ∫⁻ u : ℝ, ∫⁻ x, k (x i₀ + u) * H x :=
        lintegral_lintegral_swap ((hk.comp (((measurable_pi_apply i₀).comp measurable_fst).add
          measurable_snd)).aemeasurable.mul
          (hH.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst))
    _ = ∫⁻ u : ℝ, ∫⁻ z : ι → ℝ, k (z i₀) * H fun i ↦ z i - u := by
        refine lintegral_congr fun u ↦ ?_
        rw [← lintegral_sub_right_eq_self _ fun _ ↦ u]
        simp only [Pi.sub_apply, sub_add_cancel]
        -- `z - fun _ ↦ u` is `fun i ↦ z i - u` by definition.
        rfl
    _ = ∫⁻ z : ι → ℝ, ∫⁻ u : ℝ, k (z i₀) * H fun i ↦ z i - u :=
        lintegral_lintegral_swap ((hk.comp ((measurable_pi_apply i₀).comp
          measurable_snd)).aemeasurable.mul (hH.comp_quasiMeasurePreserving hsub))
    _ = ∫⁻ z : ι → ℝ, k (z i₀) * ∫⁻ u : ℝ, H fun i ↦ z i - u :=
        lintegral_congr fun z ↦ lintegral_const_mul' _ _ (by
          simp only [hkdef, indicator_apply]
          split_ifs <;> simp)

/-- **Decomposition of a weighted Lebesgue measure on `ι → ℝ` along the diagonal lines.** For a
measurable density `d` and an integrand `G` that is a.e. measurable for `volume.withDensity d`,
the lower integral of `G` against `volume.withDensity d` is the integral, against the indicator
of `z i₀ ∈ [0, 1]`, of the integrals of `d * G` along the lines `u ↦ z - u·1` in the parameter
`u`. -/
theorem lintegral_withDensity_eq_lintegral_indicator_mul_lintegral_sub_const {ι : Type*}
    [Fintype ι] (i₀ : ι) {d : (ι → ℝ) → ℝ≥0} (hd : Measurable d) {G : (ι → ℝ) → ℝ≥0∞}
    (hG : AEMeasurable G (volume.withDensity fun x ↦ d x)) :
    ∫⁻ x, G x ∂volume.withDensity (fun x ↦ d x) =
      ∫⁻ z : ι → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) *
        ∫⁻ u : ℝ, d (fun i ↦ z i - u) * G fun i ↦ z i - u := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hd.coe_nnreal_ennreal.aemeasurable hG]
  exact lintegral_eq_lintegral_indicator_mul_lintegral_sub_const i₀
    ((aemeasurable_withDensity_ennreal_iff hd).1 hG)

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
