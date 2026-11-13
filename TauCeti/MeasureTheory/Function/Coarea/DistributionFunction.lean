/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.MeasureTheory.Function.Coarea.Integral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Perfect
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Measurable

/-!
# The distribution function and regular level integrals

Let `h : E → ℝ` be a function on a finite-dimensional real inner product space of dimension `n`,
and let `R = {x | Dh(x) ≠ 0}` be its regular set, where `Dh` is the totalized Fréchet derivative
(zero at points of nondifferentiability). Weighting the regular part of the level surface
`{h = t}` by the reciprocal gradient norm gives the level integral

`m(t) = ∫_{R ∩ {h = t}} ‖Dh‖⁻¹ dHⁿ⁻¹`,

for the normalized Euclidean Hausdorff measure `Hⁿ⁻¹ = μHE[n - 1]`. By the coarea formula these
level integrals recover the volume of the regular part of every preimage:

`|h⁻¹(I) ∩ R| = ∫_I m(t) dt`

for every measurable `I ⊆ ℝ` (`MeasureTheory.volume_preimage_inter_setOf_fderiv_ne_zero`, in
`TauCeti.MeasureTheory.Function.Coarea.Integral`). No measurability, continuity or Lipschitz
hypothesis on `h` is needed.

The critical set `{Dh = 0}` can only add volume to the superlevel sets. So if the distribution
function `μ(t) = |{h > t}|` is finite for `t > 0`, it is differentiable at almost every `t > 0`,
and there

`m(t) ≤ -μ'(t)`

(`MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv`). This is the comparison of
the level integrals of a function with the derivative of its distribution function used in proofs
of the Pólya–Szegő inequality: by the coarea formula, a convex integral of the gradient
`∫ Φ(‖∇h‖)` is an integral over levels, and on each level Jensen's inequality and the
isoperimetric inequality bound the level contribution below in terms of `m(t)` and the perimeter
of `{h > t}`.

Equality holds when the critical values are negligible. If `h` is almost everywhere measurable
and the image `h({Dh = 0})` is a null set, then `m(t) = -μ'(t)` at almost every `t > 0`
(`MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv`). The critical set may
still have positive volume. Its contribution to the distribution function is the cumulative
function of the pushforward of volume on it under `h`. That measure is carried by the null set of
critical values, so it is singular, and by the Vitali differentiation theorem its ratio to
Lebesgue measure on small intervals tends to zero almost everywhere. This is the case of a radial
rearrangement, whose critical values form a null set.

## Main results

* `MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv`: `m(t) ≤ -μ'(t)` for almost
  every `t > 0`.
* `MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv`: `m(t) = -μ'(t)` for almost
  every `t > 0` when the critical values form a null set.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, arXiv:2206.09833, the proof of Theorem 5.8.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 (the coarea formula).
-/

public section

open MeasureTheory Measure Set Filter Module Function
open scoped ENNReal Topology

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {h : E → ℝ}

/-- The critical set only adds volume between two levels: for `u ≤ v`, the superlevel set
`{h > u}` contains `{h > v}` and the regular part of the slab `{u < h ≤ v}`, whose volume is the
integral of the level integrals over `(u, v]`. -/
private theorem measureReal_setOf_lt_add_toReal_setLIntegral_le {u v : ℝ} (huv : u ≤ v)
    (hu : volume {x | u < h x} ≠ ∞) :
    volume.real {x | v < h x} + (∫⁻ t in Ioc u v,
        ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
          ∂μHE[finrank ℝ E - 1]).toReal ≤
      volume.real {x | u < h x} := by
  have hle : volume {x | v < h x} + ∫⁻ t in Ioc u v,
        ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] ≤
      volume {x | u < h x} := by
    rw [← volume_preimage_inter_setOf_fderiv_ne_zero measurableSet_Ioc, ← measure_union
      (disjoint_left.2 fun x (hx : v < h x) (hx' : x ∈ h ⁻¹' Ioc u v ∩ _) ↦ not_lt.2 hx'.1.2 hx)
      (TauCeti.measurableSet_preimage_inter_setOf_fderiv_ne_zero measurableSet_Ioc)]
    exact measure_mono (union_subset (fun x hx ↦ huv.trans_lt hx) fun x hx ↦ hx.1.1)
  rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add
    (ne_top_of_le_ne_top hu (le_self_add.trans hle))
    (ne_top_of_le_ne_top hu (le_add_self.trans hle))]
  exact ENNReal.toReal_mono hu hle

/-- The level integrals depend almost everywhere measurably on the level. -/
private theorem aemeasurable_setLIntegral_inv_enorm_fderiv :
    AEMeasurable fun t ↦
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] := by
  have hR : MeasurableSet {x | fderiv ℝ h x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have := aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt (F := ℝ) volume
    hR.nullMeasurableSet
    (fun x hx ↦ (TauCeti.differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
    (measurable_fderiv ℝ h).eNorm.inv
  simpa only [finrank_self, Pi.inv_apply] using this

/-- Above a positive level `c`, the level integrals are a.e. finite and their real parts form an
integrable function whose interval integrals are the integrals of the level integrals. -/
private theorem integrable_indicator_Ioi_toReal_setLIntegral_inv_enorm_fderiv {c : ℝ}
    (hfin : volume {x | c < h x} ≠ ∞) :
    (∀ᵐ t ∂volume.restrict (Ioi c),
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] < ∞) ∧
    Integrable ((Ioi c).indicator fun t ↦ (∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
      ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]).toReal) ∧
    ∀ u v, c ≤ u → u ≤ v →
      ∫ t in u..v, (Ioi c).indicator (fun t ↦ (∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]).toReal) t =
      (∫⁻ t in Ioc u v, ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]).toReal := by
  set m : ℝ → ℝ≥0∞ := fun t ↦
    ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]
  have hm : AEMeasurable m := aemeasurable_setLIntegral_inv_enorm_fderiv
  -- The level integrals have finite integral over `(c, ∞)`.
  have hmc : ∫⁻ t in Ioi c, m t ≠ ∞ := by
    rw [← volume_preimage_inter_setOf_fderiv_ne_zero measurableSet_Ioi]
    exact ne_top_of_le_ne_top hfin (measure_mono fun x hx ↦ hx.1)
  have hfinite : ∀ᵐ t ∂volume.restrict (Ioi c), m t < ∞ := ae_lt_top' hm.restrict hmc
  refine ⟨hfinite, IntegrableOn.integrable_indicator
    (integrable_toReal_of_lintegral_ne_top hm.restrict hmc) measurableSet_Ioi,
    fun u v hu huv ↦ ?_⟩
  have hsub : Ioc u v ⊆ Ioi c := fun t ht ↦ hu.trans_lt ht.1
  rw [intervalIntegral.integral_of_le huv,
    setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ indicator_of_mem (hsub ht) _,
    integral_toReal hm.restrict (ae_restrict_of_ae_restrict_of_subset hsub hfinite)]

/-- The comparison `m(t) ≤ -μ'(t)` at almost every `t > c`, for a fixed `c > 0`. -/
private theorem ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv_of_lt {c : ℝ} (hc : 0 < c)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    ∀ᵐ t, c < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] ≤
        ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) := by
  obtain ⟨hfinite, hg, hint⟩ :=
    integrable_indicator_Ioi_toReal_setLIntegral_inv_enorm_fderiv (h := h) (hfin c hc)
  set m : ℝ → ℝ≥0∞ := fun t ↦
    ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]
  set μr : ℝ → ℝ := fun s ↦ volume.real {x | s < h x}
  set g : ℝ → ℝ := (Ioi c).indicator fun t ↦ (m t).toReal
  -- Between levels above `c`, `μr` drops by at least the integral of `g`.
  have hdrop {u v : ℝ} (hu : c < u) (huv : u ≤ v) : μr v + ∫ t in u..v, g t ≤ μr u := by
    rw [hint u v hu.le huv]
    exact measureReal_setOf_lt_add_toReal_setLIntegral_le huv (hfin u (hc.trans hu))
  -- Hence `μr + ∫_c g` is antitone above `c`.
  have hanti : AntitoneOn (fun u ↦ μr u + ∫ t in c..u, g t) (Ioi c) := fun u hu v _ huv ↦ by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (a := c) (b := u) (c := v)
      hg.intervalIntegrable hg.intervalIntegrable
    dsimp only
    linarith [hdrop hu huv]
  -- The distribution function is antitone, hence differentiable almost everywhere, above `0`.
  have hμr : AntitoneOn μr (Ioi 0) := fun u hu v _ huv ↦
    measureReal_mono (fun x hx ↦ huv.trans_lt hx) (hfin u hu)
  filter_upwards [hμr.neg.ae_differentiableWithinAt_of_mem,
    LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable,
    (ae_restrict_iff' measurableSet_Ioi).1 hfinite] with t hdiff hderiv hfin_t hct
  have hdμ : DifferentiableAt ℝ μr t := by
    simpa using ((hdiff (hc.trans hct)).differentiableAt (Ioi_mem_nhds (hc.trans hct))).neg
  have hacc : AccPt t (𝓟 (Ioi c)) := isOpen_Ioi.preperfect t hct
  have hnonpos :=
    ((hdμ.hasDerivAt.add (hderiv c)).hasDerivWithinAt).nonpos_of_antitoneOn hacc hanti
  have hgt : g t = (m t).toReal := indicator_of_mem hct _
  rw [hgt] at hnonpos
  have hle : (m t).toReal ≤ -deriv μr t := by linarith
  calc m t = ENNReal.ofReal (m t).toReal := (ENNReal.ofReal_toReal (hfin_t hct).ne).symm
    _ ≤ ENNReal.ofReal (-deriv μr t) := ENNReal.ofReal_le_ofReal hle

/-- **The level integrals are bounded by the derivative of the distribution function.** If the
superlevel sets `{h > t}` have finite volume for `t > 0`, then at almost every `t > 0`

`∫_{{h = t} ∩ {Dh ≠ 0}} ‖Dh‖⁻¹ dHⁿ⁻¹ ≤ -μ'(t)`,

where `μ(t) = |{h > t}|` is the distribution function. Since `μ` is antitone on `(0, ∞)`, it is
differentiable at almost every `t > 0`, so `deriv` is its actual derivative there. -/
theorem ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    ∀ᵐ t, 0 < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] ≤
        ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) := by
  have hk (k : ℕ) := ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv_of_lt
    (Nat.one_div_pos_of_nat (n := k)) hfin
  filter_upwards [ae_all_iff.2 hk] with t ht htpos
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt htpos
  exact ht k hk

/-- The exact drop of the distribution function between two levels `c ≤ u ≤ v`: the regular part
of the slab `{u < h ≤ v}` contributes the integral of the level integrals over `(u, v]`, and its
critical part is measured by the pushforward under `h` of volume on `{Dh = 0} ∩ {h > c}`. -/
private theorem measureReal_setOf_lt_eq_add_add {c u v : ℝ} (hh : AEMeasurable h)
    (hcu : c ≤ u) (huv : u ≤ v) (hu : volume {x | u < h x} ≠ ∞) :
    volume.real {x | u < h x} = volume.real {x | v < h x} +
      (∫⁻ t in Ioc u v, ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
          ∂μHE[finrank ℝ E - 1]).toReal +
      ((volume.restrict ({x | fderiv ℝ h x = 0} ∩ {x | c < h x})).map h).real (Ioc u v) := by
  have hR : MeasurableSet {x | fderiv ℝ h x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hI : NullMeasurableSet (h ⁻¹' Ioc u v) := hh.nullMeasurable measurableSet_Ioc
  -- The superlevel set `{h > u}` splits into `{h > v}` and the slab `{u < h ≤ v}`.
  have hsplit : volume {x | u < h x} = volume {x | v < h x} + volume (h ⁻¹' Ioc u v) := by
    have hunion : {x | u < h x} = h ⁻¹' Ioc u v ∪ {x | v < h x} :=
      (congrArg (h ⁻¹' ·) (Ioc_union_Ioi_eq_Ioi huv)).symm
    rw [hunion, measure_union₀' (t := {x | v < h x}) hI
      (Ioc_disjoint_Ioi_same.preimage h).aedisjoint, add_comm]
  -- The slab splits into its regular and critical parts.
  have hcrit : ((volume.restrict ({x | fderiv ℝ h x = 0} ∩ {x | c < h x})).map h) (Ioc u v) =
      volume (h ⁻¹' Ioc u v \ {x | fderiv ℝ h x ≠ 0}) := by
    rw [map_apply_of_aemeasurable hh.restrict measurableSet_Ioc,
      restrict_apply₀ (hh.restrict.nullMeasurable measurableSet_Ioc)]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, mem_ofPred_eq, Set.mem_sdiff, not_not]
    exact ⟨fun hx ↦ ⟨hx.1, hx.2.1⟩, fun hx ↦ ⟨hx.1, hx.2, hcu.trans_lt hx.1.1⟩⟩
  have hslab : volume (h ⁻¹' Ioc u v) = (∫⁻ t in Ioc u v,
        ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) +
      ((volume.restrict ({x | fderiv ℝ h x = 0} ∩ {x | c < h x})).map h) (Ioc u v) := by
    rw [hcrit, ← volume_preimage_inter_setOf_fderiv_ne_zero (h := h) measurableSet_Ioc,
      measure_inter_add_sdiff _ hR]
  rw [hslab, ← add_assoc] at hsplit
  have hfin := hsplit ▸ hu
  rw [measureReal_def, measureReal_def, measureReal_def, hsplit,
    ENNReal.toReal_add (ne_top_of_le_ne_top hfin le_self_add)
      (ne_top_of_le_ne_top hfin le_add_self),
    ENNReal.toReal_add (ne_top_of_le_ne_top hfin (le_self_add.trans le_self_add))
      (ne_top_of_le_ne_top hfin (le_add_self.trans le_self_add))]

/-- A locally finite measure on `ℝ` that is singular with respect to Lebesgue measure has right
difference quotients `ρ (t, t + δ] / δ` tending to zero at almost every `t`. -/
private theorem ae_tendsto_inv_mul_measureReal_Ioc_of_mutuallySingular {ρ : Measure ℝ}
    [IsLocallyFiniteMeasure ρ] (hρ : ρ ⟂ₘ volume) :
    ∀ᵐ t, Tendsto (fun δ : ℝ ↦ δ⁻¹ * ρ.real (Ioc t (t + δ))) (𝓝[>] 0) (𝓝 0) := by
  set v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1
  filter_upwards [v.ae_eventually_measure_zero_of_singular hρ] with t ht
  have hshift : Tendsto (fun δ : ℝ ↦ t + δ) (𝓝[>] 0) (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_const_add t).tendsto' 0 t (add_zero t)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) ↦ lt_add_of_pos_right t hδ)
  refine squeeze_zero' (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) ↦ by positivity)
    (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) ↦ ?_)
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (ht.comp ((Real.tendsto_Icc_vitaliFamily_right t).comp hshift)))
  calc δ⁻¹ * ρ.real (Ioc t (t + δ)) ≤ δ⁻¹ * ρ.real (Icc t (t + δ)) := by
        gcongr
        exacts [measure_Icc_lt_top.ne, Ioc_subset_Icc_self]
    _ = (ρ (Icc t (t + δ)) / volume (Icc t (t + δ))).toReal := by
        simp [ENNReal.toReal_div, measureReal_def, hδ.le, inv_mul_eq_div]

/-- The equality `m(t) = -μ'(t)` at almost every `t > c`, for a fixed `c > 0`, when the critical
values of `h` form a null set. -/
private theorem ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv_of_lt (hh : AEMeasurable h)
    {c : ℝ} (hc : 0 < c) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    (hcrit : volume (h '' {x | fderiv ℝ h x = 0}) = 0) :
    ∀ᵐ t, c < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] =
        ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) := by
  obtain ⟨hfinite, hg, hint⟩ :=
    integrable_indicator_Ioi_toReal_setLIntegral_inv_enorm_fderiv (h := h) (hfin c hc)
  set m : ℝ → ℝ≥0∞ := fun t ↦
    ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]
  set μr : ℝ → ℝ := fun s ↦ volume.real {x | s < h x}
  set g : ℝ → ℝ := (Ioi c).indicator fun t ↦ (m t).toReal
  -- The critical part of `{h > c}`, pushed forward to the levels, is a finite measure.
  set S := {x | fderiv ℝ h x = 0} ∩ {x | c < h x}
  set ρ := (volume.restrict S).map h
  have : IsFiniteMeasure ρ := ⟨by
    rw [map_apply_of_aemeasurable hh.restrict MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    exact (measure_mono inter_subset_right).trans_lt (hfin c hc).lt_top⟩
  -- It is carried by the null set of critical values, so it is singular.
  have hsing : ρ ⟂ₘ volume := by
    obtain ⟨N, hCN, hN, hN0⟩ := exists_measurable_superset_of_null hcrit
    refine ⟨Nᶜ, hN.compl, ?_, by rwa [compl_compl]⟩
    have hS : NullMeasurableSet S :=
      ((measurableSet_singleton 0).preimage (measurable_fderiv ℝ h)).nullMeasurableSet.inter
        (nullMeasurableSet_lt aemeasurable_const hh)
    rw [map_apply_of_aemeasurable hh.restrict hN.compl]
    refine measure_mono_null ?_ (ae_iff.1 (ae_restrict_mem₀ hS))
    exact fun x hx hxS ↦ hx (hCN (mem_image_of_mem h hxS.1))
  -- Above `c`, the distribution function plus the integral of `g` drops exactly by `ρ`.
  have hdrop {u v : ℝ} (hu : c < u) (huv : u ≤ v) :
      (μr v + ∫ s in c..v, g s) - (μr u + ∫ s in c..u, g s) = -ρ.real (Ioc u v) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (a := c) (b := u) (c := v)
      hg.intervalIntegrable hg.intervalIntegrable
    have heq : μr u = μr v + (∫⁻ t in Ioc u v, m t).toReal + ρ.real (Ioc u v) :=
      measureReal_setOf_lt_eq_add_add hh hu.le huv (hfin u (hc.trans hu))
    linarith [hint u v hu.le huv]
  have hμr : AntitoneOn μr (Ioi 0) := fun u hu v _ huv ↦
    measureReal_mono (fun x hx ↦ huv.trans_lt hx) (hfin u hu)
  filter_upwards [hμr.neg.ae_differentiableWithinAt_of_mem,
    LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable,
    (ae_restrict_iff' measurableSet_Ioi).1 hfinite,
    ae_tendsto_inv_mul_measureReal_Ioc_of_mutuallySingular hsing] with t hdiff hderiv hfin_t hρt hct
  have hdμ : DifferentiableAt ℝ μr t := by
    simpa using ((hdiff (hc.trans hct)).differentiableAt (Ioi_mem_nhds (hc.trans hct))).neg
  have hF := (hdμ.hasDerivAt.add (hderiv c)).tendsto_slope_zero_right
  -- The right difference quotients of `μr + ∫_c g` at `t` are those of `-ρ`, which tend to `0`.
  have hzero : Tendsto (fun δ : ℝ ↦ δ⁻¹ •
      ((μr (t + δ) + ∫ s in c..t + δ, g s) - (μr t + ∫ s in c..t, g s))) (𝓝[>] 0) (𝓝 0) := by
    refine (neg_zero (G := ℝ) ▸ hρt.neg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [hdrop hct (by linarith), smul_eq_mul, mul_neg]
  have hsum : deriv μr t + g t = 0 := tendsto_nhds_unique hF hzero
  rw [show g t = (m t).toReal from indicator_of_mem hct _] at hsum
  calc m t = ENNReal.ofReal (m t).toReal := (ENNReal.ofReal_toReal (hfin_t hct).ne).symm
    _ = ENNReal.ofReal (-deriv μr t) := by congr 1; linarith

/-- **The level integrals equal the derivative of the distribution function** when the critical
values are negligible. Let `h` be almost everywhere measurable, with superlevel sets `{h > t}` of
finite volume for `t > 0`, and suppose that the image under `h` of its critical set `{Dh = 0}` is
a null set. Then at almost every `t > 0`

`∫_{{h = t} ∩ {Dh ≠ 0}} ‖Dh‖⁻¹ dHⁿ⁻¹ = -μ'(t)`,

where `μ(t) = |{h > t}|` is the distribution function. The critical set may have positive volume;
its contribution to `μ` is then a singular function of the level, with derivative zero almost
everywhere. -/
theorem ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv (hh : AEMeasurable h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    (hcrit : volume (h '' {x | fderiv ℝ h x = 0}) = 0) :
    ∀ᵐ t, 0 < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] =
        ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) := by
  have hk (k : ℕ) := ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv_of_lt hh
    (Nat.one_div_pos_of_nat (n := k)) hfin hcrit
  filter_upwards [ae_all_iff.2 hk] with t ht htpos
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt htpos
  exact ht k hk

end MeasureTheory
