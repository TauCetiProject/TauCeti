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
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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
of `{h > t}`. When the critical values `h '' {Dh = 0}` form a Lebesgue-null set and `h` is
almost everywhere measurable, the pushforward of volume on `{Dh = 0}` is mutually singular with
respect to Lebesgue measure, and equality `m(t) = -μ'(t)` holds for almost every `t > 0`
(`MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv`).

## Main results

* `MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv`: `m(t) ≤ -μ'(t)` for almost
  every `t > 0`.
* `MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv`: `m(t) = -μ'(t)` for almost
  every `t > 0` when `h '' {Dh = 0}` has Lebesgue measure zero.

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

/-- The comparison `m(t) ≤ -μ'(t)` at almost every `t > c`, for a fixed `c > 0`. -/
private theorem ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv_of_lt {c : ℝ} (hc : 0 < c)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    ∀ᵐ t, c < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] ≤
        ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) := by
  set R := {x | fderiv ℝ h x ≠ 0}
  set m : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ x in R ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]
  set μr : ℝ → ℝ := fun s ↦ volume.real {x | s < h x}
  have hR : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hm : AEMeasurable m := by
    have := aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt (F := ℝ) volume
      hR.nullMeasurableSet
      (fun x hx ↦ (TauCeti.differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
      (measurable_fderiv ℝ h).eNorm.inv
    simpa only [finrank_self, Pi.inv_apply] using this
  -- The level integrals have finite integral over `(c, ∞)`.
  have hmc : ∫⁻ t in Ioi c, m t ≠ ∞ := by
    rw [← volume_preimage_inter_setOf_fderiv_ne_zero measurableSet_Ioi]
    exact ne_top_of_le_ne_top (hfin c hc) (measure_mono fun x hx ↦ hx.1)
  have hfinite : ∀ᵐ t ∂volume.restrict (Ioi c), m t < ∞ := ae_lt_top' hm.restrict hmc
  let g : ℝ → ℝ := (Ioi c).indicator fun t ↦ (m t).toReal
  have hg : Integrable g := IntegrableOn.integrable_indicator
    (integrable_toReal_of_lintegral_ne_top hm.restrict hmc) measurableSet_Ioi
  -- Between levels above `c`, `μr` drops by at least the integral of `g`.
  have hdrop {u v : ℝ} (hu : c < u) (huv : u ≤ v) : μr v + ∫ t in u..v, g t ≤ μr u := by
    have hsub : Ioc u v ⊆ Ioi c := fun t ht ↦ hu.trans ht.1
    have hint : ∫ t in u..v, g t = (∫⁻ t in Ioc u v, m t).toReal := by
      rw [intervalIntegral.integral_of_le huv,
        setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ indicator_of_mem (hsub ht) _,
        integral_toReal hm.restrict (ae_restrict_of_ae_restrict_of_subset hsub hfinite)]
    rw [hint]
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

/-- The cumulative function of a finite Borel measure on `ℝ` mutually singular with respect to
Lebesgue measure has zero derivative almost everywhere. -/
private theorem ae_hasDerivAt_measureReal_Iic_zero_of_mutuallySingular {σ : Measure ℝ}
    [IsFiniteMeasure σ] (hσ : σ ⟂ₘ volume) :
    ∀ᵐ t, HasDerivAt (fun u ↦ σ.real (Iic u)) 0 t := by
  let S : StieltjesFunction ℝ :=
    { toFun u := σ.real (Iic u)
      mono' _ _ huv := measureReal_mono (Iic_subset_Iic.2 huv)
      right_continuous' u := by
        rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
        have hI : (⋂ r > u, Iic r) = Iic u := Subset.antisymm
          (fun _ hy ↦ le_of_forall_gt_imp_ge_of_dense fun r hru ↦ mem_iInter₂.1 hy r hru)
          (fun _ hy ↦ mem_iInter₂.2 fun _ hru ↦ hy.trans hru.le)
        have hlim := tendsto_measure_biInter_gt (μ := σ) (s := Iic) (a := u)
          (fun _ _ ↦ nullMeasurableSet_Iic) (fun _ _ _ ↦ Iic_subset_Iic.2)
          ⟨u + 1, by linarith, measure_ne_top σ _⟩
        rw [hI] at hlim
        exact (ENNReal.tendsto_toReal (measure_ne_top σ _)).comp hlim }
  have hS : S.measure = σ := S.measure.ext_of_Ioc σ fun a b hab ↦ by
    rw [S.measure_Ioc, ← Iic_sdiff_Iic]
    change ENNReal.ofReal (σ.real (Iic b) - σ.real (Iic a)) = σ (Iic b \ Iic a)
    rw [← measureReal_sdiff (Iic_subset_Iic.2 hab.le) measurableSet_Iic, ofReal_measureReal]
  filter_upwards [S.ae_hasDerivAt,
    Measure.rnDeriv_eq_zero_of_mutuallySingular hσ .rfl] with t ht h0
  simpa [S, hS, h0] using ht

/-- When `h '' {Dh = 0}` has Lebesgue measure zero, `-μ'(t) ≤ m(t)` at almost every `t > c`, for a
fixed `c > 0`. -/
private theorem ae_ofReal_neg_deriv_le_setLIntegral_inv_enorm_fderiv_of_lt
    (hh : AEMeasurable h volume) {c : ℝ} (hc : 0 < c)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    (hcrit : volume (h '' {x | fderiv ℝ h x = 0}) = 0) :
    ∀ᵐ t, c < t →
      ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) ≤
        ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
          ∂μHE[finrank ℝ E - 1] := by
  set R := {x | fderiv ℝ h x ≠ 0}
  set C := {x | fderiv ℝ h x = 0}
  set Ac := {x | c < h x} ∩ C
  set m : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ x in R ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]
  set μr : ℝ → ℝ := fun s ↦ volume.real {x | s < h x}
  have hR : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hAc : NullMeasurableSet Ac volume := (nullMeasurableSet_lt aemeasurable_const hh).inter
    ((measurableSet_singleton 0).preimage (measurable_fderiv ℝ h)).nullMeasurableSet
  let ν : Measure E := volume.restrict Ac
  have : IsFiniteMeasure ν := ⟨(Measure.restrict_apply_univ Ac).trans_lt
    ((measure_mono inter_subset_left).trans_lt (hfin c hc).lt_top)⟩
  let σ : Measure ℝ := Measure.map h ν
  have : IsFiniteMeasure σ :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hh.restrict .univ]; exact measure_lt_top ν _⟩
  have hσ_sing : σ ⟂ₘ volume := by
    let N := toMeasurable volume (h '' C)
    refine ⟨Nᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      by rw [compl_compl, measure_toMeasurable, hcrit]⟩
    rw [Measure.map_apply_of_aemeasurable hh.restrict (measurableSet_toMeasurable _ _).compl,
      Measure.restrict_apply₀' hAc, eq_empty_of_forall_notMem
        (fun x (hx : x ∈ h ⁻¹' Nᶜ ∩ Ac) ↦ hx.1 (subset_toMeasurable _ _ ⟨x, hx.2.2, rfl⟩)),
      measure_empty]
  have hm : AEMeasurable m := by
    simpa only [finrank_self, Pi.inv_apply] using
      aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt (F := ℝ) volume hR.nullMeasurableSet
        (fun _ hx ↦ (TauCeti.differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
        (measurable_fderiv ℝ h).eNorm.inv
  have hmc : ∫⁻ t in Ioi c, m t ≠ ∞ := by
    rw [← volume_preimage_inter_setOf_fderiv_ne_zero measurableSet_Ioi]
    exact ne_top_of_le_ne_top (hfin c hc) (measure_mono fun _ hx ↦ hx.1)
  have hfinite : ∀ᵐ t ∂volume.restrict (Ioi c), m t < ∞ := ae_lt_top' hm.restrict hmc
  let g : ℝ → ℝ := (Ioi c).indicator fun t ↦ (m t).toReal
  have hg : Integrable g := IntegrableOn.integrable_indicator
    (integrable_toReal_of_lintegral_ne_top hm.restrict hmc) measurableSet_Ioi
  have hmono : MonotoneOn (fun u ↦ μr u + (∫ t in c..u, g t) + σ.real (Iic u)) (Ioi c) :=
    fun u hu v _ huv ↦ by
      have hsub : Ioc u v ⊆ Ioi c := fun _ ht ↦ hu.trans ht.1
      have hcov : {x | u < h x} ⊆ ({x | v < h x} ∪ (h ⁻¹' Ioc u v ∩ R)) ∪ (h ⁻¹' Ioc u v ∩ Ac) := by
        intro x hx
        rcases lt_or_ge v (h x) with hvx | hvx
        · exact .inl (.inl hvx)
        · by_cases hxR : x ∈ R
          · exact .inl (.inr ⟨⟨hx, hvx⟩, hxR⟩)
          · exact .inr ⟨⟨hx, hvx⟩, hu.trans hx, by simpa [R, C] using hxR⟩
      have hvol : volume {x | u < h x} ≤ (volume {x | v < h x} + ∫⁻ t in Ioc u v, m t) +
          σ (Ioc u v) := by
        rw [← volume_preimage_inter_setOf_fderiv_ne_zero measurableSet_Ioc,
          Measure.map_apply_of_aemeasurable hh.restrict measurableSet_Ioc,
          Measure.restrict_apply₀' hAc]
        exact (measure_mono hcov).trans ((measure_union_le _ _).trans
          (add_le_add_left (measure_union_le _ _) _))
      have hm_uv : ∫⁻ t in Ioc u v, m t ≠ ∞ := ne_top_of_le_ne_top hmc (lintegral_mono_set hsub)
      have hv_fin : volume {x | v < h x} ≠ ∞ := hfin v ((hc.trans hu).trans_le huv)
      have hreal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hv_fin, hm_uv⟩, measure_ne_top σ _⟩) hvol
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hv_fin, hm_uv⟩) (measure_ne_top σ _),
        ENNReal.toReal_add hv_fin hm_uv] at hreal
      have hint : ∫ t in u..v, g t = (∫⁻ t in Ioc u v, m t).toReal := by
        rw [intervalIntegral.integral_of_le huv,
          setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ indicator_of_mem (hsub ht) _,
          integral_toReal hm.restrict (ae_restrict_of_ae_restrict_of_subset hsub hfinite)]
      have hσ_uv : (σ (Ioc u v)).toReal = σ.real (Iic v) - σ.real (Iic u) := by
        rw [← Iic_sdiff_Iic]; exact measureReal_sdiff (Iic_subset_Iic.2 huv) measurableSet_Iic
      have hadd := intervalIntegral.integral_add_adjacent_intervals (a := c) (b := u) (c := v)
        hg.intervalIntegrable hg.intervalIntegrable
      simp only [μr, measureReal_def] at hσ_uv ⊢
      linarith [hreal, hint, hσ_uv, hadd]
  have hμr : AntitoneOn μr (Ioi 0) := fun u hu _ _ huv ↦
    measureReal_mono (fun _ hx ↦ huv.trans_lt hx) (hfin u hu)
  filter_upwards [hμr.neg.ae_differentiableWithinAt_of_mem,
    LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable,
    ae_hasDerivAt_measureReal_Iic_zero_of_mutuallySingular hσ_sing] with t hdiff hderiv hS hct
  have hdμ : DifferentiableAt ℝ μr t := by
    simpa using ((hdiff (hc.trans hct)).differentiableAt (Ioi_mem_nhds (hc.trans hct))).neg
  have hnonneg := (((hdμ.hasDerivAt.add (hderiv c)).add hS).hasDerivWithinAt).nonneg_of_monotoneOn
    (isOpen_Ioi.preperfect t hct) hmono
  dsimp only [g] at hnonneg
  rw [indicator_of_mem hct, add_zero] at hnonneg
  exact (ENNReal.ofReal_le_ofReal (by linarith : -deriv μr t ≤ (m t).toReal)).trans
    ENNReal.ofReal_toReal_le

/-- **Equality of regular level integrals and the negated derivative of the distribution function.**
If `h` is almost everywhere measurable, its positive superlevel sets have finite volume, and its
critical values `h '' {Dh = 0}` form a Lebesgue-null set, then at almost every `t > 0`

`∫_{{h = t} ∩ {Dh ≠ 0}} ‖Dh‖⁻¹ dHⁿ⁻¹ = -μ'(t)`,

where `μ(t) = |{h > t}|` is the distribution function. -/
theorem ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv
    (hh : AEMeasurable h volume) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    (hcrit : volume (h '' {x | fderiv ℝ h x = 0}) = 0) :
    ∀ᵐ t, 0 < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] =
        ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) := by
  have hk (k : ℕ) := ae_ofReal_neg_deriv_le_setLIntegral_inv_enorm_fderiv_of_lt hh
    (Nat.one_div_pos_of_nat (n := k)) hfin hcrit
  filter_upwards [ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin,
    ae_all_iff.2 hk] with t hle hge htpos
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt htpos
  exact le_antisymm (hle htpos) (hge k hk)

end MeasureTheory
