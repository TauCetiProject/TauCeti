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
import TauCeti.Analysis.InnerProductSpace.NormDet

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

for every measurable `I ⊆ ℝ` (`MeasureTheory.volume_preimage_inter_setOf_fderiv_ne_zero`). No
measurability, continuity or Lipschitz hypothesis on `h` is needed.

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

## Main results

* `MeasureTheory.measurableSet_preimage_inter_setOf_fderiv_ne_zero`: the regular part of the
  preimage of a measurable set is measurable.
* `MeasureTheory.volume_preimage_inter_setOf_fderiv_ne_zero`: the volume of the regular part of
  `h⁻¹(I)` is the integral of the level integrals over `I`.
* `MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv`: `m(t) ≤ -μ'(t)` for almost
  every `t > 0`.

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A function is differentiable wherever its totalized derivative does not vanish. -/
private theorem differentiableAt_of_fderiv_ne_zero {x : E} (hx : fderiv ℝ h x ≠ 0) :
    DifferentiableAt ℝ h x := by
  by_contra hnd
  exact hx (fderiv_zero_of_not_differentiableAt hnd)

/-- The regular part `h⁻¹(I) ∩ {Dh ≠ 0}` of the preimage of a measurable set is measurable, for
every function `h`: the function is continuous on its regular set, which is measurable. -/
theorem measurableSet_preimage_inter_setOf_fderiv_ne_zero {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet (h ⁻¹' I ∩ {x | fderiv ℝ h x ≠ 0}) := by
  classical
  have hR : MeasurableSet {x | fderiv ℝ h x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hk : Measurable ({x | fderiv ℝ h x ≠ 0}.piecewise h 0) :=
    ContinuousOn.measurable_piecewise
      (fun x hx ↦ (differentiableAt_of_fderiv_ne_zero hx).continuousAt.continuousWithinAt)
      continuousOn_const hR
  convert (hk hI).inter hR using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, and_congr_left_iff]
  intro hx
  rw [piecewise_eq_of_mem _ _ _ hx]

/-- **The coarea formula for the regular part of a preimage.** For every function `h` and
measurable set `I`, the volume of the regular part `h⁻¹(I) ∩ {Dh ≠ 0}` is the integral over `I`
of the level integrals `∫_{{h = t} ∩ {Dh ≠ 0}} ‖Dh‖⁻¹ dHⁿ⁻¹`. Both sides may be infinite. -/
theorem volume_preimage_inter_setOf_fderiv_ne_zero {I : Set ℝ} (hI : MeasurableSet I) :
    volume (h ⁻¹' I ∩ {x | fderiv ℝ h x ≠ 0}) =
      ∫⁻ t in I, ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
        ∂μHE[finrank ℝ E - 1] := by
  set R := {x | fderiv ℝ h x ≠ 0}
  have hR : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hsurj (x : E) (hx : x ∈ R) : Surjective (fderiv ℝ h x) := fun y ↦ by
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hx
    exact ⟨(y / fderiv ℝ h x v) • v, by simp [div_mul_cancel₀ y hv]⟩
  -- The weight `1_I(h) ‖Dh‖⁻¹`, written through a measurable function agreeing with `h` on `R`.
  let w : E → ℝ≥0∞ := (h ⁻¹' I ∩ R).indicator fun x ↦ ‖fderiv ℝ h x‖ₑ⁻¹
  have hw : Measurable w := (measurable_fderiv ℝ h).enorm.inv.indicator
    (measurableSet_preimage_inter_setOf_fderiv_ne_zero hI)
  have hcoarea := lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hR.nullMeasurableSet (fun x hx ↦ differentiableAt_of_fderiv_ne_zero hx) hsurj hw
  rw [finrank_self] at hcoarea
  -- On `R` the coarea Jacobian `‖Dh‖` cancels the weight.
  have hlhs : ∫⁻ x in R, ENNReal.ofReal (fderiv ℝ h x).adjoint.normDet * w x =
      ∫⁻ x in R, (h ⁻¹' I ∩ R).indicator 1 x := by
    refine setLIntegral_congr_fun hR fun x hx ↦ ?_
    dsimp only [w]
    by_cases hxI : x ∈ h ⁻¹' I ∩ R
    · rw [indicator_of_mem hxI, indicator_of_mem hxI,
        ContinuousLinearMap.normDet_adjoint_eq_norm, Pi.one_apply, ofReal_norm]
      exact ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 hx)) (by simp)
    · rw [indicator_of_notMem hxI, indicator_of_notMem hxI, mul_zero]
  -- On the fiber over `t` the weight is `‖Dh‖⁻¹` if `t ∈ I` and zero otherwise.
  have hrhs (t : ℝ) : ∫⁻ x in R ∩ h ⁻¹' {t}, w x ∂μHE[finrank ℝ E - 1] =
      I.indicator (fun t ↦ ∫⁻ x in R ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) t := by
    have hfib : MeasurableSet (R ∩ h ⁻¹' {t}) := by
      rw [inter_comm]
      exact measurableSet_preimage_inter_setOf_fderiv_ne_zero (measurableSet_singleton t)
    dsimp only [w]
    by_cases htI : t ∈ I
    · rw [indicator_of_mem htI]
      refine setLIntegral_congr_fun hfib fun x hx ↦ ?_
      have hxt : h x = t := hx.2
      exact indicator_of_mem (show x ∈ h ⁻¹' I ∩ R from ⟨by rwa [mem_preimage, hxt], hx.1⟩) _
    · rw [indicator_of_notMem htI]
      refine (setLIntegral_congr_fun hfib fun x hx ↦ ?_).trans (lintegral_zero)
      have hxt : h x = t := hx.2
      refine indicator_of_notMem (show x ∉ h ⁻¹' I ∩ R from fun h' ↦ htI ?_) _
      rw [← hxt]
      exact h'.1
  have hm := measurableSet_preimage_inter_setOf_fderiv_ne_zero (h := h) hI
  rw [hlhs, lintegral_indicator_one hm, restrict_apply hm, inter_assoc, inter_self] at hcoarea
  rw [hcoarea, lintegral_congr hrhs]
  exact lintegral_indicator hI _

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
      (measurableSet_preimage_inter_setOf_fderiv_ne_zero measurableSet_Ioc)]
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
      (fun x hx ↦ (differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
      (measurable_fderiv ℝ h).enorm.inv
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
  have hacc : AccPt t (𝓟 (Ioi c)) := accPt_iff_nhds.2 fun U hU ↦ by
    have hmem : U ∩ Ioi c ∩ Ioi t ∈ 𝓝[>] t :=
      inter_mem (mem_nhdsWithin_of_mem_nhds (inter_mem hU (Ioi_mem_nhds hct))) self_mem_nhdsWithin
    obtain ⟨y, hy, hty⟩ := Filter.nonempty_of_mem hmem
    exact ⟨y, hy, hty.ne'⟩
  have hnonpos :=
    ((hdμ.hasDerivAt.add (hderiv c)).hasDerivWithinAt).nonpos_of_antitoneOn hacc hanti
  rw [show g t = (m t).toReal from indicator_of_mem hct _] at hnonpos
  change m t ≤ _
  rw [← ENNReal.ofReal_toReal (hfin_t hct).ne]
  exact ENNReal.ofReal_le_ofReal (by linarith)

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

end MeasureTheory
