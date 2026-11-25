/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Nemytskii.Basic
public import TauCeti.Analysis.Sobolev.Circle.RealBilinear
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.Sobolev.Circle.OfContinuousMap
import TauCeti.Analysis.Sobolev.Circle.Slobodeckij
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.CompactOpen

/-!
# Sobolev membership and compact-range bounds for `C^n` Nemytskii maps on the circle

For `s > 1/2`, this file proves that postcomposition `u ↦ f ∘ u` by a `C^n` map `f : E → F`
(`⌊2s⌋₊ ≤ n`) between finite-dimensional complex normed spaces preserves `H^s`, with uniform norm
bounds on compact-range bounded subsets: for `1/2 < s < 1` via Euclidean `L²` comparison of
`CircleSobolev.slobodeckijEnergy`, and for general `s > 1/2` by half-integer bootstrap pairing
`(df) ∘ u` with `u'` via `CircleSobolev.realConvolutionAsym` and Ehrling's inequality. Smoothness
of `nemytskii f` is proved in `TauCeti/Analysis/Sobolev/Circle/Nemytskii/Smooth.lean`.

## Main statements

* `TauCeti.CircleSobolev.toContinuousMap_nemytskii_of_contDiffOn`,
  `exists_norm_nemytskii_le_of_isCompact`, and `nemytskii_comp_of_contDiffOn`.

## References

* M. E. Taylor, *Partial Differential Equations III*, Springer, 2011, Chapter 13, Section 3.
* T. Runst and W. Sickel, *Sobolev Spaces of Fractional Order, Nemytskij Operators, and Nonlinear
  Partial Differential Equations*, de Gruyter, 1996, Chapter 5.
-/

public section

noncomputable section

open MeasureTheory Complex Filter Set
open scoped ContDiff ENNReal NNReal Real Topology

universe u v

namespace TauCeti
namespace CircleSobolev

/-- Every finite-dimensional complex normed space is complete, supplying `[CompleteSpace G]` for
continuous representatives on `CircleSobolev s G`. -/
local instance instCompleteSpaceOfFiniteDimensional {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [FiniteDimensional ℂ G] : CompleteSpace G :=
  FiniteDimensional.completeSpace ℂ G

private instance {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] :
    FiniteDimensional ℝ G := Module.Finite.trans ℂ G

private instance {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂] :
    FiniteDimensional ℂ (G₁ →L[ℝ] G₂) :=
  ContinuousLinearMap.finiteDimensional_of_smulCommClass

/-! ### Action of Nemytskii maps on continuous linear operators -/

section Linear

variable {s : ℝ} [hs : Fact (1 / 2 < s)] {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Nemytskii map of a continuous real-linear operator `Ψ : E →L[ℝ] F` is `mapRealCLM Ψ`. -/
@[simp] theorem nemytskii_continuousLinearMap_real (Ψ : E →L[ℝ] F) (u : CircleSobolev s E) :
    nemytskii (Ψ : E → F) u = mapRealCLM Ψ u :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  nemytskii_eq_of_forall_toContinuousMap_apply 1 fun x ↦
    toContinuousMap_mapRealCLM_apply 1 hs.out Ψ u x

/-- The Nemytskii map of a continuous complex-linear operator `L : E →L[ℂ] F` is `mapCLM L`. -/
@[simp] theorem nemytskii_continuousLinearMap (L : E →L[ℂ] F) (u : CircleSobolev s E) :
    nemytskii (L : E → F) u = mapCLM L u := by
  rw [← mapRealCLM_restrictScalars L u]
  exact nemytskii_continuousLinearMap_real (L.restrictScalars ℝ) u

end Linear

/-! ### Fractional base case `1/2 < s < 1` via Gagliardo–Slobodeckij energy -/

section BaseCase

variable (T : ℝ) [hT : Fact (0 < T)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private theorem slobodeckijEnergy_ofContinuousMap_comp_le {s : ℝ} (hs : 1 / 2 < s) {K : Set E}
    {L : ℝ≥0} {f : E → F} (hLip : LipschitzOnWith L f K) {C₀ : ℝ}
    (hpt0 : ∀ {M : ℝ} (ψ : C(AddCircle T, F)) (υ : C(AddCircle T, E)),
      (∀ x, ‖ψ x‖ ≤ M * ‖υ x‖) → ‖ofContinuousMap T ψ‖ ≤ C₀ * M * ‖ofContinuousMap T υ‖)
    {u : CircleSobolev s E} (huK : ∀ x, toContinuousMap T hs u x ∈ K)
    (fu : C(AddCircle T, F)) (hfu : ∀ x, fu x = f (toContinuousMap T hs u x)) :
    slobodeckijEnergy T s (ofContinuousMap T fu) ≤ ENNReal.ofReal ((C₀ * L) ^ 2) *
      slobodeckijEnergy T s (inclusion (by linarith : (0 : ℝ) ≤ s) u) := by
  rw [slobodeckijEnergy_def, slobodeckijEnergy_def,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun h ↦ ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_div_assoc', ← mul_pow]; gcongr
  rw [rotate_ofContinuousMap, ← map_sub, ← ofContinuousMap_toContinuousMap T hs u,
    rotate_ofContinuousMap, ← map_sub]
  refine hpt0 _ _ fun x ↦ ?_
  simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight, hfu]
  exact hLip.norm_sub_le (huK (x + h)) (huK x)

private theorem exists_toContinuousMap_eq_comp_and_norm_le_base {s : ℝ} (hs : 1 / 2 < s)
    (hs1 : s < 1) {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) (R : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
      (∀ x, toContinuousMap T hs u x ∈ K) → ‖u‖ ≤ R → ∃ w : CircleSobolev s F,
        (∀ x, toContinuousMap T hs w x = f (toContinuousMap T hs u x)) ∧ ‖w‖ ≤ B := by
  have hs0 : 0 < s := by linarith
  obtain ⟨C₀, _, hpt0⟩ := exists_norm_ofContinuousMap_le_of_forall_norm_le (E := E) (G := F) T
  obtain ⟨L, hLip⟩ : ∃ L : ℝ≥0, LipschitzOnWith L f K :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK fun x hx ↦
      let ⟨L, t, ht, hL⟩ := (hf.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
      ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKU)
  set M := max M₀ 0
  obtain ⟨CE, _, hSlobE⟩ := exists_slobodeckijEnergy_le (E := E) T hs0 hs1
  obtain ⟨CN, hCN_top, hNormSq⟩ := exists_norm_sq_le_slobodeckijEnergy (E := F) T hs0.le
  set Bsq := (‖ofContinuousMap T (E := F)‖ * M) ^ 2 + CN.toReal * ((C₀ * L) ^ 2 * (CE * R ^ 2))
  refine ⟨√Bsq, Real.sqrt_nonneg _, fun u huK huR ↦ ?_⟩
  let fu : C(AddCircle T, F) := ⟨fun x ↦ f (toContinuousMap T hs u x),
    hf.continuousOn.comp_continuous (toContinuousMap T hs u).continuous fun x ↦ hKU (huK x)⟩
  set c : CircleSobolev 0 F := ofContinuousMap T fu with hc
  have hc_norm : ‖c‖ ≤ ‖ofContinuousMap T (E := F)‖ * M :=
    (ofContinuousMap T).le_opNorm fu |>.trans (mul_le_mul_of_nonneg_left
      ((ContinuousMap.norm_le _ (le_max_right _ _)).2 fun x ↦
        (hM₀ _ (huK x)).trans (le_max_left _ _)) (norm_nonneg _))
  have hSlob_c : slobodeckijEnergy T s c ≤ ENNReal.ofReal ((C₀ * L) ^ 2 * (CE * R ^ 2)) := by
    refine (slobodeckijEnergy_ofContinuousMap_comp_le T hs hLip hpt0 huK fu fun _ ↦ rfl).trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _)]; gcongr
    exact (hSlobE u).trans (ENNReal.ofReal_le_ofReal (by gcongr))
  obtain ⟨w, hw⟩ := (exists_inclusion_eq_iff_slobodeckijEnergy_ne_top T hs0 hs1 c).2
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSlob_c)
  have hwc : toContinuousMap T hs w = fu := (toContinuousMap_eq_iff T hs w fu).2 fun n ↦ by
    rw [← coeff_ofContinuousMap T, ← hc, ← hw, coeff_inclusion]
  refine ⟨w, fun x ↦ congrArg (· x) hwc, (Real.le_sqrt (norm_nonneg w) (by positivity)).2 <|
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ?_⟩
  refine (by simpa only [hw] using hNormSq w : ENNReal.ofReal (‖w‖ ^ 2) ≤ _).trans
    ((by gcongr : _ ≤ ENNReal.ofReal ((‖ofContinuousMap T (E := F)‖ * M) ^ 2) +
      CN * ENNReal.ofReal ((C₀ * L) ^ 2 * (CE * R ^ 2))).trans_eq ?_)
  rw [← ENNReal.ofReal_toReal hCN_top, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_add (sq_nonneg _) (by positivity)]

end BaseCase

/-! ### Inductive bootstrap to all supercritical orders `s > 1/2` -/

section Bootstrap

variable (T : ℝ) [hT : Fact (0 < T)]

section BootstrapChain

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private theorem coeff_realConvolutionAsym_sum_single {t r' r s : ℝ} (ht : 0 ≤ t)
    (htr' : t + 1 / 2 < r') (hr'r : r' < r) (hts : t + 1 = s) {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : ContDiffOn ℝ 1 f U) (S : Finset ℤ) (c : ℤ → E)
    (huU : ∀ x, toContinuousMap T (by linarith) (∑ k ∈ S, single (s := s) k (c k)) x ∈ U)
    {gS : CircleSobolev r (E →L[ℝ] F)}
    (hgS : ∀ x, toContinuousMap T (by linarith) gS x =
      fderiv ℝ f (toContinuousMap T (by linarith) (∑ k ∈ S, single (s := s) k (c k)) x)) (n : ℤ) :
    (realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gS)
      (derivative T hts.le (∑ k ∈ S, single (s := s) k (c k)))).coeff n =
      (2 * π * I * n / T : ℂ) • fourierCoeff
        (fun x ↦ f (toContinuousMap T (by linarith) (∑ k ∈ S, single (s := s) k (c k)) x)) n := by
  have hr' : 1 / 2 < r' := by linarith
  have hs : 1 / 2 < s := by linarith
  let p : CircleSobolev (r' + 1) E := ∑ k ∈ S, single k (c k)
  let uS : CircleSobolev s E := ∑ k ∈ S, single k (c k)
  have hp_incl : inclusion (by linarith : s ≤ r' + 1) p = uS := by simp [p, uS]
  have hp_deriv : inclusion (by linarith : t ≤ r') (derivative T le_rfl p) =
      derivative T hts.le uS := by rw [← hp_incl, derivative_inclusion, inclusion_derivative]
  set w := realConvolution hr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gS) (derivative T le_rfl p)
    with hw
  rw [← hp_deriv, realConvolutionAsym_inclusion_right, coeff_inclusion,
    ← fourierCoeff_toContinuousMap T hr' w n]
  refine fourierCoeff_of_hasDerivAt (f := fun x ↦ f (toContinuousMap T hs uS x)) (fun x ↦ ?_)
    (toContinuousMap T hr' w).continuous n
  have hd_p : HasDerivAt (fun y : ℝ ↦ toContinuousMap T hs uS y)
      (toContinuousMap T hr' (derivative T le_rfl p) x) x := by
    simpa only [← hp_incl, toContinuousMap_inclusion] using
      hasDerivAt_toContinuousMap T hr' le_rfl p x
  have hwx : toContinuousMap T hr' w x =
      fderiv ℝ f (toContinuousMap T hs uS x) (toContinuousMap T hr' (derivative T le_rfl p) x) := by
    rw [hw, toContinuousMap_realConvolution_apply, ContinuousLinearMap.id_apply,
      toContinuousMap_inclusion, hgS x]
  exact hwx ▸ ((hf.differentiableOn one_ne_zero).differentiableAt
    (hU.mem_nhds (huU x))).hasFDerivAt.comp_hasDerivAt x hd_p

/-- Along the partial Fourier sums `uS S = ∑ k ∈ S, single k (u.coeff k)`, the induction
hypothesis produces `H^r` lifts `gS S` of `(df) ∘ (uS S)` converging to `gu` in `H^{r'}`. -/
private theorem exists_tendsto_inclusion_fderiv_approx {r' r s : ℝ} (hr' : 1 / 2 < r')
    (hr'r : r' < r) (hrs : r < s) {U K : Set E} {δ R B₁ : ℝ} (hU : IsOpen U) (hδ : 0 < δ)
    (hKδU : Metric.cthickening δ K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (hIH : ∀ v : CircleSobolev r E,
      (∀ x, toContinuousMap T (by linarith) v x ∈ Metric.cthickening δ K) → ‖v‖ ≤ R + 1 →
      ∃ g : CircleSobolev r (E →L[ℝ] F), (∀ x, toContinuousMap T (by linarith) g x =
        fderiv ℝ f (toContinuousMap T (by linarith) v x)) ∧ ‖g‖ ≤ B₁)
    {u : CircleSobolev s E} (huK : ∀ x, toContinuousMap T (by linarith) u x ∈ K) (huR : ‖u‖ ≤ R)
    {gu : CircleSobolev r (E →L[ℝ] F)}
    (hgu : ∀ x, toContinuousMap T (by linarith) gu x =
      fderiv ℝ f (toContinuousMap T (by linarith) u x)) :
    ∃ gS : Finset ℤ → CircleSobolev r (E →L[ℝ] F),
      (∀ᶠ S in atTop, (∀ x, toContinuousMap T (by linarith)
          (∑ k ∈ S, single (s := s) k (u.coeff k)) x ∈ Metric.cthickening δ K) ∧
        ∀ x, toContinuousMap T (by linarith) (gS S) x =
          fderiv ℝ f (toContinuousMap T (by linarith)
            (∑ k ∈ S, single (s := s) k (u.coeff k)) x)) ∧
      Tendsto (fun S ↦ inclusion hr'r.le (gS S)) atTop (𝓝 (inclusion hr'r.le gu)) := by
  have hr : 1 / 2 < r := by linarith
  have hs : 1 / 2 < s := by linarith
  let uS : Finset ℤ → CircleSobolev s E := fun S ↦ ∑ k ∈ S, single k (u.coeff k)
  have huS_cont := (toContinuousMap T hs).continuous.tendsto u |>.comp (hasSum_single u)
  have hev : ∀ᶠ S in atTop, (∀ x, toContinuousMap T hs (uS S) x ∈ Metric.cthickening δ K) ∧
      ‖inclusion hrs.le (uS S)‖ ≤ R + 1 := by
    filter_upwards [Metric.tendsto_nhds.1 huS_cont δ hδ,
      Metric.tendsto_nhds.1 (hasSum_single u) 1 one_pos] with S hS1 hS2
    rw [dist_eq_norm] at hS2
    exact ⟨fun x ↦ Metric.mem_cthickening_of_dist_le _ _ δ K (huK x)
      ((ContinuousMap.dist_apply_le_dist x).trans hS1.le),
      by linarith [norm_inclusion_le hrs.le (uS S), norm_le_norm_sub_add (uS S) u]⟩
  -- Select the `H^r` derivative lifts `gS S` from `hIH` and interpolate to `H^{r'}`.
  classical
  let gS : Finset ℤ → CircleSobolev r (E →L[ℝ] F) := fun S ↦
    if h : (∀ x, toContinuousMap T hs (uS S) x ∈ Metric.cthickening δ K) ∧
        ‖inclusion hrs.le (uS S)‖ ≤ R + 1 then
      (hIH (inclusion hrs.le (uS S)) (by simpa [toContinuousMap_inclusion] using h.1) h.2).choose
    else gu
  have hgS_spec : ∀ᶠ S in atTop,
      (∀ x, toContinuousMap T hr (gS S) x = fderiv ℝ f (toContinuousMap T hs (uS S) x)) ∧
        ‖gS S‖ ≤ B₁ := hev.mono fun S hS ↦ by
    dsimp only [gS]; rw [dite_eq_left hS]
    have hspec := (hIH (inclusion hrs.le (uS S))
      (by simpa [toContinuousMap_inclusion] using hS.1) hS.2).choose_spec
    exact ⟨fun x ↦ by simpa [toContinuousMap_inclusion] using hspec.1 x, hspec.2⟩
  exact ⟨gS, (hev.and hgS_spec).mono fun _ h ↦ ⟨h.1.1, h.2.1⟩,
    tendsto_inclusion_of_norm_le_of_tendsto_toContinuousMap T hr'r hr
      (hgS_spec.mono fun _ h ↦ h.2) <| ContinuousMap.tendsto_of_eventually_eq_comp
        ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKδU) huS_cont
        (hev.mono fun _ h ↦ h.1) (fun x ↦ Metric.self_subset_cthickening _ (huK x))
        (hgS_spec.mono fun _ h ↦ h.1) hgu⟩

private theorem coeff_realConvolutionAsym_eq_deriv_fourierCoeff {t r' r s : ℝ} (ht : 0 ≤ t)
    (htr' : t + 1 / 2 < r') (hr'r : r' < r) (hrs : r < s) (hts : t + 1 = s) {U K : Set E}
    {δ R B₁ : ℝ} (hU : IsOpen U) (hδ : 0 < δ) (hKδU : Metric.cthickening δ K ⊆ U) {f : E → F}
    (hf : ContDiffOn ℝ 1 f U)
    (hIH : ∀ v : CircleSobolev r E,
      (∀ x, toContinuousMap T (by linarith) v x ∈ Metric.cthickening δ K) → ‖v‖ ≤ R + 1 →
      ∃ g : CircleSobolev r (E →L[ℝ] F), (∀ x, toContinuousMap T (by linarith) g x =
        fderiv ℝ f (toContinuousMap T (by linarith) v x)) ∧ ‖g‖ ≤ B₁)
    {u : CircleSobolev s E} (huK : ∀ x, toContinuousMap T (by linarith) u x ∈ K) (huR : ‖u‖ ≤ R)
    {gu : CircleSobolev r (E →L[ℝ] F)}
    (hgu : ∀ x, toContinuousMap T (by linarith) gu x =
      fderiv ℝ f (toContinuousMap T (by linarith) u x)) (n : ℤ) :
    (realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gu)
      (derivative T hts.le u)).coeff n =
      (2 * π * I * n / T : ℂ) • fourierCoeff
        (fun x ↦ f (toContinuousMap T (by linarith) u x)) n := by
  have hs : 1 / 2 < s := by linarith
  -- Stage 1: Approximate `gu` in `H^{r'}` along the partial Fourier sums `uS S` of `u`.
  obtain ⟨gS, hgS_ev, hgS_r'⟩ := exists_tendsto_inclusion_fderiv_approx T (by linarith) hr'r hrs
    hU hδ hKδU hf hIH huK huR hgu
  let uS : Finset ℤ → CircleSobolev s E := fun S ↦ ∑ k ∈ S, single k (u.coeff k)
  let A := realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F))
  -- Stage 2: Pass to the limit on both sides of the trigonometric-polynomial chain rule.
  have hLHS : Tendsto (fun S ↦ (A (inclusion hr'r.le (gS S)) (derivative T hts.le (uS S))).coeff n)
      atTop (𝓝 ((A (inclusion hr'r.le gu) (derivative T hts.le u)).coeff n)) := by
    simpa only [Function.comp_def, coeffCLM_apply] using ((coeffCLM n).continuous.tendsto _).comp <|
      (A.isBoundedBilinearMap.continuous.tendsto _).comp
        (hgS_r'.prodMk_nhds (((derivative T hts.le).continuous.tendsto u).comp (hasSum_single u)))
  have huK' (x : AddCircle T) : toContinuousMap T hs u x ∈ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _ (huK x)
  let fu : C(AddCircle T, F) := ⟨fun x ↦ f (toContinuousMap T hs u x),
    hf.continuousOn.comp_continuous (toContinuousMap T hs u).continuous fun x ↦ hKδU (huK' x)⟩
  classical
  let fuS : Finset ℤ → C(AddCircle T, F) := fun S ↦
    if h : ∀ x, toContinuousMap T hs (uS S) x ∈ Metric.cthickening δ K then
      ⟨fun x ↦ f (toContinuousMap T hs (uS S) x),
        hf.continuousOn.comp_continuous (toContinuousMap T hs (uS S)).continuous fun x ↦ hKδU (h x)⟩
    else fu
  have hfuS_cont : Tendsto fuS atTop (𝓝 fu) :=
    ContinuousMap.tendsto_of_eventually_eq_comp (hf.continuousOn.mono hKδU)
      ((toContinuousMap T hs).continuous.tendsto u |>.comp (hasSum_single u))
      (hgS_ev.mono fun _ h ↦ h.1) huK'
      (hgS_ev.mono fun S hS x ↦ by dsimp only [fuS, uS]; rw [dite_eq_left hS.1]; rfl) fun _ ↦ rfl
  have hRHS : Tendsto (fun S ↦ (2 * π * I * n / T : ℂ) • fourierCoeff (fuS S) n) atTop
      (𝓝 ((2 * π * I * n / T : ℂ) • fourierCoeff fu n)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, coeffCLM_apply,
      coeff_ofContinuousMap] using ((((coeffCLM n).comp (ofContinuousMap T)).continuous.tendsto
        fu).comp hfuS_cont).const_smul (2 * π * I * n / T : ℂ)
  -- Stage 3: Identify the two limits using `coeff_realConvolutionAsym_sum_single`.
  refine tendsto_nhds_unique hLHS (hRHS.congr' <| hgS_ev.mono fun S ⟨hSK', hgS⟩ ↦ ?_)
  dsimp only [fuS, uS]; rw [dite_eq_left hSK']; simp only [ContinuousMap.coe_mk]
  exact (coeff_realConvolutionAsym_sum_single T ht htr' hr'r hts hU hf S u.coeff
    (fun x ↦ hKδU (hSK' x)) hgS n).symm

private theorem exists_toContinuousMap_eq_and_norm_le_of_derivative_coeff {t r s : ℝ} (htr : t ≤ r)
    (hr : 1 / 2 < r) (hrs : r < s) (hts : t + 1 = s) {U : Set E} {f : E → F} (hf : ContinuousOn f U)
    {u : CircleSobolev s E} (huU : ∀ x, toContinuousMap T (by linarith) u x ∈ U) {B₀ Bd : ℝ}
    (ar : CircleSobolev r F)
    (har : ∀ x, toContinuousMap T hr ar x = f (toContinuousMap T (by linarith) u x))
    (har_norm : ‖ar‖ ≤ B₀) (b : CircleSobolev t F)
    (hb_coeff : ∀ n, b.coeff n = (2 * π * I * n / T : ℂ) • (inclusion htr ar).coeff n)
    (hb_norm : ‖b‖ ≤ Bd) : ∃ w : CircleSobolev s F,
      (∀ x, toContinuousMap T (by linarith) w x = f (toContinuousMap T (by linarith) u x)) ∧
        ‖w‖ ≤ √(2 * B₀ ^ 2 + 2 * (T / (2 * π)) ^ 2 * Bd ^ 2) := by
  subst hts; have hs : 1 / 2 < t + 1 := by linarith
  obtain ⟨w, hw_incl, hw_deriv⟩ := exists_inclusion_eq_and_derivative_eq T (inclusion htr ar) b
    hb_coeff
  have hw_eval (x : AddCircle T) : toContinuousMap T hs w x = f (toContinuousMap T hs u x) := by
    refine congrArg (· x) ((toContinuousMap_eq_iff T hs w ⟨fun y ↦ f (toContinuousMap T hs u y),
      hf.comp_continuous (toContinuousMap T hs u).continuous huU⟩).2 fun n ↦ ?_)
    have hw_coeff : w.coeff n = ar.coeff n := by
      simpa [coeff_inclusion] using congrArg (·.coeff n) hw_incl
    rw [hw_coeff, ← fourierCoeff_toContinuousMap T hr ar n]
    exact congrArg (fourierCoeff · n) (funext fun y ↦ (har y).symm)
  have hat_norm : ‖inclusion htr ar‖ ≤ B₀ := (norm_inclusion_le _ _).trans har_norm
  refine ⟨w, hw_eval, (Real.le_sqrt (norm_nonneg w) (by positivity)).2 ?_⟩
  exact (norm_sq_le_of_derivative T rfl w).trans ((by rw [hw_incl, hw_deriv] : _ =
    2 * ‖inclusion htr ar‖ ^ 2 + 2 * (T / (2 * π)) ^ 2 * ‖b‖ ^ 2).trans_le (by gcongr))

end BootstrapChain

private theorem exists_toContinuousMap_eq_comp_and_norm_le_aux :
    ∀ (m : ℕ) {s : ℝ} (hs : 1 / 2 < s), s < (m + 2 : ℝ) / 2 →
      ∀ {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {U : Set E}, IsOpen U →
        ∀ {f : E → F}, ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) f U → ∀ {K : Set E}, IsCompact K →
        K ⊆ U → ∀ (R : ℝ), ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
          (∀ x, toContinuousMap T hs u x ∈ K) → ‖u‖ ≤ R → ∃ w : CircleSobolev s F,
            (∀ x, toContinuousMap T hs w x = f (toContinuousMap T hs u x)) ∧ ‖w‖ ≤ B
  | 0, s, hs, hsm, _, _, _, _, _, _, _, _, _, hU, _, hf, _, hK, hKU, R =>
      exists_toContinuousMap_eq_comp_and_norm_le_base T hs (by norm_num at hsm; exact hsm)
        hU (by simpa using hf) hK hKU R
  | m + 1, s, hs, hsm, E, F, _, _, _, _, _, _, U, hU, f, hf, K, hK, hKU, R => by
      by_cases hs_prev : s < (m + 2 : ℝ) / 2
      · exact exists_toContinuousMap_eq_comp_and_norm_le_aux m hs hs_prev hU
          (hf.of_le (by norm_cast; omega)) hK hKU R
      -- Stage 1: Choose intermediate Sobolev exponents `t = s - 1` and `t + 1/2 < r' < r < s`.
      push Not at hs_prev; push_cast at hsm; have : (0 : ℝ) ≤ m := m.cast_nonneg
      set t := s - 1 with ht_def
      have ht : 0 ≤ t := by linarith [ht_def]
      have hts_eq : t + 1 = s := sub_add_cancel s 1
      set r := (t + 1 / 2 + (m + 2 : ℝ) / 2) / 2 with hr_def
      have hr : 1 / 2 < r := by linarith [hr_def]
      have hrs : r < s := by linarith [hr_def]
      have hrm : r < (m + 2 : ℝ) / 2 := by linarith [hr_def]
      set r' := (t + 1 / 2 + r) / 2 with hr'_def
      have htr' : t + 1 / 2 < r' := by linarith [hr'_def]
      have hr'r : r' < r := by linarith [hr'_def]
      -- Stage 2: Apply the induction hypothesis to `f` on `K` and to `fderiv ℝ f` on `K_δ`.
      obtain ⟨δ, hδ, hK'U⟩ := hK.exists_cthickening_subset_open hU hKU
      obtain ⟨B₀, _, hIH₀⟩ := exists_toContinuousMap_eq_comp_and_norm_le_aux m hr hrm hU
        (hf.of_le (by norm_cast; omega)) hK hKU R
      obtain ⟨B₁, _, hIH₁⟩ := exists_toContinuousMap_eq_comp_and_norm_le_aux m hr hrm hU
        (hf.fderiv_of_isOpen hU (m := ((m + 1 : ℕ) : ℕ∞ω)) (by norm_cast))
        hK.cthickening hK'U (R + 1)
      let A := realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F))
      have : 0 < T := hT.out; set Bd := ‖A‖ * B₁ * (2 * π / T * max R 0)
      refine ⟨√(2 * B₀ ^ 2 + 2 * (T / (2 * π)) ^ 2 * Bd ^ 2), Real.sqrt_nonneg _,
        fun u huK huR ↦ ?_⟩
      -- Stage 3: Pair `(df) ∘ u ∈ H^{r'}` with `u' ∈ H^t` and lift `f ∘ u` from `H^t` to `H^s`.
      obtain ⟨ar, har, har_norm⟩ := hIH₀ (inclusion hrs.le u)
        (by simpa [toContinuousMap_inclusion] using huK) ((norm_inclusion_le _ _).trans huR)
      obtain ⟨gu, hgu, hgu_norm⟩ := hIH₁ (inclusion hrs.le u)
        (fun x ↦ Metric.self_subset_cthickening _ (by simpa using huK x))
        ((norm_inclusion_le _ _).trans (by linarith))
      let b : CircleSobolev t F := A (inclusion hr'r.le gu) (derivative T hts_eq.le u)
      have hb_coeff (n : ℤ) :
          b.coeff n = (2 * π * I * n / T : ℂ) • (inclusion (by linarith : t ≤ r) ar).coeff n := by
        have har_coe : (toContinuousMap T hr ar : AddCircle T → F) =
            fun x ↦ f (toContinuousMap T (by linarith) u x) :=
          funext fun x ↦ by simpa only [toContinuousMap_inclusion] using har x
        rw [coeff_inclusion, ← fourierCoeff_toContinuousMap T hr ar n, har_coe]
        exact coeff_realConvolutionAsym_eq_deriv_fourierCoeff T ht htr' hr'r hrs hts_eq
          hU hδ hK'U (hf.of_le (by norm_cast; omega)) hIH₁ huK huR
          (fun x ↦ by simpa only [toContinuousMap_inclusion] using hgu x) n
      have hb_norm : ‖b‖ ≤ Bd := (A.le_opNorm₂ _ _).trans <| mul_le_mul
        (mul_le_mul_of_nonneg_left ((norm_inclusion_le _ _).trans hgu_norm) (norm_nonneg A))
        ((norm_derivative_le T _ u).trans
          (mul_le_mul_of_nonneg_left (huR.trans (le_max_left R 0)) (by positivity)))
        (norm_nonneg _) (by positivity)
      exact exists_toContinuousMap_eq_and_norm_le_of_derivative_coeff T (by linarith) hr hrs
        hts_eq hf.continuousOn (fun x ↦ hKU (huK x)) ar
        (fun x ↦ by simpa only [toContinuousMap_inclusion] using har x) har_norm b hb_coeff hb_norm

private theorem exists_toContinuousMap_eq_comp_and_norm_le {s : ℝ} (hs : 1 / 2 < s)
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {U K : Set E} (hU : IsOpen U)
    {n : ℕ∞ω} {f : E → F} (hf : ContDiffOn ℝ n f U) (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n) (hK : IsCompact K)
    (hKU : K ⊆ U) (R : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
      (∀ x, toContinuousMap T hs u x ∈ K) → ‖u‖ ≤ R → ∃ w : CircleSobolev s F,
        (∀ x, toContinuousMap T hs w x = f (toContinuousMap T hs u x)) ∧ ‖w‖ ≤ B := by
  have hm1 : ⌊2 * s⌋₊ - 1 + 1 = ⌊2 * s⌋₊ := Nat.sub_add_cancel (Nat.floor_pos.2 (by linarith))
  have hsm : s < ((⌊2 * s⌋₊ - 1 : ℕ) + 2 : ℝ) / 2 := by
    have : ((⌊2 * s⌋₊ - 1 : ℕ) + 2 : ℝ) = (⌊2 * s⌋₊ : ℝ) + 1 := by
      exact_mod_cast congrArg (· + 1) hm1
    linarith [Nat.lt_floor_add_one (2 * s)]
  let eF : F ≃L[ℂ] (ULift.{u} (Fin (Module.finrank ℂ F)) → ℂ) :=
    ((Module.finBasis ℂ F).reindex Equiv.ulift.symm).equivFun.toContinuousLinearEquiv
  let L := eF.symm.toContinuousLinearMap
  obtain ⟨B', hB', h⟩ := exists_toContinuousMap_eq_comp_and_norm_le_aux T (⌊2 * s⌋₊ - 1) hs hsm hU
    ((eF.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
      (hf.of_le (hm1.symm ▸ hn))) hK hKU R
  refine ⟨‖L‖ * B', mul_nonneg (norm_nonneg L) hB', fun u huK huR ↦ ?_⟩
  obtain ⟨w', hw', hw'B⟩ := h u huK huR
  refine ⟨mapCLM L w', fun x ↦ ?_,
    (norm_mapCLM_le L w').trans (mul_le_mul_of_nonneg_left hw'B (norm_nonneg L))⟩
  rw [toContinuousMap_mapCLM_apply T hs L w' x, hw' x]
  exact eF.symm_apply_apply (f (toContinuousMap T hs u x))

variable {s : ℝ} [hs : Fact (1 / 2 < s)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Smooth functions act on `H^s(E) → H^s(F)` for `s > 1/2`.** If `f : E → F` is `C^n` on an
open set `U ⊆ E` with `⌊2s⌋₊ ≤ n` (in particular if `f` is `C^∞`) and `u ∈ H^s(E)` takes values
in `U`, then the continuous representative of `nemytskii f u` is `f ∘ u`. -/
theorem toContinuousMap_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp)
    (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskii f u) x = f (toContinuousMap T hs.out u x) := by
  obtain ⟨_, _, h⟩ := exists_toContinuousMap_eq_comp_and_norm_le T hs.out hU hf hn
    (isCompact_range (toContinuousMap T hs.out u).continuous) (Set.range_subset_iff.2 hu) ‖u‖
  obtain ⟨w, hw, -⟩ := h u (fun y ↦ ⟨y, rfl⟩) le_rfl
  rw [nemytskii_eq_of_forall_toContinuousMap_apply T hw, hw x]

/-- Global version of `toContinuousMap_nemytskii_of_contDiffOn` for `f : E → F` of class `C^n`. -/
theorem toContinuousMap_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskii f u) x = f (toContinuousMap T hs.out u x) :=
  toContinuousMap_nemytskii_of_contDiffOn T isOpen_univ hf.contDiffOn (fun _ ↦ mem_univ _) hn x

/-- **Uniform `H^s` norm bound on compact-range bounded subsets.** -/
theorem exists_norm_nemytskii_le_of_isCompact {U K : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hK : IsCompact K) (hKU : K ⊆ U) (R : ℝ)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
      (∀ x, toContinuousMap T hs.out u x ∈ K) → ‖u‖ ≤ R → ‖nemytskii f u‖ ≤ B := by
  obtain ⟨B, hB, h⟩ := exists_toContinuousMap_eq_comp_and_norm_le T hs.out hU hf hn hK hKU R
  refine ⟨B, hB, fun u huK huR ↦ ?_⟩; obtain ⟨w, hw, hwB⟩ := h u huK huR
  rwa [nemytskii_eq_of_forall_toContinuousMap_apply T hw]

/-- `nemytskii f` commutes with the Sobolev inclusion `H^s(E) → H^t(E)` for `1/2 < t ≤ s`. -/
theorem nemytskii_inclusion_of_contDiffOn {t : ℝ} [ht : Fact (1 / 2 < t)] (hts : t ≤ s)
    {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F} (hf : ContDiffOn ℝ n f U)
    {u : CircleSobolev s E} (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) :
    nemytskii f (inclusion hts u) = inclusion hts (nemytskii f u) :=
  nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ by
    rw [toContinuousMap_inclusion, toContinuousMap_inclusion,
      toContinuousMap_nemytskii_of_contDiffOn T hU hf hu hn x]

/-- **Functoriality of `nemytskii` under composition.** -/
theorem nemytskii_comp_of_contDiffOn {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {n m : ℕ∞ω} {f : E → F} {g : F → G} (hf : ContDiffOn ℝ n f U) (hg : ContDiffOn ℝ m g V)
    (hUV : MapsTo f U V) {u : CircleSobolev s E} (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) (hm : (⌊2 * s⌋₊ : ℕ∞ω) ≤ m := by simp) :
    nemytskii (g ∘ f) u = nemytskii g (nemytskii f u) := by
  have hfu (x : AddCircle T) : toContinuousMap T hs.out (nemytskii f u) x ∈ V := by
    rw [toContinuousMap_nemytskii_of_contDiffOn T hU hf hu hn x]; exact hUV (hu x)
  exact nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ by
    rw [toContinuousMap_nemytskii_of_contDiffOn T hV hg hfu hm x,
      toContinuousMap_nemytskii_of_contDiffOn T hU hf hu hn x, Function.comp_apply]

/-- Global functoriality `nemytskii (g ∘ f) u = nemytskii g (nemytskii f u)` for `C^n` maps. -/
theorem nemytskii_comp_of_contDiff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {n m : ℕ∞ω} {f : E → F} {g : F → G}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ m g) (u : CircleSobolev s E)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) (hm : (⌊2 * s⌋₊ : ℕ∞ω) ≤ m := by simp) :
    nemytskii (g ∘ f) u = nemytskii g (nemytskii f u) :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  nemytskii_comp_of_contDiffOn 1 isOpen_univ isOpen_univ hf.contDiffOn hg.contDiffOn
    (mapsTo_univ f _) (fun _ ↦ mem_univ _) hn hm

end Bootstrap
end CircleSobolev
end TauCeti
