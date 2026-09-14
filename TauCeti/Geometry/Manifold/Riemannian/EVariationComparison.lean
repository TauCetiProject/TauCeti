/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.EDistComparison
public import TauCeti.Topology.EMetricSpace.BoundedVariation

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# The total variation of a curve is its Riemannian path length

The total variation `eVariationOn γ (Set.Icc a b)` of a curve in a Riemannian manifold is the
supremum of the sums of the ambient distances along finite monotone partitions of `[a, b]`. For a
`C¹` curve it equals `Manifold.pathELength I γ a b`, the integral of the norm of the velocity.
Consequently Riemannian path length is lower semicontinuous: under pointwise, and in particular
uniform, convergence of `C¹` curves to a `C¹` curve on a fixed compact interval, the length of the
limit is at most the `liminf` of the lengths.

The proof tests the total variation on an arbitrary finite monotone partition: the ambient
distance between consecutive partition points is at most the path length over that subinterval,
and `TauCeti.Manifold.sum_pathELength_eq` telescopes the resulting sum. Combined with Mathlib's
lower semicontinuity of `eVariationOn`, the bound passes to pointwise — hence to uniform — limits
of curves and gives a lower bound for the `liminf` of their Riemannian lengths. The transfer lemma
carrying that last step is stated in `TauCeti.Topology.EMetricSpace.BoundedVariation`, since its
proof uses no manifold structure.

The opposite inequality `Manifold.pathELength I γ a b ≤ eVariationOn γ (Icc a b)` needs a sharp
local comparison of the Riemannian distance with the extended chart at a point `x`, measured in the
inner product of `T_x M`. Mathlib's `eventually_norm_symmL_trivializationAt_self_comp_lt` says
that near `x` the derivative of that chart distorts Riemannian norms by a factor arbitrarily close
to `1`; a short `C¹` path from `x` stays in such a neighbourhood, so every continuous linear
functional `ℓ` on `T_x M` read in the chart is `(r ‖ℓ‖)`-Lipschitz at `x` for the Riemannian
distance, for any `r > 1`. Along a `C¹` curve this bounds the speed at every interior parameter
where the (monotone) variation function `variationOnFromTo γ (Icc a b) a` is differentiable by
its derivative, by Hahn--Banach in `T_x M`. Such parameters have full measure, and the integral
of the derivative of a monotone function is at most its increment
(`MonotoneOn.intervalIntegral_deriv_mem_uIcc`), which gives the bound.

Like the corner-smoothing comparison of
`TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`, the piecewise-`C¹` statement here
only compares the piecewise formulation with Mathlib's `C¹` `Manifold.pathELength`: no piecewise
notion of length or variation is introduced. The limit results concern arbitrary pointwise or
uniform limits of families that are eventually `C¹`.

## Main results

* `TauCeti.eVariationOn_le_liminf_of_eventually_le`: an eventual bound on the total variations of
  a family of maps bounds the total variation of a pointwise limit by the `liminf` of the bounds.
* `TauCeti.Manifold.eVariationOn_le_pathELength`: the total variation of a `C¹` curve on `[a, b]`
  is at most its Riemannian path length there.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.eVariationOn_le_pathELength`: the same bound for a
  piecewise-`C¹` curve.
* `TauCeti.Manifold.eVariationOn_le_liminf_pathELength`: the total variation of a pointwise limit
  of eventually `C¹` curves is at most the `liminf` of their Riemannian path lengths.
* `TauCeti.Manifold.eVariationOn_le_liminf_pathELength_of_tendstoUniformlyOn`: the same bound for
  a uniform limit.
* `TauCeti.Manifold.pathELength_le_eVariationOn`: the Riemannian path length of a `C¹` curve on
  `[a, b]` is at most its total variation there.
* `TauCeti.Manifold.eVariationOn_eq_pathELength`: hence the two agree for `C¹` curves.
* `TauCeti.Manifold.pathELength_le_liminf_pathELength`: **lower semicontinuity of path length**
  under pointwise convergence of eventually `C¹` curves to a `C¹` curve.
* `TauCeti.Manifold.pathELength_le_liminf_pathELength_of_tendstoUniformlyOn`: the same under
  uniform convergence.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, Section 2.7.1.
* The finite-partition proof of `TauCeti.Manifold.eVariationOn_le_pathELength` is adapted from
  `edist_le_pathELength_of_cmdiff` and `eVariationOn_le_pathELength` in the Apache-2.0 file
  `formalized-sources/DoCarmo/DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean`
  of [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture),
  revision `24f32e4d600878bfaac6bc2f2f9324175571c321`. That file carries no per-file authorship,
  so the authors above are the contributors credited for the same revision in
  `TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`.
* The reverse comparison `TauCeti.Manifold.pathELength_le_eVariationOn` is a Tau Ceti proof: it
  combines Mathlib's sharp trivialization estimate, the chart displacement bound
  `TauCeti.Manifold.enorm_sub_le_mul_pathELength`, and Mathlib's integral bound for derivatives of
  monotone functions.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Regular reparametrization and limits".
-/

public section

open Bundle Filter MeasureTheory Set
open scoped Bundle ContDiff ENNReal NNReal Manifold Topology

noncomputable section

namespace TauCeti

namespace Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {γ : ℝ → M} {a b : ℝ}

omit [IsRiemannianManifold I M] in
/-- The finite-partition argument underlying the comparison with Riemannian path length. It is
separated from the regularity assumptions so that both `C¹` and piecewise-`C¹` curves use the
same telescoping proof. -/
private theorem eVariationOn_le_pathELength_of_edist_le
    (hedist : ∀ {s t : ℝ}, a ≤ s → s ≤ t → t ≤ b →
      edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hedist' (i : ℕ) :
      edist (γ (u (i + 1))) (γ (u i)) ≤ Manifold.pathELength I γ (u i) (u (i + 1)) := by
    rw [edist_comm]
    exact hedist (hus i).1 (hu i.le_succ) (hus (i + 1)).2
  calc
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
        ≤ ∑ i ∈ Finset.range n, Manifold.pathELength I γ (u i) (u (i + 1)) :=
      Finset.sum_le_sum fun i _ ↦ hedist' i
    _ = Manifold.pathELength I γ (u 0) (u n) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun i ↦ Manifold.pathELength I γ (u i) (u (i + 1))) n]
      exact sum_pathELength_eq (fun i : Fin (n + 1) ↦ u i) fun i ↦ hu (Nat.le_succ i)
    _ ≤ Manifold.pathELength I γ a b := Manifold.pathELength_mono (hus 0).1 (hus n).2

/-- **The total variation of a `C¹` curve is bounded by its Riemannian path length.** If `γ` is
`C¹` on `[a, b]`, then `eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b`. -/
theorem eVariationOn_le_pathELength (hγ : CMDiff[Icc a b] 1 γ) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b :=
  eVariationOn_le_pathELength_of_edist_le fun has hst htb ↦
    IsRiemannianManifold.edist_le_pathELength (hγ.mono (Icc_subset_Icc has htb)) hst

/-- The total variation of a piecewise-`C¹` curve on `[a, b]` is at most its Riemannian path
length there. -/
theorem IsPiecewiseContMDiffOn.eVariationOn_le_pathELength
    (hγ : IsPiecewiseContMDiffOn I 1 γ a b) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b :=
  eVariationOn_le_pathELength_of_edist_le fun has hst htb ↦
    hγ.edist_le_pathELength_of_subset has hst htb

/-- The total variation of a pointwise limit of eventually `C¹` curves is at most the `liminf` of
their Riemannian path lengths. No regularity of the limit is needed; for a `C¹` limit the left side
is its path length, see `TauCeti.Manifold.pathELength_le_liminf_pathELength`. -/
theorem eVariationOn_le_liminf_pathELength {ι : Type*} {l : Filter ι} {γi : ι → ℝ → M}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i))
    (hγ : ∀ t ∈ Icc a b, Tendsto (fun i ↦ γi i t) l (nhds (γ t))) :
    eVariationOn γ (Icc a b) ≤
      liminf (fun i ↦ Manifold.pathELength I (γi i) a b) l :=
  eVariationOn_le_liminf_of_eventually_le
    (hγi.mono fun _ hi ↦ eVariationOn_le_pathELength hi) hγ

/-- The total variation of a uniform limit on `[a, b]` of eventually `C¹` curves is at most the
`liminf` of their Riemannian path lengths. -/
theorem eVariationOn_le_liminf_pathELength_of_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {γi : ι → ℝ → M}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i))
    (hγ : TendstoUniformlyOn γi γ l (Icc a b)) :
    eVariationOn γ (Icc a b) ≤
      liminf (fun i ↦ Manifold.pathELength I (γi i) a b) l :=
  eVariationOn_le_liminf_pathELength hγi fun _ ht ↦ hγ.tendsto_at ht

section Converse

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- At an interior parameter where the variation function of a `C¹` curve is differentiable, the
speed of the curve is at most `r` times the derivative of the variation function, for any `r > 1`.
The derivative is compared, functional by functional on the tangent space, with the right slopes
of the curve read in the chart centred at the current point. -/
private theorem norm_curveVelocityWithin_le_mul_deriv_variationOnFromTo
    (hγ : CMDiff[Icc a b] 1 γ) (hbv : LocallyBoundedVariationOn γ (Icc a b)) {t : ℝ}
    (ht : t ∈ Ioo a b) (hd : DifferentiableAt ℝ (variationOnFromTo γ (Icc a b) a) t) {r : ℝ}
    (hr : 1 < r) :
    ‖curveVelocityWithin I γ (Icc a b) t‖ ≤ r * deriv (variationOnFromTo γ (Icc a b) a) t := by
  set V := variationOnFromTo γ (Icc a b) a with hVdef
  set x := γ t
  set w : TangentSpace I x := curveVelocityWithin I γ (Icc a b) t
  have hIcc : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have htab : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have ha : a ∈ Icc a b := left_mem_Icc.2 (ht.1.trans ht.2).le
  have hcurve : HasDerivAt (extChartAt I x ∘ γ) w t :=
    (hasDerivWithinAt_extChartAt_comp_curve (hasMFDerivWithinAt_curveVelocityWithin
      ((hγ t htab).mdifferentiableWithinAt one_ne_zero))).hasDerivAt hIcc
  have hV := hd.hasDerivAt.tendsto_slope_zero_right
  have hshift : Tendsto (fun h : ℝ ↦ t + h) (𝓝[>] 0) (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).add (tendsto_id (x := 𝓝 (0 : ℝ))) |>.mono_left
      nhdsWithin_le_nhds
  have hmem : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ t + h ∈ Icc a b :=
    (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and (hshift.eventually_mem hIcc)
  -- The right slopes of `V` at `t` are nonnegative, hence so is its derivative.
  have hD : 0 ≤ deriv V t := by
    refine ge_of_tendsto hV ?_
    filter_upwards [hmem] with h hh
    have := variationOnFromTo.monotoneOn hbv ha htab hh.2 (by linarith [hh.1])
    exact smul_nonneg (inv_nonneg.2 hh.1.le) (sub_nonneg.2 this)
  have hγt : Tendsto (fun h ↦ γ (t + h)) (𝓝[>] 0) (𝓝 x) :=
    ((hγ.continuousOn.continuousAt hIcc).tendsto).comp hshift
  refine NormedSpace.norm_le_dual_bound ℝ w (by positivity) fun ℓ ↦ ?_
  -- The same functional, typed on the model space so that it can be composed with the chart.
  let ℓE : E →L[ℝ] ℝ := ℓ
  have hlim : Tendsto (fun h : ℝ ↦ ‖h⁻¹ • ((ℓE ∘ extChartAt I x ∘ γ) (t + h) -
      (ℓE ∘ extChartAt I x ∘ γ) t)‖) (𝓝[>] 0) (𝓝 ‖ℓ w‖) :=
    (continuous_norm.tendsto _).comp
      (ℓE.hasFDerivAt.comp_hasDerivAt t hcurve).tendsto_slope_zero_right
  rw [mul_right_comm]
  refine le_of_tendsto_of_tendsto hlim (hV.const_mul (r * ‖ℓ‖)) ?_
  filter_upwards [hmem, hγt.eventually (eventually_enorm_extChartAt_sub_le (I := I) x hr)]
    with h hh hy
  have hth : t ≤ t + h := by linarith [hh.1]
  -- The distance travelled on `[t, t + h]` is at most the variation there.
  have hedist : edist x (γ (t + h)) ≤ ENNReal.ofReal (V (t + h) - V t) := by
    rw [hVdef, ← variationOnFromTo.add hbv ha htab hh.2, add_sub_cancel_left,
      variationOnFromTo.eq_of_le _ _ hth, ENNReal.ofReal_toReal (hbv t (t + h) htab hh.2)]
    exact eVariationOn.edist_le γ ⟨htab, le_rfl, hth⟩ ⟨hh.2, hth, le_rfl⟩
  have hΔ : 0 ≤ V (t + h) - V t :=
    sub_nonneg.2 (variationOnFromTo.monotoneOn hbv ha htab hh.2 hth)
  have hchart : ‖ℓ (extChartAt I x (γ (t + h)) - extChartAt I x x)‖ ≤
      r * ‖ℓ‖ * (V (t + h) - V t) := by
    have := (hy ℓ).trans (by gcongr : ENNReal.ofReal r * ‖ℓ‖ₑ * edist x (γ (t + h)) ≤
      ENNReal.ofReal r * ‖ℓ‖ₑ * ENNReal.ofReal (V (t + h) - V t))
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_mul (by positivity)] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hsub : (ℓE ∘ extChartAt I x ∘ γ) (t + h) - (ℓE ∘ extChartAt I x ∘ γ) t =
      ℓ (extChartAt I x (γ (t + h)) - extChartAt I x x) := (map_sub ℓ _ _).symm
  rw [hsub, norm_smul, smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.2 hh.1.le)]
  calc h⁻¹ * ‖ℓ (extChartAt I x (γ (t + h)) - extChartAt I x x)‖
      ≤ h⁻¹ * (r * ‖ℓ‖ * (V (t + h) - V t)) := by
        gcongr
        exact inv_nonneg.2 hh.1.le
    _ = r * ‖ℓ‖ * (h⁻¹ * (V (t + h) - V t)) := by ring

/-- Letting `r` decrease to `1` in `norm_curveVelocityWithin_le_mul_deriv_variationOnFromTo`. -/
private theorem norm_curveVelocityWithin_le_deriv_variationOnFromTo
    (hγ : CMDiff[Icc a b] 1 γ) (hbv : LocallyBoundedVariationOn γ (Icc a b)) {t : ℝ}
    (ht : t ∈ Ioo a b) (hd : DifferentiableAt ℝ (variationOnFromTo γ (Icc a b) a) t) :
    ‖curveVelocityWithin I γ (Icc a b) t‖ ≤ deriv (variationOnFromTo γ (Icc a b) a) t := by
  have hc : Continuous fun r : ℝ ↦ r * deriv (variationOnFromTo γ (Icc a b) a) t := by fun_prop
  exact ge_of_tendsto ((hc.tendsto' 1 _ (one_mul _)).mono_left (nhdsWithin_le_nhds (s := Ioi 1)))
    (eventually_mem_nhdsWithin.mono fun r hr ↦
      norm_curveVelocityWithin_le_mul_deriv_variationOnFromTo hγ hbv ht hd hr)

/-- **Riemannian path length is bounded by total variation.** For a `C¹` curve on `[a, b]`, its
Riemannian path length is at most its total variation for the Riemannian distance. -/
theorem pathELength_le_eVariationOn (hγ : CMDiff[Icc a b] 1 γ) :
    Manifold.pathELength I γ a b ≤ eVariationOn γ (Icc a b) := by
  rcases le_or_gt b a with hba | hab
  · rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc,
      setLIntegral_measure_zero _ _ (by simp [hba])]
    simp
  rcases eq_or_ne (eVariationOn γ (Icc a b)) ⊤ with htop | htop
  · simp [htop]
  have hbv : LocallyBoundedVariationOn γ (Icc a b) :=
    BoundedVariationOn.locallyBoundedVariationOn htop
  set V := variationOnFromTo γ (Icc a b) a with hVdef
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  have hmono : MonotoneOn V (Icc a b) := variationOnFromTo.monotoneOn hbv ha
  -- Almost every parameter is interior and a point of differentiability of `V`.
  have hae : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b ∧ DifferentiableAt ℝ V t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hmono.ae_differentiableWithinAt_of_mem, volume.ae_ne a, volume.ae_ne b]
      with t hdiff hta htb ht
    have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩
    exact ⟨ht', (hdiff ht).differentiableAt (Icc_mem_nhds ht'.1 ht'.2)⟩
  have hspeed := hae.mono fun t ht ↦
    norm_curveVelocityWithin_le_deriv_variationOnFromTo (I := I) hγ hbv ht.1 ht.2
  have hint : IntegrableOn (deriv V) (Icc a b) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact (uIcc_of_le hab.le ▸ hmono).intervalIntegrable_deriv
  calc Manifold.pathELength I γ a b
      = ∫⁻ t in Icc a b, ‖curveVelocityWithin I γ (Icc a b) t‖ₑ := by
        simp only [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc, curveVelocityWithin_apply]
        -- The two sides reach the fibre `enorm` through different, definitionally equal, topology
        -- instances on the tangent space.
        rfl
    _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (deriv V t) :=
        lintegral_mono_ae (hspeed.mono fun t ht ↦ by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal ht)
    _ = ENNReal.ofReal (∫ t in a..b, deriv V t) := by
        rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
          ofReal_integral_eq_lintegral_ofReal hint
            (hspeed.mono fun t ht ↦ (norm_nonneg _).trans ht)]
    _ ≤ ENNReal.ofReal (V b - V a) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := (uIcc_of_le hab.le ▸ hmono).intervalIntegral_deriv_mem_uIcc
        rw [uIcc_of_le (sub_nonneg.2 (hmono ha hb hab.le))] at this
        exact this.2
    _ = eVariationOn γ (Icc a b) := by
        rw [hVdef, variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le _ _ hab.le,
          inter_self, ENNReal.ofReal_toReal htop]

/-- **The total variation of a `C¹` curve is its Riemannian path length.**

Not `@[simp]`: the model with corners `I` occurs only on the right-hand side, so `simp` cannot
infer `I` (or its model spaces) by matching the left-hand side. -/
theorem eVariationOn_eq_pathELength (hγ : CMDiff[Icc a b] 1 γ) :
    eVariationOn γ (Icc a b) = Manifold.pathELength I γ a b :=
  (eVariationOn_le_pathELength hγ).antisymm (pathELength_le_eVariationOn hγ)

/-- **Lower semicontinuity of Riemannian path length.** Let `γᵢ` be eventually `C¹` on `[a, b]`
and converge pointwise there to a `C¹` curve `γ`. Then the length of `γ` on `[a, b]` is at most the
`liminf` of the lengths of the `γᵢ`. -/
theorem pathELength_le_liminf_pathELength {ι : Type*} {l : Filter ι} {γi : ι → ℝ → M}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i)) (hγ : CMDiff[Icc a b] 1 γ)
    (hconv : ∀ t ∈ Icc a b, Tendsto (fun i ↦ γi i t) l (𝓝 (γ t))) :
    Manifold.pathELength I γ a b ≤ liminf (fun i ↦ Manifold.pathELength I (γi i) a b) l :=
  (pathELength_le_eVariationOn hγ).trans (eVariationOn_le_liminf_pathELength hγi hconv)

/-- **Lower semicontinuity of Riemannian path length under uniform convergence.** If eventually
`C¹` curves `γᵢ` converge uniformly on `[a, b]` to a `C¹` curve `γ`, then
`pathELength I γ a b ≤ liminf pathELength I γᵢ a b`. -/
theorem pathELength_le_liminf_pathELength_of_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {γi : ι → ℝ → M}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i)) (hγ : CMDiff[Icc a b] 1 γ)
    (hconv : TendstoUniformlyOn γi γ l (Icc a b)) :
    Manifold.pathELength I γ a b ≤ liminf (fun i ↦ Manifold.pathELength I (γi i) a b) l :=
  pathELength_le_liminf_pathELength hγi hγ fun _ ht ↦ hconv.tendsto_at ht

end Converse

end Manifold

end TauCeti
