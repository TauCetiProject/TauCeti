/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Minimization
public import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Rigidity of length minimizers in a normal neighbourhood

The radial geodesic from the centre `p` of a normal neighbourhood to a point `exp_p v` minimizes
Riemannian length among the `C¹` curves staying in that neighbourhood. This file proves the
equality case: every such minimizer is the radial geodesic `t ↦ exp_p (t • v)` composed with a
continuous nondecreasing surjection of `[0, 1]` onto itself. A minimizer may pause or vary its
speed, but its trace is the radial segment.

Together with the minimization inequality of `Gauss/Minimization.lean`, this identifies the length
minimizers from the centre of a normal neighbourhood by their length alone: a `C¹` curve in the
neighbourhood from `p` to `exp_p v` whose length is the radial length `‖v‖` has the radial segment
as its trace and traverses it monotonically. This is the form in which the minimizing theory
recognises a distance-realizing curve as a reparametrized geodesic, and it shows that pausing or
changing speed along a minimizer never yields a different unparametrized minimizer.

## Main results

* `TauCeti.Manifold.IsNormalDomain.enorm_riemannianLog_eq_pathELength`: along a minimizer from the
  centre, the norm of the logarithm equals the length travelled so far.
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_eq_smul_of_pathELength_eq`: the logarithm of a
  minimizer lies on the ray through `v`, at the radius given by its norm.
* `TauCeti.Manifold.IsNormalDomain.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_eq` and
  its `_le` variant: a minimizer is the radial geodesic composed with a continuous nondecreasing
  surjective reparametrization of `[0, 1]`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Proposition 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6,
  Proposition 6.11.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

section RadialNorm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable {p : M} {U : Set (TangentSpace I p)} {γ : ℝ → M}

/-- **Radial norm equals arc length along a minimizer.** If a `C¹` curve from the centre of a
normal neighbourhood has length equal to the norm of the logarithm of its endpoint, then at every
intermediate time the norm of its logarithm equals the length travelled so far. -/
theorem IsNormalDomain.enorm_riemannianLog_eq_pathELength (h : IsNormalDomain I M p U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)) (hγ0 : γ 0 = p)
    (hlen : pathELength I γ 0 1 = ‖riemannianLog I M p U (γ 1)‖ₑ) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    ‖riemannianLog I M p U (γ t)‖ₑ = pathELength I γ 0 t := by
  have hA : ENNReal.ofReal ‖riemannianLog I M p U (γ t)‖ ≤ pathELength I γ 0 t :=
    h.ofReal_norm_riemannianLog_le_pathELength ht.1 (hγ.mono (Icc_subset_Icc_right ht.2))
      (hγU.mono_left (Icc_subset_Icc_right ht.2)) hγ0
  have hB : ENNReal.ofReal (‖riemannianLog I M p U (γ 1)‖ - ‖riemannianLog I M p U (γ t)‖) ≤
      pathELength I γ t 1 :=
    (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
      (h.ofReal_abs_norm_riemannianLog_sub_norm_riemannianLog_le_pathELength ht.2
        (hγ.mono (Icc_subset_Icc_left ht.1)) (hγU.mono_left (Icc_subset_Icc_left ht.1)))
  have hsum : pathELength I γ 0 t + pathELength I γ t 1 = pathELength I γ 0 1 :=
    pathELength_add ht.1 ht.2
  have hL : pathELength I γ 0 1 ≠ ⊤ := by
    rw [hlen]
    exact enorm_ne_top
  have hA_top : pathELength I γ 0 t ≠ ⊤ :=
    ne_top_of_le_ne_top hL (hsum ▸ le_self_add)
  have hB_top : pathELength I γ t 1 ≠ ⊤ :=
    ne_top_of_le_ne_top hL (hsum ▸ le_add_self)
  have hreal : (pathELength I γ 0 t).toReal + (pathELength I γ t 1).toReal =
      ‖riemannianLog I M p U (γ 1)‖ := by
    rw [← ENNReal.toReal_add hA_top hB_top, hsum, hlen, toReal_enorm]
  have hB' := (ENNReal.ofReal_le_iff_le_toReal hB_top).1 hB
  rw [← ofReal_norm]
  refine le_antisymm hA ?_
  rw [← ENNReal.ofReal_toReal hA_top, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  linarith

/-- The exponential image of a `C¹` path in a normal domain is a `C¹` curve. -/
private theorem contMDiffOn_riemannianExp_comp (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} (hw : ContDiffOn ℝ 1 w (Icc 0 1))
    (hdom : MapsTo w (Icc 0 1) U) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (riemannianExp I M p ∘ w) (Icc 0 1) :=
  ((contMDiffOn_riemannianExp (I := I) (M := M) p).of_le (by simp)).comp
    (contMDiffOn_iff_contDiffOn.2 hw) (hdom.mono_right h.subset_expDomain)

/-- The speed of the exponential image of a `C¹` path in a normal domain is continuous. -/
private theorem continuousOn_norm_curveVelocityWithin_riemannianExp_comp
    (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} (hw : ContDiffOn ℝ 1 w (Icc 0 1))
    (hdom : MapsTo w (Icc 0 1) U) :
    ContinuousOn (fun u ↦ ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc 0 1) u‖)
      (Icc 0 1) :=
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  (contMDiffOn_riemannianExp_comp h hw hdom).continuousOn_norm_curveVelocityWithin
    (uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_Icc zero_lt_one))

/-- **The logarithm of a minimizer moves radially.** For a `C¹` path `w` in a normal domain whose
norm equals the arc length of `exp_p ∘ w`, the derivative of `w` at an interior time where `w`
does not vanish is a nonnegative multiple of `w` itself. -/
private theorem hasDerivAt_of_norm_eq_integral (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} (hw : ContDiffOn ℝ 1 w (Icc 0 1))
    (hdom : MapsTo w (Icc 0 1) U)
    (hr : ∀ t ∈ Icc 0 1, ‖w t‖ = ∫ u in 0..t,
      ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc 0 1) u‖)
    {t : ℝ} (ht : t ∈ Ioo 0 1) (hwt : w t ≠ 0) :
    HasDerivAt w ((‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc 0 1) t‖ / ‖w t‖) • w t)
      t := by
  set σ : ℝ → ℝ := fun u ↦ ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc 0 1) u‖ with hσ_def
  have htIcc : t ∈ Icc 0 1 := Ioo_subset_Icc_self ht
  have hN : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hdomt : w t ∈ expDomain I M p := h.subset_expDomain (hdom htIcc)
  have hσ : ContinuousOn σ (Icc 0 1) :=
    continuousOn_norm_curveVelocityWithin_riemannianExp_comp h hw hdom
  -- the derivative of `w` at `t`
  have hwt' : HasDerivAt w (deriv w t) t :=
    (((hw t htIcc).contDiffAt hN).differentiableAt one_ne_zero).hasDerivAt
  -- the derivative of the squared radius, computed in two ways
  have hQ : HasDerivAt (fun u ↦ inner ℝ (w u) (w u)) (2 * inner ℝ (w t) (deriv w t)) t := by
    refine (hwt'.inner ℝ hwt').congr_deriv ?_
    rw [real_inner_comm (deriv w t) (w t)]
    ring
  have hFTC : HasDerivAt (fun u ↦ ∫ s in 0..u, σ s) (σ t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((hσ.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      ((hσ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hσ.continuousAt hN)
  have hQ' : HasDerivAt (fun u ↦ inner ℝ (w u) (w u)) (2 * ‖w t‖ * σ t) t := by
    refine ((hFTC.pow 2).congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hN] with u hu
      rw [real_inner_self_eq_norm_sq, hr u hu]
      rfl
    · rw [← hr t htIcc]
      push_cast
      ring
  have hkey : inner ℝ (w t) (deriv w t) = ‖w t‖ * σ t := by
    have := hQ.unique hQ'
    linarith
  -- the speed of `exp_p ∘ w` at `t` is the differential of `exp_p` applied to `w'`
  have hspeed : σ t =
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) (deriv w t)‖ := by
    rw [hσ_def]
    dsimp only
    rw [curveVelocityWithin_of_mem_nhds hN, curveVelocity_riemannianExp_comp hwt' hdomt]
    -- both sides are the Riemannian norm at `exp_p (w t)`, presented through different fibres
    rfl
  -- the Gauss lemma turns the radial identity into an equality case of Cauchy--Schwarz
  have hG := inner_mfderiv_riemannianExp_radial (I := I) (M := M) (v := w t) (w := deriv w t)
    hdomt
  have hGn := norm_mfderiv_riemannianExp_radial (I := I) (M := M) (v := w t) hdomt
  have hCS : inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) (w t))
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) (deriv w t)) =
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) (w t)‖ *
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) (deriv w t)‖ := by
    refine hG.trans ?_
    rw [hkey, hspeed]
    exact congrArg (· * _) hGn.symm
  have hsm := inner_eq_norm_mul_iff_real.1 hCS
  have hsm' : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
      (‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) (deriv w t)‖ • w t) =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
      (‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) (w t)‖ • deriv w t) :=
    (map_smul _ _ _).trans (hsm.trans (map_smul _ _ _).symm)
  -- the differential of `exp_p` is injective on a normal domain
  have hinj : Function.Injective
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)) := fun x y hxy ↦
    ((h.isLocalDiffeomorphOn ⟨w t, hdom htIcc⟩).mfderivToContinuousLinearEquiv
      (by simp)).injective hxy
  have hrad : σ t • w t = ‖w t‖ • deriv w t := by
    rw [hspeed, ← hGn]
    exact hinj hsm'
  have hw'eq : deriv w t = (σ t / ‖w t‖) • w t := by
    rw [div_eq_inv_mul, mul_smul, hrad, smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hwt),
      one_smul]
  exact hw'eq ▸ hwt'

/-- **The logarithm of a minimizer lies on the ray of its endpoint.** For a `C¹` path `w` in a
normal domain whose norm equals the arc length of `exp_p ∘ w`, every value `w t` is a nonnegative
multiple of the final value `w 1`, in the form `‖w t‖ • w 1 = ‖w 1‖ • w t`. -/
private theorem norm_smul_eq_of_norm_eq_integral (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} (hw : ContDiffOn ℝ 1 w (Icc 0 1))
    (hdom : MapsTo w (Icc 0 1) U)
    (hr : ∀ t ∈ Icc 0 1, ‖w t‖ = ∫ u in 0..t,
      ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc 0 1) u‖)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ‖w t‖ • w 1 = ‖w 1‖ • w t := by
  set σ : ℝ → ℝ := fun u ↦ ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc 0 1) u‖
    with hσ_def
  have hσ : ContinuousOn σ (Icc 0 1) :=
    continuousOn_norm_curveVelocityWithin_riemannianExp_comp h hw hdom
  have hσ0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ σ u := fun u _ ↦ norm_nonneg _
  by_cases hwt : w t = 0
  · simp only [hwt, norm_zero, zero_smul, smul_zero]
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · rfl
  have hpos : 0 < ‖w t‖ := norm_pos_iff.2 hwt
  -- on `[t, 1]` the radius stays positive, so the radial derivative formula applies
  have hmono : ∀ s ∈ Icc t 1, ‖w t‖ ≤ ‖w s‖ := fun s hs ↦ by
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hs.1, hs.2⟩
    rw [hr t ht, hr s hs']
    exact intervalIntegral.monotoneOn_primitive_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun u hu ↦ hσ0 u ⟨hu.1.le, hu.2⟩)
      (hσ.intervalIntegrable_of_Icc zero_le_one) ht hs' hs.1
  have hne : ∀ s ∈ Icc t 1, ‖w s‖ ≠ 0 := fun s hs ↦ (hpos.trans_le (hmono s hs)).ne'
  have hderiv : ∀ s ∈ Ioo t 1, HasDerivAt w ((σ s / ‖w s‖) • w s) s := fun s hs ↦
    hasDerivAt_of_norm_eq_integral h hw hdom hr ⟨ht.1.trans_lt hs.1, hs.2⟩
      (norm_ne_zero_iff.1 (hne s (Ioo_subset_Icc_self hs)))
  have hwcont : ContinuousOn w (Icc t 1) := hw.continuousOn.mono (Icc_subset_Icc ht.1 le_rfl)
  have hσt : ContinuousOn σ (Icc t 1) := hσ.mono (Icc_subset_Icc ht.1 le_rfl)
  have hf'cont : ContinuousOn (fun s ↦ (σ s / ‖w s‖) • w s) (Icc t 1) :=
    (hσt.div hwcont.norm hne).smul hwcont
  -- the fundamental theorem of calculus for `w` on `[t, 1]`
  have hint : ∫ s in t..1, (σ s / ‖w s‖) • w s = w 1 - w t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht1.le hwcont hderiv
      (hf'cont.intervalIntegrable_of_Icc ht1.le)
  have hnorm_f' : ∀ s ∈ Icc t 1, ‖(σ s / ‖w s‖) • w s‖ = σ s := fun s hs ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hσ0 s ⟨ht.1.trans hs.1, hs.2⟩)
      (norm_nonneg _)), div_mul_cancel₀ _ (hne s hs)]
  have hint1 : IntervalIntegrable σ MeasureTheory.volume 0 1 :=
    hσ.intervalIntegrable_of_Icc zero_le_one
  have hintt : IntervalIntegrable σ MeasureTheory.volume 0 t :=
    (hσ.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  -- the chord is no longer than the arc, which equals the change in radius
  have hle : ‖w 1 - w t‖ ≤ ‖w 1‖ - ‖w t‖ := by
    calc ‖w 1 - w t‖ = ‖∫ s in t..1, (σ s / ‖w s‖) • w s‖ := by rw [hint]
      _ ≤ ∫ s in t..1, ‖(σ s / ‖w s‖) • w s‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht1.le
      _ = ∫ s in t..1, σ s :=
        intervalIntegral.integral_congr fun s hs ↦ hnorm_f' s (by rwa [uIcc_of_le ht1.le] at hs)
      _ = ‖w 1‖ - ‖w t‖ := by
        rw [hr 1 ⟨zero_le_one, le_rfl⟩, hr t ht]
        exact (intervalIntegral.integral_interval_sub_left hint1 hintt).symm
  -- equality in the triangle inequality puts `w t` and `w 1 - w t` on a common ray
  have hray : SameRay ℝ (w t) (w 1 - w t) := by
    rw [sameRay_iff_norm_add, add_sub_cancel]
    exact le_antisymm (by simpa using norm_add_le (w t) (w 1 - w t)) (by linarith)
  have hray' := (SameRay.refl (w t)).add_right hray
  rw [add_sub_cancel] at hray'
  exact hray'.norm_smul_eq

end RadialNorm

section Rigidity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable {p : M} {U : Set (TangentSpace I p)} {γ : ℝ → M} {v : TangentSpace I p}

/-- **Rigidity of length minimizers in a normal neighbourhood.** A `C¹` curve from the centre
`p` of a normal neighbourhood to `exp_p v` that stays in the neighbourhood and has the length of
the radial segment to `v` has, at each time, a logarithm on the ray through `v` at distance equal
to the length travelled so far. The competitor may pause or slow down, but it cannot leave the
radial ray. -/
theorem IsNormalDomain.riemannianLog_eq_smul_of_pathELength_eq (h : IsNormalDomain I M p U)
    (hv : v ∈ U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)) (hγ0 : γ 0 = p)
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    riemannianLog I M p U (γ t) = (‖riemannianLog I M p U (γ t)‖ / ‖v‖) • v := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hc : ContDiffOn ℝ 1 (riemannianLog I M p U ∘ γ) (Icc 0 1) := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (h.contMDiffOn_riemannianLog.of_le (by simp)).comp hγ hγU
  have hdom : MapsTo (riemannianLog I M p U ∘ γ) (Icc 0 1) U := fun u hu ↦
    h.riemannianLog_mem (hγU hu)
  have hEq : EqOn (riemannianExp I M p ∘ (riemannianLog I M p U ∘ γ)) γ (Icc 0 1) :=
    fun u hu ↦ h.riemannianExp_riemannianLog (hγU hu)
  have hc1 : riemannianLog I M p U (γ 1) = v := by
    rw [hγ1, h.riemannianLog_riemannianExp hv]
  have hlen' : pathELength I γ 0 1 = ‖riemannianLog I M p U (γ 1)‖ₑ := by
    rw [hlen, pathELength_riemannianExp_smul_zero_one h hv, hc1]
  have hσ := continuousOn_norm_curveVelocityWithin_riemannianExp_comp h hc hdom
  -- the radial norm is the arc length of the curve
  have hr : ∀ u ∈ Icc (0 : ℝ) 1, ‖(riemannianLog I M p U ∘ γ) u‖ = ∫ s in 0..u,
      ‖curveVelocityWithin I (riemannianExp I M p ∘ (riemannianLog I M p U ∘ γ)) (Icc 0 1) s‖ := by
    intro u hu
    have h1 := h.enorm_riemannianLog_eq_pathELength hγ hγU hγ0 hlen' hu
    rw [← pathELength_congr (hEq.mono (Icc_subset_Icc_right hu.2)),
      ContMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin
        (contMDiffOn_riemannianExp_comp h hc hdom)
        (uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_Icc zero_lt_one)) hu.1
        (Icc_subset_Icc_right hu.2), ← ofReal_norm] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _)
      (intervalIntegral.integral_nonneg hu.1 fun _ _ ↦ norm_nonneg _)).1 h1
  have hray := norm_smul_eq_of_norm_eq_integral h hc hdom hr ht
  simp only [Function.comp_apply, hc1] at hray
  by_cases hv0 : v = 0
  · have hle : ‖(riemannianLog I M p U ∘ γ) t‖ ≤ ‖(riemannianLog I M p U ∘ γ) 1‖ := by
      rw [hr t ht, hr 1 ⟨zero_le_one, le_rfl⟩]
      exact intervalIntegral.monotoneOn_primitive_of_nonneg
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun _ _ ↦ norm_nonneg _)
        (hσ.intervalIntegrable_of_Icc zero_le_one) ht ⟨zero_le_one, le_rfl⟩ ht.2
    simp only [Function.comp_apply, hc1, hv0, norm_zero] at hle
    rw [hv0, smul_zero]
    exact norm_le_zero_iff.1 hle
  · rw [div_eq_inv_mul, mul_smul, hray, smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0),
      one_smul]

/-- A length-minimizing `C¹` curve from the centre of a normal neighbourhood to `exp_p v` is, at
each time, the exponential of a nonnegative multiple of `v`, at the radius given by its
logarithm. -/
theorem IsNormalDomain.eq_riemannianExp_smul_of_pathELength_eq (h : IsNormalDomain I M p U)
    (hv : v ∈ U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)) (hγ0 : γ 0 = p)
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    γ t = riemannianExp I M p ((‖riemannianLog I M p U (γ t)‖ / ‖v‖) • v) := by
  rw [← h.riemannianLog_eq_smul_of_pathELength_eq hv hγ hγU hγ0 hγ1 hlen ht,
    h.riemannianExp_riemannianLog (hγU ht)]

/-- **Minimizers are reparametrized radial geodesics.** A `C¹` curve from the centre of a normal
neighbourhood to `exp_p v`, staying in the neighbourhood and having the length of the radial
segment, is the radial geodesic `t ↦ exp_p (t • v)` composed with a continuous nondecreasing
surjection of `[0, 1]` onto itself. Pauses of the competitor are absorbed by the
reparametrization. -/
theorem IsNormalDomain.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_eq
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)) (hγ0 : γ 0 = p)
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    ∃ φ : ℝ → ℝ, MonotoneOn φ (Icc 0 1) ∧ ContinuousOn φ (Icc 0 1) ∧
      SurjOn φ (Icc 0 1) (Icc 0 1) ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t = riemannianExp I M p (φ t • v) := by
  by_cases hv0 : v = 0
  · refine ⟨id, monotoneOn_id, continuousOn_id, surjOn_id _, rfl, rfl, fun t ht ↦ ?_⟩
    rw [h.eq_riemannianExp_smul_of_pathELength_eq hv hγ hγU hγ0 hγ1 hlen ht, hv0, smul_zero,
      smul_zero]
  have hlen' : pathELength I γ 0 1 = ‖riemannianLog I M p U (γ 1)‖ₑ := by
    rw [hlen, pathELength_riemannianExp_smul_zero_one h hv, hγ1, h.riemannianLog_riemannianExp hv]
  have hcont : ContinuousOn (fun t ↦ ‖riemannianLog I M p U (γ t)‖ / ‖v‖) (Icc 0 1) :=
    ((h.continuousOn_riemannianLog.comp hγ.continuousOn hγU).norm).div_const _
  have h0 : ‖riemannianLog I M p U (γ 0)‖ / ‖v‖ = 0 := by
    rw [hγ0, h.riemannianLog_self, norm_zero, zero_div]
  have h1 : ‖riemannianLog I M p U (γ 1)‖ / ‖v‖ = 1 := by
    rw [hγ1, h.riemannianLog_riemannianExp hv, div_self (norm_ne_zero_iff.2 hv0)]
  refine ⟨fun t ↦ ‖riemannianLog I M p U (γ t)‖ / ‖v‖, ?_, ?_, ?_, h0, h1,
    fun t ht ↦ h.eq_riemannianExp_smul_of_pathELength_eq hv hγ hγU hγ0 hγ1 hlen ht⟩
  · intro s hs t ht hst
    have hle := h.enorm_riemannianLog_eq_pathELength hγ hγU hγ0 hlen' hs ▸
      h.enorm_riemannianLog_eq_pathELength hγ hγU hγ0 hlen' ht ▸
      pathELength_mono (I := I) (γ := γ) le_rfl hst
    exact div_le_div_of_nonneg_right (enorm_le_iff_norm_le.1 hle) (norm_nonneg _)
  · exact hcont
  · have hsurj := hcont.surjOn_Icc (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    rwa [h0, h1] at hsurj

/-- A `C¹` curve from the centre of a normal neighbourhood to `exp_p v`, staying in the
neighbourhood and no longer than the radial segment, is the radial geodesic composed with a
continuous nondecreasing surjection of `[0, 1]` onto itself. -/
theorem IsNormalDomain.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_le
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)) (hγ0 : γ 0 = p)
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 ≤
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    ∃ φ : ℝ → ℝ, MonotoneOn φ (Icc 0 1) ∧ ContinuousOn φ (Icc 0 1) ∧
      SurjOn φ (Icc 0 1) (Icc 0 1) ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t = riemannianExp I M p (φ t • v) :=
  h.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_eq hv hγ hγU hγ0 hγ1
    (le_antisymm hlen (h.pathELength_riemannianExp_smul_le hv zero_le_one hγ hγU hγ0 hγ1))

end Rigidity

end TauCeti.Manifold

end
