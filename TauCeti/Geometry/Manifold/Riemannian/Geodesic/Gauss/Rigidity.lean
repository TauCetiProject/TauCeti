/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Minimization
public import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Normed.Module.Ray
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Rigidity of length minimizers in a normal neighbourhood

The radial geodesic from the centre `p` of a normal neighbourhood to a point `exp_p v` minimizes
Riemannian length among the piecewise `C¹` curves staying in that neighbourhood. This file proves
the equality case: every such minimizer is the radial geodesic `t ↦ exp_p (t • v)` composed with a
continuous nondecreasing surjection of its parameter interval onto `[0, 1]`. A minimizer may pause,
vary its speed, or have corners, but its trace is the radial segment.

Together with the minimization inequality of `Gauss/Minimization.lean`, this identifies the length
minimizers from the centre of a normal neighbourhood by their length alone: a piecewise `C¹` curve
in the neighbourhood from `p` to `exp_p v` whose length is the radial length `‖v‖` has the radial
segment as its trace and traverses it monotonically. This is the form in which the minimizing
theory recognises a distance-realizing curve as a reparametrized geodesic, and it shows that
pausing, changing speed, or breaking a minimizer never yields a different unparametrized minimizer.

The argument runs on a general compact parameter interval `[a, b]`. The polar length comparison
forces the norm of the logarithm to equal the arc length travelled so far; on each `C¹` piece of a
partition, the equality case of the Gauss lemma then confines the logarithm to the ray through the
endpoint of that piece, and the rays are chained through the partition points
(`TauCeti.sameRay_of_partition_of_monotoneOn_norm`). A `C¹` competitor is the one-piece case,
reached through `IsPiecewiseContMDiffOn.of_contMDiffOn`.

## Main results

* `TauCeti.Manifold.IsNormalDomain.enorm_riemannianLog_eq_pathELength_of_piecewise`: along a
  piecewise `C¹` minimizer from the centre, the norm of the logarithm equals the length travelled
  so far.
* `TauCeti.Manifold.IsNormalDomain.monotoneOn_norm_riemannianLog_of_pathELength_eq_of_piecewise`:
  the norm of the logarithm is nondecreasing along a piecewise `C¹` minimizer.
* `TauCeti.Manifold.IsNormalDomain.riemannianLog_eq_smul_of_pathELength_eq_of_piecewise`: the
  logarithm of a piecewise `C¹` minimizer lies on the ray through `v`, at the radius given by its
  norm.
* `IsNormalDomain.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_eq_of_piecewise` and
  its `_le` variant: a piecewise `C¹` minimizer is the radial geodesic composed with a continuous
  nondecreasing surjection of its parameter interval onto `[0, 1]`.

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
  [T2Space M]

variable {p : M} {U : Set (TangentSpace I p)} {γ : ℝ → M} {a b : ℝ}

/-- **Radial norm equals arc length along a piecewise `C¹` minimizer.** If a piecewise `C¹` curve
from the centre of a normal neighbourhood has length equal to the norm of the logarithm of its
endpoint, then at every intermediate time the norm of its logarithm equals the length travelled so
far. -/
theorem IsNormalDomain.enorm_riemannianLog_eq_pathELength_of_piecewise (h : IsNormalDomain I M p U)
    (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hlen : pathELength I γ a b = ‖riemannianLog I M p U (γ b)‖ₑ) {t : ℝ}
    (ht : t ∈ Icc a b) :
    ‖riemannianLog I M p U (γ t)‖ₑ = pathELength I γ a t := by
  have hA : ENNReal.ofReal ‖riemannianLog I M p U (γ t)‖ ≤ pathELength I γ a t :=
    h.ofReal_norm_riemannianLog_le_pathELength_of_piecewise hγ hγU hγa ht
  have hB : ENNReal.ofReal (‖riemannianLog I M p U (γ b)‖ - ‖riemannianLog I M p U (γ t)‖) ≤
      pathELength I γ t b :=
    (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
      (h.ofReal_abs_norm_riemannianLog_sub_norm_riemannianLog_le_pathELength_of_piecewise hγ hγU
        ht.1 ht.2 le_rfl)
  have hsum : pathELength I γ a t + pathELength I γ t b = pathELength I γ a b :=
    pathELength_add ht.1 ht.2
  have hL : pathELength I γ a b ≠ ⊤ := by
    rw [hlen]
    exact enorm_ne_top
  have hA_top : pathELength I γ a t ≠ ⊤ :=
    ne_top_of_le_ne_top hL (hsum ▸ le_self_add)
  have hB_top : pathELength I γ t b ≠ ⊤ :=
    ne_top_of_le_ne_top hL (hsum ▸ le_add_self)
  have hreal : (pathELength I γ a t).toReal + (pathELength I γ t b).toReal =
      ‖riemannianLog I M p U (γ b)‖ := by
    rw [← ENNReal.toReal_add hA_top hB_top, hsum, hlen, toReal_enorm]
  have hB' := (ENNReal.ofReal_le_iff_le_toReal hB_top).1 hB
  rw [← ofReal_norm]
  refine le_antisymm hA ?_
  rw [← ENNReal.ofReal_toReal hA_top, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  linarith

/-- The exponential image of a `C¹` path in a normal domain is a `C¹` curve. -/
private theorem contMDiffOn_riemannianExp_comp (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} {c d : ℝ} (hw : ContDiffOn ℝ 1 w (Icc c d))
    (hdom : MapsTo w (Icc c d) U) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (riemannianExp I M p ∘ w) (Icc c d) :=
  ((contMDiffOn_riemannianExp (I := I) (M := M) p).of_le (by simp)).comp
    (contMDiffOn_iff_contDiffOn.2 hw) (hdom.mono_right h.subset_expDomain)

/-- The speed of the exponential image of a `C¹` path in a normal domain is continuous. -/
private theorem continuousOn_norm_curveVelocityWithin_riemannianExp_comp
    (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} {c d : ℝ} (hcd : c < d) (hw : ContDiffOn ℝ 1 w (Icc c d))
    (hdom : MapsTo w (Icc c d) U) :
    ContinuousOn (fun u ↦ ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc c d) u‖)
      (Icc c d) :=
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  (contMDiffOn_riemannianExp_comp h hw hdom).continuousOn_norm_curveVelocityWithin
    (uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_Icc hcd))

/-- **The logarithm of a minimizer moves radially.** For a `C¹` path `w` in a normal domain whose
norm grows exactly by the arc length of `exp_p ∘ w`, the derivative of `w` at an interior time
where `w` does not vanish is a nonnegative multiple of `w` itself. -/
private theorem hasDerivAt_of_norm_eq_add_integral (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} {c d : ℝ} (hw : ContDiffOn ℝ 1 w (Icc c d))
    (hdom : MapsTo w (Icc c d) U)
    (hr : ∀ t ∈ Icc c d, ‖w t‖ = ‖w c‖ + ∫ u in c..t,
      ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc c d) u‖)
    {t : ℝ} (ht : t ∈ Ioo c d) (hwt : w t ≠ 0) :
    HasDerivAt w ((‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc c d) t‖ / ‖w t‖) • w t)
      t := by
  set σ : ℝ → ℝ := fun u ↦ ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc c d) u‖
    with hσ_def
  have htIcc : t ∈ Icc c d := Ioo_subset_Icc_self ht
  have hN : Icc c d ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hdomt : w t ∈ expDomain I M p := h.subset_expDomain (hdom htIcc)
  have hσ : ContinuousOn σ (Icc c d) :=
    continuousOn_norm_curveVelocityWithin_riemannianExp_comp h (ht.1.trans ht.2) hw hdom
  -- the derivative of `w` at `t`
  have hwt' : HasDerivAt w (deriv w t) t :=
    (((hw t htIcc).contDiffAt hN).differentiableAt one_ne_zero).hasDerivAt
  -- the derivative of the squared radius, computed in two ways
  have hQ : HasDerivAt (fun u ↦ inner ℝ (w u) (w u)) (2 * inner ℝ (w t) (deriv w t)) t := by
    refine (hwt'.inner ℝ hwt').congr_deriv ?_
    rw [real_inner_comm (deriv w t) (w t)]
    ring
  have hFTC : HasDerivAt (fun u ↦ ∫ s in c..u, σ s) (σ t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((hσ.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      ((hσ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hσ.continuousAt hN)
  have hQ' : HasDerivAt (fun u ↦ inner ℝ (w u) (w u)) (2 * ‖w t‖ * σ t) t := by
    refine (((hFTC.const_add ‖w c‖).pow 2).congr_of_eventuallyEq ?_).congr_deriv ?_
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
normal domain whose norm grows exactly by the arc length of `exp_p ∘ w`, every value `w t` lies
on the same ray as the final value `w d`. -/
private theorem sameRay_of_norm_eq_add_integral (h : IsNormalDomain I M p U)
    {w : ℝ → TangentSpace I p} {c d : ℝ} (hcd : c < d) (hw : ContDiffOn ℝ 1 w (Icc c d))
    (hdom : MapsTo w (Icc c d) U)
    (hr : ∀ t ∈ Icc c d, ‖w t‖ = ‖w c‖ + ∫ u in c..t,
      ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc c d) u‖)
    {t : ℝ} (ht : t ∈ Icc c d) : SameRay ℝ (w t) (w d) := by
  set σ : ℝ → ℝ := fun u ↦ ‖curveVelocityWithin I (riemannianExp I M p ∘ w) (Icc c d) u‖
  have hσ : ContinuousOn σ (Icc c d) :=
    continuousOn_norm_curveVelocityWithin_riemannianExp_comp h hcd hw hdom
  have hσ0 : ∀ u ∈ Icc c d, 0 ≤ σ u := fun u _ ↦ norm_nonneg _
  by_cases hwt : w t = 0
  · simp only [hwt, SameRay.zero_left]
  rcases eq_or_lt_of_le ht.2 with rfl | htd
  · exact SameRay.rfl
  have hpos : 0 < ‖w t‖ := norm_pos_iff.2 hwt
  -- on `[t, d]` the radius stays positive, so the radial derivative formula applies
  have hmono : ∀ s ∈ Icc t d, ‖w t‖ ≤ ‖w s‖ := fun s hs ↦ by
    have hs' : s ∈ Icc c d := ⟨ht.1.trans hs.1, hs.2⟩
    rw [hr t ht, hr s hs']
    gcongr
    exact intervalIntegral.monotoneOn_primitive_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun u hu ↦ hσ0 u ⟨hu.1.le, hu.2⟩)
      (hσ.intervalIntegrable_of_Icc hcd.le) ht hs' hs.1
  have hne : ∀ s ∈ Icc t d, ‖w s‖ ≠ 0 := fun s hs ↦ (hpos.trans_le (hmono s hs)).ne'
  have hderiv : ∀ s ∈ Ioo t d, HasDerivAt w ((σ s / ‖w s‖) • w s) s := fun s hs ↦
    hasDerivAt_of_norm_eq_add_integral h hw hdom hr ⟨ht.1.trans_lt hs.1, hs.2⟩
      (norm_ne_zero_iff.1 (hne s (Ioo_subset_Icc_self hs)))
  have hwcont : ContinuousOn w (Icc t d) := hw.continuousOn.mono (Icc_subset_Icc ht.1 le_rfl)
  have hσt : ContinuousOn σ (Icc t d) := hσ.mono (Icc_subset_Icc ht.1 le_rfl)
  have hf'cont : ContinuousOn (fun s ↦ (σ s / ‖w s‖) • w s) (Icc t d) :=
    (hσt.div hwcont.norm hne).smul hwcont
  -- the fundamental theorem of calculus for `w` on `[t, d]`
  have hint : ∫ s in t..d, (σ s / ‖w s‖) • w s = w d - w t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htd.le hwcont hderiv
      (hf'cont.intervalIntegrable_of_Icc htd.le)
  have hnorm_f' : ∀ s ∈ Icc t d, ‖(σ s / ‖w s‖) • w s‖ = σ s := fun s hs ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hσ0 s ⟨ht.1.trans hs.1, hs.2⟩)
      (norm_nonneg _)), div_mul_cancel₀ _ (hne s hs)]
  have hintd : IntervalIntegrable σ MeasureTheory.volume c d :=
    hσ.intervalIntegrable_of_Icc hcd.le
  have hintt : IntervalIntegrable σ MeasureTheory.volume c t :=
    (hσ.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  -- the chord is no longer than the arc, which equals the change in radius
  have hle : ‖w d - w t‖ ≤ ‖w d‖ - ‖w t‖ := by
    calc ‖w d - w t‖ = ‖∫ s in t..d, (σ s / ‖w s‖) • w s‖ := by rw [hint]
      _ ≤ ∫ s in t..d, ‖(σ s / ‖w s‖) • w s‖ :=
        intervalIntegral.norm_integral_le_integral_norm htd.le
      _ = ∫ s in t..d, σ s :=
        intervalIntegral.integral_congr fun s hs ↦ hnorm_f' s (by rwa [uIcc_of_le htd.le] at hs)
      _ = ‖w d‖ - ‖w t‖ := by
        rw [hr d ⟨hcd.le, le_rfl⟩, hr t ht, add_sub_add_left_eq_sub]
        exact (intervalIntegral.integral_interval_sub_left hintd hintt).symm
  -- equality in the triangle inequality puts `w t` and `w d - w t` on a common ray
  have hray : SameRay ℝ (w t) (w d - w t) := by
    rw [sameRay_iff_norm_add, add_sub_cancel]
    exact le_antisymm (by simpa using norm_add_le (w t) (w d - w t)) (by linarith)
  have hray' := (SameRay.refl (w t)).add_right hray
  rwa [add_sub_cancel] at hray'

/-- **The logarithm of a minimizer lies on the ray of its endpoint, along one `C¹` piece.** For a
`C¹` curve in the image of a normal domain whose logarithm has norm growing exactly by the arc
length travelled, the logarithm at every time lies on the ray of the logarithm at the final
time. -/
private theorem IsNormalDomain.sameRay_riemannianLog_of_enorm_eq_add_pathELength
    (h : IsNormalDomain I M p U) {c d : ℝ} (hcd : c < d)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc c d))
    (hγU : MapsTo γ (Icc c d) (riemannianExp I M p '' U))
    (hL : ∀ t ∈ Icc c d, ‖riemannianLog I M p U (γ t)‖ₑ =
      ‖riemannianLog I M p U (γ c)‖ₑ + pathELength I γ c t)
    {t : ℝ} (ht : t ∈ Icc c d) :
    SameRay ℝ (riemannianLog I M p U (γ t)) (riemannianLog I M p U (γ d)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hc : ContDiffOn ℝ 1 (riemannianLog I M p U ∘ γ) (Icc c d) := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (h.contMDiffOn_riemannianLog.of_le (by simp)).comp hγ hγU
  have hdom : MapsTo (riemannianLog I M p U ∘ γ) (Icc c d) U := fun u hu ↦
    h.riemannianLog_mem (hγU hu)
  have hEq : EqOn (riemannianExp I M p ∘ (riemannianLog I M p U ∘ γ)) γ (Icc c d) :=
    fun u hu ↦ h.riemannianExp_riemannianLog (hγU hu)
  -- the radial norm grows by the arc length of the curve
  have hr : ∀ u ∈ Icc c d, ‖(riemannianLog I M p U ∘ γ) u‖ =
      ‖(riemannianLog I M p U ∘ γ) c‖ + ∫ s in c..u,
        ‖curveVelocityWithin I (riemannianExp I M p ∘ (riemannianLog I M p U ∘ γ))
          (Icc c d) s‖ := by
    intro u hu
    have hnn : 0 ≤ ∫ s in c..u,
        ‖curveVelocityWithin I (riemannianExp I M p ∘ (riemannianLog I M p U ∘ γ))
          (Icc c d) s‖ :=
      intervalIntegral.integral_nonneg hu.1 fun _ _ ↦ norm_nonneg _
    have h1 := hL u hu
    rw [← pathELength_congr (hEq.mono (Icc_subset_Icc_right hu.2)),
      ContMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin
        (contMDiffOn_riemannianExp_comp h hc hdom)
        (uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_Icc hcd)) hu.1
        (Icc_subset_Icc_right hu.2), ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) hnn] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (add_nonneg (norm_nonneg _) hnn)).1 h1
  exact sameRay_of_norm_eq_add_integral h hcd hc hdom hr ht

end RadialNorm

section Rigidity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable {p : M} {U : Set (TangentSpace I p)} {γ : ℝ → M} {v : TangentSpace I p} {a b : ℝ}

/-- **The radial norm is nondecreasing along a piecewise `C¹` minimizer.** Along a piecewise `C¹`
curve from the centre `p` of a normal neighbourhood to `exp_p v`, staying in the neighbourhood and
having the length of the radial segment to `v`, the norm of the logarithm is nondecreasing in the
parameter. -/
theorem IsNormalDomain.monotoneOn_norm_riemannianLog_of_pathELength_eq_of_piecewise
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hγb : γ b = riemannianExp I M p v)
    (hlen : pathELength I γ a b =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    MonotoneOn (fun u ↦ ‖riemannianLog I M p U (γ u)‖) (Icc a b) := by
  have hlen' : pathELength I γ a b = ‖riemannianLog I M p U (γ b)‖ₑ := by
    rw [hlen, pathELength_riemannianExp_smul_zero_one h hv, hγb, h.riemannianLog_riemannianExp hv]
  intro s hs u hu hsu
  refine enorm_le_iff_norm_le.1 ?_
  rw [h.enorm_riemannianLog_eq_pathELength_of_piecewise hγ hγU hγa hlen' hs,
    h.enorm_riemannianLog_eq_pathELength_of_piecewise hγ hγU hγa hlen' hu]
  exact pathELength_mono le_rfl hsu

/-- **Rigidity of piecewise `C¹` length minimizers in a normal neighbourhood.** A piecewise `C¹`
curve from the centre `p` of a normal neighbourhood to `exp_p v` that stays in the neighbourhood
and has the length of the radial segment to `v` has, at each time, a logarithm on the ray through
`v`, at the radius given by its norm. The competitor may pause, slow down, or have corners, but it
cannot leave the radial ray. -/
theorem IsNormalDomain.riemannianLog_eq_smul_of_pathELength_eq_of_piecewise
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hγb : γ b = riemannianExp I M p v)
    (hlen : pathELength I γ a b =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1)
    {t : ℝ} (ht : t ∈ Icc a b) :
    riemannianLog I M p U (γ t) = (‖riemannianLog I M p U (γ t)‖ / ‖v‖) • v := by
  have hcb : riemannianLog I M p U (γ b) = v := by
    rw [hγb, h.riemannianLog_riemannianExp hv]
  have hlen' : pathELength I γ a b = ‖riemannianLog I M p U (γ b)‖ₑ := by
    rw [hlen, pathELength_riemannianExp_smul_zero_one h hv, hcb]
  -- the radial norm is the arc length travelled so far, hence nondecreasing
  have hr : ∀ u ∈ Icc a b, ‖riemannianLog I M p U (γ u)‖ₑ = pathELength I γ a u :=
    fun u hu ↦ h.enorm_riemannianLog_eq_pathELength_of_piecewise hγ hγU hγa hlen' hu
  have hmono := h.monotoneOn_norm_riemannianLog_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb
    hlen
  -- on each piece of a partition the logarithm stays on the ray of the piece's endpoint
  have hray : SameRay ℝ (riemannianLog I M p U (γ t)) (riemannianLog I M p U (γ b)) := by
    obtain ⟨k, τ, rfl, rfl, hτ, hpieces⟩ := hγ.exists_partition
    have hτmono : Monotone τ := Fin.monotone_iff_le_succ.mpr fun i ↦ (hτ i).le
    refine sameRay_of_partition_of_monotoneOn_norm τ (fun i ↦ (hτ i).le) (fun i u hu ↦ ?_)
      hmono ht
    have hsub : Icc (τ i.castSucc) (τ i.succ) ⊆ Icc (τ 0) (τ (Fin.last (k + 1))) :=
      Icc_subset_Icc (hτmono (Fin.zero_le _)) (hτmono (Fin.le_last _))
    refine h.sameRay_riemannianLog_of_enorm_eq_add_pathELength (hτ i) (hpieces i)
      (hγU.mono_left hsub) (fun s hs ↦ ?_) hu
    rw [hr s (hsub hs), hr (τ i.castSucc) (hsub (left_mem_Icc.2 (hτ i).le)),
      pathELength_add (hτmono (Fin.zero_le _)) hs.1]
  by_cases hv0 : v = 0
  · have hle := hmono ht (right_mem_Icc.2 (ht.1.trans ht.2)) ht.2
    simp only [hcb, hv0, norm_zero] at hle
    rw [hv0, smul_zero]
    exact norm_le_zero_iff.1 hle
  · rw [hcb] at hray
    rw [div_eq_inv_mul, mul_smul, hray.norm_smul_eq, smul_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0), one_smul]

/-- A length-minimizing piecewise `C¹` curve from the centre of a normal neighbourhood to
`exp_p v` is, at each time, the exponential of a nonnegative multiple of `v`, at the radius given
by its logarithm. -/
theorem IsNormalDomain.eq_riemannianExp_smul_of_pathELength_eq_of_piecewise
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hγb : γ b = riemannianExp I M p v)
    (hlen : pathELength I γ a b =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1)
    {t : ℝ} (ht : t ∈ Icc a b) :
    γ t = riemannianExp I M p ((‖riemannianLog I M p U (γ t)‖ / ‖v‖) • v) := by
  rw [← h.riemannianLog_eq_smul_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb hlen ht,
    h.riemannianExp_riemannianLog (hγU ht)]

/-- **Piecewise `C¹` minimizers are reparametrized radial geodesics.** A piecewise `C¹` curve on
`[a, b]` from the centre of a normal neighbourhood to `exp_p v`, staying in the neighbourhood and
having the length of the radial segment, is the radial geodesic `t ↦ exp_p (t • v)` composed with
a continuous nondecreasing surjection of `[a, b]` onto `[0, 1]`. Pauses and corners of the
competitor are absorbed by the reparametrization. -/
theorem IsNormalDomain.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_eq_of_piecewise
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hγb : γ b = riemannianExp I M p v)
    (hlen : pathELength I γ a b =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    ∃ φ : ℝ → ℝ, MonotoneOn φ (Icc a b) ∧ ContinuousOn φ (Icc a b) ∧
      SurjOn φ (Icc a b) (Icc 0 1) ∧ φ a = 0 ∧ φ b = 1 ∧
      ∀ t ∈ Icc a b, γ t = riemannianExp I M p (φ t • v) := by
  have hab : a ≤ b := hγ.lt.le
  by_cases hv0 : v = 0
  · -- the curve is constant at `p`; any nondecreasing surjection serves as reparametrization
    have hφa : (a - a) / (b - a) = 0 := by simp
    have hφb : (b - a) / (b - a) = 1 := div_self (sub_ne_zero.2 hγ.lt.ne')
    have hφ : ContinuousOn (fun t ↦ (t - a) / (b - a)) (Icc a b) := by fun_prop
    refine ⟨fun t ↦ (t - a) / (b - a), fun s _ t _ hst ↦
      div_le_div_of_nonneg_right (sub_le_sub_right hst a) (sub_nonneg.2 hab), hφ, ?_, hφa, hφb,
      fun t ht ↦ ?_⟩
    · have hsurj := hφ.surjOn_Icc (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
      rwa [hφa, hφb] at hsurj
    · rw [h.eq_riemannianExp_smul_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb hlen ht, hv0,
        smul_zero, smul_zero]
  have hmono := h.monotoneOn_norm_riemannianLog_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb
    hlen
  have hcont : ContinuousOn (fun t ↦ ‖riemannianLog I M p U (γ t)‖ / ‖v‖) (Icc a b) :=
    ((h.continuousOn_riemannianLog.comp hγ.continuousOn hγU).norm).div_const _
  have h0 : ‖riemannianLog I M p U (γ a)‖ / ‖v‖ = 0 := by
    rw [hγa, h.riemannianLog_self, norm_zero, zero_div]
  have h1 : ‖riemannianLog I M p U (γ b)‖ / ‖v‖ = 1 := by
    rw [hγb, h.riemannianLog_riemannianExp hv, div_self (norm_ne_zero_iff.2 hv0)]
  refine ⟨fun t ↦ ‖riemannianLog I M p U (γ t)‖ / ‖v‖, ?_, ?_, ?_, h0, h1,
    fun t ht ↦ h.eq_riemannianExp_smul_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb hlen ht⟩
  · exact fun s hs t ht hst ↦ div_le_div_of_nonneg_right (hmono hs ht hst) (norm_nonneg _)
  · exact hcont
  · have hsurj := hcont.surjOn_Icc (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
    rwa [h0, h1] at hsurj

/-- A piecewise `C¹` curve on `[a, b]` from the centre of a normal neighbourhood to `exp_p v`,
staying in the neighbourhood and no longer than the radial segment, is the radial geodesic
composed with a continuous nondecreasing surjection of `[a, b]` onto `[0, 1]`. -/
theorem IsNormalDomain.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_le_of_piecewise
    (h : IsNormalDomain I M p U) (hv : v ∈ U) (hγ : IsPiecewiseContMDiffOn I 1 γ a b)
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p)
    (hγb : γ b = riemannianExp I M p v)
    (hlen : pathELength I γ a b ≤
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1) :
    ∃ φ : ℝ → ℝ, MonotoneOn φ (Icc a b) ∧ ContinuousOn φ (Icc a b) ∧
      SurjOn φ (Icc a b) (Icc 0 1) ∧ φ a = 0 ∧ φ b = 1 ∧
      ∀ t ∈ Icc a b, γ t = riemannianExp I M p (φ t • v) :=
  h.exists_monotoneOn_eq_riemannianExp_smul_of_pathELength_eq_of_piecewise hv hγ hγU hγa hγb
    (le_antisymm hlen (h.pathELength_riemannianExp_smul_le_of_piecewise hv hγ hγU hγa hγb))

end Rigidity

end TauCeti.Manifold

end
