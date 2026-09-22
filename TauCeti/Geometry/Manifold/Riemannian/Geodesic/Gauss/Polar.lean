/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Polar length comparison in a normal domain

The Gauss lemma controls the radial part of the differential of the Riemannian exponential map.
Its Cauchy--Schwarz consequence says that the radial derivative of a polar lift is no larger than
the speed of its image under the exponential map.  Integrating this estimate shows that a curve
inside a normal neighbourhood has length at least the absolute change in the norm of its logarithm.

The comparison needs no nonvanishing hypothesis, so it also covers curves passing through the
centre of the normal neighbourhood.

## Main results

* `TauCeti.Manifold.abs_inner_le_norm_mul_norm_mfderiv_riemannianExp`: the pointwise radial
  differential estimate.
* `IsNormalDomain.ofReal_abs_norm_riemannianLog_sub_norm_riemannianLog_le_pathELength`: the polar
  length comparison for a `C¹` curve in a normal neighbourhood.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Proposition 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6.
* The smoothed-radius argument follows `DoCarmoLib/Riemannian/Exponential/Minimizing.lean` in the
  Apache-2.0 [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, adapted to Tau Ceti's
  intrinsic exponential map and normal-domain API.
-/

public section

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- **The pointwise polar inequality.** The radial component of a tangent vector at `v` is no
larger than the norm of its image under the differential of the Riemannian exponential map. -/
theorem abs_inner_le_norm_mul_norm_mfderiv_riemannianExp {p : M}
    {v w : TangentSpace I p} (hv : v ∈ expDomain I M p) :
    |inner ℝ v w| ≤ ‖v‖ *
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
  calc
    |inner ℝ v w| =
        |inner ℝ
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)| := by
      rw [inner_mfderiv_riemannianExp_radial hv]
    _ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v‖ *
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖v‖ * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ := by
      rw [norm_mfderiv_riemannianExp_radial hv]

/-- The derivative of the smoothed radius `√(⟪w ·, w ·⟫ + δ)`, for `δ > 0`, along a `C¹` path `w`
in the natural domain of `exp_p` is dominated by the speed of `exp_p ∘ w`.

This is the pointwise polar inequality divided by a radius that has been smoothed at the origin,
where the norm itself is not differentiable. -/
private theorem enorm_derivWithin_sqrt_real_inner_add_le_enorm_mfderiv {p : M}
    {w : ℝ → TangentSpace I p} {a b δ : ℝ} (hδ : 0 < δ)
    (hw : ContDiffOn ℝ 1 w (Icc a b))
    (hdom : MapsTo w (Icc a b) (expDomain I M p)) {t : ℝ} (ht : t ∈ Ioo a b) :
    ‖derivWithin (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) t‖ₑ ≤
      ‖mfderiv 𝓘(ℝ, ℝ) I (riemannianExp I M p ∘ w) t (1 : ℝ)‖ₑ := by
  have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have htN : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hwt : HasDerivAt w (derivWithin w (Icc a b) t) t := by
    have hdiff := ((hw t htIcc).contDiffAt htN).differentiableAt one_ne_zero
    simpa only [derivWithin_of_mem_nhds htN] using hdiff.hasDerivAt
  have hQ : HasDerivAt (fun u ↦ inner ℝ (w u) (w u))
      (2 * inner ℝ (w t) (derivWithin w (Icc a b) t)) t := by
    have hinner := hwt.inner ℝ hwt
    refine hinner.congr_deriv ?_
    rw [real_inner_comm (derivWithin w (Icc a b) t) (w t)]
    ring
  have hQδ : HasDerivAt (fun u ↦ inner ℝ (w u) (w u) + δ)
      (2 * inner ℝ (w t) (derivWithin w (Icc a b) t)) t := hQ.add_const δ
  have hpos : 0 < inner ℝ (w t) (w t) + δ := by
    have : 0 ≤ inner ℝ (w t) (w t) := real_inner_self_nonneg
    positivity
  have hsqrt : HasDerivAt (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ))
      (inner ℝ (w t) (derivWithin w (Icc a b) t) /
        Real.sqrt (inner ℝ (w t) (w t) + δ)) t := by
    have h := (Real.hasDerivAt_sqrt hpos.ne').comp t hQδ
    refine h.congr_deriv ?_
    have hsqrt_pos : 0 < Real.sqrt (inner ℝ (w t) (w t) + δ) :=
      Real.sqrt_pos.mpr hpos
    field_simp
  have hreal :
      ‖derivWithin (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) t‖ ≤
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
          (derivWithin w (Icc a b) t)‖ := by
    rw [derivWithin_of_mem_nhds htN, hsqrt.deriv, Real.norm_eq_abs, abs_div,
      abs_of_pos (Real.sqrt_pos.mpr hpos)]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hpos)).2
    have hpolar := abs_inner_le_norm_mul_norm_mfderiv_riemannianExp
      (I := I) (M := M) (v := w t) (w := derivWithin w (Icc a b) t) (hdom htIcc)
    calc
      |inner ℝ (w t) (derivWithin w (Icc a b) t)| ≤
          ‖w t‖ *
            ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
              (derivWithin w (Icc a b) t)‖ := hpolar
      _ ≤ Real.sqrt (inner ℝ (w t) (w t) + δ) *
            ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
              (derivWithin w (Icc a b) t)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [norm_eq_sqrt_real_inner]
        exact Real.sqrt_le_sqrt (le_add_of_nonneg_right hδ.le)
      _ = ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
              (derivWithin w (Icc a b) t)‖ *
            Real.sqrt (inner ℝ (w t) (w t) + δ) := by
        rw [mul_comm]
  calc
    ‖derivWithin (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) t‖ₑ =
        ENNReal.ofReal
          ‖derivWithin (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) t‖ :=
      (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
          (derivWithin w (Icc a b) t)‖ := ENNReal.ofReal_le_ofReal hreal
    _ = ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t)
          (derivWithin w (Icc a b) t)‖ₑ := ofReal_norm _
    _ = ‖mfderiv 𝓘(ℝ, ℝ) I (riemannianExp I M p ∘ w) t (1 : ℝ)‖ₑ := by
      rw [← curveVelocity_apply,
        curveVelocity_riemannianExp_comp hwt (hdom htIcc)]
      rfl

/-- The smoothed radius `√(⟪w ·, w ·⟫ + δ)`, for `δ > 0`, changes along a `C¹` path `w` in the
natural domain of `exp_p` by at most the length of `exp_p ∘ w`. -/
private theorem ofReal_abs_sqrt_real_inner_add_sub_le_pathELength_riemannianExp {p : M}
    {w : ℝ → TangentSpace I p} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hw : ContDiffOn ℝ 1 w (Icc a b))
    (hdom : MapsTo w (Icc a b) (expDomain I M p)) :
    ENNReal.ofReal
        |Real.sqrt (inner ℝ (w b) (w b) + δ) -
          Real.sqrt (inner ℝ (w a) (w a) + δ)| ≤
      Manifold.pathELength I (riemannianExp I M p ∘ w) a b := by
  have hr : ContDiff ℝ 1 fun v : TangentSpace I p ↦ Real.sqrt (inner ℝ v v + δ) := by
    apply ContDiff.sqrt
    · exact (contDiff_id.inner ℝ contDiff_id).add contDiff_const
    · intro v
      have hv : 0 ≤ inner ℝ v v := real_inner_self_nonneg
      positivity
  have hrw : ContDiffOn ℝ 1 (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) :=
    hr.comp_contDiffOn hw
  have hdisplacement :
      ‖Real.sqrt (inner ℝ (w b) (w b) + δ) - Real.sqrt (inner ℝ (w a) (w a) + δ)‖ₑ ≤
        ∫⁻ t in Icc a b,
          ‖derivWithin (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) t‖ₑ :=
    enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hrw hab
  calc
    ENNReal.ofReal
        |Real.sqrt (inner ℝ (w b) (w b) + δ) -
          Real.sqrt (inner ℝ (w a) (w a) + δ)| =
        ‖Real.sqrt (inner ℝ (w b) (w b) + δ) - Real.sqrt (inner ℝ (w a) (w a) + δ)‖ₑ := by
      rw [← ofReal_norm, Real.norm_eq_abs]
    _ ≤ ∫⁻ t in Icc a b,
        ‖derivWithin (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) t‖ₑ :=
      hdisplacement
    _ = ∫⁻ t in Ioo a b,
        ‖derivWithin (fun u ↦ Real.sqrt (inner ℝ (w u) (w u) + δ)) (Icc a b) t‖ₑ := by
      rw [restrict_Ioo_eq_restrict_Icc]
    _ ≤ ∫⁻ t in Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I (riemannianExp I M p ∘ w) t (1 : ℝ)‖ₑ :=
      setLIntegral_mono' measurableSet_Ioo fun t ht ↦
        enorm_derivWithin_sqrt_real_inner_add_le_enorm_mfderiv hδ hw hdom ht
    _ = Manifold.pathELength I (riemannianExp I M p ∘ w) a b :=
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo.symm

/-- **Polar length comparison for the exponential map.** If a `C¹` path `w` in the tangent
space stays in the natural domain of `exp_p`, then the length of `exp_p ∘ w` is at least the
absolute change in the radial norm of `w`.

No nonvanishing hypothesis is imposed on `w`, so the bound also applies to paths through the
origin. -/
theorem ofReal_abs_norm_sub_norm_le_pathELength_riemannianExp {p : M}
    {w : ℝ → TangentSpace I p} {a b : ℝ} (hab : a ≤ b)
    (hw : ContDiffOn ℝ 1 w (Icc a b))
    (hdom : MapsTo w (Icc a b) (expDomain I M p)) :
    ENNReal.ofReal |‖w b‖ - ‖w a‖| ≤
      Manifold.pathELength I (riemannianExp I M p ∘ w) a b := by
  have htend : Tendsto
      (fun δ : ℝ ↦ ENNReal.ofReal
        |Real.sqrt (inner ℝ (w b) (w b) + δ) -
          Real.sqrt (inner ℝ (w a) (w a) + δ)|)
      (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal |‖w b‖ - ‖w a‖|)) := by
    have hcont : Continuous (fun δ : ℝ ↦ ENNReal.ofReal
        |Real.sqrt (inner ℝ (w b) (w b) + δ) -
          Real.sqrt (inner ℝ (w a) (w a) + δ)|) := by
      exact ENNReal.continuous_ofReal.comp
        (continuous_abs.comp
          ((Real.continuous_sqrt.comp (continuous_const.add continuous_id)).sub
            (Real.continuous_sqrt.comp (continuous_const.add continuous_id))))
    have hzero := hcont.tendsto 0
    simpa only [add_zero, norm_eq_sqrt_real_inner] using
      hzero.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact le_of_tendsto htend (eventually_mem_nhdsWithin.mono fun δ hδ ↦
    ofReal_abs_sqrt_real_inner_add_sub_le_pathELength_riemannianExp hab hδ hw hdom)

/-- **Polar length comparison in a normal neighbourhood.** Along a `C¹` curve contained in the
image of a normal domain, the absolute change in the norm of its Riemannian logarithm is at most
the length of the curve. -/
theorem IsNormalDomain.ofReal_abs_norm_riemannianLog_sub_norm_riemannianLog_le_pathELength
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) :
    ENNReal.ofReal
        |‖riemannianLog I M p U (γ b)‖ - ‖riemannianLog I M p U (γ a)‖| ≤
      Manifold.pathELength I γ a b := by
  let w : ℝ → TangentSpace I p := riemannianLog I M p U ∘ γ
  have hw : ContDiffOn ℝ 1 w (Icc a b) := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (h.contMDiffOn_riemannianLog.of_le (by simp)).comp hγ hγU
  have hdom : MapsTo w (Icc a b) (expDomain I M p) := fun t ht ↦
    h.subset_expDomain (h.riemannianLog_mem (hγU ht))
  have hpolar := ofReal_abs_norm_sub_norm_le_pathELength_riemannianExp
    (I := I) (M := M) hab hw hdom
  have hc : EqOn (riemannianExp I M p ∘ w) γ (Icc a b) := fun t ht ↦ by
    exact h.riemannianExp_riemannianLog (hγU ht)
  rw [Manifold.pathELength_congr hc] at hpolar
  exact hpolar

/-- A `C¹` curve from the centre of a normal neighbourhood to a point `q` has length at least
the norm of `log_p q`. -/
theorem IsNormalDomain.ofReal_norm_riemannianLog_le_pathELength
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) (riemannianExp I M p '' U)) (hγa : γ a = p) :
    ENNReal.ofReal ‖riemannianLog I M p U (γ b)‖ ≤
      Manifold.pathELength I γ a b := by
  simpa only [hγa, h.riemannianLog_self, norm_zero, sub_zero, abs_norm] using
    h.ofReal_abs_norm_riemannianLog_sub_norm_riemannianLog_le_pathELength hab hγ hγU

end TauCeti.Manifold

end
