/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic

/-!
# Local behaviour of geodesics

For a tangent vector `v ∈ T_p M`, the maximal geodesic `γ_v` from `p` with initial velocity `v`
is the radial geodesic `s ↦ exp_p (s • v)`. This file proves three local properties of these
geodesics, used to cut simple closed geodesic polygons out of radial geodesics.

* A geodesic with nonzero velocity is injective near every interior parameter in the same
  connected component, since its derivative is injective there.
* Two radial geodesics from `p` whose initial velocities do not lie on a common ray do not meet
  for small positive parameters, by injectivity of `exp_p` on a normal ball.
* Near a closed set of parameters of its maximal interval, a maximal geodesic agrees with a curve
  which is smooth on the whole line. Its affine reparametrizations admit smooth extensions
  preserving the endpoint germs and the rescaled velocity on compact intervals.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.exists_mem_nhds_injOn`: geodesics are locally injective.
* `TauCeti.Manifold.exists_mem_nhds_injOn_maximalGeodesic`: the maximal-geodesic specialization.
* `TauCeti.Manifold.exists_pos_maximalGeodesic_eq_iff_of_not_sameRay`: radial geodesics
  in directions on no common ray meet near the origin only at zero parameters.
* `TauCeti.Manifold.exists_contMDiff_eventuallyEq_maximalGeodesic`: a maximal geodesic agrees near
  a closed set of parameters with a curve smooth on the whole line.
* `TauCeti.Manifold.exists_contMDiff_isGeodesicCurveOn_maximalGeodesic`: the same for an affine
  reparametrization on a compact interval, preserving the germs and affine velocity formula.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5 and 6.
-/

public section

open Bundle Filter Function Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

section LocalInjectivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- A geodesic with nonzero velocity at `a` is locally injective at every interior parameter in
its connected component. -/
theorem IsGeodesicCurveOn.exists_mem_nhds_injOn {γ : ℝ → M} {s : Set ℝ}
    (h : IsGeodesicCurveOn I γ s) {a t : ℝ} (ht : t ∈ connectedComponentIn s a)
    (hs : s ∈ 𝓝 t) (ha : curveVelocityWithin I γ s a ≠ 0) :
    ∃ U ∈ 𝓝 t, InjOn γ U := by
  apply (h.contMDiffOn.contMDiffAt hs).exists_mem_nhds_injOn_of_curveVelocity_ne_zero (by simp)
  rw [← curveVelocityWithin_of_mem_nhds hs]
  exact h.curveVelocityWithin_ne_zero_of_mem_connectedComponentIn ht ha

end LocalInjectivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p}

/-- **Geodesics are locally injective.** A maximal geodesic with nonzero initial velocity is
injective on a neighbourhood of each parameter of its maximal interval. -/
theorem exists_mem_nhds_injOn_maximalGeodesic {t : ℝ} (hv : v ≠ 0)
    (ht : t ∈ geodesicInterval I M p v) :
    ∃ U ∈ 𝓝 t, InjOn (maximalGeodesic I M p v) U := by
  exact (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.exists_mem_nhds_injOn
    (mem_connectedComponentIn ht) (isOpen_geodesicInterval.mem_nhds ht)
    (by simpa only [curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds ht)] using
      curveVelocity_maximalGeodesic_ne_zero hv ht)

/-- **Radial geodesics in different directions separate.** If the tangent vectors `v` and
`w` at `p` do not lie on a common ray, the radial geodesics from `p` with these initial
velocities meet for small nonnegative parameters exactly when both parameters vanish. -/
theorem exists_pos_maximalGeodesic_eq_iff_of_not_sameRay {w : TangentSpace I p}
    (hvw : ¬ SameRay ℝ v w) :
    ∃ ε > 0, ∀ a ∈ Ico 0 ε, ∀ b ∈ Ico 0 ε,
      maximalGeodesic I M p v a = maximalGeodesic I M p w b ↔ a = 0 ∧ b = 0 := by
  obtain ⟨r, hr, hN⟩ := exists_isNormalDomain_ball (I := I) p
  have hmem {x : TangentSpace I p} {a : ℝ} (ha : a ∈ Ico 0 (r / (‖x‖ + 1))) :
      a • x ∈ ball (0 : TangentSpace I p) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
    have h := ha.2
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith [norm_nonneg x, ha.1]
  refine ⟨min (r / (‖v‖ + 1)) (r / (‖w‖ + 1)), by positivity, fun a ha b hb ↦ ?_⟩
  refine ⟨fun hab ↦ ?_, ?_⟩
  · have hav := hmem (x := v) ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩
    have hbw := hmem (x := w) ⟨hb.1, hb.2.trans_le (min_le_right _ _)⟩
    rw [← riemannianExp_smul, ← riemannianExp_smul] at hab
    have heq := hN.injOn hav hbw hab
    by_cases ha0 : a = 0
    · refine ⟨ha0, ?_⟩
      have hw : w ≠ 0 := fun hw ↦ hvw (by simp [hw])
      simpa [ha0, hw] using heq.symm
    · by_cases hb0 : b = 0
      · have hv : v ≠ 0 := fun hv ↦ hvw (by simp [hv])
        have : a = 0 := by simpa [hb0, hv] using heq
        exact (ha0 this).elim
      · exact (hvw (Or.inr (Or.inr ⟨a, b, lt_of_le_of_ne ha.1 (Ne.symm ha0),
          lt_of_le_of_ne hb.1 (Ne.symm hb0), heq⟩))).elim
  · rintro ⟨rfl, rfl⟩
    simp

/-- **Smooth extension of a geodesic segment.** Near a closed set `K` of parameters in its
maximal interval, the maximal geodesic from `p` with initial velocity `v` agrees with a curve
which is smooth on the whole line. -/
theorem exists_contMDiff_eventuallyEq_maximalGeodesic {K : Set ℝ} (hK : IsClosed K)
    (hKG : K ⊆ geodesicInterval I M p v) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧ ∀ t ∈ K, f =ᶠ[𝓝 t] maximalGeodesic I M p v := by
  exact (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn
    |>.exists_contMDiff_eventuallyEq isOpen_geodesicInterval isPreconnected_geodesicInterval
      ⟨0, zero_mem_geodesicInterval⟩ hK hKG

/-- **An affinely reparametrized geodesic segment as a smooth geodesic piece.** If `t₀ < t₁` and
`m * u + k` lies in the maximal interval of `v` for `u ∈ [t₀, t₁]`, there is a curve smooth on
the whole line which agrees near each point of `[t₀, t₁]` with `u ↦ γ_v (m * u + k)`, is a
geodesic there and has the corresponding affinely rescaled velocity. -/
theorem exists_contMDiff_isGeodesicCurveOn_maximalGeodesic {m k t₀ t₁ : ℝ}
    (ht : t₀ < t₁) (hG : ∀ u ∈ Icc t₀ t₁, m * u + k ∈ geodesicInterval I M p v) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧
      (∀ u ∈ Icc t₀ t₁, f =ᶠ[𝓝 u] fun x ↦ maximalGeodesic I M p v (m * x + k)) ∧
      IsGeodesicCurveOn I f (Icc t₀ t₁) ∧ ∀ u ∈ Icc t₀ t₁,
        curveVelocity I f u = m • curveVelocity I (maximalGeodesic I M p v) (m * u + k) := by
  have hφ : Continuous fun u : ℝ ↦ m * u + k := by fun_prop
  obtain ⟨g, hg, hev⟩ := exists_contMDiff_eventuallyEq_maximalGeodesic (I := I) (v := v)
    (isCompact_Icc.image hφ).isClosed (image_subset_iff.2 hG)
  have hev' (u : ℝ) (hu : u ∈ Icc t₀ t₁) :
      (fun x ↦ g (m * x + k)) =ᶠ[𝓝 u] fun x ↦ maximalGeodesic I M p v (m * x + k) :=
    (hev _ (mem_image_of_mem _ hu)).comp_tendsto hφ.continuousAt
  have heq : EqOn (fun x ↦ g (m * x + k)) (fun x ↦ maximalGeodesic I M p v (m * x + k))
      (Icc t₀ t₁) := fun u hu ↦ (hev' u hu).self_of_nhds
  refine ⟨fun x ↦ g (m * x + k), hg.comp (contDiff_const.mul contDiff_id |>.add
    contDiff_const).contMDiff, hev', ?_, fun u hu ↦ ?_⟩
  · exact ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.comp_affine m k
      (uniqueDiffOn_Icc ht) hG).congr heq
  · have hd : HasDerivAt (fun x : ℝ ↦ m * x + k) m u := by
      simpa using ((hasDerivAt_id u).const_mul m).add_const k
    have hγ : MDifferentiableAt 𝓘(ℝ) I (maximalGeodesic I M p v) (m * u + k) :=
      ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.contMDiffAt_infty
        (isOpen_geodesicInterval.mem_nhds (hG u hu))).mdifferentiableAt (by simp)
    have hvel : curveVelocity I (fun x ↦ g (m * x + k)) u =
        curveVelocity I (maximalGeodesic I M p v ∘ fun x ↦ m * x + k) u :=
      (hev' u hu).curveVelocity_eq
    rw [hvel, curveVelocity_comp hd hγ]

end TauCeti.Manifold
