/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
public import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic

/-!
# Local behaviour of maximal geodesics

For a tangent vector `v ∈ T_p M`, the maximal geodesic `γ_v` from `p` with initial velocity `v`
is the radial geodesic `s ↦ exp_p (s • v)`. This file proves three local properties of these
geodesics, used to cut simple closed geodesic polygons out of radial geodesics.

* A maximal geodesic with nonzero initial velocity is injective near every parameter of its
  interval, since its derivative is injective there.
* Two radial geodesics from `p` whose initial velocities do not lie on a common ray do not meet
  for small positive parameters, by injectivity of `exp_p` on a normal ball.
* Near a compact set of parameters of its maximal interval, a maximal geodesic agrees with a curve
  which is smooth on the whole line: its composition with a smooth function of the parameter
  equal to the identity near the compact set and with values in the maximal interval. The same
  holds for its affine reparametrizations, which are moreover geodesics with nonzero velocity
  on a compact interval mapped into the maximal interval.

## Main results

* `TauCeti.Manifold.exists_mem_nhds_injOn_maximalGeodesic`: geodesics are locally injective.
* `TauCeti.Manifold.exists_pos_maximalGeodesic_ne_of_not_sameRay`: radial geodesics in directions
  on no common ray do not meet near `p`.
* `TauCeti.Manifold.exists_contMDiff_eventuallyEq_maximalGeodesic`: a maximal geodesic agrees near
  a compact set of parameters with a curve smooth on the whole line.
* `TauCeti.Manifold.exists_contMDiff_isGeodesicCurveOn_maximalGeodesic`: the same for an affine
  reparametrization on a compact interval, which is a geodesic with nonzero velocity there.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5 and 6.
-/

public section

open Bundle Filter Function Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

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
  have hγ := (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.contMDiffAt_infty
    (isOpen_geodesicInterval.mem_nhds ht)
  refine hγ.exists_mem_nhds_injOn (by simp) ?_
  rw [(hasMFDerivAt_curveVelocity (hγ.mdifferentiableAt (by simp))).mfderiv]
  exact smul_left_injective ℝ (curveVelocity_maximalGeodesic_ne_zero hv ht)

/-- **Radial geodesics in different directions separate.** If the tangent vectors `v` and
`w` at `p` do not lie on a common ray, the radial geodesics from `p` with these initial
velocities do not meet for small positive parameters. -/
theorem exists_pos_maximalGeodesic_ne_of_not_sameRay {w : TangentSpace I p}
    (hvw : ¬ SameRay ℝ v w) :
    ∃ ε > 0, ∀ a ∈ Ioo 0 ε, ∀ b ∈ Ioo 0 ε,
      maximalGeodesic I M p v a ≠ maximalGeodesic I M p w b := by
  obtain ⟨r, hr, hN⟩ := exists_isNormalDomain_ball (I := I) p
  have hmem {x : TangentSpace I p} {a : ℝ} (ha : a ∈ Ioo 0 (r / (‖x‖ + 1))) :
      a • x ∈ ball (0 : TangentSpace I p) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha.1]
    have h := ha.2
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith [norm_nonneg x, ha.1]
  refine ⟨min (r / (‖v‖ + 1)) (r / (‖w‖ + 1)), by positivity, fun a ha b hb hab ↦ hvw ?_⟩
  have hav := hmem (x := v) ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩
  have hbw := hmem (x := w) ⟨hb.1, hb.2.trans_le (min_le_right _ _)⟩
  rw [← riemannianExp_smul, ← riemannianExp_smul] at hab
  exact Or.inr (Or.inr ⟨a, b, ha.1, hb.1, hN.injOn hav hbw hab⟩)

/-- **Smooth extension of a geodesic segment.** Near a compact set `K` of parameters in its
maximal interval, the maximal geodesic from `p` with initial velocity `v` agrees with a curve
which is smooth on the whole line. -/
theorem exists_contMDiff_eventuallyEq_maximalGeodesic {K : Set ℝ} (hK : IsCompact K)
    (hKG : K ⊆ geodesicInterval I M p v) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧ ∀ t ∈ K, f =ᶠ[𝓝 t] maximalGeodesic I M p v := by
  exact (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.contMDiffOn_infty
    |>.exists_contMDiff_eventuallyEq_of_convex isOpen_geodesicInterval
      isPreconnected_geodesicInterval.ordConnected.convex zero_mem_geodesicInterval hK hKG

/-- **An affinely reparametrized geodesic segment as a smooth geodesic piece.** If `v ≠ 0`,
`m ≠ 0`, `t₀ < t₁` and `m * u + k` lies in the maximal interval of `v` for `u ∈ [t₀, t₁]`, there
is a curve smooth on the whole line which agrees with `u ↦ γ_v (m * u + k)` on `[t₀, t₁]`, is a
geodesic there and has nonzero velocity there. -/
theorem exists_contMDiff_isGeodesicCurveOn_maximalGeodesic {m k t₀ t₁ : ℝ} (hv : v ≠ 0)
    (hm : m ≠ 0) (ht : t₀ < t₁) (hG : ∀ u ∈ Icc t₀ t₁, m * u + k ∈ geodesicInterval I M p v) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧
      EqOn f (fun u ↦ maximalGeodesic I M p v (m * u + k)) (Icc t₀ t₁) ∧
      IsGeodesicCurveOn I f (Icc t₀ t₁) ∧ ∀ u ∈ Icc t₀ t₁, curveVelocity I f u ≠ 0 := by
  have hφ : Continuous fun u : ℝ ↦ m * u + k := by fun_prop
  obtain ⟨g, hg, hev⟩ := exists_contMDiff_eventuallyEq_maximalGeodesic (I := I) (v := v)
    (isCompact_Icc.image hφ) (image_subset_iff.2 hG)
  have hev' (u : ℝ) (hu : u ∈ Icc t₀ t₁) :
      (fun x ↦ g (m * x + k)) =ᶠ[𝓝 u] fun x ↦ maximalGeodesic I M p v (m * x + k) :=
    (hev _ (mem_image_of_mem _ hu)).comp_tendsto hφ.continuousAt
  have heq : EqOn (fun x ↦ g (m * x + k)) (fun x ↦ maximalGeodesic I M p v (m * x + k))
      (Icc t₀ t₁) := fun u hu ↦ (hev' u hu).self_of_nhds
  refine ⟨fun x ↦ g (m * x + k), hg.comp (contDiff_const.mul contDiff_id |>.add
    contDiff_const).contMDiff, heq, ?_, fun u hu ↦ ?_⟩
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
    exact smul_ne_zero hm (curveVelocity_maximalGeodesic_ne_zero hv (hG u hu))

end TauCeti.Manifold
