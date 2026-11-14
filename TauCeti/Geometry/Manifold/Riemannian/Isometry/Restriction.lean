/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Curvature of a metric restricted to an open submanifold

Let `g` be a smooth Riemannian metric on `M` and `U ⊆ M` an open set. The inclusion
`U → M` is a local Riemannian isometry from the restricted metric `g|_U`
(`Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace`) to `g`, so every curvature quantity
of `g|_U` at `x ∈ U` is that of `g` at `x`. In particular `Scal(g|_U) = Scal(g)` on `U`.

Consequently scalar curvature is local in the metric: two metrics that agree on a neighbourhood of
`x` have the same scalar curvature at `x`, and two metrics that agree on an open set have the same
scalar curvature there. This is what lets constructions that modify a metric only away from a set,
such as gluing along collars or interpolating in a tube, keep the scalar curvature unchanged
where the metric is unchanged.

Likewise, the restriction of a metric on `M × ℝ` to the manifold with boundary `M × [a, b]`
(`Bundle.ContMDiffRiemannianMetric.restrictIcc`) is a pullback along a map with invertible
differential, so its scalar curvature at `(x, t)` is that of the metric at `(x, t)`.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.subtype_val`: the inclusion of an open submanifold equipped
  with `TauCeti.Manifold.instRiemannianBundleOpen` is a local Riemannian isometry.
* `TauCeti.exists_riemannianIsometry_ball_of_inner_mfderiv_eq`: a smooth map into an inner-product
  space `F` whose differential is a linear isometry near an interior point restricts to a smooth
  `RiemannianIsometry` from an open submanifold onto an open ball around `0 : F`.
* `Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_restrictOpenTangentSpace`: the
  inclusion of an open submanifold is a local Riemannian isometry from the restricted metric.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_restrictOpenTangentSpace`: the scalar
  curvature of the restricted metric is the scalar curvature of the metric.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_of_eventually_inner_eq`: metrics that agree
  near a point have the same scalar curvature at `x`.
* `Bundle.ContMDiffRiemannianMetric.eqOn_scalarCurvature`: metrics that agree on an open set have
  the same scalar curvature on it.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_restrictIcc`: restriction to `M × [a, b]`
  preserves scalar curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (local isometries) and Proposition 7.6 (naturality of the curvature tensor).
-/

public section

open Bundle Manifold Filter Set TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

open scoped TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion `(Subtype.val : U → M)` of an open submanifold, equipped with the restricted
Riemannian bundle `TauCeti.Manifold.instRiemannianBundleOpen U`, is a local Riemannian isometry. -/
theorem IsLocalRiemannianIsometry.subtype_val
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    IsLocalRiemannianIsometry I I (Subtype.val : U → M) where
  contMDiff := contMDiff_subtype_val
  isInvertible_mfderiv x :=
    ⟨Manifold.tangentSpaceOpenEquiv (I := I) x, (Manifold.mfderiv_subtype_val x).symm⟩
  inner_mfderiv x v w := by
    rw [Manifold.inner_tangentSpace_open U x v w, Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe]
    -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
    rfl

/-- If a smooth map `Φ : M → F` sends an interior point `x₀` to `0`, has differential `L` at `x₀`
for a linear isometric equivalence `L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F`, and preserves inner products on
tangent spaces across an open neighbourhood `W₂ ⊆ U` of `x₀`, then `Φ` restricts to a smooth
`RiemannianIsometry` from an open neighbourhood `W ⊆ U` of `x₀` onto an open ball around `0 : F`. -/
theorem exists_riemannianIsometry_ball_of_inner_mfderiv_eq
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) {U W₂ : Set M} (hW₂open : IsOpen W₂)
    (hx₀W₂ : x₀ ∈ W₂) (hW₂U : W₂ ⊆ U) (L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F)
    {Φ : M → F} (hΦ_smooth : CMDiff ∞ Φ) (hΦ_x₀ : Φ x₀ = 0)
    (hΦ_mv_x₀ : ∀ v : TangentSpace I x₀, mvfderiv I Φ x₀ v = L v)
    (hΦ_inner : ∀ {y : M}, y ∈ W₂ → ∀ v w : TangentSpace I y,
      inner ℝ (mfderiv I 𝓘(ℝ, F) Φ y v) (mfderiv I 𝓘(ℝ, F) Φ y w) = inner ℝ v w) :
    ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r)
      (Ψ : RiemannianIsometry I 𝓘(ℝ, F) W (⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩ : Opens F)),
      (W : Set M) ⊆ U ∧ (Ψ ⟨x₀, hx₀W⟩ : F) = 0 ∧
      ∀ v : TangentSpace I (⟨x₀, hx₀W⟩ : W),
        mvfderiv I ((Subtype.val : (⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩ : Opens F) → F) ∘ Ψ)
            ⟨x₀, hx₀W⟩ v =
          L (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x₀, hx₀W⟩ v) := by
  have : FiniteDimensional ℝ F := L.toLinearEquiv.finiteDimensional
  let e₀ : TangentSpace I x₀ ≃L[ℝ] TangentSpace 𝓘(ℝ, F) (Φ x₀) :=
    L.toLinearEquiv.toContinuousLinearEquiv.trans (NormedSpace.fromTangentSpace (Φ x₀)).symm
  have he₀ : (e₀ : TangentSpace I x₀ →L[ℝ] TangentSpace 𝓘(ℝ, F) (Φ x₀)) =
      mfderiv I 𝓘(ℝ, F) Φ x₀ := by
    ext v
    apply (NormedSpace.fromTangentSpace (Φ x₀)).injective
    simpa [e₀, mvfderiv] using (hΦ_mv_x₀ v).symm
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ Φ x₀ :=
    isLocalDiffeomorphAt_of_mfderiv_eq hΦ_smooth.contMDiffOn isOpen_univ (mem_univ x₀) hx₀
      (by simp) he₀
  let ψ := hloc.localInverse
  let S : Set F := ψ.source ∩ ψ ⁻¹' W₂
  have hS_open : IsOpen S :=
    hloc.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage ψ.open_source hW₂open
  have h0S : (0 : F) ∈ S := by
    refine ⟨hΦ_x₀ ▸ hloc.localInverse_mem_source, ?_⟩
    simpa only [mem_preimage, ψ, ← hΦ_x₀,
      hloc.localInverse_left_inv hloc.localInverse_mem_target] using hx₀W₂
  obtain ⟨r, hr, hr_sub⟩ := Metric.isOpen_iff.1 hS_open 0 h0S
  let W_set : Set M := (ψ.target ∩ W₂) ∩ Φ ⁻¹' Metric.ball (0 : F) r
  have hW_open : IsOpen W_set :=
    (ψ.open_target.inter hW₂open).inter (Metric.isOpen_ball.preimage hΦ_smooth.continuous)
  have hx₀W : x₀ ∈ W_set := ⟨⟨hloc.localInverse_mem_target, hx₀W₂⟩, by simp [hΦ_x₀, hr]⟩
  let W : Opens M := ⟨W_set, hW_open⟩
  let B : Opens F := ⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩
  have hψ_maps {z : F} (hz : z ∈ Metric.ball (0 : F) r) : ψ z ∈ W_set := by
    obtain ⟨hz_src, hψW₂⟩ := hr_sub hz
    refine ⟨⟨ψ.map_source hz_src, hψW₂⟩, ?_⟩
    simpa only [mem_preimage, ψ, hloc.localInverse_right_inv hz_src] using hz
  let d : Diffeomorph I 𝓘(ℝ, F) W B ∞ :=
    { toFun := fun y ↦ ⟨Φ y.1, y.2.2⟩
      invFun := fun z ↦ ⟨ψ z.1, hψ_maps z.2⟩
      left_inv := fun y ↦ Subtype.ext (hloc.localInverse_left_inv y.2.1.1)
      right_inv := fun z ↦ Subtype.ext (hloc.localInverse_right_inv (hr_sub z.2).1)
      contMDiff_toFun :=
        (ContMDiff.subtypeVal_comp_iff B _).mp (hΦ_smooth.comp contMDiff_subtype_val)
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff W _).mp <|
        contMDiffOn_univ.1 <|
          hloc.contMDiffOn_localInverse.comp contMDiff_subtype_val.contMDiffOn
            fun z _ ↦ (hr_sub z.2).1 }
  have hcomp_coe : ((Subtype.val : B → F) ∘ d) = (Φ ∘ (Subtype.val : W → M)) := rfl
  let Ψ : RiemannianIsometry I 𝓘(ℝ, F) W B :=
    { toDiffeomorph := d
      inner_mfderiv' := fun y v w ↦ by
        have hιB := IsLocalRiemannianIsometry.subtype_val (I := 𝓘(ℝ, F)) B
        have hιW := IsLocalRiemannianIsometry.subtype_val (I := I) W
        have hdf (u : TangentSpace I y) :
            mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : B → F) (d y) (mfderiv I 𝓘(ℝ, F) d y u) =
              mfderiv I 𝓘(ℝ, F) Φ y.1 (mfderiv I I (Subtype.val : W → M) y u) := by
          rw [← mfderiv_comp_apply y (hιB.mdifferentiableAt (d y))
              (d.contMDiff.mdifferentiableAt (by simp)),
            hcomp_coe,
            mfderiv_comp_apply y (hΦ_smooth.mdifferentiableAt (by simp)) (hιW.mdifferentiableAt y)]
        rw [← hιB.inner_mfderiv (d y), hdf v, hdf w, hΦ_inner y.2.1.2, hιW.inner_mfderiv y] }
  refine ⟨W, hx₀W, r, hr, Ψ, fun y hy ↦ hW₂U hy.1.2, hΦ_x₀, fun v ↦ ?_⟩
  have hmv := mvfderiv_comp_apply (⟨x₀, hx₀W⟩ : W) (hΦ_smooth.mdifferentiableAt (by simp))
    ((IsLocalRiemannianIsometry.subtype_val (I := I) W).mdifferentiableAt ⟨x₀, hx₀W⟩) v
  rw [Manifold.mfderiv_subtype_val, hΦ_mv_x₀] at hmv
  exact hmv

end TauCeti

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of an open submanifold `U ⊆ M` is a local Riemannian isometry from the
restriction of a metric `g` to `U` to the metric `g` itself. -/
theorem isLocalRiemannianIsometry_restrictOpenTangentSpace [IsManifold I 1 M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    letI : RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I I (Subtype.val : U → M) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact g.riemannianBundle_restrictOpenTangentSpace_eq U ▸
    TauCeti.IsLocalRiemannianIsometry.subtype_val U

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- **Scalar curvature is local.** The scalar curvature of the restriction of a metric `g` to an
open submanifold `U` is the scalar curvature of `g` at each point of `U`. -/
@[simp]
theorem scalarCurvature_restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (U : Opens M) (x : U) :
    (g.restrictOpenTangentSpace U).scalarCurvature x = g.scalarCurvature x := by
  let _ : RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
    ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [scalarCurvature_def, scalarCurvature_def,
    (g.isLocalRiemannianIsometry_restrictOpenTangentSpace U).scalarCurvature_map x]

/-- **Locality of scalar curvature.** Two metrics that agree on a neighbourhood of `x` have the
same scalar curvature at `x`. -/
theorem scalarCurvature_eq_of_eventually_inner_eq
    {g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (h : ∀ᶠ y in 𝓝 x, g₁.inner y = g₂.inner y) :
    g₁.scalarCurvature x = g₂.scalarCurvature x := by
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 h
  have hres := restrictOpenTangentSpace_eq_of_inner_eq ⟨U, hUo⟩ hU
  rw [← scalarCurvature_restrictOpenTangentSpace g₁ ⟨U, hUo⟩ ⟨x, hxU⟩, hres,
    scalarCurvature_restrictOpenTangentSpace]

/-- Two metrics that agree on an open set have the same scalar curvature on it. -/
theorem eqOn_scalarCurvature
    {g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {U : Set M}
    (hU : IsOpen U) (h : ∀ x ∈ U, g₁.inner x = g₂.inner x) :
    Set.EqOn g₁.scalarCurvature g₂.scalarCurvature U := fun _ hx ↦
  scalarCurvature_eq_of_eventually_inner_eq (eventually_of_mem (hU.mem_nhds hx) h)

/-- The scalar curvature of the restriction of a metric `G` on `M × ℝ` to `M × [a, b]` at
`(x, t)` is that of `G` at `(x, t)`. -/
@[simp]
theorem scalarCurvature_restrictIcc {a b : ℝ} [Fact (a < b)]
    (G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)) (p : M × Set.Icc a b) :
    (G.restrictIcc a b).scalarCurvature p = G.scalarCurvature (p.1, p.2) := by
  rw [restrictIcc_eq_pullback]
  exact scalarCurvature_pullback_of_isInvertible G _
    TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc p

end Bundle.ContMDiffRiemannianMetric
