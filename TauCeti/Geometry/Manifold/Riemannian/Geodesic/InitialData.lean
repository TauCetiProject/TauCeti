/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Flow
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Smooth variations of geodesic initial data

At an initial tangent vector `(p, v)`, one can prescribe both the velocity of the base
point and the covariant velocity of the initial vector. The resulting tangent-bundle
curve is smooth throughout one neighbourhood of zero. Composing it with the geodesic
flow gives smooth variations with arbitrary infinitesimal initial data.

The construction follows `CovariantDerivative.exists_contMDiffAt_tangentCurve_initialData`,
strengthening pointwise smoothness to smoothness throughout a fixed neighbourhood. It uses
a short maximal geodesic and globally smooth section extensions to obtain this stronger
regularity without a completeness assumption.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (geodesic variations with prescribed Jacobi initial data).
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p}

/-- Through any initial tangent vector, there is a tangent-bundle curve smooth throughout
a neighbourhood of zero, with prescribed base velocity and covariant velocity for the
Levi-Civita connection. This supplies arbitrary smooth variations of geodesic initial data. -/
theorem _root_.TangentSpace.exists_smooth_initialData (u w : TangentSpace I p) :
    ∃ σ : ℝ → TangentBundle I M,
      σ 0 = TotalSpace.mk' E p v ∧
      (∀ᶠ q in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ σ q) ∧
      curveVelocity I (fun q ↦ (σ q).proj) 0 = u ∧
      alongCurve (leviCivitaConnection I M) (fun q ↦ (σ q).proj)
        (fun q ↦ (σ q).2) 0 = w := by
  let γ := maximalGeodesic I M p u
  let S := geodesicInterval I M p u
  have hS : S ∈ 𝓝 0 := isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ S :=
    (contMDiffOn_maximalGeodesic (I := I) (M := M)).comp
      ((contMDiff_const (c := TotalSpace.mk' E p u)).prodMk contMDiff_id).contMDiffOn
      (fun _ ht ↦ ht)
  have hγ0 : γ 0 = p := maximalGeodesic_zero p u
  have hγvel : curveVelocity I γ 0 = u := by
    rw [← curveVelocityWithin_of_mem_nhds hS]
    exact eq_of_heq (isGeodesicCurveOnFrom_maximalGeodesic p u).velocity_heq
  -- Keep the correction in the fibre over γ 0 until the final initial-state equality.
  let v₀ : TangentSpace I (γ 0) := v
  let w₀ : TangentSpace I (γ 0) := w
  obtain ⟨A, hA, hAv⟩ := exists_contMDiff_section_eq I E ∞ v₀
  obtain ⟨B, hB, hBw⟩ := exists_contMDiff_section_eq I E ∞
    (w₀ - leviCivitaConnection I M A (γ 0) (curveVelocity I γ 0))
  let V : ∀ q, TangentSpace I (γ q) := fun q ↦ A (γ q) + q • B (γ q)
  have hAp : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun q ↦ TotalSpace.mk' E (γ q) (A (γ q))) S := hA.comp_contMDiffOn hγ
  have hBp : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun q ↦ TotalSpace.mk' E (γ q) (B (γ q))) S := hB.comp_contMDiffOn hγ
  have hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun q ↦ TotalSpace.mk' E (γ q) (V q)) S := fun q hq ↦
    (hAp q hq).add_sectionAlong
      ((contMDiff_id q).contMDiffWithinAt.smul_totalSpace (hBp q hq))
  refine ⟨fun q ↦ TotalSpace.mk' E (γ q) (V q), ?_, ?_, hγvel, ?_⟩
  · apply TotalSpace.ext hγ0
    simp only [V, zero_smul, add_zero]
    exact heq_of_eq hAv
  · filter_upwards [hS] with q hq
    exact hV.contMDiffAt (isOpen_geodesicInterval.mem_nhds hq)
  · have hcoordA := differentiableWithinAt_sectionCoord (s := Set.univ) γ (fun q ↦ A (γ q))
      ((hAp.contMDiffAt hS).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ 0))
    have hcoordB := differentiableWithinAt_sectionCoord (s := Set.univ) γ (fun q ↦ B (γ q))
      ((hBp.contMDiffAt hS).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ 0))
    -- The initial-state curve was constructed as the pair (γ, V); expose its two projections.
    change alongCurve (leviCivitaConnection I M) γ V 0 = w₀
    dsimp only [V]
    rw [← alongCurveWithin_univ, alongCurveWithin_add _ _ _ _ Set.univ hcoordA
      (by rw [sectionCoord_smul]; exact differentiableWithinAt_id.fun_smul hcoordB),
      alongCurveWithin_smul _ _ _ (fun q : ℝ ↦ q) Set.univ
        differentiableWithinAt_id hcoordB,
      alongCurveWithin_pullback_curveVelocityWithin _ _ _ uniqueDiffWithinAt_univ
        ((hγ.contMDiffAt hS).mdifferentiableAt (by simp)).mdifferentiableWithinAt
        (hA.mdifferentiableAt (by simp))]
    simp [derivWithin_id', hBw, curveVelocityWithin_univ]

end TauCeti.Manifold
