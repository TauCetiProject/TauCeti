/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Cone
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WarpedProd

/-!
# The Riemannian cone metric

This file constructs `Bundle.ContMDiffRiemannianMetric.cone`, the intrinsic `C^n` warped
metric `dr² + r²g` on `radiusDomain × M`, its inner-product formula, and its `IsWarpedProduct`
identification. It also proves that the radial vector has unit norm in the inherited real metric.
Use `open scoped TauCeti` to install that radial metric via
`TauCeti.Manifold.instRiemannianBundleOpen`.

The induced-metric identity for a spherical isometric immersion is downstream motivation;
this file constructs the intrinsic metric without an immersion hypothesis.

Adapted from Yangyang Li's formalization, ported by Riccardo Brasca in commit
`247d17d130a24baafcb83278fbea532f606084b4` of TauCetiProject/TauCeti (Apache 2.0).
-/

public noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff TauCeti

namespace TauCeti.Manifold.Cone

/-- The outward radial vector has squared length one in the inherited real metric. -/
@[simp high]
theorem inner_radialVector_self (r : radiusDomain) :
    inner ℝ (radialVector r) (radialVector r) = 1 := by
  rw [inner_tangentSpace_open_vectorSpace, Real.inner_apply,
    mvfderiv_subtype_val_radialVector, one_mul]

/-- The outward radial vector is a unit vector in the inherited real metric. -/
@[simp high]
theorem norm_radialVector (r : radiusDomain) : ‖radialVector r‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, inner_radialVector_self]
  simp

end TauCeti.Manifold.Cone

open TauCeti.Manifold TauCeti.Manifold.Cone

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : ℕ∞ω}

/-- The `C^n` warped metric `dr²+r²g` on the positive-radius cone parameter domain. -/
def cone (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    ContMDiffRiemannianMetric ((𝓘(ℝ)).prod I) n (ℝ × E)
      (fun p : radiusDomain × M ↦ TangentSpace ((𝓘(ℝ)).prod I) p) :=
  ContMDiffRiemannianMetric.warpedProdTangentSpace
    (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle :
      ContMDiffRiemannianMetric 𝓘(ℝ) n ℝ (fun r : radiusDomain ↦ TangentSpace 𝓘(ℝ) r))
    (fun r : radiusDomain ↦ (r : ℝ)) contMDiff_subtype_val
    (fun r ↦ (coe_radiusDomain_pos r).ne') g

/-- The cone metric is the orthogonal sum of the radial metric and the link metric
multiplied by radius squared. -/
@[simp]
theorem cone_inner (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (p : radiusDomain × M) (v w : TangentSpace ((𝓘(ℝ)).prod I) p) :
    (cone g).inner p v w =
      Inner.inner ℝ (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
        (p.1 : ℝ) ^ 2 * g.inner p.2
          (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2 := by
  rw [cone, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

/-- Installing the constructed metric gives the native warped-product structure of the
regular cone. -/
theorem isWarpedProduct_cone
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle
        (fun p : radiusDomain × M ↦ TangentSpace ((𝓘(ℝ)).prod I) p) :=
      ⟨(cone g).toRiemannianMetric⟩
    IsWarpedProduct 𝓘(ℝ) I M (fun r : radiusDomain ↦ (r : ℝ)) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle
      (fun p : radiusDomain × M ↦ TangentSpace ((𝓘(ℝ)).prod I) p) :=
    ⟨(cone g).toRiemannianMetric⟩
  exact ⟨cone_inner g⟩

end Bundle.ContMDiffRiemannianMetric
