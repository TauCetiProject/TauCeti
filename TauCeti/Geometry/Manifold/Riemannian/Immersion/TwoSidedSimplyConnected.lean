/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.TwoSided
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Geometry.Manifold.Topology

/-!
# Two-sidedness of hypersurfaces with simply connected source

A hypersurface immersion with simply connected source has a unit normal field. Lift the
identity of the source to its unit normal double cover and use the two-sidedness criterion
for a continuous section of that cover.
-/

public section

open Bundle Manifold Module
open scoped ContDiff Manifold

namespace TauCeti

universe u

variable {E H G N : Type*} {V M : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  [FiniteDimensional ℝ V] {n m : ℕ∞ω} [IsManifold J (m + 1) N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]

/-- A codimension-one immersion of a simply connected manifold has a `C^m` unit normal if
its ambient metric is `C^m` and the immersion is at least `C^{m+1}`. -/
theorem isTwoSidedHypersurface_of_simplyConnectedSpace [SimplyConnectedSpace M]
    {f : M → N} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n)
    (hr : finrank ℝ V = finrank ℝ E + 1) :
    IsTwoSidedHypersurface I J m f := by
  let g : C(M, N) := ⟨f, hf.continuous⟩
  have hg : ContMDiff I J n g := hf
  have : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let := orthogonalNormalFiberBundle hg hinj hm hr
  let := orthogonalNormalVectorBundle hg hinj hm hr
  apply (isTwoSidedHypersurface_iff_exists_section_sphereBundle hg hinj hm hr).2
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨v, hv⟩ := sphereBundleProj_surjective (Fin 1 → ℝ)
    (fun x ↦ orthogonalNormalSpace I J g x) x
  obtain ⟨s, _, hs⟩ := ((isCoveringMap_sphereBundleProj_orthogonalNormalSpace
    hg hinj hm hr).existsUnique_continuousMap_lifts (ContinuousMap.id M) x v hv).exists
  exact ⟨s, s.continuous, congrFun hs⟩

end TauCeti
