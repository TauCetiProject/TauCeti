/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Basic
public import TauCeti.Geometry.Manifold.Groupoid.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.SeparatedMap

/-!
# Étale topological groupoids as Lie groupoids

For a topological groupoid on finite-dimensional real manifolds with boundaryless models,
Hausdorff objects and second-countable total arrows, locally diffeomorphic source and target
give a Lie groupoid structure on the given atlases.
-/

public section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti.IsTopologicalGroupoid

variable {E H F K C : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [J.Boundaryless]
  [Category C] [IsGroupoid C] [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace K (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsTopologicalGroupoid C]

/-- A topological groupoid with locally diffeomorphic source and target on boundaryless real
manifolds is a Lie groupoid when its objects are Hausdorff and its total arrows are second
countable. The source fibres are discrete. -/
theorem isLieGroupoid_of_isLocalDiffeomorph [T2Space C]
    [SecondCountableTopology (Quiver.Total C)]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C)) :
    IsLieGroupoid I J C := by
  have hsub : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C) :=
    (hs.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      fun a ↦ ((hs a).mfderivToContinuousLinearEquiv (by simp)).surjective).isSubmersion
  have hinv := contMDiff_inverse hs ht
  have h₂ (x : C) : T2Space {a : Quiver.Total C // a.left = x} := by
    have : DiscreteTopology {a : Quiver.Total C // a.left = x} :=
      (hs.isLocalHomeomorph.isLocallyInjective.isDiscrete_preimage_singleton x).to_subtype
    infer_instance
  refine ⟨inferInstance, inferInstance, hsub, contMDiff_unit hs, hinv, ?_, h₂⟩
  let htrans := fun (p : Quiver.Total C × Quiver.Total C) (_ : p.1.right = p.2.left) ↦
    transverse_of_isSubmersion_right (IX := J) (f := Quiver.Total.right)
      (by simp) hsub p
  let := transverseFiberProductChartedSpace
    (f := (Quiver.Total.right : Quiver.Total C → C))
    (g := (Quiver.Total.left : Quiver.Total C → C)) (n := ∞) (by simp)
    (hsub.contMDiff.comp hinv) hsub.contMDiff htrans
  have hcoe := (isSmoothEmbedding_coe_transverseFiberProduct
    (f := (Quiver.Total.right : Quiver.Total C → C))
    (g := (Quiver.Total.left : Quiver.Total C → C)) (n := ∞) (by simp)
    (hsub.contMDiff.comp hinv) hsub.contMDiff htrans).contMDiff
  refine ContMDiff.of_comp_isLocalDiffeomorph hs continuous_comp ?_
  simpa only [Function.comp_def, Quiver.Total.comp_left] using hs.contMDiff.comp hcoe.fst

end TauCeti.IsTopologicalGroupoid
