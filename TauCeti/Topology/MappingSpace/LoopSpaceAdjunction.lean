/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Sphere

/-!
# The double loop space inside the free loop space of the loop space

A double loop is a loop in the loop space `ΩX`, that is, a based map from the circle to `ΩX`. So
the double loop space `Ω²X` embeds in the space `Map(S¹, ΩX)` of all maps from the circle to `ΩX`,
and evaluation `S¹ × Map(S¹, ΩX) → ΩX` restricts to a continuous map
`S¹ × Ω²X → ΩX`. On singular homology, composing the cross product with the fundamental class of
`S¹` with the map induced by this evaluation gives the degree-raising map
`H_*(Ω²X) → H_{*+1}(ΩX)`.

All maps are natural in the based space `X`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.loopSpace2Homeomorph`: `Ω²X ≃ₜ Map_*(S¹, ΩX)`.
* `TauCeti.BasedTopologicalSpace.loopSpace2ToMapCircle`: the embedding `Ω²X → Map(S¹, ΩX)`, with
  `TauCeti.BasedTopologicalSpace.loopSpace2ToMapCircle_map` its naturality.
* `TauCeti.BasedTopologicalSpace.evalCircle`: the evaluation `S¹ × Ω²X → ΩX`, with
  `TauCeti.BasedTopologicalSpace.evalCircle_map` its naturality.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2.
-/

public section

noncomputable section

open Metric Topology

namespace TauCeti

namespace BasedTopologicalSpace

universe u

/-- The unit circle `S¹ ⊆ ℝ²`. -/
abbrev Circle2 : Type := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

variable (X : BasedTopologicalSpace.{u}) (s₀ : Circle2)

/-- **Double loops are based maps from the circle to the loop space**: `Ω²X ≃ₜ Map_*(S¹, ΩX)`. -/
def loopSpace2Homeomorph :
    (X.iteratedLoopSpace 2).carrier ≃ₜ
      BasedMap Circle2 X.loopSpace.carrier s₀ X.loopSpace.basepoint :=
  (basedMapSphereHomeomorphIteratedLoopSpace 1 X.loopSpace s₀).symm

/-- A double loop as a map from the circle to the loop space. -/
def loopSpace2ToMapCircle : C((X.iteratedLoopSpace 2).carrier, C(Circle2, X.loopSpace.carrier)) :=
  ⟨fun γ => (loopSpace2Homeomorph X s₀ γ).1,
    continuous_subtype_val.comp (loopSpace2Homeomorph X s₀).continuous⟩

theorem loopSpace2ToMapCircle_apply (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2ToMapCircle X s₀ γ = (loopSpace2Homeomorph X s₀ γ).1 := by
  rw [loopSpace2ToMapCircle]
  rfl

theorem isEmbedding_loopSpace2ToMapCircle : IsEmbedding (loopSpace2ToMapCircle X s₀) :=
  IsEmbedding.subtypeVal.comp (loopSpace2Homeomorph X s₀).isEmbedding

/-- Evaluation of a double loop on the circle: `S¹ × Ω²X → ΩX`. -/
def evalCircle : C(Circle2 × (X.iteratedLoopSpace 2).carrier, X.loopSpace.carrier) :=
  ⟨fun p => loopSpace2ToMapCircle X s₀ p.2 p.1,
    continuous_eval.comp (Continuous.prodMk
      ((loopSpace2ToMapCircle X s₀).continuous.comp continuous_snd) continuous_fst)⟩

theorem evalCircle_apply (z : Circle2) (γ : (X.iteratedLoopSpace 2).carrier) :
    evalCircle X s₀ (z, γ) = loopSpace2ToMapCircle X s₀ γ z := by
  rw [evalCircle]
  rfl

variable {X} {Y : BasedTopologicalSpace.{u}}

/-- **Naturality of the embedding `Ω²X → Map(S¹, ΩX)`** in the based space `X`. -/
theorem loopSpace2ToMapCircle_map (f : Hom X Y) (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2ToMapCircle Y s₀ (f.iteratedLoopSpace 2 γ) =
      f.loopSpace.toContinuousMap.comp (loopSpace2ToMapCircle X s₀ γ) := by
  have h := basedMapSphereHomeomorphIteratedLoopSpace_map 1 f.loopSpace s₀
    ((loopSpace2Homeomorph X s₀) γ)
  have h' : (loopSpace2Homeomorph Y s₀) (f.iteratedLoopSpace 2 γ) =
      BasedMap.map f.loopSpace.toContinuousMap f.loopSpace.map_basepoint
        (loopSpace2Homeomorph X s₀ γ) := by
    apply (basedMapSphereHomeomorphIteratedLoopSpace 1 Y.loopSpace s₀).injective
    rw [h, Hom.iteratedLoopSpace_succ]
    exact (Homeomorph.apply_symm_apply _ _).trans
      (congrArg _ (Homeomorph.apply_symm_apply _ _).symm)
  rw [loopSpace2ToMapCircle_apply, loopSpace2ToMapCircle_apply, h']
  exact ContinuousMap.ext fun b => BasedMap.map_apply _ _ _ b

/-- **Naturality of the evaluation `S¹ × Ω²X → ΩX`** in the based space `X`. -/
theorem evalCircle_map (f : Hom X Y) (z : Circle2) (γ : (X.iteratedLoopSpace 2).carrier) :
    evalCircle Y s₀ (z, f.iteratedLoopSpace 2 γ) = f.loopSpace (evalCircle X s₀ (z, γ)) := by
  rw [evalCircle_apply, evalCircle_apply, loopSpace2ToMapCircle_map]
  exact ContinuousMap.comp_apply _ _ _

end BasedTopologicalSpace

end TauCeti
