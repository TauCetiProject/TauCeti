/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Sphere.Circle

/-!
# The double loop space inside the free loop space of the loop space

A double loop is a loop in the loop space `ΩX`, that is, a based map from the circle to `ΩX`,
the circle being parametrized by the standard loop `t ↦ (cos 2πt, sin 2πt)` (`TauCeti.circleLoop`),
based at `(1, 0)`. So the double loop space `Ω²X` embeds in the space `Map(S¹, ΩX)` of all maps
from the circle to `ΩX`, and evaluation `S¹ × Map(S¹, ΩX) → ΩX` restricts to a continuous map
`S¹ × Ω²X → ΩX`. On singular homology, composing the cross product with the fundamental class of
`S¹` with the map induced by this evaluation gives the degree-raising map
`H_*(Ω²X) → H_{*+1}(ΩX)`.

All maps are natural in the based space `X`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.loopSpace2Homeomorph`: `Ω²X ≃ₜ Map_*(S¹, ΩX)`, natural in `X`
  by `TauCeti.BasedTopologicalSpace.loopSpace2Homeomorph_map`.
* `TauCeti.BasedTopologicalSpace.loopSpace2ToMapCircle`: the embedding `Ω²X → Map(S¹, ΩX)`, with
  `TauCeti.BasedTopologicalSpace.isEmbedding_loopSpace2ToMapCircle` its embedding property and
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

variable (X : BasedTopologicalSpace.{u})

-- `Ω^[2] X` is `Ω^[1] (Ω X)` by the definition of the iterate, so the inverse of
-- `basedMapCircleHomeomorph (Ω X)` is defined on the double loop space.
/-- **Double loops are based maps from the circle to the loop space**: `Ω²X ≃ₜ Map_*(S¹, ΩX)`,
for the standard parametrization of the circle. -/
def loopSpace2Homeomorph :
    (X.iteratedLoopSpace 2).carrier ≃ₜ
      BasedMap Sphere1 X.loopSpace.carrier Sphere1.east X.loopSpace.basepoint :=
  (basedMapCircleHomeomorph X.loopSpace).symm

/-- Reading the double loop `γ` as a based map from the circle and back gives `γ`. -/
theorem basedMapCircleHomeomorph_loopSpace2Homeomorph (γ : (X.iteratedLoopSpace 2).carrier) :
    basedMapCircleHomeomorph X.loopSpace (loopSpace2Homeomorph X γ) = γ :=
  (basedMapCircleHomeomorph X.loopSpace).apply_symm_apply γ

/-- A double loop as a map from the circle to the loop space. -/
def loopSpace2ToMapCircle : C((X.iteratedLoopSpace 2).carrier, C(Sphere1, X.loopSpace.carrier)) :=
  ⟨fun γ => (loopSpace2Homeomorph X γ).1,
    continuous_subtype_val.comp (loopSpace2Homeomorph X).continuous⟩

/-- The double loop as a map from the circle is the underlying map of the based map. -/
theorem loopSpace2ToMapCircle_apply (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2ToMapCircle X γ = (loopSpace2Homeomorph X γ).1 := by
  rw [loopSpace2ToMapCircle]
  rfl

/-- The embedding of the double loop space in the space of maps from the circle to the loop space
is a topological embedding. -/
theorem isEmbedding_loopSpace2ToMapCircle : IsEmbedding (loopSpace2ToMapCircle X) :=
  IsEmbedding.subtypeVal.comp (loopSpace2Homeomorph X).isEmbedding

/-- Evaluation of a double loop on the circle: `S¹ × Ω²X → ΩX`. -/
def evalCircle :
    C(Sphere1 × (X.iteratedLoopSpace 2).carrier, Path X.basepoint X.basepoint) :=
  ⟨fun p => loopSpace2ToMapCircle X p.2 p.1,
    continuous_eval.comp (Continuous.prodMk
      ((loopSpace2ToMapCircle X).continuous.comp continuous_snd) continuous_fst)⟩

/-- Evaluating a double loop on the circle is evaluating its map from the circle. -/
@[simp]
theorem evalCircle_apply (z : Sphere1) (γ : (X.iteratedLoopSpace 2).carrier) :
    evalCircle X (z, γ) = loopSpace2ToMapCircle X γ z := by
  rw [evalCircle]
  rfl

variable {X} {Y : BasedTopologicalSpace.{u}}

/-- **Naturality of `Ω²X ≃ₜ Map_*(S¹, ΩX)`** in the based space `X`. -/
theorem loopSpace2Homeomorph_map (f : Hom X Y) (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2Homeomorph Y (f.iteratedLoopSpace 2 γ) =
      BasedMap.map f.loopSpace.toContinuousMap f.loopSpace.map_basepoint
        (loopSpace2Homeomorph X γ) := by
  apply (basedMapCircleHomeomorph Y.loopSpace).injective
  have e : f.iteratedLoopSpace 2 γ = f.loopSpace.iteratedLoopSpace 1 γ := by
    rw [Hom.iteratedLoopSpace_succ]
    rfl
  rw [basedMapCircleHomeomorph_map f.loopSpace, basedMapCircleHomeomorph_loopSpace2Homeomorph,
    basedMapCircleHomeomorph_loopSpace2Homeomorph, e]

/-- **Naturality of the embedding `Ω²X → Map(S¹, ΩX)`** in the based space `X`. -/
theorem loopSpace2ToMapCircle_map (f : Hom X Y) (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2ToMapCircle Y (f.iteratedLoopSpace 2 γ) =
      f.loopSpace.toContinuousMap.comp (loopSpace2ToMapCircle X γ) := by
  rw [loopSpace2ToMapCircle_apply, loopSpace2ToMapCircle_apply, loopSpace2Homeomorph_map]
  exact ContinuousMap.ext fun b => BasedMap.map_apply _ _ _ b

/-- **Naturality of the evaluation `S¹ × Ω²X → ΩX`** in the based space `X`. -/
theorem evalCircle_map (f : Hom X Y) (z : Sphere1) (γ : (X.iteratedLoopSpace 2).carrier) :
    evalCircle Y (z, f.iteratedLoopSpace 2 γ) = f.loopSpace (evalCircle X (z, γ)) := by
  rw [evalCircle_apply, evalCircle_apply, loopSpace2ToMapCircle_map]
  exact ContinuousMap.comp_apply _ _ _

end BasedTopologicalSpace

end TauCeti
