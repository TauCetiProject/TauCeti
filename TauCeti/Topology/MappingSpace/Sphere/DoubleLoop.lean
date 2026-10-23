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

/-- The double-loop homeomorphism is the inverse of `basedMapCircleHomeomorph` of the loop space.
The definition body is not unfolded outside this module. -/
theorem loopSpace2Homeomorph_def :
    loopSpace2Homeomorph X = (basedMapCircleHomeomorph X.loopSpace).symm := by
  rw [loopSpace2Homeomorph]

/-- A double loop as a map from the circle to the loop space: the underlying map of the based map
that corresponds to it under `loopSpace2Homeomorph`. -/
def loopSpace2ToMapCircle :
    C((X.iteratedLoopSpace 2).carrier, C(Sphere1, Path X.basepoint X.basepoint)) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
    C(BasedMap Sphere1 X.loopSpace.carrier Sphere1.east X.loopSpace.basepoint,
      C(Sphere1, Path X.basepoint X.basepoint))).comp (loopSpace2Homeomorph X : C(_, _))

/-- Along the standard parametrization of the circle, the map of a double loop is the loop of the
loop space that it is: its value at `circleLoop t` is the value of the double loop, read as a
cube loop in `Ω X`, at `t`. -/
@[simp]
theorem loopSpace2ToMapCircle_circleLoop (γ : (X.iteratedLoopSpace 2).carrier)
    (t : Fin 1 → unitInterval) :
    loopSpace2ToMapCircle X γ (circleLoop t) = iteratedLoopSpaceHomeomorph 1 X.loopSpace γ t := by
  have h : basedMapCircleHomeomorph X.loopSpace (loopSpace2Homeomorph X γ) = γ :=
    (basedMapCircleHomeomorph X.loopSpace).apply_symm_apply _
  have := iteratedLoopSpaceHomeomorph_basedMapCircleHomeomorph X.loopSpace
    (loopSpace2Homeomorph X γ) t
  rw [h] at this
  -- the map of a double loop is the underlying map of its based map, by definition
  exact this.symm

/-- The map of a double loop is based: it sends the basepoint `(1, 0)` of the circle to the
constant loop. -/
@[simp]
theorem loopSpace2ToMapCircle_east (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2ToMapCircle X γ Sphere1.east = Path.refl X.basepoint :=
  (loopSpace2Homeomorph X γ).2

/-- The embedding of the double loop space in the space of maps from the circle to the loop space
is a topological embedding. -/
theorem isEmbedding_loopSpace2ToMapCircle : IsEmbedding (loopSpace2ToMapCircle X) :=
  -- the loop space carrier is the type of paths, so the subtype of based maps is that of
  -- `C(S¹, Path _ _)`
  (IsEmbedding.subtypeVal (X := C(Sphere1, Path X.basepoint X.basepoint))).comp
    (loopSpace2Homeomorph X).isEmbedding

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
  -- unfolding the bundled map leaves evaluation of the map from the circle
  rfl

/-- Evaluating a double loop along the standard parametrization of the circle gives the loop of
the loop space that it is. -/
theorem evalCircle_circleLoop (γ : (X.iteratedLoopSpace 2).carrier) (t : Fin 1 → unitInterval) :
    evalCircle X (circleLoop t, γ) = iteratedLoopSpaceHomeomorph 1 X.loopSpace γ t := by
  rw [evalCircle_apply, loopSpace2ToMapCircle_circleLoop]

/-- Evaluating a double loop at the basepoint of the circle gives the constant loop. -/
theorem evalCircle_east (γ : (X.iteratedLoopSpace 2).carrier) :
    evalCircle X (Sphere1.east, γ) = Path.refl X.basepoint := by
  rw [evalCircle_apply, loopSpace2ToMapCircle_east]

variable {X} {Y : BasedTopologicalSpace.{u}}

/-- **Naturality of `Ω²X ≃ₜ Map_*(S¹, ΩX)`** in the based space `X`. -/
theorem loopSpace2Homeomorph_map (f : Hom X Y) (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2Homeomorph Y (f.iteratedLoopSpace 2 γ) =
      BasedMap.map f.loopSpace.toContinuousMap f.loopSpace.map_basepoint
        (loopSpace2Homeomorph X γ) := by
  have e : f.iteratedLoopSpace 2 γ = f.loopSpace.iteratedLoopSpace 1 γ := by
    rw [Hom.iteratedLoopSpace_succ]
    -- `Ω^[2] X` is `Ω^[1] (Ω X)` by definition of the iterate, so both maps agree
    rfl
  apply (basedMapCircleHomeomorph Y.loopSpace).injective
  -- `Ω^[2] X` is `Ω^[1] (Ω X)` by definition, so `apply_symm_apply` applies up to this unfolding
  have h1 : basedMapCircleHomeomorph Y.loopSpace
      (loopSpace2Homeomorph Y (f.iteratedLoopSpace 2 γ)) = f.iteratedLoopSpace 2 γ :=
    (basedMapCircleHomeomorph Y.loopSpace).apply_symm_apply _
  have h2 : basedMapCircleHomeomorph X.loopSpace (loopSpace2Homeomorph X γ) = γ :=
    (basedMapCircleHomeomorph X.loopSpace).apply_symm_apply _
  rw [h1, basedMapCircleHomeomorph_map f.loopSpace, h2, e]

/-- **Naturality of the embedding `Ω²X → Map(S¹, ΩX)`** in the based space `X`. -/
theorem loopSpace2ToMapCircle_map (f : Hom X Y) (γ : (X.iteratedLoopSpace 2).carrier) :
    loopSpace2ToMapCircle Y (f.iteratedLoopSpace 2 γ) =
      f.loopSpace.toContinuousMap.comp (loopSpace2ToMapCircle X γ) := by
  refine ContinuousMap.ext fun b => ?_
  rw [loopSpace2ToMapCircle, loopSpace2ToMapCircle, ContinuousMap.comp_apply,
    ContinuousMap.comp_apply]
  -- the coercions of the homeomorphisms to bundled maps evaluate as the homeomorphisms
  change (loopSpace2Homeomorph Y (f.iteratedLoopSpace 2 γ)).1 b = _
  rw [loopSpace2Homeomorph_map]
  exact BasedMap.map_apply _ _ _ b

/-- **Naturality of the evaluation `S¹ × Ω²X → ΩX`** in the based space `X`. -/
theorem evalCircle_map (f : Hom X Y) (z : Sphere1) (γ : (X.iteratedLoopSpace 2).carrier) :
    evalCircle Y (z, f.iteratedLoopSpace 2 γ) = f.loopSpace (evalCircle X (z, γ)) := by
  rw [evalCircle_apply, evalCircle_apply, loopSpace2ToMapCircle_map]
  exact ContinuousMap.comp_apply _ _ _

end BasedTopologicalSpace

end TauCeti
