/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.IteratedLoopSpace.Homeomorph
public import TauCeti.Topology.MappingSpace.Based
public import TauCeti.Topology.Sphere.StandardCircle

/-!
# Based maps out of the circle are loops

Parametrizing the circle `S¹ ⊆ ℝ²` by the standard loop `t ↦ (cos 2πt, sin 2πt)`
(`TauCeti.circleLoop`), which is a quotient map `I¹ → S¹` collapsing the end points to `(1, 0)`, the
space `Map_*(S¹, Y)` of maps from the circle sending `(1, 0)` to the basepoint of `Y` is
homeomorphic to the loop space `ΩY`, naturally in `Y`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.basedMapCircleHomeomorph`: `Map_*(S¹, Y) ≃ₜ ΩY`.
* `TauCeti.BasedTopologicalSpace.iteratedLoopSpaceHomeomorph_basedMapCircleHomeomorph`: the value
  of the loop of a based map `φ` at `t` is `φ (circleLoop t)`.
* `TauCeti.BasedTopologicalSpace.basedMapCircleHomeomorph_map`: naturality in `Y`.
-/

public section

noncomputable section

namespace TauCeti

namespace BasedTopologicalSpace

universe u

/-- Based maps from the circle to a based space `Y` are the loops `Ω Y`, through the standard
parametrization `circleLoop` of the circle. -/
def basedMapCircleHomeomorph (Y : BasedTopologicalSpace.{u}) :
    BasedMap Sphere1 Y.carrier Sphere1.east Y.basepoint ≃ₜ (Y.iteratedLoopSpace 1).carrier :=
  (BasedMap.homeomorphGenLoop circleLoop Sphere1.east circleLoop_eq_east_iff
    circleLoop_surjective fun _ _ h => eq_or_of_circleLoop_eq h).trans
      (iteratedLoopSpaceHomeomorph 1 Y).symm

/-- A based map `φ` from the circle, read as a loop, is the generalized loop `t ↦ φ (circleLoop t)`:
the value of the loop at `t` is the value of `φ` at the point `(cos 2πt, sin 2πt)`. -/
theorem iteratedLoopSpaceHomeomorph_basedMapCircleHomeomorph (Y : BasedTopologicalSpace.{u})
    (φ : BasedMap Sphere1 Y.carrier Sphere1.east Y.basepoint) (t : Fin 1 → unitInterval) :
    iteratedLoopSpaceHomeomorph 1 Y (basedMapCircleHomeomorph Y φ) t = φ.1 (circleLoop t) := by
  rw [basedMapCircleHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  exact BasedMap.homeomorphGenLoop_apply _ _ _ _ _ _ _

variable {X Y : BasedTopologicalSpace.{u}}

/-- Naturality of `basedMapCircleHomeomorph` in the based space. -/
theorem basedMapCircleHomeomorph_map (f : Hom X Y)
    (φ : BasedMap Sphere1 X.carrier Sphere1.east X.basepoint) :
    basedMapCircleHomeomorph Y (BasedMap.map f.toContinuousMap f.map_basepoint φ) =
      f.iteratedLoopSpace 1 (basedMapCircleHomeomorph X φ) := by
  apply (iteratedLoopSpaceHomeomorph 1 Y).injective
  rw [iteratedLoopSpaceHomeomorph_map, basedMapCircleHomeomorph, basedMapCircleHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]
  exact BasedMap.homeomorphGenLoop_map _ _ _ _ _ _ _ _

end BasedTopologicalSpace

end TauCeti
