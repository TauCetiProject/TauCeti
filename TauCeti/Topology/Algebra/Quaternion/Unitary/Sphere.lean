/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Field.UnitBall
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The three-sphere as a topological group

Let `S³` be the unit sphere of a real normed space of dimension `4`. It is homeomorphic to the unit
quaternions (`TauCeti.threeSphereHomeomorphUnitQuaternion`), a topological group, and transporting
their multiplication makes `S³` a topological group (`TauCeti.threeSphereGroup`,
`TauCeti.isTopologicalGroup_threeSphere`), with identity the point `TauCeti.threeSphereOne`
corresponding to the unit quaternion `1`. The homeomorphism then preserves the identity, products
and inverses.

## Main declarations

* `TauCeti.threeSphereHomeomorphUnitQuaternion`: `S³` is homeomorphic to the unit quaternions.
* `TauCeti.threeSphereGroup`, `TauCeti.isTopologicalGroup_threeSphere`: the topological group
  structure on `S³` transported from the unit quaternions, with identity `TauCeti.threeSphereOne`
  (`TauCeti.threeSphereGroup_one`).
* `TauCeti.threeSphereHomeomorphUnitQuaternion_threeSphereOne`,
  `TauCeti.threeSphereHomeomorphUnitQuaternion_mul`,
  `TauCeti.threeSphereHomeomorphUnitQuaternion_inv`: the homeomorphism with the unit quaternions
  is a group isomorphism.
-/

public section

noncomputable section

universe u

open Metric Module
open scoped Quaternion

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3 + 1)

include hE in
/-- The unit sphere of a four-dimensional real normed space is homeomorphic to the unit
quaternions. -/
def threeSphereHomeomorphUnitQuaternion : sphere (0 : E) 1 ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  sphereHomeomorphOfFinrankEq (by rw [hE, Quaternion.finrank_eq_four])

/-- The group structure on the three-sphere transported from the unit quaternions. -/
abbrev threeSphereGroup : Group (sphere (0 : E) 1) :=
  (threeSphereHomeomorphUnitQuaternion hE).toEquiv.group

/-- With the multiplication transported from the unit quaternions, the three-sphere is a
topological group: the homeomorphism with the unit quaternions is then a group isomorphism. -/
theorem isTopologicalGroup_threeSphere :
    @IsTopologicalGroup (sphere (0 : E) 1) _ (threeSphereGroup hE) :=
  letI := threeSphereGroup hE
  (threeSphereHomeomorphUnitQuaternion hE).isInducing.isTopologicalGroup
    (threeSphereHomeomorphUnitQuaternion hE).toEquiv.mulEquiv

/-- The point of the three-sphere corresponding to the unit quaternion `1`, the identity of
`TauCeti.threeSphereGroup` (`TauCeti.threeSphereGroup_one`). Its body is exposed so that loops
based at it are loops based at that identity by definition. -/
@[expose] def threeSphereOne : sphere (0 : E) 1 :=
  (threeSphereHomeomorphUnitQuaternion hE).symm 1

/-- The identity of `TauCeti.threeSphereGroup` is `TauCeti.threeSphereOne`. -/
theorem threeSphereGroup_one :
    (letI := threeSphereGroup hE; (1 : sphere (0 : E) 1)) = threeSphereOne hE :=
  rfl

/-- The homeomorphism with the unit quaternions sends `TauCeti.threeSphereOne` to `1`. -/
@[simp]
theorem threeSphereHomeomorphUnitQuaternion_threeSphereOne :
    threeSphereHomeomorphUnitQuaternion hE (threeSphereOne hE) = 1 :=
  (threeSphereHomeomorphUnitQuaternion hE).apply_symm_apply 1

/-- The homeomorphism with the unit quaternions sends products in `TauCeti.threeSphereGroup` to
products of unit quaternions. -/
@[simp]
theorem threeSphereHomeomorphUnitQuaternion_mul (x y : sphere (0 : E) 1) :
    letI := threeSphereGroup hE
    threeSphereHomeomorphUnitQuaternion hE (x * y) =
      threeSphereHomeomorphUnitQuaternion hE x * threeSphereHomeomorphUnitQuaternion hE y :=
  (threeSphereHomeomorphUnitQuaternion hE).apply_symm_apply _

/-- The homeomorphism with the unit quaternions sends inverses in `TauCeti.threeSphereGroup` to
inverses of unit quaternions. -/
@[simp]
theorem threeSphereHomeomorphUnitQuaternion_inv (x : sphere (0 : E) 1) :
    letI := threeSphereGroup hE
    threeSphereHomeomorphUnitQuaternion hE x⁻¹ = (threeSphereHomeomorphUnitQuaternion hE x)⁻¹ :=
  (threeSphereHomeomorphUnitQuaternion hE).apply_symm_apply _

end TauCeti
