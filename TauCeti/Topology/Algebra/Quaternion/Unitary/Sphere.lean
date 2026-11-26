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
corresponding to the unit quaternion `1`.

## Main declarations

* `TauCeti.threeSphereHomeomorphUnitQuaternion`: `S³` is homeomorphic to the unit quaternions.
* `TauCeti.threeSphereGroup`, `TauCeti.isTopologicalGroup_threeSphere`: the topological group
  structure on `S³` transported from the unit quaternions, with identity `TauCeti.threeSphereOne`.
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
`TauCeti.threeSphereGroup`. -/
@[expose] def threeSphereOne : sphere (0 : E) 1 :=
  (threeSphereHomeomorphUnitQuaternion hE).symm 1

end TauCeti
