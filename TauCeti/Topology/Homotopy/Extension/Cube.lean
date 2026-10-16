/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Ball
public import TauCeti.Topology.Homotopy.Cube.Basic
public import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# The boundary of a cube is a closed cofibration

For a finite index type `N`, the boundary `Cube.boundary N` of the cube `I^N` has the homotopy
extension property in the cube. The affine homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the
cube onto the closed unit ball of the sup norm on `N → ℝ` carries the boundary onto the unit sphere
(`TauCeti.norm_cubeHomeomorphClosedBall_eq_one_iff`), and the unit sphere has the homotopy
extension property in the closed unit ball
(`TauCeti.hasHomotopyExtensionProperty_sphere_closedBall`).

The same holds for the boundary `TauCeti.Cube.prodBoundary N` of the cube `I × I^N` with a
distinguished first direction, on which relative cubes are defined: it corresponds to the boundary
of `I^(Option N)` under `TauCeti.piOptionEquivProdHomeomorph`.

## Main declarations

* `TauCeti.hasHomotopyExtensionProperty_cubeBoundary`: the boundary of `I^N` has the homotopy
  extension property.
* `TauCeti.hasHomotopyExtensionProperty_prodBoundary`: the boundary of `I × I^N` has the homotopy
  extension property.
-/

public section

open Metric Set Topology unitInterval

namespace TauCeti

variable {N : Type*} [Finite N]

/-- The boundary of the cube `I^N` has the homotopy extension property in the cube. -/
theorem hasHomotopyExtensionProperty_cubeBoundary :
    HasHomotopyExtensionProperty (Cube.boundary N) := by
  have := Fintype.ofFinite N
  convert (hasHomotopyExtensionProperty_sphere_closedBall (E := N → ℝ)).image
    (cubeHomeomorphClosedBall N).symm using 1
  ext y
  simp [Homeomorph.image_symm, norm_cubeHomeomorphClosedBall_eq_one_iff]

/-- The boundary of the cube `I × I^N` has the homotopy extension property in the cube. -/
theorem hasHomotopyExtensionProperty_prodBoundary :
    HasHomotopyExtensionProperty (Cube.prodBoundary N) := by
  convert (hasHomotopyExtensionProperty_cubeBoundary (N := Option N)).image
    (piOptionEquivProdHomeomorph fun _ ↦ I) using 1
  ext y
  rw [Homeomorph.image_eq_preimage_symm, mem_preimage,
    ← piOptionEquivProdHomeomorph_mem_prodBoundary_iff, Homeomorph.apply_symm_apply]

end TauCeti
