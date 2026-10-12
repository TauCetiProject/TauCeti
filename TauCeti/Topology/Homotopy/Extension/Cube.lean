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
of `I^(Option N)` under `TauCeti.piOptionEquivProdHomeomorph`. For `N = Fin n`, the closed unit
ball of the sup norm on `Fin (n + 1) → ℝ` is the cube `I × I^(Fin n)`
(`TauCeti.closedBallHomeomorphProd`), and its unit sphere corresponds to `Cube.prodBoundary`.

## Main declarations

* `TauCeti.hasHomotopyExtensionProperty_cubeBoundary`: the boundary of `I^N` has the homotopy
  extension property.
* `TauCeti.hasHomotopyExtensionProperty_prodBoundary`: the boundary of `I × I^N` has the homotopy
  extension property.
* `TauCeti.closedBallHomeomorphProd`: the closed unit ball of the sup norm on `Fin (n + 1) → ℝ` is
  homeomorphic to `I × I^(Fin n)`, carrying the unit sphere onto `Cube.prodBoundary (Fin n)`.
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

/-- The closed unit ball of the sup norm on `Fin (n + 1) → ℝ` is the cube `I × I^(Fin n)`, through
the affine homeomorphism `TauCeti.cubeHomeomorphClosedBall` followed by splitting off the first
coordinate. -/
@[expose] noncomputable def closedBallHomeomorphProd (n : ℕ) :
    closedBall (0 : Fin (n + 1) → ℝ) 1 ≃ₜ I × I^(Fin n) :=
  (cubeHomeomorphClosedBall (Fin (n + 1))).symm.trans
    { toFun z := (z 0, Fin.tail z)
      invFun q := Fin.cons q.1 q.2
      left_inv := Fin.cons_self_tail
      right_inv _ := by simp
      continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun _ ↦ continuous_apply _)
      continuous_invFun := Continuous.finCons (A := fun _ ↦ I) continuous_fst continuous_snd }

@[simp]
theorem closedBallHomeomorphProd_apply {n : ℕ} (x : closedBall (0 : Fin (n + 1) → ℝ) 1) :
    closedBallHomeomorphProd n x = ((cubeHomeomorphClosedBall (Fin (n + 1))).symm x 0,
      Fin.tail ((cubeHomeomorphClosedBall (Fin (n + 1))).symm x)) :=
  rfl

@[simp]
theorem closedBallHomeomorphProd_symm_apply {n : ℕ} (q : I × I^(Fin n)) :
    (closedBallHomeomorphProd n).symm q =
      cubeHomeomorphClosedBall (Fin (n + 1)) (Fin.cons q.1 q.2) :=
  rfl

/-- `TauCeti.closedBallHomeomorphProd` carries the unit sphere onto the boundary of
`I × I^(Fin n)`. -/
theorem closedBallHomeomorphProd_mem_prodBoundary_iff {n : ℕ}
    (x : closedBall (0 : Fin (n + 1) → ℝ) 1) :
    closedBallHomeomorphProd n x ∈ Cube.prodBoundary (Fin n) ↔
      (x : Fin (n + 1) → ℝ) ∈ sphere 0 1 := by
  have hx : ‖(x : Fin (n + 1) → ℝ)‖ = 1 ↔
      (cubeHomeomorphClosedBall (Fin (n + 1))).symm x ∈ Cube.boundary (Fin (n + 1)) := by
    rw [← norm_cubeHomeomorphClosedBall_eq_one_iff, Homeomorph.apply_symm_apply]
  rw [mem_sphere_zero_iff_norm, hx, Cube.boundary_fin_succ_iff, closedBallHomeomorphProd_apply,
    Cube.mem_prodBoundary_iff]

end TauCeti
