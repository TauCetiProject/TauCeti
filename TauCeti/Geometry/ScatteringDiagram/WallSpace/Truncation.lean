/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Ray

/-!
# Finite-order directed wall spaces

The images of directed wall spaces in a degree quotient satisfy the same normal
and bracket laws. Lowering the cutoff sends each wall space onto its lower-order
image. Thus the finite-order spaces are compatible with the Lie truncation tower,
without a freeness or flatness assumption. The quotient maps preserve the original wall spaces.

The construction uses `DirectedWallSpaces.map` on the canonical quotient maps.

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/Truncation.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original notice: Copyright (c) 2026 Mei contributors. All rights reserved.
Authors: Codex.
-/

public section

namespace TauCeti.DirectedWallSpaces

variable {Γ : Type} {Λ R L : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ]

/-- Wall spaces at order `k` are the actual quotient images of the original spaces. -/
def truncated (k : ℕ) : DirectedWallSpaces ρ (d.truncatedGrading ℒ k) :=
  H.map (d.degreeIdeal ℒ k).mkQ (d.truncatedGrading ℒ k)
    (by intro n; rw [PositiveDegrees.truncatedGrading_eq]; exact le_rfl)

/-- Truncation takes each wall space to its image in the Lie quotient. -/
@[simp]
theorem truncated_wall (k : ℕ) (n : Γ) (m : Λ →+ ℤ) :
    (H.truncated d k).wall n m =
      (H.wall n m).map (d.degreeIdeal ℒ k).mkQ.toLinearMap := by
  rw [truncated, map_wall]

/-- The canonical graded quotient homomorphism preserves directed wall spaces. -/
theorem mkQ_mem_truncated_wall (k : ℕ) (n : Γ) (m : Λ →+ ℤ) (x : L)
    (hx : x ∈ H.wall n m) :
    (d.degreeIdeal ℒ k).mkQ x ∈ (H.truncated d k).wall n m := by
  rw [truncated_wall]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/-- Every finite-order wall space maps onto its image at a lower cutoff. -/
theorem map_truncationMap_wall {k l : ℕ} (h : k ≤ l) (n : Γ) (m : Λ →+ ℤ) :
    ((H.truncated d l).wall n m).map (d.truncationMap ℒ h).toLinearMap =
      (H.truncated d k).wall n m := by
  have square : (d.truncationMap ℒ h).toLinearMap.comp
      (d.degreeIdeal ℒ l).mkQ.toLinearMap = (d.degreeIdeal ℒ k).mkQ.toLinearMap := by
    ext x
    simp
  rw [truncated_wall, ← Submodule.map_comp, square, truncated_wall]

end TauCeti.DirectedWallSpaces

namespace TauCeti.DirectedWallSpaces

variable {Γ : Type} {Λ R L : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ]

/-- A finite-order supported-ray wall sum is the quotient image of the original sum. -/
@[simp]
theorem truncated_raySubmodule (k : ℕ) (w : SupportedRay d) (m : Λ →+ ℤ) :
    (H.truncated d k).raySubmodule w m =
      (H.raySubmodule w m).map (d.degreeIdeal ℒ k).mkQ.toLinearMap := by
  simp only [truncated, map_raySubmodule]

/-- Lowering the cutoff maps a supported-ray wall sum onto its lower-order counterpart. -/
theorem map_truncationMap_raySubmodule {k l : ℕ} (h : k ≤ l)
    (w : SupportedRay d) (m : Λ →+ ℤ) :
    ((H.truncated d l).raySubmodule w m).map (d.truncationMap ℒ h).toLinearMap =
      (H.truncated d k).raySubmodule w m := by
  simp only [raySubmodule_def, Submodule.map_iSup, map_truncationMap_wall]

end TauCeti.DirectedWallSpaces
