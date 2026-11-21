/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Basic

/-!
# Images of directed wall spaces

A Lie homomorphism carrying each homogeneous piece into a specified target piece
pushes directed wall spaces forward by submodule image. In particular this
constructs the wall spaces on a degree truncation. No injectivity, surjectivity or
homogeneous decomposition is required. Images respect identity and composition.

The construction uses Mathlib's `Submodule.map` and `LieHom.map_lie`.

## Attribution

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/Map.lean`
in Mei at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Geometry/ScatteringDiagram/WallSpace/Map.lean
-/

public section

namespace TauCeti.DirectedWallSpaces

variable {Γ Λ R L L' L'' : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}
  (H : DirectedWallSpaces ρ ℒ)

/-- Push wall spaces forward along a Lie homomorphism preserving the indexed pieces. -/
def map (f : L →ₗ⁅R⁆ L') (ℒ' : Γ → Submodule R L')
    (hf : ∀ n, (ℒ n).map f.toLinearMap ≤ ℒ' n) : DirectedWallSpaces ρ ℒ' where
  wall n m := (H.wall n m).map f.toLinearMap
  wall_le_piece n m := (Submodule.map_mono (H.wall_le_piece n m)).trans (hf n)
  zero_normal n := by rw [H.zero_normal, Submodule.map_bot]
  nontangent n m hm := by rw [H.nontangent n m hm, Submodule.map_bot]
  rescale n m c hc := by rw [H.rescale n m c hc]
  bracket_mem := by
    rintro n n' m m' _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨⁅x, y⁆, H.bracket_mem hx hy, f.map_lie x y⟩

/-- Each pushed-forward wall space is the image of the original wall space. -/
@[simp]
theorem map_wall (f : L →ₗ⁅R⁆ L') (ℒ' : Γ → Submodule R L')
    (hf : ∀ n, (ℒ n).map f.toLinearMap ≤ ℒ' n) (n : Γ) (m : Λ →+ ℤ) :
    (H.map f ℒ' hf).wall n m = (H.wall n m).map f.toLinearMap := (rfl)

/-- A wall-space image under the identity is the original wall-space datum. -/
@[simp]
theorem map_id : H.map LieHom.id ℒ (by intro n; exact (Submodule.map_id _).le) = H := by
  apply DirectedWallSpaces.ext
  intro n m
  exact Submodule.map_id _

/-- Successive wall-space images agree with the image under the composite. -/
@[simp]
theorem map_map (f : L →ₗ⁅R⁆ L') (ℒ' : Γ → Submodule R L')
    (hf : ∀ n, (ℒ n).map f.toLinearMap ≤ ℒ' n)
    (g : L' →ₗ⁅R⁆ L'') (ℒ'' : Γ → Submodule R L'')
    (hg : ∀ n, (ℒ' n).map g.toLinearMap ≤ ℒ'' n) :
    (H.map f ℒ' hf).map g ℒ'' hg =
      H.map (g.comp f) ℒ'' (fun n => by
        rw [LieHom.toLinearMap_comp, Submodule.map_comp]
        exact (Submodule.map_mono (hf n)).trans (hg n)) := by
  ext n m
  simp only [map_wall, LieHom.toLinearMap_comp, Submodule.map_comp]

end TauCeti.DirectedWallSpaces
