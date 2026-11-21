/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Graded

/-!
# Transporting graded Lie brackets

Images and inverse images of homogeneous pieces under a Lie homomorphism retain bracket
compatibility. These constructions do not assert a direct-sum decomposition: that requires
additional hypotheses, such as homogeneity of the subalgebra or ideal being used.

Adapted from `Mei/Algebra/Lie/Graded/{Hom,Map}.lean` in
[Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

namespace LieHom

variable {ι R L L' : Type*} [VAdd ι ι] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- The inverse images of pieces with a graded bracket have a graded bracket. -/
instance instGradedBracketComap (f : L →ₗ⁅R⁆ L') (ℒ : ι → Submodule R L')
    [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (fun i ↦ (ℒ i).comap f.toLinearMap)
      (fun i ↦ (ℒ i).comap f.toLinearMap) where
  bracket_mem := by
    intro i j x y hx hy
    rw [Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie]
    exact SetLike.GradedBracket.bracket_mem hx hy

/-- The images of pieces with a graded bracket have a graded bracket. Neither injectivity
nor surjectivity of the homomorphism is needed. -/
theorem gradedBracket_map (f : L →ₗ⁅R⁆ L') (ℒ : ι → Submodule R L)
    [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (fun i ↦ (ℒ i).map f.toLinearMap)
      (fun i ↦ (ℒ i).map f.toLinearMap) := by
  constructor
  intro i j x y hx hy
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hy
  exact Submodule.mem_map.2
    ⟨⁅a, b⁆, SetLike.GradedBracket.bracket_mem ha hb, f.map_lie a b⟩

end LieHom
