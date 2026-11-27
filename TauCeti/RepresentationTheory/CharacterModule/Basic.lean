/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Additive character duals of representations

The additive character dual of an `R`-linear representation on `M` is the representation on
`CharacterModule M = Hom(M, ℚ/ℤ)` given by precomposition with the inverse action. Its scalar
action also comes from precomposition on `M`; no `R`-module structure on `ℚ/ℤ` is required.

Equivariant coefficient maps induce maps in the opposite direction on character duals.
Restriction along a group homomorphism commutes with this construction. These are the
untwisted additive duals used in comparing finite linear duality with Cartier duality;
the cyclotomic character must additionally twist the contragredient action for the latter.
-/

public section

namespace Representation

variable {R G M N P : Type*} [CommRing R] [Group G]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The contragredient representation on additive characters, with action
`(g • η)(m) = η(g⁻¹ • m)`. -/
def characterDual (ρ : Representation R G M) : Representation R G (CharacterModule M) where
  toFun g := CharacterModule.dual (ρ g⁻¹)
  map_one' := by ext η m; simp only [inv_one, map_one]; rfl
  map_mul' g h := by
    rw [mul_inv_rev, map_mul, Module.End.mul_eq_comp, CharacterModule.dual_comp]
    rfl

/-- Each operator on the character dual is precomposition with the inverse operator. -/
theorem characterDual_apply (ρ : Representation R G M) (g : G) :
    ρ.characterDual g = CharacterModule.dual (ρ g⁻¹) :=
  (rfl)

/-- Evaluation of the contragredient action on an additive character. -/
@[simp]
theorem characterDual_apply_apply (ρ : Representation R G M) (g : G)
    (η : CharacterModule M) (m : M) :
    ρ.characterDual g η m = η (ρ g⁻¹ m) :=
  (rfl)

/-- Restriction of a character dual is the character dual of the restriction. -/
@[simp]
theorem characterDual_comp (ρ : Representation R G M) {H : Type*} [Group H] (f : H →* G) :
    characterDual (ρ.comp f) = ρ.characterDual.comp f := by
  ext h η m
  simp

namespace IntertwiningMap

variable {ρ : Representation R G M} {σ : Representation R G N}
  {τ : Representation R G P}

/-- Precomposition with an equivariant coefficient map, on additive character duals. -/
def characterDual (f : IntertwiningMap ρ σ) : IntertwiningMap σ.characterDual ρ.characterDual where
  toLinearMap := CharacterModule.dual f.toLinearMap
  isIntertwining' g := by
    ext η m
    exact congrArg η (DFunLike.congr_fun (f.isIntertwining' g⁻¹) m).symm

/-- The character-dual coefficient map is precomposition. -/
@[simp]
theorem characterDual_apply (f : IntertwiningMap ρ σ) (η : CharacterModule N) (m : M) :
    f.characterDual η m = η (f m) :=
  (rfl)

/-- Character duality preserves identity maps. -/
@[simp]
theorem characterDual_id :
    (IntertwiningMap.id ρ).characterDual = IntertwiningMap.id ρ.characterDual := by
  ext η m
  rfl

/-- Character duality reverses composition of coefficient maps. -/
@[simp]
theorem characterDual_comp (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ) :
    (g.comp f).characterDual = f.characterDual.comp g.characterDual := by
  ext η m
  rfl

end IntertwiningMap

end Representation
