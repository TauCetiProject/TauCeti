/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import TauCeti.Algebra.Category.LieModuleCat.EssentiallySmall
public import TauCeti.CategoryTheory.GrothendieckGroup.Split

/-!
# The dimension of virtual finite Lie modules

Let `L` be a Lie algebra over a commutative ring `R` satisfying the rank-nullity theorem (for
instance, a field). Lie modules finite over `R` form the essentially small category
`TauCeti.FGLieModuleCat R L` with binary biproducts, so they have a split Grothendieck group
`TauCeti.SplitK0 (FGLieModuleCat R L)`: the group of virtual finite modules `[M] - [N]`, with
`[M ⊕ N] = [M] + [N]`. Dimension is an isomorphism invariant, additive on direct sums, so it
descends to a homomorphism

`TauCeti.FGLieModuleCat.finrankK0 R : SplitK0 (FGLieModuleCat R L) →+ ℤ`

sending `[M] - [N]` to `dim M - dim N`.

## Main definitions

* `TauCeti.FGLieModuleCat.finrankK0`: the dimension of a virtual module.

## Main results

* `TauCeti.FGLieModuleCat.finrankK0_splitK0_of`: the value on the class of a module.
-/

public section

open CategoryTheory CategoryTheory.Limits Module

universe w u v

namespace TauCeti.FGLieModuleCat

variable (R : Type u) {L : Type v} [CommRing R] [HasRankNullity.{w} R] [LieRing L]
  [LieAlgebra R L]

/-- Dimension as an invariant of finite Lie modules, additive on biproducts. -/
private noncomputable def finrankInvariant :
    SplitK0.AdditiveInvariant (FGLieModuleCat.{w} R L) ℤ where
  obj M := Module.finrank R M.obj
  map_iso _ _ e := congrArg Nat.cast e.fgLieModuleCatIsoToLieModuleEquiv.toLinearEquiv.finrank_eq
  map_biprod M N := by
    -- Rank-nullity for the first projection, whose kernel is the image of the second inclusion.
    have h := (LinearMap.ker (LinearMap.fst R M.obj N.obj)).finrank_quotient_add_finrank
    rw [((LinearMap.fst R M.obj N.obj).quotKerEquivOfSurjective
        LinearMap.fst_surjective).finrank_eq, LinearMap.ker_fst,
      (LinearEquiv.ofInjective _ (LinearMap.inr_injective (R := R))).finrank_eq.symm] at h
    rw [(biprodLieModuleEquiv M N).toLinearEquiv.finrank_eq, ← h, Nat.cast_add]

/-- **The dimension of a virtual finite Lie module**: the homomorphism on the split Grothendieck
group sending `[M] - [N]` to `dim M - dim N`. -/
noncomputable def finrankK0 : SplitK0 (FGLieModuleCat.{w} R L) →+ ℤ :=
  SplitK0.lift (finrankInvariant R)

/-- The dimension of the class of a module is its dimension. -/
@[simp]
theorem finrankK0_splitK0_of (M : FGLieModuleCat.{w} R L) :
    finrankK0 R (SplitK0.of M) = Module.finrank R M.obj :=
  SplitK0.lift_of _ M

end TauCeti.FGLieModuleCat
