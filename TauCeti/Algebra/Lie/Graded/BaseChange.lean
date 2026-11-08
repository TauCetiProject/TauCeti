/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.BaseChange
public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Algebra.Lie.BaseChange

/-!
# Extension of scalars for graded Lie algebras

Extending each homogeneous piece gives a Lie grading on the scalar extension,
and extending the pieces of a graded representation preserves its graded action.
The decomposition is Mathlib's `DirectSum.Decomposition.baseChange`; homogeneous
projections commute with pure tensors by
`DirectSum.coe_decompose_baseChange_tmul`. No flatness, freeness, or dimension
hypothesis is imposed on the pieces or the coefficient algebra.

Adapted from `Mei/Algebra/Lie/Graded/BaseChange.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

open TensorProduct

variable {N R S L M ι κ : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [LieRing L] [LieAlgebra R L]

/-- Scalar extension preserves a graded bracket action, independently of any decomposition. -/
instance SetLike.GradedBracket.baseChange [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] [VAdd ι κ]
    (ℒ : ι → Submodule R L) (ℳ : κ → Submodule R M)
    [SetLike.GradedBracket ℒ ℳ] :
    SetLike.GradedBracket (fun i => (ℒ i).baseChange S)
      (fun j => (ℳ j).baseChange S) where
  bracket_mem := by
    intro i j x y hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      induction y using TensorProduct.inductionOn with
      | tmul t y =>
        simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
          LieAlgebra.ExtendScalars.bracket_tmul] using
          Submodule.tmul_mem_baseChange_of_mem (s * t)
            (SetLike.GradedBracket.bracket_mem x.property y.property)
      | add y z hy hz =>
        rw [map_add, lie_add]
        exact Submodule.add_mem _ hy hz
    | add x z hx hz =>
      rw [map_add, add_lie ((ℒ i).subtype.baseChange S x)
        ((ℒ i).subtype.baseChange S z) ((ℳ j).subtype.baseChange S y)]
      exact Submodule.add_mem _ hx hz

variable [AddCommMonoid N] [DecidableEq N] (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]

/-- The extended homogeneous pieces form a Lie grading on the scalar extension. -/
instance GradedLieAlgebra.baseChange :
    GradedLieAlgebra (fun n => (ℒ n).baseChange S) where
  toDecomposition := inferInstance
  toGradedBracket := inferInstance

/-- Scalar extension preserves the grading of a representation of a graded Lie algebra. -/
instance GradedLieModule.baseChange [DecidableEq ι] [AddCommMonoid ι]
    [DecidableEq κ] [VAdd ι κ] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M]
    (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]
    (ℳ : κ → Submodule R M) [DirectSum.Decomposition ℳ] [GradedLieModule ℒ ℳ] :
    GradedLieModule (fun i => (ℒ i).baseChange S) (fun j => (ℳ j).baseChange S) where
  toGradedBracket := inferInstance
