/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.RestrictScalars
public import Mathlib.Algebra.Lie.Graded

/-!
# Restriction of scalars for graded Lie algebras

A grading of a Lie algebra remains a grading after restricting scalars in its
homogeneous pieces. Its homogeneous components have the same underlying values
by `DirectSum.coe_decompose_restrictScalars`, without freeness or flatness
assumptions. The bracket compatibility is unchanged.

Adapted from `Mei/Algebra/Lie/Graded/RestrictScalars.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

variable {R S L ι : Type*} [CommRing R] [CommRing S] [LieRing L]
  [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]
  [DecidableEq ι] [AddCommMonoid ι] (ℒ : ι → Submodule S L)

/-- Restricting scalars preserves a bracket-compatible internal grading. -/
instance GradedLieAlgebra.restrictScalars [GradedLieAlgebra ℒ] :
    GradedLieAlgebra (fun i => (ℒ i).restrictScalars R) where
  toDecomposition := inferInstance
  bracket_mem := SetLike.GradedBracket.bracket_mem (ℒ := ℒ) (ℳ := ℒ)
