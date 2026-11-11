/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Hom
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import Mathlib.Algebra.Lie.Quotient

/-!
# Lie gradings on homogeneous quotients

The quotient by a homogeneous Lie ideal inherits a Lie grading on the images of the
homogeneous pieces. This file equips the existing `TauCeti.InternalGrading.quotient` with
bracket compatibility, retaining its module decomposition and homogeneous projection API.
Zero pieces remain zero, so support restrictions pass to the quotient.

Use `TauCeti.InternalGrading.ofDecomposition` to start from a `GradedLieAlgebra`.
The existing `quotient_piece`, `mem_quotient_piece_iff`, and `decompose_quotient_mk`
characterize the pieces and compute their projections.

Adapted from `Mei/Algebra/Lie/Graded/Quotient.lean` in
[Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

namespace LieIdeal

variable {ι : Type} {R L : Type*} [DecidableEq ι] [AddCommMonoid ι]
  [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The quotient by a homogeneous Lie ideal inherits the Lie grading on the images of the
homogeneous pieces, using the existing homogeneous module quotient grading. -/
noncomputable instance instGradedLieAlgebraQuotient (I : LieIdeal R L)
    (G : TauCeti.InternalGrading R L ι) [SetLike.GradedBracket G.piece G.piece]
    (hI : DirectSum.SetLike.IsHomogeneous G.piece I.toSubmodule) :
    GradedLieAlgebra (L := L ⧸ I) (G.quotient I.toSubmodule hI).piece where
  toDecomposition := inferInstance
  toGradedBracket := by
    -- The Lie quotient map has the same underlying linear map as the module quotient map.
    have hpieces : (G.quotient I.toSubmodule hI).piece =
        fun i ↦ (G.piece i).map I.mkQ.toLinearMap :=
      funext (G.quotient_piece I.toSubmodule hI)
    rw [hpieces]
    exact I.mkQ.gradedBracket_map G.piece

end LieIdeal
