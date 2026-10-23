/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Center
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Adjoint.Basic

/-!
# The projective general linear group is adjoint

The projective general linear group is semisimple with trivial scheme-theoretic center.
Thus it is the adjoint semisimple group in the standard central isogeny `SLₙ → PGLₙ`,
including when the characteristic divides `n` and the kernel is not reduced.
-/

public section

namespace TauCeti.ProjectiveGeneralLinear

universe u

/-- `PGLₙ` is adjoint semisimple over every field, in every rank and characteristic. -/
theorem adjointSemisimpleCommHopfAlgProperty_coordinateHopfAlgebra
    (n : ℕ) (k : Type u) [Field k] :
    adjointSemisimpleCommHopfAlgProperty k
      ⟨FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra n k),
        semisimpleCommHopfAlgProperty_coordinateHopfAlgebra n k⟩ :=
  (adjointSemisimpleCommHopfAlgProperty_iff _).mpr (centerDefiningIdeal_eq_augmentation n k)

end TauCeti.ProjectiveGeneralLinear
