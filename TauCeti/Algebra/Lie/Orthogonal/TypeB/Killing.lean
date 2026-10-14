/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Center
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Standard
import Mathlib.Algebra.Lie.Semisimple.Lemmas

/-!
# The Killing form of the split odd orthogonal Lie algebra

The split odd orthogonal Lie algebra has nondegenerate Killing form in characteristic zero
when each endomorphism in its standard action is triangularizable. In particular this applies
over every algebraically closed field of characteristic zero. The Killing certificate makes
Mathlib's abstract root system available for the concrete diagonal Cartan.

Triangularizability here concerns every element of the full Lie algebra in its standard action.
Splitness of the diagonal Cartan alone does not supply this hypothesis.

## References

* Mathlib's `LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`
  (faithful irreducible modules and reductivity).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§5, 6, 19.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate II.
-/

public section

namespace TauCeti

open LieAlgebra

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The Killing form of the split odd orthogonal Lie algebra is nondegenerate in
characteristic zero if each endomorphism in the standard action is triangularizable. Algebraic
closedness of the field supplies this hypothesis automatically. -/
instance isKilling_typeB [CharZero K]
    [LieModule.IsTriangularizable K (Orthogonal.typeB ι K) (Unit ⊕ ι ⊕ ι → K)] :
    LieAlgebra.IsKilling K (Orthogonal.typeB ι K) := by
  obtain ⟨h, _⟩ := hasCentralRadical_and_of_isIrreducible_of_isFaithful
    K (Orthogonal.typeB ι K) (Unit ⊕ ι ⊕ ι → K)
  let _ : HasTrivialRadical K (Orthogonal.typeB ι K) :=
    (hasTrivialRadical_iff K (Orthogonal.typeB ι K)).mpr (by
      rw [(hasCentralRadical_iff K (Orthogonal.typeB ι K)).mp h,
        center_typeB_eq_bot (IsRegular.of_ne_zero (NeZero.ne (2 : K)))])
  infer_instance

end TauCeti
