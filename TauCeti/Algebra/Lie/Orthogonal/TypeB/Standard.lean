/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.RingTheory.SimpleModule.Rank
import TauCeti.Algebra.Lie.Orthogonal.Basic
import TauCeti.Algebra.Lie.Orthogonal.Killing

/-!
# The standard module of the split odd orthogonal Lie algebra

The standard module of `LieAlgebra.Orthogonal.typeB ι K` is irreducible over a field of
characteristic different from two, including when `ι` is empty. This supplies a faithful
irreducible module for the reductivity criterion.

For nonempty `ι`, the Gram matrix `LieAlgebra.Orthogonal.JB ι K` is nondegenerate and
the standard module is covered by
`TauCeti.isIrreducible_skewAdjointMatricesLieSubalgebra_standard`. For empty `ι`, the
standard module is one-dimensional.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lecture 20 (the standard orthogonal module).
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate II.
-/

public section

namespace TauCeti

open LieAlgebra

variable {K ι : Type*} [Fintype ι] [DecidableEq ι] [Field K] [NeZero (2 : K)]

/-- The standard module of the split odd orthogonal Lie algebra is irreducible over any field
in which two is nonzero, including the one-dimensional module when `ι` is empty. -/
instance isIrreducible_typeB_standard :
    LieModule.IsIrreducible K (Orthogonal.typeB ι K) (Unit ⊕ ι ⊕ ι → K) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have : IsSimpleModule K (Unit ⊕ ι ⊕ ι → K) :=
      isSimpleModule_iff_finrank_eq_one.mpr (by simp)
    apply LieModule.IsIrreducible.mk
    intro N hN
    exact (LieSubmodule.toSubmodule_eq_top N).mp
      ((IsSimpleOrder.eq_bot_or_eq_top N.toSubmodule).resolve_left
        ((LieSubmodule.toSubmodule_eq_bot N).not.mpr hN))
  | inr h =>
    apply isIrreducible_skewAdjointMatricesLieSubalgebra_standard
    · exact Orthogonal.isSymm_JB
    · exact Orthogonal.isUnit_JB (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K)))
    · simp only [Fintype.card_sum, Fintype.card_unit]
      have := Fintype.card_pos_iff.mpr h
      omega

end TauCeti
