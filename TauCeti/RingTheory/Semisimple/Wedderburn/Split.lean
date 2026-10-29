/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.Wedderburn.Presentation
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Split Wedderburn presentations from scalar endomorphisms

A semisimple algebra is a product of matrix algebras over the opposites of the
endomorphism algebras of its simple left ideals. If each such endomorphism algebra
is one-dimensional over the base field, each coefficient algebra is the base field.
This gives a split presentation without assuming that the base is algebraically closed.

Only simple left ideals need to be tested: over a semisimple ring every simple
module is isomorphic to a simple left ideal. No separate finite-dimensionality
assumption is needed for this criterion.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, §3.
* Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite` supplies
  the endomorphism-algebra presentation used here.
-/

public section

namespace TauCeti.IsSemisimpleRing

variable (k A : Type*) [Field k] [Ring A] [Algebra k A] [IsSemisimpleRing A]

/-- A semisimple algebra admits a split Wedderburn presentation if the endomorphism
algebra of each simple left ideal has dimension one over the base field. -/
theorem nonempty_splitWedderburnAlgebraPresentation_of_finrank_end_eq_one
    (h : ∀ S : Ideal A, IsSimpleModule A S → Module.finrank k (Module.End A S) = 1) :
    Nonempty (SplitWedderburnAlgebraPresentation k A) := by
  classical
  obtain ⟨n, S, d, hS, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite k A
  let (i : Fin n) : IsSimpleModule A (S i) := hS i
  let (i : Fin n) : NeZero (d i) := hd i
  have hcoeff (i : Fin n) : Nonempty (k ≃ₐ[k] Module.End A (S i)) :=
    Module.nonempty_algEquiv_iff_finrank_eq_one.mpr (h (S i) (hS i))
  let f (i : Fin n) : (Module.End A (S i))ᵐᵒᵖ ≃ₐ[k] k :=
    (AlgEquiv.op (hcoeff i).some.symm).trans (AlgEquiv.toOpposite k k).symm
  exact ⟨{
    blockCount := n
    degree := d
    equiv := e.trans (AlgEquiv.piCongrRight fun i ↦ AlgEquiv.mapMatrix (f i)) }⟩

end TauCeti.IsSemisimpleRing
