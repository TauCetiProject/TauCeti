/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.Wedderburn.Presentation
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.RingTheory.SimpleRing.Pi
import TauCeti.RingTheory.Semisimple.IsotypicEnd
import TauCeti.RingTheory.Semisimple.MatrixDivisionRing

/-!
# Split Wedderburn presentations and scalar endomorphisms

A semisimple algebra is a product of matrix algebras over the opposites of the
endomorphism algebras of its simple left ideals. If each such endomorphism algebra
is one-dimensional over the base field, each coefficient algebra is the base field.
This gives a split presentation without assuming that the base is algebraically closed.

Only simple left ideals need to be tested: over a semisimple ring every simple
module is isomorphic to a simple left ideal. No separate finite-dimensionality
assumption is needed for this criterion.

Conversely, a split presentation makes the endomorphism algebra of every simple
left ideal isomorphic to the base field. Thus scalar endomorphisms characterize
split semisimple algebras over arbitrary fields, including nonclosed fields and
positive characteristic.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, §3.
* Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite` supplies
  the endomorphism-algebra presentation used here.
-/

public section

namespace IsSemisimpleRing

variable (k A : Type*) [Field k] [Ring A] [Algebra k A] [IsSemisimpleRing A]

/-- A semisimple algebra admits a split Wedderburn presentation if the endomorphism
algebra of each simple left ideal has dimension one over the base field. -/
theorem nonempty_splitWedderburnAlgebraPresentation_of_finrank_end_eq_one
    (h : ∀ S : Ideal A, IsSimpleModule A S → Module.finrank k (Module.End A S) = 1) :
    Nonempty (TauCeti.SplitWedderburnAlgebraPresentation k A) := by
  classical
  obtain ⟨n, S, d, hS, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite k A
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

end IsSemisimpleRing

namespace TauCeti.SplitWedderburnAlgebraPresentation

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- In a split semisimple algebra, every simple left ideal has endomorphism algebra
isomorphic to the base field. -/
theorem nonempty_end_algEquiv_self (P : SplitWedderburnAlgebraPresentation k A)
    (S : Ideal A) [IsSimpleModule A S] : Nonempty (Module.End A S ≃ₐ[k] k) := by
  classical
  have : IsSemisimpleRing A := P.equiv.symm.toRingEquiv.isSemisimpleRing
  have hm : ∀ i, IsSimpleRing (Matrix (Fin (P.degree i)) (Fin (P.degree i)) k) :=
    fun i ↦ inferInstance
  have hs : ∀ c : isotypicComponents A A, IsSimpleRing (Module.End A c.1) :=
    fun c ↦ (IsIsotypic.isotypicComponents c.2).isSimpleRing_moduleEnd
  -- Compare the factors of End_A(A), retaining the base field through the opposite algebra.
  let E : (∀ c : isotypicComponents A A, Module.End A c.1) ≃ₐ[k]
      ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) k :=
    (IsSemisimpleModule.endAlgEquiv k A A).symm.trans <|
      (AlgEquiv.moduleEndSelf k).symm.trans <|
        (AlgEquiv.op P.equiv).trans <|
          (AlgEquiv.piMulOpposite _ _).trans <|
            AlgEquiv.piCongrRight fun _ ↦ AlgEquiv.mopMatrix.symm.trans <|
              AlgEquiv.mapMatrix (AlgEquiv.toOpposite k k).symm
  obtain ⟨σ, hσ⟩ := E.exists_equiv_factors
  -- The S-isotypic component is a nonzero finite power of S. Matrix-algebra uniqueness
  -- therefore recovers End_A(S) from its matched split block.
  let c : isotypicComponents A A := ⟨isotypicComponent A A S, S, inferInstance, rfl⟩
  have : Nontrivial (isotypicComponent A A S) :=
    Submodule.nontrivial_iff_ne_bot.mpr (bot_lt_isotypicComponent S).ne'
  obtain ⟨n, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent A A S).linearEquiv_fun
  have : NeZero n := ⟨fun hn ↦ by
    subst n
    exact not_subsingleton (isotypicComponent A A S) e.subsingleton⟩
  obtain ⟨f, -⟩ := hσ c
  exact nonempty_algEquiv_of_algEquiv_matrix
    ((e.conjAlgEquiv k).trans (endVecAlgEquivMatrixEnd (Fin n) k A S)) f

end TauCeti.SplitWedderburnAlgebraPresentation

namespace IsSemisimpleRing

variable (k A : Type*) [Field k] [Ring A] [Algebra k A] [IsSemisimpleRing A]

/-- A semisimple algebra is split exactly when every simple left ideal has a
one-dimensional endomorphism algebra over the base field. -/
theorem nonempty_splitWedderburnAlgebraPresentation_iff_finrank_end_eq_one :
    Nonempty (TauCeti.SplitWedderburnAlgebraPresentation k A) ↔
      ∀ S : Ideal A, IsSimpleModule A S → Module.finrank k (Module.End A S) = 1 := by
  refine ⟨?_, nonempty_splitWedderburnAlgebraPresentation_of_finrank_end_eq_one k A⟩
  rintro ⟨P⟩ S hS
  have : IsSimpleModule A S := hS
  obtain ⟨e⟩ := P.nonempty_end_algEquiv_self S
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]

end IsSemisimpleRing
