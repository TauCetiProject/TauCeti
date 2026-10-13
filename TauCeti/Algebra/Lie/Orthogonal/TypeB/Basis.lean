/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Cartan
public import TauCeti.Algebra.Lie.Basis.Root
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.CartanBasis
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Generation
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SerreRelations
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

/-!
# A Lie algebra basis for the split odd orthogonal Lie algebra

The diagonal Cartan and the Bourbaki-numbered simple-root matrices of the split odd orthogonal Lie
algebra `LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K` form a `LieAlgebra.Basis`. Its Cartan matrix
is the type-`B` Cartan matrix `CartanMatrix.B (n + 1)`, the terminal node `Fin.last n` being the
short simple root `εₙ`; its Cartan generators are the simple coroots, and its raising and lowering
generators are the positive and negative simple-root matrices.

This package makes the concrete matrix realization available to the generic Lie-basis API. The
numbered generators lie in the simple-root spaces (`TauCeti.lieBasis_e_mem_rootSpace` and
`TauCeti.lieBasis_f_mem_rootSpace`), in characteristic zero the Cartan action is triangularizable
(`LieAlgebra.Basis.isTriangularizable`), and the basis dual to the simple coroots
`LieAlgebra.Basis.cartanBasis` is the basis of fundamental weights. Over a field of characteristic
zero, once the Killing form is known to be nondegenerate, the generic results also describe the
compatible Borel subalgebra
(`LieAlgebra.Basis.borelSubalgebra_eq_sup_lieSpan_e`) and reduce highest-weight vectors to
annihilation by the raising generators (`LieAlgebra.Basis.isHighestWeightVector_iff_forall_e`).

## Main declarations

* `TauCeti.typeBLieBasis`: the standard type-`Bₙ₊₁` Lie algebra basis.
* `TauCeti.typeBLieBasis_A`: its Cartan matrix is `CartanMatrix.B (n + 1)`.
* `TauCeti.typeBLieBasis_h`, `TauCeti.typeBLieBasis_e` and `TauCeti.typeBLieBasis_f`: its
  generators are the numbered simple coroots and simple-root matrices.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§12--14.
* The construction follows the split type-`D` Lie algebra basis `TauCeti.TypeDStd.lieBasis` in
  `TauCeti/Algebra/Lie/Orthogonal/TypeD/Basis.lean`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The standard Chevalley-style basis of the split odd orthogonal Lie algebra of type `Bₙ₊₁`,
on the diagonal Cartan.

The Cartan matrix and the generators use Bourbaki's numbering, the terminal node `Fin.last n`
being the short simple root. -/
noncomputable def typeBLieBasis (n : ℕ) :
    LieAlgebra.Basis (Fin (n + 1)) (typeBDiagonalCartan K (Fin (n + 1))) where
  A := CartanMatrix.B (n + 1)
  h := typeBSimpleCorootGenerator
  e := typeBSimpleRootGenerator
  f := typeBSimpleNegativeRootGenerator
  cartan_eq_lieSpan :=
    letI := invertibleOfNonzero (NeZero.ne (2 : K))
    typeBDiagonalCartan_eq_lieSpan_typeBSimpleCorootGenerator
  span_ef :=
    lieSpan_range_typeBSimpleRootGenerator_union_range_typeBSimpleNegativeRootGenerator_eq_top n
  linInd :=
    letI := invertibleOfNonzero (NeZero.ne (2 : K))
    linearIndependent_typeBSimpleCorootGenerator
  nondegen := Matrix.Nondegenerate.of_det_ne_zero (by
    rw [CartanMatrix.B_det n.succ_pos]
    norm_num)
  sl2 := isSl2Triple_typeBSimpleRootGenerator
  lie_h_h := typeBSimpleCorootGenerator_lie_eq_zero
  lie_h_e i j := typeBSimpleCorootGenerator_lie_root j i
  lie_h_f i j := by rw [typeBSimpleCorootGenerator_lie_negativeRoot, neg_smul]
  lie_e_f_ne := typeBSimpleRootGenerator_lie_negative_of_ne

variable (n : ℕ)

/-- The Cartan matrix of the standard split type-`B` basis is `CartanMatrix.B (n + 1)`. -/
@[simp]
theorem typeBLieBasis_A : (typeBLieBasis (K := K) n).A = CartanMatrix.B (n + 1) := (rfl)

/-- The Cartan generators of the standard split type-`B` basis are the numbered simple
coroots. -/
@[simp]
theorem typeBLieBasis_h (i : Fin (n + 1)) :
    (typeBLieBasis (K := K) n).h i = typeBSimpleCorootGenerator i := (rfl)

/-- The raising generators of the standard split type-`B` basis are the positive simple-root
generators. -/
@[simp]
theorem typeBLieBasis_e (i : Fin (n + 1)) :
    (typeBLieBasis (K := K) n).e i = typeBSimpleRootGenerator i := (rfl)

/-- The lowering generators of the standard split type-`B` basis are the negative simple-root
generators. -/
@[simp]
theorem typeBLieBasis_f (i : Fin (n + 1)) :
    (typeBLieBasis (K := K) n).f i = typeBSimpleNegativeRootGenerator i := (rfl)

end TauCeti
