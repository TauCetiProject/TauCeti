/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Root
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generation

/-!
# A Lie algebra basis for the split even orthogonal Lie algebra

The diagonal Cartan and the numbered simple-root matrices of the split even orthogonal Lie algebra
form a `LieAlgebra.Basis`. Its Cartan matrix is the type-`D` Cartan matrix in Bourbaki numbering,
its Cartan generators are the diagonal matrices associated to the simple roots, and its raising and
lowering generators are the corresponding positive and negative root matrices.

This package makes the concrete matrix realization available to the generic Lie-basis API. In
particular, it determines the upper and lower nilpotent subalgebras, proves triangularizability of
the Cartan action in characteristic zero, and places the numbered generators in the simple-root
spaces.

## Main declarations

* `TauCeti.TypeDStd.lieBasis`: the standard type-`D` Lie algebra basis.
* `TauCeti.TypeDStd.lieBasis_A_eq`: its Cartan matrix is `CartanMatrix.D n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§12--14.
-/

public section

namespace TauCeti.TypeDStd

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The standard Chevalley-style basis of the split even orthogonal Lie algebra of type `Dₙ`.

The Cartan matrix and generators use Bourbaki's numbering. The two copies of `Fin n` indexing
`rootGenerator` distinguish raising from lowering generators. -/
noncomputable def lieBasis (n : ℕ) (hn : 4 ≤ n) :
    LieAlgebra.Basis (Fin n) (typeDDiagonalCartan K (Fin n)) where
  A := CartanMatrix.D n
  h := cartanGenerator n hn
  e i := rootGenerator n hn (.inl i)
  f i := rootGenerator n hn (.inr i)
  cartan_eq_lieSpan := typeDDiagonalCartan_eq_lieSpan_cartanGenerator n hn
  span_ef := lieSpan_rootGenerator_eq_top n hn
  linInd := linearIndependent_cartanGenerator n hn
  nondegen := Matrix.Nondegenerate.of_det_ne_zero (by
    rw [CartanMatrix.D_det (by omega : 2 ≤ n)]
    norm_num)
  sl2 := isSl2Triple_rootGenerator n hn
  lie_h_h := lie_cartanGenerator_cartanGenerator n hn
  lie_h_e i j := by
    simpa only [rootGeneratorWeight_inl, Int.cast_smul_eq_zsmul] using
      lie_cartanGenerator_rootGenerator (K := K) n hn (.inl i) j
  lie_h_f i j := by
    simpa only [rootGeneratorWeight_inr, Int.cast_smul_eq_zsmul] using
      lie_cartanGenerator_rootGenerator (K := K) n hn (.inr i) j
  lie_e_f_ne i j hij := by
    rw [lie_rootGenerator_inl_inr, ite_eq_right hij]

/-- The Cartan matrix of the standard split type-`D` basis is `CartanMatrix.D n`. -/
@[simp]
theorem lieBasis_A_eq (n : ℕ) (hn : 4 ≤ n) :
    (lieBasis (K := K) n hn).A = CartanMatrix.D n := by
  rw [lieBasis]

/-- The Cartan generators of the standard split type-`D` basis are the numbered diagonal
generators. -/
@[simp]
theorem lieBasis_h (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (lieBasis (K := K) n hn).h i = cartanGenerator n hn i := by
  rw [lieBasis]

/-- The raising generators of the standard split type-`D` basis are the positive simple-root
generators. -/
@[simp]
theorem lieBasis_e (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (lieBasis (K := K) n hn).e i = rootGenerator n hn (.inl i) := by
  rw [lieBasis]

/-- The lowering generators of the standard split type-`D` basis are the negative simple-root
generators. -/
@[simp]
theorem lieBasis_f (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (lieBasis (K := K) n hn).f i = rootGenerator n hn (.inr i) := by
  rw [lieBasis]

end TauCeti.TypeDStd
