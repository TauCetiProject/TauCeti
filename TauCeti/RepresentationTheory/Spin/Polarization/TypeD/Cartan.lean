/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.RootGenerators
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan

/-!
# The simple-root basis of the split type-D Cartan

The explicit type-D Chevalley generators use the Bourbaki simple roots as diagonal coordinates.
This file lifts those matrices into the diagonal Cartan subalgebra and packages them as a module
basis.  The coordinate theorem at the end records the identification with the pinned classical
type-D root datum, so a later Lie-algebra basis can use the same Cartan coordinates as the spin
polarization.

The independence argument transports the integral independence of the Bourbaki simple roots to a
characteristic-zero field.  Thus the result does not choose an inverse of the Cartan matrix or
depend on a particular field beyond the hypotheses needed for scalar extension.

## Main declarations

* `TypeDStd.cartanGenerator_mem_typeDDiagonalCartan`: the explicit Cartan generator lies in the
  standard diagonal Cartan.
* `TypeDStd.cartanGeneratorBasis`: the simple-root Cartan generators as a module basis.
* `TypeDStd.typeDDiagonalCartanBasis_repr_cartanGenerator`: its coordinates in the ambient
  diagonal basis are the pinned type-D simple roots.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace TauCeti.TypeDStd

variable {K : Type*} [Field K]

/-- The diagonal type-D Cartan contains every explicit simple-root Cartan generator. -/
theorem cartanGenerator_mem_typeDDiagonalCartan (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    cartanGenerator (K := K) n hn i ∈ typeDDiagonalCartan K (Fin n) := by
  rw [mem_typeDDiagonalCartan_iff_isDiag, val_cartanGenerator]
  intro a b hab
  rw [typeDDiagonalMatrix_apply]
  exact ite_eq_right hab

variable [CharZero K]

private theorem linearIndependent_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (fun i : Fin n =>
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n))) := by
  let A : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => (DynkinType.typeDSimpleRoot n hn i j : K)
  have hdetZ : (Matrix.of (DynkinType.typeDSimpleRoot n hn)).det ≠ 0 := by
    exact Matrix.nonsingular_iff_det_ne_zero.mp
      (Matrix.Nonsingular.of_linearIndependent_row
        (DynkinType.linearIndependent_typeDSimpleRoot hn))
  have hdet : A.det ≠ 0 := by
    have hdetcast : A.det = ((Matrix.of (DynkinType.typeDSimpleRoot n hn)).det : K) := by
      rw [show A = (Matrix.of (DynkinType.typeDSimpleRoot n hn)).map (Int.castRingHom K) by
        ext i j
        rfl]
      exact (Int.cast_det (R := K) (Matrix.of (DynkinType.typeDSimpleRoot n hn))).symm
    rw [hdetcast]
    exact_mod_cast hdetZ
  have hrows : LinearIndependent K (fun i => A i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  let v : Fin n → typeDDiagonalCartan K (Fin n) := fun i =>
    ⟨cartanGenerator (K := K) n hn i, cartanGenerator_mem_typeDDiagonalCartan n hn i⟩
  have hv : v = (fun i => typeDDiagonalEquiv (K := K) (ι := Fin n) (A i)) := by
    funext i
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_typeDDiagonalEquiv_apply, val_cartanGenerator]
    rfl
  -- The statement's subtype family is the local lifted family `v`; expose it before transporting
  -- independence through the coordinate equivalence.
  change LinearIndependent K v
  rw [hv]
  exact hrows.map' (typeDDiagonalEquiv (K := K) (ι := Fin n)).toLinearMap
    (by exact (typeDDiagonalEquiv (K := K) (ι := Fin n)).ker)

private theorem span_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    Submodule.span K (Set.range (fun i : Fin n =>
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n)))) = ⊤ := by
  exact (linearIndependent_cartanGenerator n hn).span_eq_top_of_card_eq_finrank' (by
    simp [finrank_typeDDiagonalCartan])

/-- The simple-root Cartan generators form a basis of the split diagonal Cartan. -/
noncomputable def cartanGeneratorBasis (n : ℕ) (hn : 4 ≤ n) :
    Module.Basis (Fin n) K (typeDDiagonalCartan K (Fin n)) :=
  Module.Basis.mk (linearIndependent_cartanGenerator n hn) (span_cartanGenerator n hn).ge

/-- The vectors of `cartanGeneratorBasis` are the explicit matrix Cartan generators. -/
@[simp]
theorem cartanGeneratorBasis_apply (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    cartanGeneratorBasis (K := K) n hn i =
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n)) := by
  simp [cartanGeneratorBasis]

/-- The ambient diagonal coordinates of a simple-root Cartan generator are the pinned simple root.
-/
theorem typeDDiagonalCartanBasis_repr_cartanGenerator (n : ℕ) (hn : 4 ≤ n)
    (i j : Fin n) :
    (typeDDiagonalCartanBasis (K := K) (ι := Fin n)).repr
        (cartanGeneratorBasis (K := K) n hn i) j =
      (DynkinType.typeDSimpleRoot n hn i j : K) := by
  rw [cartanGeneratorBasis_apply,
    typeDDiagonalCartanBasis_repr_apply, val_cartanGenerator]
  simp only [typeDDiagonalMatrix_apply, typeDDiagonalValue_inl, eq_self, ite_true]

end TauCeti.TypeDStd
