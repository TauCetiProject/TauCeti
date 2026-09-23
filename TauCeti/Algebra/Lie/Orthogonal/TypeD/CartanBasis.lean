/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.RootGenerators
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

/-!
# The simple-root basis of the split type-D Cartan

The explicit type-D Chevalley generators use the Bourbaki simple roots as diagonal coordinates.
This file lifts those matrices into the diagonal Cartan subalgebra and packages them as a module
basis. The coordinate theorem records the identification with the pinned classical type-D root
datum, so a later Lie-algebra basis can use the same Cartan coordinates.

The independence argument transports the integral independence of the Bourbaki simple roots to a
field in which `2` is invertible. The ambient independence and Lie-span theorems are exposed for
the later `LieAlgebra.Basis` construction.

## Main declarations

* `TypeDStd.cartanGenerator_mem_typeDDiagonalCartan`: the explicit Cartan generator lies in the
  standard diagonal Cartan.
* `DynkinType.det_typeDSimpleRoot_sq`: the determinant square of the integral simple-root matrix.
* `TypeDStd.linearIndependent_cartanGenerator`: the ambient Cartan generators are independent.
* `TypeDStd.typeDDiagonalCartan_eq_lieSpan_cartanGenerator`: they span the diagonal Cartan as a
  Lie subalgebra.
* `TypeDStd.cartanGeneratorBasis`: the simple-root Cartan generators as a module basis.
* `TypeDStd.typeDDiagonalCartanBasis_repr_cartanGeneratorBasis`: their coordinates in the ambient
  diagonal basis are the pinned type-D simple roots.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace TauCeti

namespace DynkinType

/-! The determinant identity is useful whenever the simple roots are transported to a coefficient
field. -/

theorem det_typeDSimpleRoot_sq (n : ℕ) (hn : 4 ≤ n) :
    (Matrix.of (typeDSimpleRoot n hn)).det ^ 2 = 4 := by
  have hmul : Matrix.of (typeDSimpleRoot n hn) *
      Matrix.transpose (Matrix.of (typeDSimpleRoot n hn)) = CartanMatrix.D n := by
    ext i j
    rw [Matrix.mul_apply,
      ← typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j]
    simp [dotProduct]
  have hsq : (CartanMatrix.D n).det = (Matrix.of (typeDSimpleRoot n hn)).det ^ 2 := by
    rw [← hmul, Matrix.det_mul, Matrix.det_transpose, sq]
  rw [CartanMatrix.D_det (by omega)] at hsq
  exact hsq.symm

end DynkinType

namespace TypeDStd

section CommRing

variable {K : Type*} [CommRing K]

/-- The diagonal type-D Cartan contains every explicit simple-root Cartan generator. -/
theorem cartanGenerator_mem_typeDDiagonalCartan (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    cartanGenerator (K := K) n hn i ∈ typeDDiagonalCartan K (Fin n) := by
  rw [mem_typeDDiagonalCartan_iff_isDiag, val_cartanGenerator]
  intro a b hab
  rw [typeDDiagonalMatrix_apply]
  exact ite_eq_right hab

/-- The ambient diagonal coordinates of a lifted simple-root Cartan generator are the pinned
type-D simple root. -/
theorem typeDDiagonalCartanBasis_repr_cartanGenerator (n : ℕ) (hn : 4 ≤ n)
    (i j : Fin n) :
    (typeDDiagonalCartanBasis (K := K) (ι := Fin n)).repr
        (⟨cartanGenerator (K := K) n hn i,
          cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n)) j =
      (DynkinType.typeDSimpleRoot n hn i j : K) := by
  rw [typeDDiagonalCartanBasis_repr_apply, val_cartanGenerator]
  simp only [typeDDiagonalMatrix_apply, typeDDiagonalValue_inl, eq_self, ite_true]

end CommRing

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

private theorem linearIndependent_cartanGenerator_subtype (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (fun i : Fin n =>
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n))) := by
  let A : Matrix (Fin n) (Fin n) K :=
    (Matrix.of (DynkinType.typeDSimpleRoot n hn)).map (Int.castRingHom K)
  have hdetcast : A.det = ((Matrix.of (DynkinType.typeDSimpleRoot n hn)).det : K) := by
    dsimp [A]
    exact (Int.cast_det (R := K) (Matrix.of (DynkinType.typeDSimpleRoot n hn))).symm
  have hdet_sq : A.det ^ 2 = (4 : K) := by
    rw [hdetcast]
    simpa only [Int.cast_pow, Int.cast_ofNat] using
      congrArg (fun z : ℤ => (z : K)) (DynkinType.det_typeDSimpleRoot_sq n hn)
  have hdet : A.det ≠ 0 := by
    intro hzero
    have hfour : (4 : K) ≠ 0 := by
      rw [show (4 : K) = (2 : K) ^ 2 by norm_num]
      exact pow_ne_zero 2 (NeZero.ne _)
    exact hfour (by simpa [hzero] using hdet_sq.symm)
  have hrows : LinearIndependent K (fun i => A i) := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mpr
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  have hcoord : LinearIndependent K (fun i =>
      typeDDiagonalEquiv (K := K) (ι := Fin n) (A i)) :=
    hrows.map' (typeDDiagonalEquiv (K := K) (ι := Fin n)).toLinearMap
      (typeDDiagonalEquiv (K := K) (ι := Fin n)).ker
  convert hcoord using 1
  funext i
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_typeDDiagonalEquiv_apply, val_cartanGenerator]
  rfl

/-- The explicit simple-root Cartan generators are linearly independent in the ambient
type-D Lie algebra. -/
theorem linearIndependent_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (cartanGenerator (K := K) n hn) := by
  let A : Matrix (Fin n) (Fin n) K :=
    (Matrix.of (DynkinType.typeDSimpleRoot n hn)).map (Int.castRingHom K)
  have hdetcast : A.det = ((Matrix.of (DynkinType.typeDSimpleRoot n hn)).det : K) := by
    dsimp [A]
    exact (Int.cast_det (R := K) (Matrix.of (DynkinType.typeDSimpleRoot n hn))).symm
  have hdet_sq : A.det ^ 2 = (4 : K) := by
    rw [hdetcast]
    simpa only [Int.cast_pow, Int.cast_ofNat] using
      congrArg (fun z : ℤ => (z : K)) (DynkinType.det_typeDSimpleRoot_sq n hn)
  have hdet : A.det ≠ 0 := by
    intro hzero
    have hfour : (4 : K) ≠ 0 := by
      rw [show (4 : K) = (2 : K) ^ 2 by norm_num]
      exact pow_ne_zero 2 (NeZero.ne _)
    exact hfour (by simpa [hzero] using hdet_sq.symm)
  have hrows : LinearIndependent K (fun i => A i) :=
    by
      apply Matrix.linearIndependent_rows_iff_isUnit.mpr
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      exact hdet
  rw [Fintype.linearIndependent_iff] at hrows ⊢
  intro g hg k
  apply hrows g
  have hsum : ∑ i, g i •
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ :
          typeDDiagonalCartan K (Fin n)) = 0 := by
    apply Subtype.ext
    change (typeDDiagonalCartan K (Fin n)).incl
        (∑ i, g i •
          (⟨cartanGenerator (K := K) n hn i,
            cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ :
              typeDDiagonalCartan K (Fin n))) = 0
    rw [map_sum]
    simp only [map_smul, LieSubalgebra.coe_incl]
    exact hg
  have hcoord := congrArg (typeDDiagonalEquiv (K := K) (ι := Fin n)).symm hsum
  have hgen (i : Fin n) :
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ :
          typeDDiagonalCartan K (Fin n)) =
        typeDDiagonalEquiv (K := K) (ι := Fin n) (A i) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [val_cartanGenerator, coe_typeDDiagonalEquiv_apply]
    change typeDDiagonalMatrix
        (fun j => (DynkinType.typeDSimpleRoot n hn i j : K)) =
      typeDDiagonalMatrix (A i)
    congr 1
  rw [map_sum, map_zero] at hcoord
  simp_rw [map_smul, hgen, LinearEquiv.symm_apply_apply] at hcoord
  exact hcoord

/-- The simple-root Cartan generators form a basis of the split diagonal Cartan. -/
noncomputable def cartanGeneratorBasis (n : ℕ) (hn : 4 ≤ n) :
    Module.Basis (Fin n) K (typeDDiagonalCartan K (Fin n)) :=
  basisOfLinearIndependentOfCardEqFinrank' _
    (linearIndependent_cartanGenerator_subtype n hn)
    (by simp [finrank_typeDDiagonalCartan])

/-- The vectors of `cartanGeneratorBasis` are the explicit matrix Cartan generators. -/
@[simp]
theorem cartanGeneratorBasis_apply (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    cartanGeneratorBasis (K := K) n hn i =
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n)) := by
  exact congr_fun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i

/-- The explicit simple-root Cartan generators span the diagonal Cartan as a Lie subalgebra. -/
theorem typeDDiagonalCartan_eq_lieSpan_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    typeDDiagonalCartan K (Fin n) =
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (cartanGenerator (K := K) n hn)) := by
  apply LieSubalgebra.toSubmodule_injective
  rw [LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero]
  · apply le_antisymm
    · intro x hx
      let b := cartanGeneratorBasis (K := K) n hn
      have hrepr := b.sum_repr ⟨x, hx⟩
      have hxsum : x = ∑ i, b.repr ⟨x, hx⟩ i •
          (b i : LieAlgebra.Orthogonal.typeD (Fin n) K) := by
        change ((⟨x, hx⟩ : typeDDiagonalCartan K (Fin n)) :
          LieAlgebra.Orthogonal.typeD (Fin n) K) = _
        have hmaprepr := congrArg (fun z : typeDDiagonalCartan K (Fin n) =>
          (typeDDiagonalCartan K (Fin n)).incl z) hrepr.symm
        simpa only [map_sum, map_smul, LieSubalgebra.coe_incl] using hmaprepr
      rw [hxsum]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem _ _
      rw [cartanGeneratorBasis_apply]
      exact Submodule.subset_span (Set.mem_range_self i)
    · refine Submodule.span_le.2 ?_
      rintro x ⟨i, rfl⟩
      exact cartanGenerator_mem_typeDDiagonalCartan n hn i
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    change ⁅(cartanGenerator (K := K) n hn i : LieAlgebra.Orthogonal.typeD (Fin n) K),
      cartanGenerator (K := K) n hn j⁆ = 0
    apply Subtype.ext
    exact lie_eq_zero_of_isDiag
      (mem_typeDDiagonalCartan_iff_isDiag.mp (cartanGenerator_mem_typeDDiagonalCartan n hn i))
      (mem_typeDDiagonalCartan_iff_isDiag.mp (cartanGenerator_mem_typeDDiagonalCartan n hn j))

/-- The coordinates of a `cartanGeneratorBasis` vector are the pinned type-D simple root. -/
theorem typeDDiagonalCartanBasis_repr_cartanGeneratorBasis (n : ℕ) (hn : 4 ≤ n)
    (i j : Fin n) :
    (typeDDiagonalCartanBasis (K := K) (ι := Fin n)).repr
        (cartanGeneratorBasis (K := K) n hn i) j =
      (DynkinType.typeDSimpleRoot n hn i j : K) := by
  rw [cartanGeneratorBasis_apply]
  exact typeDDiagonalCartanBasis_repr_cartanGenerator n hn i j

end Field

end TypeDStd

end TauCeti
