/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generators
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

/-!
# The simple-coroot basis of the split type-D Cartan

The explicit type-D Chevalley generators use the Bourbaki simple roots as diagonal coordinates.
Over a commutative ring with invertible two, these vectors form a basis of the diagonal Cartan.
Their coordinates are prefix sums of the upper diagonal entries along the chain. At the two
fork nodes they are half the upper diagonal total minus its last entry and half that total,
respectively. The basis-span theorem gives the Lie-span result used by the native split Lie
algebra basis.

Independence over a commutative domain only requires that `2` be nonzero. This weaker result
comes from `DynkinType.linearIndependent_typeDSimpleRoot_cast`: the doubled fundamental
coweights pair with the simple roots diagonally by `2`, which is regular in such a domain.
The generator membership and coordinate lemmas live in `Root/Generators.lean`.

## Main declarations

* `TypeDStd.typeDSimpleCorootBasis`: the numbered simple coroots form a basis of the diagonal
  Cartan when two is invertible.
* `TypeDStd.typeDSimpleCorootBasis_repr_apply`: explicit coefficients from upper diagonal entries.
* `TypeDStd.linearIndependent_cartanGenerator`: the ambient Cartan generators are independent.
* `TypeDStd.typeDDiagonalCartan_eq_lieSpan_cartanGenerator_of_invertible`: they span the diagonal
  Cartan as a Lie subalgebra when two is invertible.
* `TypeDStd.typeDDiagonalCartan_eq_lieSpan_cartanGenerator`: the field corollary with nonzero two.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace TauCeti

namespace TypeDStd

section Domain

variable {K : Type*} [CommRing K] [IsDomain K] [NeZero (2 : K)]

private theorem linearIndependent_cartanGenerator_subtype (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (fun i : Fin n =>
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n))) := by
  have hrows : LinearIndependent K (fun i j =>
      (DynkinType.typeDSimpleRoot n hn i j : K)) :=
    DynkinType.linearIndependent_typeDSimpleRoot_cast
      (IsRegular.of_ne_zero (NeZero.ne (2 : K))).right hn
  have hcoord : LinearIndependent K (fun i =>
      typeDDiagonalEquiv (K := K) (ι := Fin n)
        (fun j => (DynkinType.typeDSimpleRoot n hn i j : K))) :=
    hrows.map' (typeDDiagonalEquiv (K := K) (ι := Fin n)).toLinearMap
      (typeDDiagonalEquiv (K := K) (ι := Fin n)).ker
  convert hcoord using 1
  funext i
  apply Subtype.ext
  exact cartanGenerator_eq_typeDDiagonalEquiv (K := K) n hn i

/-- The explicit simple-root Cartan generators are linearly independent in the ambient
type-D Lie algebra. -/
theorem linearIndependent_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (cartanGenerator (K := K) n hn) := by
  exact (linearIndependent_cartanGenerator_subtype (K := K) n hn).map'
    (typeDDiagonalCartan K (Fin n)).toSubmodule.subtype (Submodule.ker_subtype _)

end Domain

section InvertibleTwo

variable {K : Type*} [CommRing K] [Invertible (2 : K)]

/-- The Bourbaki simple coroots as a basis of the split type-`Dₙ` diagonal Cartan. -/
noncomputable def typeDSimpleCorootBasis (n : ℕ) (hn : 4 ≤ n) :
    Module.Basis (Fin n) K (typeDDiagonalCartan K (Fin n)) :=
  (DynkinType.typeDSimpleRootBasis K n hn).map typeDDiagonalEquiv

/-- The simple-coroot basis consists of the numbered Cartan generators. -/
@[simp]
theorem coe_typeDSimpleCorootBasis_apply (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    ((typeDSimpleCorootBasis (K := K) n hn i : typeDDiagonalCartan K (Fin n)) :
      LieAlgebra.Orthogonal.typeD (Fin n) K) = cartanGenerator n hn i := by
  rw [typeDSimpleCorootBasis, Module.Basis.map_apply, DynkinType.typeDSimpleRootBasis_apply]
  exact (cartanGenerator_eq_typeDDiagonalEquiv n hn i).symm

/-- Simple-coroot coordinates are prefix sums of the upper diagonal entries for `k < n - 2`.
At the two fork nodes they are half that total minus its last entry and half that total. -/
theorem typeDSimpleCorootBasis_repr_apply (n : ℕ) (hn : 4 ≤ n)
    (A : typeDDiagonalCartan K (Fin n)) (k : Fin n) :
    (typeDSimpleCorootBasis (K := K) n hn).repr A k =
      if (k : ℕ) + 2 < n then ∑ j ∈ Finset.Iic k, A.1.1 (Sum.inl j) (Sum.inl j)
      else if (k : ℕ) + 1 < n then
        ⅟ (2 : K) * (∑ j, A.1.1 (Sum.inl j) (Sum.inl j)) -
          A.1.1 (Sum.inl ⟨n - 1, by omega⟩) (Sum.inl ⟨n - 1, by omega⟩)
      else ⅟ (2 : K) * (∑ j, A.1.1 (Sum.inl j) (Sum.inl j)) := by
  rw [typeDSimpleCorootBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
  simpa only [typeDDiagonalEquiv_symm_apply] using
    DynkinType.typeDSimpleRootBasis_repr_apply K hn
      ((typeDDiagonalEquiv (K := K) (ι := Fin n)).symm A) k

/-- The explicit simple-root Cartan generators span the diagonal Cartan whenever two is
invertible in the coefficient ring. -/
theorem typeDDiagonalCartan_eq_lieSpan_cartanGenerator_of_invertible (n : ℕ) (hn : 4 ≤ n) :
    typeDDiagonalCartan K (Fin n) =
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (cartanGenerator (K := K) n hn)) := by
  apply le_antisymm
  · intro x hx
    have h := Submodule.mem_map_of_mem
      (f := (typeDDiagonalCartan K (Fin n)).toSubmodule.subtype)
      ((typeDSimpleCorootBasis (K := K) n hn).mem_span ⟨x, hx⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have hgenerators : (typeDDiagonalCartan K (Fin n)).toSubmodule.subtype ∘
        typeDSimpleCorootBasis (K := K) n hn = cartanGenerator (K := K) n hn := by
      funext i
      exact coe_typeDSimpleCorootBasis_apply n hn i
    rw [hgenerators] at h
    exact LieSubalgebra.submodule_span_le_lieSpan h
  · rw [LieSubalgebra.lieSpan_le]
    rintro x ⟨i, rfl⟩
    exact cartanGenerator_mem_typeDDiagonalCartan n hn i

end InvertibleTwo

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The explicit simple-root Cartan generators span the diagonal Cartan as a Lie subalgebra. -/
theorem typeDDiagonalCartan_eq_lieSpan_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    typeDDiagonalCartan K (Fin n) =
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (cartanGenerator (K := K) n hn)) := by
  let := invertibleOfNonzero (NeZero.ne (2 : K))
  exact typeDDiagonalCartan_eq_lieSpan_cartanGenerator_of_invertible n hn

end Field

end TypeDStd

end TauCeti
