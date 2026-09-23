/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.RootGenerators
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

/-!
# The simple-root generators of the split type-D Cartan

The explicit type-D Chevalley generators use the Bourbaki simple roots as diagonal coordinates.
This file lifts those matrices into the diagonal Cartan subalgebra and records their ambient
coordinates against the standard Cartan basis. It exposes the independence and Lie-span results
needed to use these generators as the split Cartan's simple-root coordinates.

The independence argument transports the integral independence of the Bourbaki simple roots to a
commutative domain in which `2` is nonzero. The ambient independence and Lie-span theorems expose
the resulting split Cartan structure.

## Main declarations

* `TypeDStd.cartanGenerator_mem_typeDDiagonalCartan`: the explicit Cartan generator lies in the
  standard diagonal Cartan.
* `TypeDStd.linearIndependent_cartanGenerator`: the ambient Cartan generators are independent.
* `TypeDStd.typeDDiagonalCartan_eq_lieSpan_cartanGenerator`: they span the diagonal Cartan as a
  Lie subalgebra.
* `TypeDStd.typeDDiagonalCartanBasis_repr_cartanGenerator`: their coordinates in the ambient
  diagonal basis are the pinned type-D simple roots.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace TauCeti

namespace TypeDStd

section CommRing

variable {K : Type*} [CommRing K]

private theorem cartanGenerator_eq_coe_typeDDiagonalEquiv (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    cartanGenerator (K := K) n hn i =
      (typeDDiagonalEquiv (K := K) (ι := Fin n)
        (fun j => (DynkinType.typeDSimpleRoot n hn i j : K)) :
        LieAlgebra.Orthogonal.typeD (Fin n) K) := by
  apply Subtype.ext
  rw [val_cartanGenerator, coe_typeDDiagonalEquiv_apply]

/-- The diagonal type-D Cartan contains every explicit simple-root Cartan generator. -/
theorem cartanGenerator_mem_typeDDiagonalCartan (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    cartanGenerator (K := K) n hn i ∈ typeDDiagonalCartan K (Fin n) := by
  rw [cartanGenerator_eq_coe_typeDDiagonalEquiv]
  exact (typeDDiagonalEquiv (K := K) (ι := Fin n)
    (fun j => (DynkinType.typeDSimpleRoot n hn i j : K))).2

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

section Domain

variable {K : Type*} [CommRing K] [IsDomain K] [NeZero (2 : K)]

private theorem linearIndependent_cartanGenerator_subtype (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (fun i : Fin n =>
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n))) := by
  have hrows : LinearIndependent K (fun i j =>
      (DynkinType.typeDSimpleRoot n hn i j : K)) :=
    DynkinType.linearIndependent_typeDSimpleRoot_cast (K := K) hn
  have hcoord : LinearIndependent K (fun i =>
      typeDDiagonalEquiv (K := K) (ι := Fin n)
        (fun j => (DynkinType.typeDSimpleRoot n hn i j : K))) :=
    hrows.map' (typeDDiagonalEquiv (K := K) (ι := Fin n)).toLinearMap
      (typeDDiagonalEquiv (K := K) (ι := Fin n)).ker
  convert hcoord using 1
  funext i
  apply Subtype.ext
  exact cartanGenerator_eq_coe_typeDDiagonalEquiv (K := K) n hn i

/-- The explicit simple-root Cartan generators are linearly independent in the ambient
type-D Lie algebra. -/
theorem linearIndependent_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (cartanGenerator (K := K) n hn) := by
  exact (linearIndependent_cartanGenerator_subtype (K := K) n hn).map'
    (typeDDiagonalCartan K (Fin n)).toSubmodule.subtype (Submodule.ker_subtype _)

end Domain

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The explicit simple-root Cartan generators span the diagonal Cartan as a Lie subalgebra. -/
theorem typeDDiagonalCartan_eq_lieSpan_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    typeDDiagonalCartan K (Fin n) =
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (cartanGenerator (K := K) n hn)) := by
  apply LieSubalgebra.toSubmodule_injective
  rw [LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero]
  · rw [← Submodule.map_subtype_top (typeDDiagonalCartan K (Fin n)).toSubmodule,
      ← (linearIndependent_cartanGenerator_subtype (K := K) n hn).span_eq_top_of_card_eq_finrank'
        (by simp [finrank_typeDDiagonalCartan]),
      Submodule.map_span, ← Set.range_comp]
    rfl
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact lie_cartanGenerator_cartanGenerator n hn i j

end Field

end TypeDStd

end TauCeti
