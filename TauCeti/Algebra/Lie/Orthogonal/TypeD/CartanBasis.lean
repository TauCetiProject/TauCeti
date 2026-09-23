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
* `TypeDStd.linearIndependent_cartanGenerator`: the ambient Cartan generators are independent.
* `TypeDStd.typeDDiagonalCartan_eq_lieSpan_cartanGenerator`: they span the diagonal Cartan as a
  Lie subalgebra.
* `TypeDStd.cartanGeneratorBasis`: the simple-root Cartan generators as a module basis.
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

/-- The diagonal type-D Cartan contains every explicit simple-root Cartan generator. -/
theorem cartanGenerator_mem_typeDDiagonalCartan (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    cartanGenerator (K := K) n hn i ∈ typeDDiagonalCartan K (Fin n) := by
  have hgen : cartanGenerator (K := K) n hn i =
      (typeDDiagonalEquiv (K := K) (ι := Fin n)
        (fun j => (DynkinType.typeDSimpleRoot n hn i j : K)) :
        LieAlgebra.Orthogonal.typeD (Fin n) K) := by
    apply Subtype.ext
    rw [val_cartanGenerator, coe_typeDDiagonalEquiv_apply]
  rw [hgen]
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

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)]

private theorem linearIndependent_cartanGenerator_subtype (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (fun i : Fin n =>
      (⟨cartanGenerator (K := K) n hn i,
        cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ : typeDDiagonalCartan K (Fin n))) := by
  have hrows : LinearIndependent K (fun i j =>
      (DynkinType.typeDSimpleRoot n hn i j : K)) :=
    DynkinType.linearIndependent_typeDSimpleRoot_cast hn
  have hcoord : LinearIndependent K (fun i =>
      typeDDiagonalEquiv (K := K) (ι := Fin n)
        (fun j => (DynkinType.typeDSimpleRoot n hn i j : K))) :=
    hrows.map' (typeDDiagonalEquiv (K := K) (ι := Fin n)).toLinearMap
      (typeDDiagonalEquiv (K := K) (ι := Fin n)).ker
  convert hcoord using 1
  funext i
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_typeDDiagonalEquiv_apply, val_cartanGenerator]

/-- The explicit simple-root Cartan generators are linearly independent in the ambient
type-D Lie algebra. -/
theorem linearIndependent_cartanGenerator (n : ℕ) (hn : 4 ≤ n) :
    LinearIndependent K (cartanGenerator (K := K) n hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hsub := Fintype.linearIndependent_iff.mp
    (linearIndependent_cartanGenerator_subtype (K := K) n hn)
  apply hsub g
  · apply Subtype.ext
    -- Map the subtype relation through the Cartan inclusion to compare it with the ambient sum.
    change (typeDDiagonalCartan K (Fin n)).incl _ = 0
    rw [map_sum]
    simp only [map_smul, LieSubalgebra.coe_incl]
    exact hg

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
  · rw [← Submodule.map_subtype_top (typeDDiagonalCartan K (Fin n)).toSubmodule,
      ← (cartanGeneratorBasis (K := K) n hn).span_eq, Submodule.map_span, ← Set.range_comp]
    have hfun : (typeDDiagonalCartan K (Fin n)).toSubmodule.subtype ∘
        cartanGeneratorBasis (K := K) n hn =
        cartanGenerator (K := K) n hn := by
      funext i
      rw [Function.comp_apply, cartanGeneratorBasis_apply]
      -- Expose the subtype coercion after replacing the basis vector by its generator.
      change cartanGenerator (K := K) n hn i = cartanGenerator (K := K) n hn i
      rfl
    rw [hfun]
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact lie_cartanGenerator_cartanGenerator n hn i j

end Field

end TypeDStd

end TauCeti
