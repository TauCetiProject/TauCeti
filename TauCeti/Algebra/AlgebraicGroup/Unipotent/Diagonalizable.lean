/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic

/-!
# Homomorphisms from diagonalizable groups to unipotent groups are trivial

Over a field, a bialgebra whose group-like elements span it has no nonzero primitive elements:
expanding a primitive element in the basis of group-like elements and comparing coefficients of
`g ⊗ 1` in its comultiplication shows every coefficient vanishes. Feeding this into the
comultiplication `Δ cᵢⱼ = ∑ₗ cᵢₗ ⊗ cₗⱼ` of the coefficients of an upper-unitriangular
representation, an induction on `j - i` shows that every coalgebra morphism to such a bialgebra
sends the coefficient matrix to the identity matrix.

A reduced finite-type affine group over an algebraically closed field whose rational points are
unipotent has a faithful upper-unitriangular representation, whose coefficients and their
antipodes generate its coordinate algebra. Hence every homomorphism into it from a
diagonalizable group is trivial; contravariantly, every bialgebra morphism from its coordinate
algebra to a group-like-spanned commutative Hopf algebra is the counit. In particular a
diagonalizable closed subgroup of such a unipotent group is trivial, with no reducedness
assumption on the subgroup: this is the scheme-theoretic form, which also sees infinitesimal
subgroups such as `μₚ`. It is the input showing that a torus of a smooth connected solvable
group meets its unipotent radical trivially.

## Main declarations

* `TauCeti.eq_zero_of_comul_eq_of_groupLikeSetSpan_eq_top`: a group-like-spanned bialgebra over
  a field has no nonzero primitive elements.
* `TauCeti.Comodule.map_coefficientMatrix_eq_one_of_isUpperUnitriangular`: a coalgebra morphism
  preserving `1` to a group-like-spanned bialgebra sends an upper-unitriangular coefficient matrix
  to the identity matrix.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.eq_of_groupLikeSetSpan_eq_top`: a
  bialgebra morphism from the coordinate algebra of a reduced unipotent group to a
  group-like-spanned commutative Hopf algebra is the counit.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.bijective_algebraMap_of_surjective`:
  a diagonalizable closed subgroup of a reduced unipotent group is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 14 (unipotent groups) and Theorem 16.33.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), Chapter 8.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

section Primitive

variable {k : Type u} {K : Type v} [Field k] [Ring K] [Bialgebra k K]

/-- **A group-like-spanned bialgebra over a field has no nonzero primitive elements.** If the
group-like elements span `K` and `Δ x = x ⊗ 1 + 1 ⊗ x`, then `x = 0`. -/
theorem eq_zero_of_comul_eq_of_groupLikeSetSpan_eq_top
    (hK : Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤) {x : K}
    (hx : Coalgebra.comul (R := k) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x) : x = 0 := by
  classical
  let b := Subcoalgebra.groupLikeBasis hK
  let one : GroupLike k K := ⟨1, IsGroupLikeElem.one⟩
  -- Pair the two sides of `hx` with `coord g ⊗ coord 1` and multiply.
  have key (g : GroupLike k K) :
      (TensorProduct.lid k k) (TensorProduct.map (b.coord g) (b.coord one)
        (Coalgebra.comul (R := k) x)) =
      (TensorProduct.lid k k) (TensorProduct.map (b.coord g) (b.coord one)
        (x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x)) := by rw [hx]
  have hb1 : (1 : K) = b one := (Subcoalgebra.groupLikeBasis_apply hK one).symm
  have hcomul : Coalgebra.comul (R := k) x =
      ∑ g ∈ (b.repr x).support, b.repr x g • (b g ⊗ₜ[k] b g) := by
    conv_lhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [map_smul, Subcoalgebra.groupLikeBasis_apply, g.isGroupLikeElem_val.comul_eq_tmul_self]
  have hpair (g : GroupLike k K) :
      ∑ g' ∈ (b.repr x).support,
          b.repr x g' * ((if g' = g then 1 else 0) * if g' = one then 1 else 0) =
        b.repr x g * (if one = one then 1 else 0) + (if one = g then 1 else 0) * b.repr x one := by
    have h := key g
    rw [hcomul] at h
    simpa only [map_sum, map_smul, TensorProduct.map_tmul, TensorProduct.lid_tmul, map_add,
      Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, hb1,
      Finsupp.single_apply] using h
  have h1 : b.repr x one = 0 := by
    have h := hpair one
    rw [Finset.sum_eq_single one (fun _ _ hne ↦ by simp [hne])
      (fun h' ↦ by simp [Finsupp.notMem_support_iff.mp h'])] at h
    simp only [ite_true, mul_one, one_mul] at h
    simpa using h
  refine b.ext_elem fun g ↦ ?_
  rw [map_zero, Finsupp.zero_apply]
  by_cases hg : g = one
  · rw [hg, h1]
  · have h := hpair g
    rw [Finset.sum_eq_zero fun g' _ ↦ by
      by_cases h' : g' = g <;> simp [h', hg]] at h
    simpa [Ne.symm hg] using h.symm

end Primitive

namespace Comodule

variable {k : Type u} {H : Type*} {K : Type v} {M : Type*}
variable [Field k] [Semiring H] [Module k H] [Coalgebra k H]
variable [Ring K] [Bialgebra k K]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- **A coalgebra morphism to a group-like-spanned bialgebra trivializes an upper-unitriangular
representation.** If `f` preserves `1` on the diagonal coefficients, then it sends the
coefficient matrix of an upper-unitriangular basis to the identity matrix. -/
theorem map_coefficientMatrix_eq_one_of_isUpperUnitriangular {n : ℕ}
    (b : Module.Basis (Fin n) k M)
    (hb : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hK : Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤)
    (f : H →ₗc[k] K) (hf : ∀ i, f (coefficientMatrix (C := H) b i i) = 1) :
    (coefficientMatrix (C := H) b).map f = 1 := by
  -- Entries below the diagonal vanish, and the diagonal maps to `1`.
  have hlow {i j : Fin n} (h : j < i) : f (coefficientMatrix (C := H) b i j) = 0 := by
    rw [hb.isUpperTriangular h, map_zero]
  -- Above the diagonal, induct on the distance `j - i` to the diagonal.
  suffices h : ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) - i = d → i < j →
      f (coefficientMatrix (C := H) b i j) = 0 by
    ext i j
    rw [Matrix.map_apply]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [Matrix.one_apply_ne hij.ne, h _ i j rfl hij]
    · rw [Matrix.one_apply_eq, hf]
    · rw [Matrix.one_apply_ne hij.ne', hlow hij]
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij
    apply eq_zero_of_comul_eq_of_groupLikeSetSpan_eq_top hK
    rw [← CoalgHomClass.map_comp_comul_apply, comul_coefficientMatrix_eq_sum, map_sum]
    simp only [TensorProduct.map_tmul, CoalgHom.coe_linearMapOfClass]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.ne, Finset.mem_univ i⟩)]
    -- The intermediate terms vanish: below the diagonal, or by the inductive hypothesis.
    have hrest : ∑ l ∈ (Finset.univ.erase j).erase i,
        f (coefficientMatrix (C := H) b i l) ⊗ₜ[k] f (coefficientMatrix (C := H) b l j) = 0 := by
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      simp only [Finset.mem_erase] at hl
      rcases lt_or_gt_of_ne hl.1 with hl' | hl'
      · rw [hlow hl', TensorProduct.zero_tmul]
      rcases lt_or_gt_of_ne hl.2.1 with hl'' | hl''
      · rw [ih ((j : ℕ) - l) (by omega) l j rfl hl'', TensorProduct.tmul_zero]
      · rw [hlow hl'', TensorProduct.tmul_zero]
    have hi := hf i
    have hj := hf j
    rw [hrest, hi, hj, add_zero, add_comm]

end Comodule

namespace geometricallyUnipotentPointsCommHopfAlgProperty

open Comodule

variable {k H K : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable [CommRing K] [HopfAlgebra k K]

/-- **A homomorphism from a diagonalizable group to a reduced unipotent group is trivial.** Over
an algebraically closed field, a bialgebra morphism from the coordinate algebra of a reduced
finite-type affine group with unipotent points to a commutative Hopf algebra spanned by its
group-like elements is the counit. -/
theorem eq_of_groupLikeSetSpan_eq_top [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (hK : Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤)
    (φ : H →ₐc[k] K) :
    φ.toAlgHom = (Algebra.ofId k K).comp (Bialgebra.counitAlgHom k H) := by
  obtain ⟨M, n, b, hb, hsurj⟩ :=
    exists_coordinateBialgHom_surjective_of_forall_isUnipotentPoint (forall_isUnipotentPoint hH)
  have hone := map_coefficientMatrix_eq_one_of_isUpperUnitriangular (H := H) b hb hK
    φ.toCoalgHom fun i ↦ by
      rw [((Matrix.isUpperUnitriangular_def _).mp hb).2 i]
      exact map_one φ
  have hcomp : φ.toAlgHom.comp (coordinateBialgHom (H := H) b).toAlgHom =
      ((Algebra.ofId k K).comp (Bialgebra.counitAlgHom k H)).comp
        (coordinateBialgHom (H := H) b).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext k n
    intro i j
    have h := congrFun (congrFun hone i) j
    simp only [Matrix.map_apply] at h
    simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
    erw [coordinateBialgHom_X]
    change φ (coefficientMatrix (C := H) b i j) = _
    rw [show φ (coefficientMatrix (C := H) b i j) = _ from h, counit_coefficientMatrix,
      Matrix.one_apply]
    split_ifs <;> simp
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact AlgHom.congr_fun hcomp y

/-- **A diagonalizable closed subgroup of a reduced unipotent group is trivial**, over an
algebraically closed field. If a surjective bialgebra morphism `H → K` exhibits the group
represented by `K` as a closed subgroup, and `K` is spanned by its group-like elements, then `K`
is the base field. No reducedness of `K` is assumed. -/
theorem bijective_algebraMap_of_surjective [IsAlgClosed k] [Algebra.FiniteType k H]
    [IsReduced H]
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (hK : Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤)
    (φ : H →ₐc[k] K) (hφ : Function.Surjective φ) :
    Function.Bijective (algebraMap k K) := by
  have h := eq_of_groupLikeSetSpan_eq_top hH hK φ
  -- The counit `K → k` sends `1` to `1`, so `K` is not the zero ring.
  have : Nontrivial K := ⟨⟨0, 1, fun h0 ↦ by
    simpa using congrArg (Coalgebra.counit (R := k) (A := K)) h0⟩⟩
  refine ⟨(algebraMap k K).injective, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨Bialgebra.counitAlgHom k H x, (AlgHom.congr_fun h x).symm⟩

end geometricallyUnipotentPointsCommHopfAlgProperty

end TauCeti
