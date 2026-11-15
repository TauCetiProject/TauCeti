/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent

/-!
# Symplectic bases extending a prescribed Lagrangian basis

Every basis of a Lagrangian subspace of a finite-dimensional symplectic space extends to a
symplectic basis, with the original vectors at the `Sum.inl` positions. In particular, an
ordered basis adapted to a flag in the Lagrangian retains that flag after the extension.
This allows a triangularizing basis on an invariant Lagrangian to be used as the isotropic
half of symplectic coordinates.

The construction works in every characteristic. First extend the coordinate functionals of
the prescribed basis to the ambient space using Mathlib's `Subspace.dualLift`, then use
`LinearMap.BilinForm.toDual` to find dual partners. Correct the partners by a strictly
triangular combination of the original vectors to make them isotropic. The correction uses
no division by two and is proved over a commutative ring.

The resulting family is a basis by the Gram determinant criterion
`LinearMap.BilinForm.linearIndependent_of_det_ne_zero` and dimension counting.

Our convention is Mathlib's `Matrix.J`: the dual vector pairs to `1` with its prescribed
partner, and the prescribed vector pairs to `-1` with its dual.

## References

* E. Artin, *Geometric Algebra* (1957), Theorem 3.7.
* J. S. Milne, *Algebraic Groups* (2017), §24.6 (symplectic groups and isotropic flags).
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module Submodule

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  {ι : Type*} [Finite ι] [DecidableEq ι] {B : BilinForm R V}

/-- Dual partners of an isotropic family can be chosen isotropic, over any commutative ring.
Here `B (f i) (e j) = δᵢⱼ` fixes the signs to agree with `Matrix.J`. -/
theorem IsAlt.exists_dual_isotropic_family (hB : B.IsAlt) (e f : ι → V)
    (he : ∀ i j, B (e i) (e j) = 0)
    (hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0) :
    ∃ f' : ι → V,
      (∀ i j, B (f' i) (e j) = if i = j then 1 else 0) ∧
      (∀ i j, B (f' i) (f' j) = 0) := by
  let : Fintype ι := Fintype.ofFinite ι
  -- This auxiliary enumeration chooses a strict triangle without reindexing the given family.
  let a := Fintype.equivFin ι
  let c (i j : ι) : R := if a j < a i then B (f i) (f j) else 0
  let f' (i : ι) : V := f i + ∑ j, c i j • e j
  have hf'e (i j : ι) : B (f' i) (e j) = if i = j then 1 else 0 := by
    simp [f', he, hfe]
  have hef' (i j : ι) : B (e i) (f' j) = -(if j = i then 1 else 0) := by
    rw [← hB.neg_eq, hf'e]
  have hff' (i j : ι) : B (f i) (f' j) = B (f i) (f j) + c j i := by
    simp [f', hfe]
  refine ⟨f', hf'e, fun i j ↦ ?_⟩
  have hpair : B (f' i) (f' j) = B (f i) (f j) + c j i - c i j := by
    simp [f', hff', hef', sub_eq_add_neg]
  rw [hpair]
  rcases lt_trichotomy (a i) (a j) with hij | hij | hji
  · simp only [c, hij, not_lt_of_gt hij, ite_true, ite_false, sub_zero]
    rw [← hB.neg_eq (f i) (f j), add_neg_cancel]
  · obtain rfl := a.injective hij
    simp [c, hB.self_eq_zero]
  · simp [c, hji, not_lt_of_gt hji]

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {B : BilinForm K V}

/-- A prescribed basis of an isotropic subspace of half the ambient dimension extends to a
symplectic basis. The original basis vectors occupy the `Sum.inl` positions, in their given
order; the result holds in characteristic two as well. -/
theorem IsAlt.exists_basis_toMatrix_eq_J_inl_eq_of_finrank
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {U : Submodule K V} (e : Basis ι K U)
    (hU : U ≤ B.orthogonal U) (hdim : Fintype.card ι + Fintype.card ι = finrank K V) :
    ∃ b : Basis (ι ⊕ ι) K V,
      toMatrix b B = Matrix.J ι K ∧ ∀ i, b (Sum.inl i) = (e i : V) := by
  classical
  let f (i : ι) : V := (B.toDual hnd).symm (Subspace.dualLift U (e.coord i))
  have hfe (i j : ι) : B (f i) (e j) = if i = j then 1 else 0 := by
    by_cases hij : i = j <;> simp [f, hij]
  have he (i j : ι) : B (e i) (e j) = 0 :=
    (mem_orthogonal_iff.mp (hU (e j).property)) (e i) (e i).property
  obtain ⟨f', hf'e, hf'f'⟩ := hB.exists_dual_isotropic_family (fun i ↦ (e i : V)) f he hfe
  let d : ι ⊕ ι → V := Sum.elim (fun i ↦ (e i : V)) f'
  have hd (i j : ι ⊕ ι) : B (d i) (d j) = Matrix.J ι K i j := by
    rcases i with i | i <;> rcases j with j | j
    · simpa [d, Matrix.J, Matrix.fromBlocks] using he i j
    · simpa [d, Matrix.J, Matrix.fromBlocks, Matrix.one_apply, eq_comm]
        using (hB.neg_eq (f' j) (e i)).symm.trans (congrArg Neg.neg (hf'e j i))
    · simpa [d, Matrix.J, Matrix.fromBlocks, Matrix.one_apply] using hf'e i j
    · simpa [d, Matrix.J, Matrix.fromBlocks] using hf'f' i j
  have hgram : (Matrix.of fun i j ↦ B (d i) (d j)) = Matrix.J ι K := Matrix.ext hd
  have hli : LinearIndependent K d := by
    apply B.linearIndependent_of_det_ne_zero
    rw [hgram]
    exact (Matrix.isUnit_det_J ι K).ne_zero
  have hcard : Fintype.card (ι ⊕ ι) = finrank K V := by
    simpa using hdim
  let b := basisOfLinearIndependentOfCardEqFinrank' d hli hcard
  have hb : ⇑b = d := coe_basisOfLinearIndependentOfCardEqFinrank' d hli hcard
  refine ⟨b, Matrix.ext fun i j ↦ ?_, fun i ↦ ?_⟩
  · rw [toMatrix_apply, hb, hd]
  · rw [hb]
    rfl

/-- Every prescribed basis of a Lagrangian subspace extends to a symplectic basis, with
the prescribed vectors as its isotropic half. A Lagrangian is expressed by `U = B.orthogonal U`;
no restriction on the characteristic or on the finite basis index type is needed. -/
theorem IsAlt.exists_basis_toMatrix_eq_J_inl_eq
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {U : Submodule K V} (e : Basis ι K U)
    (hU : U = B.orthogonal U) :
    ∃ b : Basis (ι ⊕ ι) K V,
      toMatrix b B = Matrix.J ι K ∧ ∀ i, b (Sum.inl i) = (e i : V) := by
  have hdim := finrank_add_finrank_orthogonal hB.isRefl U
  rw [orthogonal_top_eq_bot hnd, inf_bot_eq, finrank_bot, add_zero, ← hU,
    finrank_eq_card_basis e] at hdim
  exact hB.exists_basis_toMatrix_eq_J_inl_eq_of_finrank hnd e hU.le hdim

end Field

end LinearMap.BilinForm
