/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.GroupTheory.Perm.Subgroup
import TauCeti.LinearAlgebra.Matrix.Determinant.SumElim

/-!
# Plücker relations among minors

Let `A` be an `m × n` matrix over a commutative ring and fix a family of columns `c : t → n`. For
a family of rows `r : t → m`, write `[r]` for the minor `det (A.submatrix r c)`. The rows of `r`
need not be distinct or sorted: `[r]` vanishes when two of them coincide and changes sign under a
permutation of `t`. The products `[r] * [s]` of two such minors satisfy quadratic relations, the
Plücker relations, which come from the fact that an alternating form in more vectors than the
dimension of the space vanishes.

The general form is the shuffle relation (the van der Waerden syzygy). Split the positions of `t`
for each of two minors into a fixed part and a moving part, `e₁ : t ≃ ι₁ ⊕ κ₁` and
`e₂ : t ≃ ι₂ ⊕ κ₂`, put fixed rows `α` and `β` on the fixed parts, and distribute a family `γ` of
`#κ₁ + #κ₂` moving rows over the two moving parts by a permutation `σ` of `κ₁ ⊕ κ₂`. When there
are more moving rows than the size `#t` of the minors, the signed sum of the products of the two
minors over `σ` vanishes. Permutations that differ by a permutation of `κ₁` and one of `κ₂` give
the same term, so the sum runs over a left transversal of the subgroup `Perm κ₁ × Perm κ₂` of
`Perm (κ₁ ⊕ κ₂)`, for instance over the shuffles.

Moving a single row gives the exchange relation: for row families `r` and `s` and a position `i`,
`[r] * [s] = ∑ j, [r with s j at i] * [s with r i at j]`.

These identities hold over every commutative ring. They are the quadratic relations used to
straighten products of maximal minors into standard monomials.

## Main results

* `Matrix.sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero`: the shuffle relation among
  minors of a matrix, summed over a left transversal of `Perm κ₁ × Perm κ₂`.
* `Matrix.det_submatrix_mul_det_submatrix_eq_sum`: the exchange relation.

## Implementation notes

The shuffle relation is Mathlib's exterior product `AlternatingMap.domCoprod`, whose summands are
indexed by the cosets of `Perm κ₁ × Perm κ₂`, applied to the two determinants with their fixed
rows inserted (`Matrix.detRowAlternatingSumElim`): it is an alternating map in more vectors than
the rank of the free module, hence zero.

## References

* B. Sturmfels, *Algorithms in Invariant Theory*, Springer, 1993, §3.1 (van der Waerden
  syzygies and the straightening algorithm).
* E. Miller, B. Sturmfels, *Combinatorial Commutative Algebra*, Graduate Texts in Mathematics
  227, Springer, 2005, Chapter 14 (Plücker relations).
-/

public section

open Equiv

namespace Matrix

variable {R : Type*} [CommRing R] {m n t : Type*} [Fintype t] [DecidableEq t]

section AlternatingSumElim

variable {ι κ : Type*}

/-- Inserting rows of `A.submatrix id c` along `e` gives a minor of `A` on the columns `c`. -/
private theorem det_of_sumElim_submatrix (e : t ≃ ι ⊕ κ) (A : Matrix m n R) (c : t → n)
    (α : ι → m) (γ : κ → m) :
    (of fun k => Sum.elim (fun i => A.submatrix id c (α i)) (fun j => A.submatrix id c (γ j))
      (e k)).det = (A.submatrix (Sum.elim α γ ∘ e) c).det := by
  congr 1
  ext k l
  cases h : e k <;> simp [h]

end AlternatingSumElim

section Shuffle

variable {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂]

/-- **The shuffle relation** (van der Waerden syzygy) among minors on the columns `c`. The first
minor has fixed rows `α` and the second fixed rows `β`, inserted along `e₁` and `e₂`; the moving
rows `γ` are distributed over their remaining positions by `σ`. If there are more moving rows
than the size of the minors, the signed sum of the products over a left transversal `T` of
`Perm κ₁ × Perm κ₂` in `Perm (κ₁ ⊕ κ₂)` vanishes. -/
theorem sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero (A : Matrix m n R) (c : t → n)
    (e₁ : t ≃ ι₁ ⊕ κ₁) (e₂ : t ≃ ι₂ ⊕ κ₂) (α : ι₁ → m) (β : ι₂ → m) (γ : κ₁ ⊕ κ₂ → m)
    (hcard : Fintype.card t < Fintype.card κ₁ + Fintype.card κ₂)
    {T : Finset (Perm (κ₁ ⊕ κ₂))}
    (hT : Subgroup.IsComplement (T : Set (Perm (κ₁ ⊕ κ₂))) (Perm.sumCongrHom κ₁ κ₂).range) :
    ∑ σ ∈ T, Perm.sign σ •
      ((A.submatrix (Sum.elim α (γ ∘ σ ∘ Sum.inl) ∘ e₁) c).det *
        (A.submatrix (Sum.elim β (γ ∘ σ ∘ Sum.inr) ∘ e₂) c).det) = 0 := by
  classical
  let B := A.submatrix id c
  let a := detRowAlternatingSumElim e₁ fun i => B (α i)
  let b := detRowAlternatingSumElim e₂ fun i => B (β i)
  have hzero : a.domCoprod b = 0 := by
    refine (Pi.basisFun R t).ext_alternating fun v hv => ?_
    have := Fintype.card_le_of_injective v hv
    simp only [Fintype.card_sum] at this
    omega
  have key : ∑ q, LinearMap.mul' R R (AlternatingMap.domCoprod.summand a b q fun k => B (γ k)) =
      0 := by
    rw [← map_sum, ← sum_apply, ← AlternatingMap.domCoprod_coe,
      AlternatingMap.coe_multilinearMap, hzero, zero_apply, map_zero]
  rw [← key, ← Finset.sum_coe_sort T]
  refine (Fintype.sum_equiv (hT.leftQuotientEquiv.trans
    (Equiv.subtypeEquivRight fun _ => Finset.mem_coe)) _ _ fun q => ?_).symm
  conv_lhs => rw [← hT.quotientGroupMk_leftQuotientEquiv q]
  rw [AlternatingMap.domCoprod.summand_mk'']
  simp only [smul_apply, MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    AlternatingMap.coe_multilinearMap, Equiv.trans_apply, subtypeEquivRight_apply_coe, a, b]
  rw [Units.smul_def, Units.smul_def, map_zsmul, LinearMap.mul'_apply,
    detRowAlternatingSumElim_apply, detRowAlternatingSumElim_apply, det_of_sumElim_submatrix,
    det_of_sumElim_submatrix]
  simp only [Function.comp_def]

/-- **The exchange relation** among minors on the columns `c`: the product of the minors on the
rows `r` and `s` is the sum, over the positions `j`, of the products obtained by exchanging the row
of `r` at `i` with the row of `s` at `j`. -/
theorem det_submatrix_mul_det_submatrix_eq_sum (A : Matrix m n R) (r s : t → m) (c : t → n)
    (i : t) :
    (A.submatrix r c).det * (A.submatrix s c).det =
      ∑ j, (A.submatrix (Function.update r i (s j)) c).det *
        (A.submatrix (Function.update s j (r i)) c).det := by
  classical
  -- The row `r i` moves from the first minor, and all rows of `s` from the second.
  let e₁ : t ≃ {k // k ≠ i} ⊕ Unit := (optionSubtypeNe i).symm.trans (optionEquivSumPUnit.{0} _)
  let γ : Unit ⊕ t → m := Sum.elim (fun _ => r i) s
  have h := sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero A c e₁ (emptySum Empty t).symm
    (fun k => r k) Empty.elim γ (by simp) (Perm.isComplement_image_swap_inl_sumCongrHom_range t)
  have h₁ (σ : Perm (Unit ⊕ t)) : Sum.elim (fun k : {k // k ≠ i} => r k) (γ ∘ σ ∘ Sum.inl) ∘ e₁ =
      Function.update r i (γ (σ (.inl ()))) := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp [e₁]
    · simp [e₁, hk, optionSubtypeNe_symm_of_ne hk]
  have h₂ (f : t → m) : Sum.elim Empty.elim f ∘ (emptySum Empty t).symm = f := by
    ext k
    simp [emptySum]
  have h₃ (j : t) : γ ∘ swap (.inl ()) (.inr j) ∘ Sum.inr = Function.update s j (r i) := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp [γ]
    · simp [γ, hk, swap_apply_of_ne_of_ne]
  rw [Finset.sum_image fun x _ y _ hxy => by simpa using congr($hxy (.inl ())),
    Fintype.sum_sum_type] at h
  simp only [h₁, h₂, h₃, Fintype.univ_unit, Finset.sum_singleton, swap_self, Perm.sign_refl,
    one_smul, Perm.sign_swap Sum.inl_ne_inr, Units.neg_smul, Finset.sum_neg_distrib] at h
  simp only [coe_refl, id_eq, CompTriple.comp_eq, swap_apply_left, γ, Sum.elim_inl, Sum.elim_inr,
    Function.update_eq_self, Sum.elim_comp_inr] at h
  rwa [← sub_eq_add_neg, sub_eq_zero] at h

end Shuffle

end Matrix
