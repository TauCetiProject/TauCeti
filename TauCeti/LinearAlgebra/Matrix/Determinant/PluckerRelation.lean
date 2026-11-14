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
import TauCeti.LinearAlgebra.Alternating.Curry

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
`Perm (κ₁ ⊕ κ₂)`, for instance over the shuffles
(`Equiv.Perm.isComplement_setOf_strictMono_sumCongrHom_range`).

More generally, the two minors may have different sizes and be taken on columns `c ∘ j₁` and
`c ∘ j₂`, for `j₁ : t₁ → t` and `j₂ : t₂ → t`, factoring through a common family `c : t → n`, for
instance on nested columns as for flag minors; the relation then holds when there are more moving
rows than `#t`.

Moving a single row gives the exchange relation: for row families `r` and `s` and a position `i`,
`[r] * [s] = ∑ j, [r with s j at i] * [s with r i at j]`. It also holds when `[r]` is a minor on
columns `c ∘ j` and `[s]` one on columns `c`.

These identities hold over every commutative ring. They are the quadratic relations used to
straighten products of maximal minors into standard monomials.

## Main results

* `Matrix.sum_sign_smul_det_submatrix_comp_mul_det_submatrix_comp_eq_zero`: the shuffle relation
  among minors on columns `c ∘ j₁` and `c ∘ j₂`, summed over a left transversal of
  `Perm κ₁ × Perm κ₂`.
* `Matrix.sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero`: the shuffle relation among
  minors on the same columns.
* `Matrix.det_submatrix_comp_mul_det_submatrix_eq_sum`,
  `Matrix.det_submatrix_mul_det_submatrix_eq_sum`: the exchange relation, for minors on nested
  and on the same columns.

## Implementation notes

The shuffle relation is Mathlib's exterior product `AlternatingMap.domCoprod`, whose summands are
indexed by the cosets of `Perm κ₁ × Perm κ₂`, applied to the two determinants with their fixed
rows inserted (`AlternatingMap.currySum`), both viewed as alternating maps of rows in `t → R`: it
is an alternating map in more vectors than the rank of the free module `t → R`, hence zero.

## References

* B. Sturmfels, *Algorithms in Invariant Theory*, Springer, 1993, §3.1 (van der Waerden
  syzygies and the straightening algorithm).
* E. Miller, B. Sturmfels, *Combinatorial Commutative Algebra*, Graduate Texts in Mathematics
  227, Springer, 2005, Chapter 14 (Plücker relations).
-/

public section

open Equiv

namespace Matrix

variable {R : Type*} [CommRing R] {m n t t₁ t₂ : Type*} [Fintype t₁] [DecidableEq t₁] [Fintype t₂]
  [DecidableEq t₂]

/-- Restricting rows of `A.submatrix id c` along `j` and inserting them along `e` gives a minor of
`A` on the columns `c ∘ j`. -/
private theorem currySum_domDomCongr_compLinearMap_funLeft_detRowAlternating {ι κ : Type*}
    (e : t₁ ≃ ι ⊕ κ) (A : Matrix m n R) (c : t → n) (j : t₁ → t) (α : ι → m) (γ : κ → m) :
    (((detRowAlternating : (t₁ → R) [⋀^t₁]→ₗ[R] R).compLinearMap
      (LinearMap.funLeft R R j)).domDomCongr e).currySum (fun i => A.submatrix id c (α i))
      (fun l => A.submatrix id c (γ l)) = (A.submatrix (Sum.elim α γ ∘ e) (c ∘ j)).det := by
  rw [AlternatingMap.currySum_apply, AlternatingMap.domDomCongr_apply,
    AlternatingMap.compLinearMap_apply, det]
  congr 1
  ext k l
  cases h : e k <;> simp [h]

section Shuffle

variable [Fintype t] {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁]
  [DecidableEq κ₂]

/-- **The shuffle relation** (van der Waerden syzygy) among minors on the columns `c ∘ j₁` and
`c ∘ j₂`. The first minor has fixed rows `α` and the second fixed rows `β`, inserted along `e₁` and
`e₂`; the moving rows `γ` are distributed over their remaining positions by `σ`. If there are more
moving rows than `#t`, the signed sum of the products over a left transversal `T` of
`Perm κ₁ × Perm κ₂` in `Perm (κ₁ ⊕ κ₂)`, such as the shuffles
(`Equiv.Perm.isComplement_setOf_strictMono_sumCongrHom_range`), vanishes. -/
theorem sum_sign_smul_det_submatrix_comp_mul_det_submatrix_comp_eq_zero (A : Matrix m n R)
    (c : t → n) (j₁ : t₁ → t) (j₂ : t₂ → t) (e₁ : t₁ ≃ ι₁ ⊕ κ₁) (e₂ : t₂ ≃ ι₂ ⊕ κ₂) (α : ι₁ → m)
    (β : ι₂ → m) (γ : κ₁ ⊕ κ₂ → m) (hcard : Fintype.card t < Fintype.card κ₁ + Fintype.card κ₂)
    {T : Finset (Perm (κ₁ ⊕ κ₂))}
    (hT : Subgroup.IsComplement (T : Set (Perm (κ₁ ⊕ κ₂))) (Perm.sumCongrHom κ₁ κ₂).range) :
    ∑ σ ∈ T, Perm.sign σ •
      ((A.submatrix (Sum.elim α (γ ∘ σ ∘ Sum.inl) ∘ e₁) (c ∘ j₁)).det *
        (A.submatrix (Sum.elim β (γ ∘ σ ∘ Sum.inr) ∘ e₂) (c ∘ j₂)).det) = 0 := by
  classical
  -- Both minors are alternating maps of their moving rows, viewed as rows of `A.submatrix id c`.
  let B := A.submatrix id c
  let a := (((detRowAlternating : (t₁ → R) [⋀^t₁]→ₗ[R] R).compLinearMap
    (LinearMap.funLeft R R j₁)).domDomCongr e₁).currySum fun i => B (α i)
  let b := (((detRowAlternating : (t₂ → R) [⋀^t₂]→ₗ[R] R).compLinearMap
    (LinearMap.funLeft R R j₂)).domDomCongr e₂).currySum fun i => B (β i)
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
    currySum_domDomCongr_compLinearMap_funLeft_detRowAlternating,
    currySum_domDomCongr_compLinearMap_funLeft_detRowAlternating]
  simp only [Function.comp_def]

/-- **The shuffle relation** (van der Waerden syzygy) among minors on the columns `c`. The first
minor has fixed rows `α` and the second fixed rows `β`, inserted along `e₁` and `e₂`; the moving
rows `γ` are distributed over their remaining positions by `σ`. If there are more moving rows
than the size of the minors, the signed sum of the products over a left transversal `T` of
`Perm κ₁ × Perm κ₂` in `Perm (κ₁ ⊕ κ₂)` vanishes. -/
theorem sum_sign_smul_det_submatrix_mul_det_submatrix_eq_zero [DecidableEq t] (A : Matrix m n R)
    (c : t → n)
    (e₁ : t ≃ ι₁ ⊕ κ₁) (e₂ : t ≃ ι₂ ⊕ κ₂) (α : ι₁ → m) (β : ι₂ → m) (γ : κ₁ ⊕ κ₂ → m)
    (hcard : Fintype.card t < Fintype.card κ₁ + Fintype.card κ₂)
    {T : Finset (Perm (κ₁ ⊕ κ₂))}
    (hT : Subgroup.IsComplement (T : Set (Perm (κ₁ ⊕ κ₂))) (Perm.sumCongrHom κ₁ κ₂).range) :
    ∑ σ ∈ T, Perm.sign σ •
      ((A.submatrix (Sum.elim α (γ ∘ σ ∘ Sum.inl) ∘ e₁) c).det *
        (A.submatrix (Sum.elim β (γ ∘ σ ∘ Sum.inr) ∘ e₂) c).det) = 0 :=
  sum_sign_smul_det_submatrix_comp_mul_det_submatrix_comp_eq_zero A c id id e₁ e₂ α β γ hcard hT

/-- **The exchange relation** between a minor on the columns `c ∘ j` and one on the columns `c`:
the product of the minors on the rows `r` and `s` is the sum, over the positions `k`, of the
products obtained by exchanging the row of `r` at `i` with the row of `s` at `k`. -/
theorem det_submatrix_comp_mul_det_submatrix_eq_sum [DecidableEq t] (A : Matrix m n R)
    (r : t₁ → m) (s : t → m) (c : t → n) (j : t₁ → t) (i : t₁) :
    (A.submatrix r (c ∘ j)).det * (A.submatrix s c).det =
      ∑ k, (A.submatrix (Function.update r i (s k)) (c ∘ j)).det *
        (A.submatrix (Function.update s k (r i)) c).det := by
  classical
  -- The row `r i` moves from the first minor, and all rows of `s` from the second.
  let e₁ : t₁ ≃ {l // l ≠ i} ⊕ Unit := (optionSubtypeNe i).symm.trans (optionEquivSumPUnit.{0} _)
  let γ : Unit ⊕ t → m := Sum.elim (fun _ => r i) s
  have h := sum_sign_smul_det_submatrix_comp_mul_det_submatrix_comp_eq_zero A c j id e₁
    (emptySum Empty t).symm (fun l => r l) Empty.elim γ (by simp)
    (T := Finset.univ.image fun x : Unit ⊕ t => swap (.inl ()) x)
    (by simpa using Perm.isComplement_range_swap_inl_sumCongrHom_range Unit t)
  have h₁ (σ : Perm (Unit ⊕ t)) : Sum.elim (fun l : {l // l ≠ i} => r l) (γ ∘ σ ∘ Sum.inl) ∘ e₁ =
      Function.update r i (γ (σ (.inl ()))) := by
    ext l
    by_cases hl : l = i
    · subst hl
      simp [e₁]
    · simp [e₁, hl, optionSubtypeNe_symm_of_ne hl]
  have h₂ (f : t → m) : Sum.elim Empty.elim f ∘ (emptySum Empty t).symm = f := by
    ext l
    simp [emptySum]
  have h₃ (k : t) : γ ∘ swap (.inl ()) (.inr k) ∘ Sum.inr = Function.update s k (r i) := by
    ext l
    by_cases hl : l = k
    · subst hl
      simp [γ]
    · simp [γ, hl, swap_apply_of_ne_of_ne]
  rw [Finset.sum_image fun x _ y _ hxy => by simpa using congr($hxy (.inl ())),
    Fintype.sum_sum_type] at h
  simp only [h₁, h₂, h₃, Fintype.univ_unit, Finset.sum_singleton, swap_self, Perm.sign_refl,
    one_smul, Perm.sign_swap Sum.inl_ne_inr, Units.neg_smul, Finset.sum_neg_distrib] at h
  simp only [coe_refl, id_eq, CompTriple.comp_eq, swap_apply_left, γ, Sum.elim_inl, Sum.elim_inr,
    Function.update_eq_self, Sum.elim_comp_inr] at h
  rwa [← sub_eq_add_neg, sub_eq_zero] at h

/-- **The exchange relation** among minors on the columns `c`: the product of the minors on the
rows `r` and `s` is the sum, over the positions `k`, of the products obtained by exchanging the row
of `r` at `i` with the row of `s` at `k`. -/
theorem det_submatrix_mul_det_submatrix_eq_sum [DecidableEq t] (A : Matrix m n R) (r s : t → m)
    (c : t → n) (i : t) :
    (A.submatrix r c).det * (A.submatrix s c).det =
      ∑ k, (A.submatrix (Function.update r i (s k)) c).det *
        (A.submatrix (Function.update s k (r i)) c).det :=
  det_submatrix_comp_mul_det_submatrix_eq_sum A r s c id i

end Shuffle

end Matrix
