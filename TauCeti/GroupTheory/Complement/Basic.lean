/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
import TauCeti.Algebra.Group.Subgroup.Normalizer

/-!
# Coset evaluation and product laws for complement decompositions

Mathlib packages the unique product decomposition of a complement `Subgroup.IsComplement` as
`Subgroup.IsComplement.equiv` and relates complements to coset spaces via
`Subgroup.IsComplement.leftQuotientEquiv` and, for subgroup complements `Subgroup.IsComplement'`,
the quotient isomorphism `Subgroup.IsComplement'.QuotientMulEquiv`.

This file evaluates those quotient maps on explicit cosets in terms of `Subgroup.IsComplement.equiv`
and deduces the multiplicative and conjugation-twisted product laws for the two components of
`Subgroup.IsComplement.equiv` when the left factor is normal.

## Main results

* `Subgroup.IsComplement'.normal_left_of_le_normalizer`: a subgroup complemented by a subgroup
  normalizing it is normal in the ambient group.
* `Subgroup.IsComplement.leftQuotientEquiv_mk`: `leftQuotientEquiv` sends the coset of `g` to the
  left component of `g` in `Subgroup.IsComplement.equiv`.
* `Subgroup.IsComplement'.quotientMulEquiv_mk`,
  `Subgroup.IsComplement'.symm_quotientMulEquiv_mk`: `Subgroup.IsComplement'.QuotientMulEquiv`
  evaluates on a coset to the corresponding complement component of `Subgroup.IsComplement.equiv`.
* `Subgroup.IsComplement'.equiv_snd_mul`, `Subgroup.IsComplement'.equiv_fst_mul`: when `N` is
  normal and `N.IsComplement' K`, the `K`-component of `Subgroup.IsComplement.equiv` is
  multiplicative and the `N`-component satisfies the conjugation-twisted product law.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {N K H : Subgroup G}

/-- A subgroup complemented by a subgroup normalizing it is normal in the ambient group. -/
theorem IsComplement'.normal_left_of_le_normalizer (h : N.IsComplement' K)
    (hLE : K ≤ normalizer (N : Set G)) : N.Normal :=
  normal_of_le_normalizer_of_sup_eq_top hLE h.sup_eq_top

/-- Evaluating `Subgroup.IsComplement.leftQuotientEquiv` at the coset of `g` returns the left
component of `g` in the complement decomposition. -/
@[simp]
theorem IsComplement.leftQuotientEquiv_mk {S : Set G} (h : IsComplement S K) (g : G) :
    h.leftQuotientEquiv (g : G ⧸ K) = (h.equiv g).1 := by
  apply (isComplement_subgroup_right_iff_bijective.mp h).1
  rw [Set.domRestrict_apply, Set.domRestrict_apply]
  refine (h.quotientGroupMk_leftQuotientEquiv (g : G ⧸ K)).trans ?_
  rw [eq_comm, QuotientGroup.eq, ← h.equiv_snd_eq_inv_mul g]
  exact (h.equiv g).2.property

/-- For a complement `H` of a normal subgroup `K`, the isomorphism `G ⧸ K ≃* H` sends the coset
of `g` to the `H`-component of `g`. -/
theorem IsComplement'.quotientMulEquiv_mk [K.Normal] (h : H.IsComplement' K) (g : G) :
    h.QuotientMulEquiv (g : G ⧸ K) = (h.equiv g).1 := by
  apply Subtype.ext
  rw [IsComplement'.QuotientMulEquiv_apply, h.leftQuotientEquiv_mk]

/-- For a complement `K` of a normal subgroup `N`, the isomorphism `G ⧸ N ≃* K` sends the coset
of `g` to the `K`-component of `g`. -/
theorem IsComplement'.symm_quotientMulEquiv_mk [N.Normal] (h : N.IsComplement' K) (g : G) :
    h.symm.QuotientMulEquiv (g : G ⧸ N) = (h.equiv g).2 := by
  have hg : (g : G ⧸ N) = (((h.equiv g).2 : G) : G ⧸ N) := by
    conv_lhs => rw [← h.equiv_fst_mul_equiv_snd g]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (h.equiv g).1.property, one_mul]
  rw [hg, h.symm.quotientMulEquiv_mk,
    h.symm.equiv_fst_eq_self_of_mem_of_one_mem N.one_mem (h.equiv g).2.property]

/-- When `N` is normal and `N.IsComplement' K`, the `K`-component of `g` in the reverse
decomposition `K × N ≃ G` agrees with its `K`-component in `N × K ≃ G`. -/
theorem IsComplement'.symm_equiv_fst [N.Normal] (h : N.IsComplement' K) (g : G) :
    (h.symm.equiv g).1 = (h.equiv g).2 :=
  (h.symm.quotientMulEquiv_mk g).symm.trans (h.symm_quotientMulEquiv_mk g)

/-- When `N` is normal, the projection to a complementary subgroup `K` in
`Subgroup.IsComplement.equiv` is multiplicative. -/
theorem IsComplement'.equiv_snd_mul [N.Normal] (h : N.IsComplement' K) (g₁ g₂ : G) :
    (h.equiv (g₁ * g₂)).2 = (h.equiv g₁).2 * (h.equiv g₂).2 := by
  rw [← h.symm_quotientMulEquiv_mk, QuotientGroup.mk_mul, map_mul,
    h.symm_quotientMulEquiv_mk, h.symm_quotientMulEquiv_mk]

/-- When `N` is normal, the `N`-component of a product in `Subgroup.IsComplement.equiv` twists
the second factor by conjugation by the `K`-component of the first. -/
theorem IsComplement'.equiv_fst_mul [N.Normal] (h : N.IsComplement' K) (g₁ g₂ : G) :
    (h.equiv (g₁ * g₂)).1 =
      (h.equiv g₁).1 * MulAut.conjNormal ((h.equiv g₁).2 : G) (h.equiv g₂).1 := by
  have hmul : h.equiv.symm ((h.equiv g₁).1 * MulAut.conjNormal ((h.equiv g₁).2 : G) (h.equiv g₂).1,
      (h.equiv g₁).2 * (h.equiv g₂).2) = g₁ * g₂ := by
    calc
      (h.equiv.symm ((h.equiv g₁).1 * MulAut.conjNormal ((h.equiv g₁).2 : G) (h.equiv g₂).1,
          (h.equiv g₁).2 * (h.equiv g₂).2) : G)
        = ((h.equiv g₁).1 : G) * (h.equiv g₁).2 * (((h.equiv g₂).1 : G) * (h.equiv g₂).2) := by
          rw [IsComplement.equiv_symm_apply]
          simp [mul_assoc]
      _ = g₁ * g₂ := by
          rw [h.equiv_fst_mul_equiv_snd, h.equiv_fst_mul_equiv_snd]
  exact (congrArg Prod.fst ((h.equiv.apply_symm_apply _).symm.trans (congrArg h.equiv hmul))).symm

end Subgroup
