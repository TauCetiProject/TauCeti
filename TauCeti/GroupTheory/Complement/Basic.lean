/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement

/-!
# Coset evaluation for subgroup complements

For a left transversal `S` of a subgroup `K`, `Subgroup.IsComplement.leftQuotientEquiv` sends the
left coset `(g : G ⧸ K)` to the first component of `Subgroup.IsComplement.equiv g`. Specializing to
subgroup complements with a normal factor identifies `Subgroup.IsComplement'.QuotientMulEquiv` on
cosets with the left or right component of the product decomposition.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {N H K : Subgroup G}

/-- Evaluating `IsComplement.leftQuotientEquiv` on a left coset extracts the first component of the
complement decomposition. -/
theorem IsComplement.leftQuotientEquiv_mk {S : Set G} (h : IsComplement S K) (g : G) :
    h.leftQuotientEquiv (g : G ⧸ K) = (h.equiv g).1 :=
  (isComplement_iff_existsUnique_inv_mul_mem.mp h g).unique
    (by
      simpa only [SetLike.mem_coe, IsComplement.toLeftFun, Function.comp_apply] using
        h.inv_toLeftFun_mul_mem g)
    (h.equiv_snd_eq_inv_mul g ▸ (h.equiv g).2.property)

/-- Evaluating `IsComplement'.QuotientMulEquiv` on a coset extracts the left component of the
complement decomposition. -/
theorem IsComplement'.quotientMulEquiv_mk [K.Normal] (h : H.IsComplement' K) (g : G) :
    h.QuotientMulEquiv (g : G ⧸ K) = (h.equiv g).1 := by
  rw [IsComplement'.QuotientMulEquiv_apply, h.leftQuotientEquiv_mk]

/-- When the left subgroup is normal, the quotient isomorphism to the complement extracts the
right component of the complement decomposition. -/
theorem IsComplement'.symm_quotientMulEquiv_mk [N.Normal] (h : N.IsComplement' K) (g : G) :
    h.symm.QuotientMulEquiv (g : G ⧸ N) = (h.equiv g).2 := by
  have hq : (g : G ⧸ N) = (((h.equiv g).2 : G) : G ⧸ N) := by
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv, ← h.equiv_fst_eq_mul_inv]
    exact (h.equiv g).1.property
  rw [hq, h.symm.quotientMulEquiv_mk]
  exact h.symm.equiv_fst_eq_self_of_mem_of_one_mem N.one_mem (h.equiv g).2.property

end Subgroup
