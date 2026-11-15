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
    h.leftQuotientEquiv (g : G ⧸ K) = (h.equiv g).1 := by
  have hleft : (h.leftQuotientEquiv (g : G ⧸ K) : G)⁻¹ * g ∈ K :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact' (h.quotientGroupMk_leftQuotientEquiv (g : G ⧸ K)))
  have hequiv : ((h.equiv g).1 : G)⁻¹ * g ∈ K :=
    h.equiv_snd_eq_inv_mul g ▸ (h.equiv g).2.property
  exact (isComplement_iff_existsUnique_inv_mul_mem.mp h g).unique hleft hequiv

/-- Evaluating `IsComplement'.QuotientMulEquiv` on a coset extracts the left component of the
complement decomposition. -/
theorem IsComplement'.quotientMulEquiv_mk [K.Normal] (h : H.IsComplement' K) (g : G) :
    h.QuotientMulEquiv (g : G ⧸ K) = (h.equiv g).1 := by
  rw [IsComplement'.QuotientMulEquiv_apply, h.leftQuotientEquiv_mk]

/-- When the left subgroup is normal, the quotient isomorphism to the complement extracts the
right component of the complement decomposition. -/
theorem IsComplement'.symm_quotientMulEquiv_mk [N.Normal] (h : N.IsComplement' K) (g : G) :
    h.symm.QuotientMulEquiv (g : G ⧸ N) = (h.equiv g).2 := by
  apply h.symm.QuotientMulEquiv.symm.injective
  have hsymm : h.symm.QuotientMulEquiv.symm (h.equiv g).2 = (((h.equiv g).2 : G) : G ⧸ N) :=
    h.symm.QuotientMulEquiv_symm_apply (h.equiv g).2
  rw [MulEquiv.symm_apply_apply, hsymm]
  conv_lhs => rw [← h.equiv_fst_mul_equiv_snd g]
  rw [← QuotientGroup.mk'_apply, map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff _).mpr (h.equiv g).1.property, one_mul]

end Subgroup
