/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# A basis of a finite abelian group

By the structure theorem a finite abelian group is a product of cyclic groups. Read through the
generators of the factors, this says that a finite abelian group `G` has a finite family of
elements `σ i` that generates it and whose orders multiply to `|G|`
(`CommGroup.exists_closure_range_eq_top_and_prod_orderOf_eq_card`). The product formula is what
distinguishes such a basis from an arbitrary finite generating family, whose orders multiply to a
multiple of `|G|`; it is the input to determinant arguments over the group ring of `G`, where the
order of each basis element appears as a diagonal entry.
-/

public section

namespace CommGroup

/-- **A finite abelian group has a basis**: a finite generating family whose orders multiply to
the order of the group. -/
theorem exists_closure_range_eq_top_and_prod_orderOf_eq_card (G : Type*) [CommGroup G]
    [Finite G] : ∃ (ι : Type) (_ : Fintype ι) (σ : ι → G),
      Subgroup.closure (Set.range σ) = ⊤ ∧ ∏ i, orderOf (σ i) = Nat.card G := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := equiv_prod_multiplicative_zmod_of_finite G
  have : ∀ i, NeZero (n i) := fun i ↦ ⟨by have := hn i; omega⟩
  let σ : ι → G := fun i ↦ e.symm (Pi.mulSingle i (.ofAdd 1))
  have hσ : ∀ i, orderOf (σ i) = n i := fun i ↦ by
    simpa only [σ, MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using ZMod.addOrderOf_one (n i)
  refine ⟨ι, inferInstance, σ, eq_top_iff.2 fun x _ ↦ ?_, ?_⟩
  · -- Every element is a product of powers of the generators of the cyclic factors.
    have hx : x = ∏ i, σ i ^ (e x i).toAdd.val := by
      apply e.injective
      rw [map_prod e]
      refine ((Finset.prod_congr rfl fun i _ ↦ ?_).trans (Finset.univ_prod_mulSingle (e x))).symm
      rw [map_pow, MulEquiv.apply_symm_apply, ← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one,
        ZMod.natCast_zmod_val, ofAdd_toAdd]
    rw [hx]
    exact Subgroup.prod_mem _ fun i _ ↦ pow_mem (Subgroup.subset_closure (Set.mem_range_self i)) _
  · simp_rw [hσ, Nat.card_congr e.toEquiv, Nat.card_pi, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]

end CommGroup
