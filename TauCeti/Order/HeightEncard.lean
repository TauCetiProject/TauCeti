/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Order.Height
public import Mathlib.Order.KrullDimension

/-!
# Order height and cardinality of lower intervals

In a preorder, element height is the strict chain height of the lower interval.
In a linear order this equals the extended cardinality of that interval. The dual
statements describe coheight and upper intervals.
-/

public section

namespace Order

variable {α : Type*}

/-- In a preorder, the height of an element `a` is the supremum of the cardinalities of the sets
of elements less than `a` that are chains for `<`. -/
theorem height_eq_chainHeight_Iio [Preorder α] (a : α) :
    height a = (Set.Iio a).chainHeight (· < ·) := by
  refine le_antisymm (height_le fun p hp ↦ ?_) (ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_)
  · have hf : StrictMono fun i ↦ p (Fin.castSucc i) := p.strictMono.comp Fin.strictMono_castSucc
    simpa [hf.injective.encard_range] using Set.encard_le_chainHeight_of_isChain (Set.Iio a) _
      (Set.range_subset_iff.mpr fun i ↦ (p.strictMono (Fin.castSucc_lt_last i)).trans_eq hp)
      (Set.image_univ ▸ (isChain_of_trichotomous _).image_of_map_rel _ _ _ fun _ _ ↦ (hf ·))
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, hta, htn, htc⟩ := Set.exists_isChain_of_le_chainHeight _ hn
    obtain ⟨m, hm⟩ := (Set.finite_of_encard_eq_coe htn).exists_maximal
      (Set.nonempty_of_encard_ne_zero (by simp [htn]))
    grw [Nat.cast_add_one, ih m ?_, height_add_one_le (hta hm.1)]
    simpa [Set.encard_sdiff_singleton_of_mem hm.1, htn] using
      Set.encard_le_chainHeight_of_isChain (Set.Iio m) (t \ {m})
        (fun _ hx ↦ (htc hx.1 hm.1 hx.2).resolve_right (hm.not_gt hx.1)) htc.diff

/-- In a preorder, the coheight of an element `a` is the supremum of the cardinalities of the sets
of elements greater than `a` that are chains for `<`. -/
theorem coheight_eq_chainHeight_Ioi [Preorder α] (a : α) :
    coheight a = (Set.Ioi a).chainHeight (· < ·) :=
  (height_eq_chainHeight_Iio (α := αᵒᵈ) a).trans (Set.chainHeight_flip _ _)

theorem height_le_encard_Iio [Preorder α] (a : α) : height a ≤ (Set.Iio a).encard :=
  (height_eq_chainHeight_Iio a).trans_le (Set.chainHeight_le_encard _ _)

theorem coheight_le_encard_Ioi [Preorder α] (a : α) : coheight a ≤ (Set.Ioi a).encard :=
  height_le_encard_Iio (α := αᵒᵈ) a

/-- In a linear order, the height of an element `a` is the cardinality of the set of elements
less than `a`. -/
theorem height_eq_encard_Iio [LinearOrder α] (a : α) : height a = (Set.Iio a).encard :=
  (height_eq_chainHeight_Iio a).trans
    (Set.encard_eq_chainHeight_of_isChain _ (isChain_of_trichotomous _)).symm

/-- In a linear order, the coheight of an element `a` is the cardinality of the set of elements
greater than `a`. -/
theorem coheight_eq_encard_Ioi [LinearOrder α] (a : α) : coheight a = (Set.Ioi a).encard :=
  height_eq_encard_Iio (α := αᵒᵈ) a

end Order
