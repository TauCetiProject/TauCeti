/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Ordered products of normalizing subgroups

If each subgroup in a finite list normalizes the join of the subsequent subgroups, their join
is their ordered set product. Thus every element has one factor from each subgroup, in the
specified order. This is the group-theoretic collection argument for height-ordered root groups;
it does not assert uniqueness of the factors.
-/

public section

namespace Subgroup

variable {ι G : Type*} [Group G]

/-- If each subgroup normalizes the join of those after it, every element of the join has an
ordered factorization. The list has no repetitions so the factors may be indexed by `ι`. -/
theorem mem_iSup_list_iff_exists_prod (H : ι → Subgroup G) (l : List ι) (hl : l.Nodup)
    (hn : ∀ p i s, l = p ++ i :: s → H i ≤ normalizer (⨆ j ∈ s, H j : Subgroup G)) (g : G) :
    g ∈ (⨆ i ∈ l, H i) ↔
      ∃ f : ι → G, (∀ i ∈ l, f i ∈ H i) ∧ (l.map f).prod = g := by
  classical
  induction l generalizing g with
  | nil => simp [eq_comm]
  | cons i l ih =>
      have hjoin : (⨆ j ∈ i :: l, H j) = H i ⊔ ⨆ j ∈ l, H j := by
        simp only [List.mem_cons, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
      constructor
      · intro hg
        rw [hjoin, ← SetLike.mem_coe,
          coe_mul_of_left_le_normalizer_right _ _ (hn [] i l rfl)] at hg
        obtain ⟨a, ha, b, hb, rfl⟩ := hg
        obtain ⟨f, hf, hprod⟩ := (ih hl.of_cons (fun p j s hs =>
          hn (i :: p) j s (by simp [hs])) b).mp hb
        refine ⟨Function.update f i a, ?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · simpa using ha
          · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj (List.nodup_cons.mp hl).1)]
            exact hf j hj
        · rw [List.map_cons, List.prod_cons, Function.update_self]
          have heq : l.map (Function.update f i a) = l.map f := by
            apply List.map_congr_left
            intro j hj
            exact Function.update_of_ne (ne_of_mem_of_not_mem hj (List.nodup_cons.mp hl).1) _ _
          rw [heq, hprod]
      · rintro ⟨f, hf, rfl⟩
        exact Subgroup.list_prod_mem _ fun x hx => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
          exact (show H j ≤ ⨆ k ∈ i :: l, H k from
            le_iSup_of_le j (le_iSup_of_le hj le_rfl)) (hf j hj)

end Subgroup
