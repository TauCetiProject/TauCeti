/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.OrderClass

/-!
# Examples: coded linear orders and coded trees

The code of `(ℕ, ≤)` is a coded linear order and a coded tree (one infinite branch). The code of
`(ℕ, <)` is not a coded linear order, as it is irreflexive, and the code of `(ℕ, ≥)` is not a
coded tree, as it has no least element. The coded trees on `ℕ` do not form a closed class.

The code in which every pair is related fails antisymmetry, and the code of divisibility on `ℕ` is
a partial order that is not total, so neither is a coded linear order. The code of the star, in
which `0` lies below every element and other pairs are incomparable, is a coded tree, while the
code of `(ℤ, ≤)` transported to `ℕ` is not, having no least element.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- The code of `(ℕ, ≤)` is a coded linear order.
example : @ofStructure Language.order ℕ (orderStructure ℕ) ∈ linearOrderClass :=
  ofStructure_mem_linearOrderClass

-- The code of `(ℕ, ≤)` is a coded tree.
example : @ofStructure Language.order ℕ (orderStructure ℕ) ∈ treeClass :=
  ofStructure_mem_treeClass strictMono_id

-- The code of `(ℕ, <)` is not a coded linear order: it is irreflexive.
example : ofRel (fun x y : ℕ => x < y) ∉ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_ofRel]
  intro h
  exact lt_irrefl 0 (h.refl 0)

-- The code of `(ℕ, ≥)` is not a coded tree: it has no least element.
example : ofRel (fun x y : ℕ => y ≤ x) ∉ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  intro h
  obtain ⟨a, ha⟩ := h.exists_forall
  exact Nat.not_succ_le_self a (ha (a + 1))

-- The coded trees on `ℕ` do not form a closed class.
example : ¬ IsClosed (treeClass (V := ℕ)) :=
  not_isClosed_treeClass

-- The code in which every pair is related is not a coded linear order: it is not antisymmetric.
example : ofRel (fun _ _ : ℕ => True) ∉ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_ofRel]
  intro h
  exact absurd (h.antisymm 0 1 trivial trivial) (by decide)

-- The code of divisibility on `ℕ` is a partial order.
example : IsPartialOrder ℕ (codeRel leSymb (ofRel (fun x y : ℕ => x ∣ y))) := by
  rw [codeRel_ofRel]
  infer_instance

-- The code of divisibility on `ℕ` is not a coded linear order: `2` and `3` are incomparable.
example : ofRel (fun x y : ℕ => x ∣ y) ∉ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_ofRel]
  intro h
  rcases h.total 2 3 with h₂ | h₃
  · exact absurd h₂ (by decide)
  · exact absurd h₃ (by decide)

-- The code of the star, in which `0` lies below every element and other pairs are incomparable,
-- is a coded tree.
example : ofRel (fun x y : ℕ => x = 0 ∨ x = y) ∈ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  have hpo : IsPartialOrder ℕ (fun x y : ℕ => x = 0 ∨ x = y) :=
    { refl := fun _ => .inr rfl
      trans := by rintro a b c (h | h) (h' | h') <;> omega
      antisymm := by rintro a b (h | h) (h' | h') <;> omega }
  refine ⟨hpo, ⟨0, fun _ => .inl rfl⟩, fun x => ?_, fun x => ?_⟩
  · exact ((Set.finite_singleton 0).union (Set.finite_singleton x)).subset fun y hy => by
      simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] using hy
  · rintro a (h | h) b (h' | h') - <;> omega

-- The code of `(ℤ, ≤)` transported to `ℕ` is not a coded tree: it has no least element.
example :
    ofRel (fun x y : ℕ => Equiv.intEquivNat.symm x ≤ Equiv.intEquivNat.symm y) ∉ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  intro h
  obtain ⟨a, ha⟩ := h.exists_forall
  have := ha (Equiv.intEquivNat (Equiv.intEquivNat.symm a - 1))
  simp at this
