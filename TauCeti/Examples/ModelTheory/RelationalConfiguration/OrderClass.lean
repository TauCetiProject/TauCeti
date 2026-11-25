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
