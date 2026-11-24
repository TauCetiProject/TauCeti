/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-! # Subsemiring pullbacks and subring closure joins

For a subsemiring containing the kernel of a ring homomorphism, membership can be
tested in its image, and pulling back that image recovers the original subsemiring.
Joining a subring `S` with `Subring.closure s` agrees on underlying subsemirings with joining
`S.toSubsemiring` and `Subsemiring.closure s` (`Subring.toSubsemiring_sup_closure`).
-/

public section

namespace Subsemiring

variable {A B : Type*} [Ring A] [Ring B]

/-- A subsemiring containing the kernel contains every lift of each image point. -/
theorem mem_map_iff_mem_of_ker_subset {f : A →+* B} {P : Subsemiring A}
    (hker : (RingHom.ker f : Set A) ⊆ P) {x : A} : f x ∈ P.map f ↔ x ∈ P := by
  rw [mem_map]
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have hk : x - y ∈ P := hker (RingHom.mem_ker.mpr (by rw [map_sub, hxy, sub_self]))
  simpa using P.add_mem hy hk

/-- Pulling back the image recovers a subsemiring containing the kernel. -/
@[simp] theorem comap_map_eq_of_ker_subset {f : A →+* B} {P : Subsemiring A}
    (hker : (RingHom.ker f : Set A) ⊆ P) : (P.map f).comap f = P := by
  ext x
  exact mem_map_iff_mem_of_ker_subset hker

end Subsemiring

namespace Subring

/-- Joining a subring `S` with `Subring.closure s` agrees as a subsemiring with joining
`S.toSubsemiring` and `Subsemiring.closure s`. -/
@[simp] theorem toSubsemiring_sup_closure {B : Type*} [Ring B] (S : Subring B) (s : Set B) :
    (S ⊔ Subring.closure s).toSubsemiring = S.toSubsemiring ⊔ Subsemiring.closure s := by
  refine le_antisymm ?_ (sup_le (fun _ hb ↦ (le_sup_left : S ≤ S ⊔ Subring.closure s) hb) <|
    Subsemiring.closure_le.mpr fun _ hb ↦
      (le_sup_right : Subring.closure s ≤ S ⊔ Subring.closure s) (Subring.subset_closure hb))
  let T : Subsemiring B := S.toSubsemiring ⊔ Subsemiring.closure s
  have hST : S.toSubsemiring ≤ T := le_sup_left
  have hclT : Subsemiring.closure s ≤ T := le_sup_right
  let T' : Subring B :=
    { T with neg_mem' {a} ha := by simpa using T.mul_mem (hST (S.neg_mem S.one_mem)) ha }
  exact (sup_le (fun _ hb ↦ hST hb)
    (Subring.closure_le.mpr fun _ hb ↦ hclT (Subsemiring.subset_closure hb)) : _ ≤ T')

end Subring
