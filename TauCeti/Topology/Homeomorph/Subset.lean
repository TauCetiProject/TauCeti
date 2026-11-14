/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Restricting homeomorphisms between subsets

`Homeomorph.subsetRestrict` restricts a homeomorphism between subsets to smaller corresponding
subsets of the ambient spaces. Unlike restriction to predicates on the subtype, the resulting
homeomorphism has no nested subtypes. Its forward and inverse coercion lemmas identify the
underlying maps. This is useful for transporting ambient interiors and frontiers.
-/

public section

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {A s : Set X} {B t : Set Y}

/-- Restrict a homeomorphism between subsets to smaller subsets whose membership it preserves. -/
def subsetRestrict (e : A ≃ₜ B) (hs : s ⊆ A) (ht : t ⊆ B)
    (h : ∀ x : A, x.val ∈ s ↔ (e x).val ∈ t) : s ≃ₜ t where
  toFun x := ⟨e ⟨x.val, hs x.property⟩, (h _).mp x.property⟩
  invFun y := ⟨e.symm ⟨y.val, ht y.property⟩, (h _).mpr (by simp)⟩
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun :=
    (e.continuous.comp (continuous_inclusion hs)).subtype_val.subtype_mk _
  continuous_invFun :=
    (e.symm.continuous.comp (continuous_inclusion ht)).subtype_val.subtype_mk _

/-- Restriction agrees with the original homeomorphism on underlying points. -/
@[simp]
theorem subsetRestrict_apply_coe (e : A ≃ₜ B) (hs : s ⊆ A) (ht : t ⊆ B)
    (h : ∀ x : A, x.val ∈ s ↔ (e x).val ∈ t) (x : s) :
    (e.subsetRestrict hs ht h x).val = (e ⟨x.val, hs x.property⟩).val := (rfl)

/-- Inverse restriction agrees with the inverse homeomorphism on underlying points. -/
@[simp]
theorem subsetRestrict_symm_apply_coe (e : A ≃ₜ B) (hs : s ⊆ A) (ht : t ⊆ B)
    (h : ∀ x : A, x.val ∈ s ↔ (e x).val ∈ t) (y : t) :
    ((e.subsetRestrict hs ht h).symm y).val = (e.symm ⟨y.val, ht y.property⟩).val := (rfl)

end Homeomorph
