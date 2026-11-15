/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-! # Subsemirings containing the kernel of a ring map

For a subsemiring containing the kernel of a ring homomorphism, membership can be
tested in its image, and pulling back that image recovers the original subsemiring.
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
