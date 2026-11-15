/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Absorption of fixed elements in a nonarchimedean ring

When multiplication by a fixed element `a` is continuous and the additive group is
nonarchimedean, every neighbourhood `V` of zero absorbs `a`: some open additive subgroup `Z`
satisfies `a * Z ⊆ V`. For a single element in a nonarchimedean ring this is Mathlib's
`NonarchimedeanRing.left_mul_subset`. This file adds the finite-family form: one open subgroup
absorbs each of finitely many fixed elements into its own target neighbourhood.

## Main results

* `NonarchimedeanAddGroup.exists_openAddSubgroup_forall_mul_mem`: finitely many fixed elements
  are absorbed into their own targets by a single open subgroup.
-/

public section

namespace NonarchimedeanAddGroup

variable {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A] [SeparatelyContinuousMul A]
  [NonarchimedeanAddGroup A]

/-- **The finite-family absorption lemma**: one open additive subgroup `Z` absorbs each of
finitely many fixed elements `a i` into its own neighbourhood `V i` of zero, i.e.
`a i * z ∈ V i` for all `i ∈ s` and `z ∈ Z`. The single-element case in a nonarchimedean ring is
Mathlib's `NonarchimedeanRing.left_mul_subset`. -/
theorem exists_openAddSubgroup_forall_mul_mem {ι : Type*} (s : Finset ι) (a : ι → A)
    (V : ι → Set A) (hV : ∀ i ∈ s, V i ∈ nhds (0 : A)) :
    ∃ Z : OpenAddSubgroup A, ∀ i ∈ s, ∀ z ∈ Z, a i * z ∈ V i := by
  obtain ⟨Z, hZ⟩ := is_nonarchimedean _ <| s.eventually_all.2 fun i hi ↦
    ((continuous_const_mul (a i)).tendsto' 0 0 (mul_zero _)).eventually_mem (hV i hi)
  exact ⟨Z, fun i hi z hz ↦ hZ hz i hi⟩

end NonarchimedeanAddGroup
