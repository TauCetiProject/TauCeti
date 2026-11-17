/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# The range of a concatenated homotopy

The concatenation `F.trans G` of homotopies runs `F` on the first half of the interval and `G` on
the second half, so every value it takes is a value of `F` or of `G`
(`ContinuousMap.Homotopy.range_trans_subset`). In particular, if both homotopies take values in a
set `S`, so does their concatenation (`ContinuousMap.Homotopy.trans_apply_mem`); this is how
homotopies avoiding a compact set are chained in conditions such as simple connectivity at
infinity. Likewise, if both homotopies keep each point `x` in the fibre of a map `π` over `q x`,
so does their concatenation (`ContinuousMap.Homotopy.trans_apply_eq_of_forall`): homotopies
through maps over a base concatenate to a homotopy through maps over the base.
-/

public section

open Set
open scoped unitInterval

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ f₂ : C(X, Y)}

/-- Every value of a concatenated homotopy `F.trans G` is a value of `F` or of `G`. -/
theorem range_trans_subset (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    range (F.trans G) ⊆ range F ∪ range G := by
  rintro _ ⟨x, rfl⟩
  rw [trans_apply]
  split_ifs
  exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]

/-- If two homotopies take values in `S`, so does their concatenation. -/
theorem trans_apply_mem {S : Set Y} {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂}
    (hF : ∀ x, F x ∈ S) (hG : ∀ x, G x ∈ S) (x : I × X) : F.trans G x ∈ S := by
  obtain ⟨y, hy⟩ | ⟨y, hy⟩ := range_trans_subset F G ⟨x, rfl⟩
  exacts [hy ▸ hF y, hy ▸ hG y]

/-- If two homotopies keep each point `x` in the fibre of `π` over `q x`, so does their
concatenation. -/
theorem trans_apply_eq_of_forall {B : Type*} {π : Y → B} {q : X → B} {F : Homotopy f₀ f₁}
    {G : Homotopy f₁ f₂} (hF : ∀ t x, π (F (t, x)) = q x) (hG : ∀ t x, π (G (t, x)) = q x)
    (t : I) (x : X) : π (F.trans G (t, x)) = q x := by
  rw [trans_apply]
  split_ifs
  exacts [hF _ x, hG _ x]

end ContinuousMap.Homotopy
