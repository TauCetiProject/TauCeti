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
set `S x` depending on the point `x`, so does their concatenation
(`ContinuousMap.Homotopy.trans_apply_mem`). With `S` constant, this is how homotopies avoiding a
compact set are chained in conditions such as simple connectivity at infinity. With `S x` the
fibre of a map `π` over `q x`, it says that homotopies through maps over a base concatenate to a
homotopy through maps over the base.
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

/-- If two homotopies take values in `S x` at each point `x`, so does their concatenation. -/
theorem trans_apply_mem {S : X → Set Y} {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂}
    (hF : ∀ t x, F (t, x) ∈ S x) (hG : ∀ t x, G (t, x) ∈ S x) (t : I) (x : X) :
    F.trans G (t, x) ∈ S x := by
  rw [trans_apply]
  split_ifs
  exacts [hF _ x, hG _ x]

end ContinuousMap.Homotopy
