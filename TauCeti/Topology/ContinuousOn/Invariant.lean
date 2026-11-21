/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Invariant neighbourhoods for finitely many local maps

Let finitely many maps `f g : X → X`, indexed by a finite type `M` with a multiplication, be
continuous on open sets `T g` containing a point `x`, and fix `x`. Suppose they compose like `M`
on a neighbourhood `V` of `x` (`f (g * h) y = f g (f h y)`), and that each `f h` sends `V` into
every `T g`. Then `x` has an open neighbourhood inside `V` and inside every `T g` that every
`f h` sends into itself
(`TauCeti.exists_isOpen_forall_mem_of_continuousOn_mul`).

This shrinks a neighbourhood on which a finite group acts only by local maps to an invariant one,
such as the local action of an isotropy group on a neighbourhood in an étale groupoid.
-/

public section

open Set

namespace TauCeti

variable {X M : Type*} [TopologicalSpace X] [Mul M] [Finite M]

/-- Shrinking a neighbourhood `V` of `x` on which finitely many maps `f g`, each continuous on an
open set `T g` containing `x` and fixing `x`, compose like `M`, to an open neighbourhood `U`
of `x` that each `f h` maps into itself. -/
theorem exists_isOpen_forall_mem_of_continuousOn_mul {f : M → X → X} {T : M → Set X} {V : Set X}
    {x : X} (hV : IsOpen V) (hxV : x ∈ V) (hT : ∀ g, IsOpen (T g))
    (hf : ∀ g, ContinuousOn (f g) (T g)) (hxT : ∀ g, x ∈ T g) (hfx : ∀ g, f g x = x)
    (hVT : ∀ y ∈ V, ∀ g h, f h y ∈ T g)
    (hmul : ∀ y ∈ V, ∀ g h, f (g * h) y = f g (f h y)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ (∀ y ∈ U, ∀ g, y ∈ T g) ∧
      ∀ y ∈ U, ∀ h, f h y ∈ U := by
  refine ⟨V ∩ ⋂ g, T g ∩ f g ⁻¹' V,
    hV.inter (isOpen_iInter_of_finite fun g ↦ (hf g).isOpen_inter_preimage (hT g) hV),
    ⟨hxV, Set.mem_iInter.2 fun g ↦ ⟨hxT g, by simp only [Set.mem_preimage, hfx]; exact hxV⟩⟩,
    Set.inter_subset_left, fun y hy g ↦ (Set.mem_iInter.1 hy.2 g).1, fun y hy h ↦ ?_⟩
  refine ⟨(Set.mem_iInter.1 hy.2 h).2, Set.mem_iInter.2 fun g ↦ ⟨hVT y hy.1 g h, ?_⟩⟩
  have := (Set.mem_iInter.1 hy.2 (g * h)).2
  rwa [Set.mem_preimage, hmul y hy.1] at this

end TauCeti
