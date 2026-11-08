/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Set

/-!
# The function defined by a functional graph

A set `G ⊆ X × Y` with injective first projection defines a function on `Prod.fst '' G`.
`Set.InjOn.graphValue` names that function without extending it outside its domain and without
requiring `Y` to be nonempty. Its values are characterized by membership in `G`.

The construction uses the inverse of `Set.BijOn.equiv` for the first projection. In measurable
spaces, this description allows Lusin–Souslin to prove measurability of the resulting function.
-/

public section

open Set

namespace Set.InjOn

variable {X Y : Type*} {G : Set (X × Y)}

/-- The function on the domain of a graph with injective first projection. No value outside
`Prod.fst '' G` is chosen. -/
noncomputable def graphValue (hG : InjOn Prod.fst G) (x : Prod.fst '' G) : Y :=
  ((hG.bijOn_image.equiv Prod.fst).symm x).val.2

/-- Every value of the function defined by a functional graph belongs to that graph. -/
@[simp]
theorem graphValue_mem (hG : InjOn Prod.fst G) (x : Prod.fst '' G) :
    ((x : X), hG.graphValue x) ∈ G := by
  let e := hG.bijOn_image.equiv Prod.fst
  -- The forward map of this Set.BijOn.equiv is definitionally the first projection.
  have hx : (e.symm x).val.1 = (x : X) := congrArg Subtype.val (e.apply_symm_apply x)
  have hm : ((e.symm x).val.1, (e.symm x).val.2) ∈ G := (e.symm x).property
  dsimp only [graphValue]
  simpa only [hx] using hm

/-- A point of a functional graph determines the value of its associated function. -/
theorem graphValue_eq_of_mem (hG : InjOn Prod.fst G) {x : X} {y : Y} (h : (x, y) ∈ G) :
    hG.graphValue ⟨x, mem_image_of_mem Prod.fst h⟩ = y :=
  congrArg Prod.snd (hG (hG.graphValue_mem _) h rfl)

/-- The value of the function defined by a functional graph is uniquely characterized by
membership in that graph. -/
@[simp]
theorem graphValue_eq_iff (hG : InjOn Prod.fst G) (x : Prod.fst '' G) (y : Y) :
    hG.graphValue x = y ↔ ((x : X), y) ∈ G := by
  refine ⟨fun h ↦ h ▸ hG.graphValue_mem x, fun h ↦ ?_⟩
  exact congrArg Prod.snd (hG (hG.graphValue_mem x) h rfl)

/-- Evaluating the function defined by a graph of an existing function recovers that function. -/
@[simp]
theorem graphValue_graphOn {s : Set X} {f : X → Y} (x : Prod.fst '' s.graphOn f) :
    (fst_injOn_graph : InjOn Prod.fst (s.graphOn f)).graphValue x = f x := by
  apply (graphValue_eq_iff _ _ _).2
  have hx : (x : X) ∈ s := by simpa only [image_fst_graphOn] using x.property
  simp [hx]

/-- The graph is exactly the range of its domain parametrization. -/
@[simp]
theorem range_prodMk_graphValue (hG : InjOn Prod.fst G) :
    range (fun x : Prod.fst '' G ↦ ((x : X), hG.graphValue x)) = G := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact hG.graphValue_mem x
  · intro hp
    exact ⟨⟨p.1, mem_image_of_mem Prod.fst hp⟩,
      Prod.ext rfl (hG.graphValue_eq_of_mem hp)⟩

/-- Any function on the domain whose values lie in the graph equals the graph's function. -/
theorem eq_graphValue (hG : InjOn Prod.fst G) {f : (Prod.fst '' G) → Y}
    (hf : ∀ x : Prod.fst '' G, ((x : X), f x) ∈ G) : f = hG.graphValue := by
  ext x
  exact ((hG.graphValue_eq_iff x (f x)).2 (hf x)).symm

end Set.InjOn
