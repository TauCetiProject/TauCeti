/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Order.Sublevel

/-!
# Homotopy groups of sublevels inside a globally bounded sublevel

Let `f : X → β` take values in a preorder `β`, with `a ≤ b` and `f x ≤ b` for every `x : X`. Then
`TauCeti.sublevelHomeomorphUniv` identifies the upper sublevel `{f ≤ b}` homeomorphically with `X`,
carrying `TauCeti.sublevelInclusion f a b hab : {f ≤ a} ↪ {f ≤ b}` to the subtype inclusion
`{f ≤ a} ↪ X`. Consequently, `{f ≤ a} ↪ X` and `{f ≤ a} ↪ {f ≤ b}` induce the same homotopy-group
maps up to `HomotopyGroup.homeomorphEquiv`, and in particular one is surjective, injective, or
bijective at a base point `x` if and only if the other is.

## Main results

* `HomotopyGroup.map_subtypeVal_eq_homeomorphEquivOfEq_comp_sublevelInclusion`: factors the `π_N`
  map of `{f ≤ a} ↪ X` through `{f ≤ a} ↪ {f ≤ b}` and `TauCeti.sublevelHomeomorphUniv`.
* `HomotopyGroup.surjective_map_subtypeVal_iff_sublevelInclusion`,
  `HomotopyGroup.injective_map_subtypeVal_iff_sublevelInclusion`,
  `HomotopyGroup.bijective_map_subtypeVal_iff_sublevelInclusion`: equivalence of surjectivity,
  injectivity, and bijectivity on `π_N`.
-/

public section

open TauCeti
open scoped Topology Topology.Homotopy

namespace HomotopyGroup

variable {N X β : Type*} [TopologicalSpace X] [Preorder β] {f : X → β} {a b : β}

/-- When `f ≤ b` everywhere on `X`, the map on `π_N` induced by `{f ≤ a} ↪ X` is the map induced
by `TauCeti.sublevelInclusion f a b hab : {f ≤ a} ↪ {f ≤ b}` followed by
`HomotopyGroup.homeomorphEquivOfEq (TauCeti.sublevelHomeomorphUniv hfb) _`. -/
theorem map_subtypeVal_eq_homeomorphEquivOfEq_comp_sublevelInclusion (hab : a ≤ b)
    (hfb : ∀ x, f x ≤ b) (x : {x | f x ≤ a}) :
    map (N := N) (x := x) (ContinuousMap.subtypeVal {x | f x ≤ a}) rfl =
      homeomorphEquivOfEq (sublevelHomeomorphUniv hfb) (by simp) ∘
        map (N := N) (x := x) (sublevelInclusion f a b hab) rfl := by
  funext p
  simp only [Function.comp_apply, homeomorphEquivOfEq_apply, map_comp_apply]
  exact map_congr (coe_sublevelHomeomorphUniv_comp_sublevelInclusion hab hfb).symm _ _ p

/-- When `f ≤ b` everywhere on `X`, `{f ≤ a} ↪ X` induces a surjection on `π_N` at `x` if and only
if `TauCeti.sublevelInclusion f a b hab : {f ≤ a} ↪ {f ≤ b}` does. -/
theorem surjective_map_subtypeVal_iff_sublevelInclusion (hab : a ≤ b) (hfb : ∀ x, f x ≤ b)
    (x : {x | f x ≤ a}) :
    Function.Surjective (map (N := N) (x := x) (ContinuousMap.subtypeVal {x | f x ≤ a}) rfl) ↔
      Function.Surjective (map (N := N) (x := x) (sublevelInclusion f a b hab) rfl) := by
  rw [map_subtypeVal_eq_homeomorphEquivOfEq_comp_sublevelInclusion hab hfb x, Equiv.comp_surjective]

/-- When `f ≤ b` everywhere on `X`, `{f ≤ a} ↪ X` induces an injection on `π_N` at `x` if and only
if `TauCeti.sublevelInclusion f a b hab : {f ≤ a} ↪ {f ≤ b}` does. -/
theorem injective_map_subtypeVal_iff_sublevelInclusion (hab : a ≤ b) (hfb : ∀ x, f x ≤ b)
    (x : {x | f x ≤ a}) :
    Function.Injective (map (N := N) (x := x) (ContinuousMap.subtypeVal {x | f x ≤ a}) rfl) ↔
      Function.Injective (map (N := N) (x := x) (sublevelInclusion f a b hab) rfl) := by
  rw [map_subtypeVal_eq_homeomorphEquivOfEq_comp_sublevelInclusion hab hfb x, Equiv.comp_injective]

/-- When `f ≤ b` everywhere on `X`, `{f ≤ a} ↪ X` induces a bijection on `π_N` at `x` if and only
if `TauCeti.sublevelInclusion f a b hab : {f ≤ a} ↪ {f ≤ b}` does. -/
theorem bijective_map_subtypeVal_iff_sublevelInclusion (hab : a ≤ b) (hfb : ∀ x, f x ≤ b)
    (x : {x | f x ≤ a}) :
    Function.Bijective (map (N := N) (x := x) (ContinuousMap.subtypeVal {x | f x ≤ a}) rfl) ↔
      Function.Bijective (map (N := N) (x := x) (sublevelInclusion f a b hab) rfl) := by
  rw [map_subtypeVal_eq_homeomorphEquivOfEq_comp_sublevelInclusion hab hfb x, Equiv.comp_bijective]

end HomotopyGroup
