/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Homeomorphisms and covering maps

A homeomorphism is a covering map with one-point fibres: the whole base is evenly covered. In
particular the identity of a space is a covering map, the trivial one-sheeted cover. Conversely, on
a preconnected covering space, two continuous lifts that cover a left-inverse pair and compose to
the identity at a single point are left inverses everywhere
(`IsCoveringMap.leftInverse_of_comp_eq`).

## Main results

* `IsCoveringMap.id`: the identity of a space is a covering map.
* `IsHomeomorph.isCoveringMap`: a homeomorphism is a covering map.
* `Homeomorph.isCoveringMap`: the bundled form of the previous result.
* `IsCoveringMap.leftInverse_of_comp_eq`: continuous lifts covering a left-inverse pair on a
  preconnected covering space and satisfying `R (L x) = x` at one point satisfy `LeftInverse R L`.
-/

public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The identity of a space is a covering map, the trivial one-sheeted cover: the whole space is
an evenly covered neighbourhood of every point. -/
protected theorem IsCoveringMap.id : IsCoveringMap (@id X) := fun _ ↦
  IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Unit)
    ⟨inferInstance, .univ, trivial, isOpen_univ, isOpen_univ, (Homeomorph.prodPUnit _).symm,
      fun _ ↦ rfl⟩

/-- A homeomorphism is a covering map, with the whole base as an evenly covered neighbourhood. -/
theorem IsHomeomorph.isCoveringMap {f : X → Y} (hf : IsHomeomorph f) : IsCoveringMap f := by
  convert IsCoveringMap.id.homeomorph_comp (hf.homeomorph f) using 1
  ext
  simp

/-- A bundled homeomorphism is a covering map; see `IsHomeomorph.isCoveringMap`. -/
theorem Homeomorph.isCoveringMap (e : X ≃ₜ Y) : IsCoveringMap e := by
  simpa only [Function.comp_id] using IsCoveringMap.id.homeomorph_comp e

/-- On a preconnected covering space, if continuous maps `L : M₁ → M₂` and `R : M₂ → M₁`
intertwine `f₁ : M₁ → N₁` and `f₂ : M₂ → N₂` with maps `φ : N₁ → N₂` and `ψ : N₂ → N₁` satisfying
`LeftInverse ψ φ`, and `R (L x) = x` at one point `x`, then `R` is a left inverse of `L`. -/
theorem IsCoveringMap.leftInverse_of_comp_eq {M₁ M₂ N₁ N₂ : Type*}
    [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace N₁]
    [PreconnectedSpace M₁] {f₁ : M₁ → N₁} {f₂ : M₂ → N₂} (hcov : IsCoveringMap f₁)
    {L : M₁ → M₂} {R : M₂ → M₁} {φ : N₁ → N₂} {ψ : N₂ → N₁}
    (hL_cont : Continuous L) (hR_cont : Continuous R)
    (hL : f₂ ∘ L = φ ∘ f₁) (hR : f₁ ∘ R = ψ ∘ f₂) (hψφ : Function.LeftInverse ψ φ)
    {x : M₁} (hx : R (L x) = x) :
    Function.LeftInverse R L := by
  have hcomp : f₁ ∘ (R ∘ L) = f₁ ∘ id := by
    funext z
    calc
      f₁ (R (L z)) = ψ (f₂ (L z)) := congrFun hR (L z)
      _ = ψ (φ (f₁ z)) := congrArg ψ (congrFun hL z)
      _ = f₁ z := hψφ (f₁ z)
  exact congrFun (hcov.eq_of_comp_eq (hR_cont.comp hL_cont) continuous_id hcomp x hx)
