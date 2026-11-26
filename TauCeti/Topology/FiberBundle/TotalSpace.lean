/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Topology.Continuous

/-!
# Continuity of fibrewise maps conjugated by continuous maps of total spaces

A fibrewise map `g` from the total space of `E₂` to that of `F₂` over a base `B` is often obtained
from a continuous fibrewise map `f` from the total space of `E₁` to that of `F₁` by reading it
through maps of total spaces, for instance through chosen charts or a change of fibre universe.
When those maps are continuous, lie over `B` and act fibrewise,
`TauCeti.continuous_totalSpace_conj` shows that `g` is continuous. The total spaces carry
arbitrary topologies: no fibre bundle structure is assumed.
-/

public section

open Bundle

namespace TauCeti

variable {B M₁ M₂ N₁ N₂ : Type*} {E₁ E₂ : B → Type*} {F₁ F₂ : B → Type*}
  [TopologicalSpace (TotalSpace M₁ E₁)] [TopologicalSpace (TotalSpace M₂ E₂)]
  [TopologicalSpace (TotalSpace N₁ F₁)] [TopologicalSpace (TotalSpace N₂ F₂)]

/-- A fibrewise map `g` of total spaces is continuous when it is a continuous fibrewise map `f`
composed on either side with continuous maps `e` and `e'` of total spaces over the base that act
fibrewise, by `a` and by `b`. -/
theorem continuous_totalSpace_conj
    {e : TotalSpace M₂ E₂ → TotalSpace M₁ E₁} {e' : TotalSpace N₁ F₁ → TotalSpace N₂ F₂}
    (hec : Continuous e) (he'c : Continuous e')
    {a : ∀ p : TotalSpace M₂ E₂, E₁ p.proj} {b : ∀ q : TotalSpace N₁ F₁, F₂ q.proj}
    {f : ∀ q : TotalSpace M₁ E₁, F₁ q.proj} {g : ∀ p : TotalSpace M₂ E₂, F₂ p.proj}
    (he : ∀ p, e p = ⟨p.proj, a p⟩) (he' : ∀ q, e' q = ⟨q.proj, b q⟩)
    (hg : ∀ p, g p = b ⟨p.proj, f ⟨p.proj, a p⟩⟩)
    (hf : Continuous fun q : TotalSpace M₁ E₁ ↦ (⟨q.proj, f q⟩ : TotalSpace N₁ F₁)) :
    Continuous fun p : TotalSpace M₂ E₂ ↦ (⟨p.proj, g p⟩ : TotalSpace N₂ F₂) :=
  (he'c.comp (hf.comp hec)).congr fun p ↦ by
    rw [Function.comp_apply, Function.comp_apply, he, he', hg]

end TauCeti
