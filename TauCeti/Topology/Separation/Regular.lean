/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Order.Filter.Curry

/-!
# Iterated limits in regular spaces

Let `f` be a function of two variables with values in a regular space, converging to `a` along a
product filter `l₁ ×ˢ l₂`. If, for each `x`, the function `f x` converges along `l₂` to `g x`,
then `g` converges to `a` along `l₁`, provided `l₂` is not trivial
(`Filter.Tendsto.tendsto_of_forall_tendsto`): the closed neighbourhoods of `a` form a basis, and
each of them contains the partial limits of the values it eventually contains. The same holds for
the partial limits in the first variable (`Filter.Tendsto.tendsto_of_forall_tendsto'`).
-/

public section

open Filter Topology

namespace Filter.Tendsto

variable {α β X : Type*} [TopologicalSpace X] [RegularSpace X] {l₁ : Filter α} {l₂ : Filter β}
  {f : α → β → X} {a : X}

/-- **Partial limits in the second variable converge to the joint limit.** If `f` converges to
`a` along `l₁ ×ˢ l₂` and `f x` converges to `g x` along `l₂` for every `x`, then `g` converges to
`a` along `l₁`. -/
theorem tendsto_of_forall_tendsto [l₂.NeBot]
    (h : Tendsto (fun p : α × β ↦ f p.1 p.2) (l₁ ×ˢ l₂) (𝓝 a)) {g : α → X}
    (hg : ∀ x, Tendsto (f x) l₂ (𝓝 (g x))) : Tendsto g l₁ (𝓝 a) := by
  rw [(closed_nhds_basis a).tendsto_right_iff]
  rintro s ⟨hs, hsc⟩
  filter_upwards [(h.eventually hs).curry] with x hx
  exact hsc.mem_of_tendsto (hg x) hx

/-- **Partial limits in the first variable converge to the joint limit.** If `f` converges to
`a` along `l₁ ×ˢ l₂` and `x ↦ f x y` converges to `g y` along `l₁` for every `y`, then `g`
converges to `a` along `l₂`. -/
theorem tendsto_of_forall_tendsto' [l₁.NeBot]
    (h : Tendsto (fun p : α × β ↦ f p.1 p.2) (l₁ ×ˢ l₂) (𝓝 a)) {g : β → X}
    (hg : ∀ y, Tendsto (fun x ↦ f x y) l₁ (𝓝 (g y))) : Tendsto g l₂ (𝓝 a) :=
  tendsto_of_forall_tendsto (f := fun y x ↦ f x y) (h.comp (tendsto_snd.prodMk tendsto_fst)) hg

end Filter.Tendsto
