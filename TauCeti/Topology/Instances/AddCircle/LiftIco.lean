/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Functions on the additive circle lifted from a fundamental interval

For a function `f : 𝕜 → B`, Mathlib's `AddCircle.liftIco p a f` is the function on
`AddCircle p` which agrees with `f` on the fundamental interval `[a, a + p)`. This file records
its range, its injectivity, and its values on the closed interval `[a, a + p]` when
`f a = f (a + p)`. Together with `AddCircle.liftIco_continuous`, a closed curve `γ`, continuous
on `[a, b]` with `γ a = γ b`, thus factors through the circle `AddCircle (b - a)` as a continuous
map with the same trace, injective exactly when `γ` is injective on `[a, b)`.

## Main results

* `AddCircle.liftIco_coe_apply_of_mem_Icc`: if `f a = f (a + p)`, the lift agrees with `f` on
  `[a, a + p]`.
* `AddCircle.range_liftIco`: the range of the lift is the image of `[a, a + p)` under `f`.
* `AddCircle.injective_liftIco_iff`: the lift is injective exactly when `f` is injective on
  `[a, a + p)`.
-/

public section

open Function Set

namespace AddCircle

variable {𝕜 B : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  {p a : 𝕜} [hp : Fact (0 < p)] {f : 𝕜 → B}

/-- If `f a = f (a + p)`, the lift of `f` to `AddCircle p` agrees with `f` on the closed interval
`[a, a + p]`. -/
theorem liftIco_coe_apply_of_mem_Icc (hf : f a = f (a + p)) {x : 𝕜} (hx : x ∈ Icc a (a + p)) :
    liftIco p a f x = f x := by
  rcases hx.2.lt_or_eq with h | rfl
  · exact liftIco_coe_apply ⟨hx.1, h⟩
  · rw [← liftIoc_eq_liftIco hf]
    exact liftIoc_coe_apply ⟨lt_add_of_pos_right a hp.out, le_rfl⟩

/-- The range of the lift of `f` to `AddCircle p` is the image of `[a, a + p)` under `f`. -/
theorem range_liftIco : range (liftIco p a f) = f '' Ico a (a + p) := by
  rw [← image_univ, ← coe_image_Ico_eq p a, image_image]
  exact image_congr fun _ hx ↦ liftIco_coe_apply hx

/-- The lift of `f` to `AddCircle p` is injective exactly when `f` is injective on the
fundamental interval `[a, a + p)`. -/
theorem injective_liftIco_iff : Injective (liftIco p a f) ↔ InjOn f (Ico a (a + p)) := by
  refine ⟨fun h x hx y hy hxy ↦ ?_, fun h x y hxy ↦ ?_⟩
  · rw [← liftIco_coe_apply (f := f) hx, ← liftIco_coe_apply (f := f) hy] at hxy
    exact (coe_eq_coe_iff_of_mem_Ico hx hy).1 (h hxy)
  · obtain ⟨s, hs, rfl⟩ : ∃ s ∈ Ico a (a + p), (s : AddCircle p) = x :=
      ⟨equivIco p a x, (equivIco p a x).2, coe_equivIco⟩
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ Ico a (a + p), (t : AddCircle p) = y :=
      ⟨equivIco p a y, (equivIco p a y).2, coe_equivIco⟩
    rw [liftIco_coe_apply hs, liftIco_coe_apply ht] at hxy
    rw [h hs ht hxy]

end AddCircle
