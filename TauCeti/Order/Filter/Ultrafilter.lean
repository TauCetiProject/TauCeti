/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Lifting ultrafilters and free ultrafilters

Let `f : α → β` and let `𝒰` be an ultrafilter on `β`. If `f` carries every member of a filter `l`
on `α` onto a member of `𝒰`, then `𝒰` is the image under `f` of an ultrafilter on `α` finer than
`l` (`Ultrafilter.exists_le_map_eq`). This generalizes Mathlib's
`Ultrafilter.ofComapInfPrincipal`, which is the case of a principal filter `l = 𝓟 s`.

For example, if `f` is an open map and `𝒰` converges to `f x`, then `l = 𝓝 x` satisfies the
hypothesis, so `𝒰` lifts to an ultrafilter converging to `x`. This is how convergence in an orbit
space is lifted to convergence of representatives, for instance to prove that an action on an
orbit space is proper.

An ultrafilter on `α` is finer than `Filter.cofinite` if and only if it is free (not equal to
`pure a` for any `a : α`, `Ultrafilter.le_cofinite_iff_forall_ne_pure`). On `ℕ`, where
`Filter.cofinite = Filter.atTop`, this characterizes free ultrafilters as those finer than
`Filter.atTop` (`Ultrafilter.le_atTop_iff_forall_ne_pure`).
-/

public section

open Filter

namespace Ultrafilter

variable {α β : Type*}

/-- **Lifting an ultrafilter along a map.** If `f` carries every member of a filter `l` onto a
member of an ultrafilter `𝒰`, then `𝒰` is the image under `f` of an ultrafilter finer than `l`. -/
theorem exists_le_map_eq {f : α → β} {l : Filter α} (𝒰 : Ultrafilter β)
    (h : ∀ s ∈ l, f '' s ∈ 𝒰) : ∃ 𝒱 : Ultrafilter α, ↑𝒱 ≤ l ∧ 𝒱.map f = 𝒰 := by
  have : (Filter.comap f 𝒰 ⊓ l).NeBot := by
    refine ⟨fun h₀ ↦ ?_⟩
    obtain ⟨t, ht, s, hs, hts⟩ := Filter.inf_eq_bot_iff.1 h₀
    obtain ⟨u, hu, hut⟩ := Filter.mem_comap.1 ht
    obtain ⟨_, ⟨a, ha, rfl⟩, hau⟩ := 𝒰.nonempty_of_mem (𝒰.inter_mem (h s hs) hu)
    exact (Set.eq_empty_iff_forall_notMem.1 hts) a ⟨hut hau, ha⟩
  obtain ⟨𝒱, h𝒱⟩ := exists_ultrafilter_le (Filter.comap f 𝒰 ⊓ l)
  refine ⟨𝒱, h𝒱.trans inf_le_right, coe_le_coe.1 ?_⟩
  rw [coe_map]
  exact map_le_iff_le_comap.2 (h𝒱.trans inf_le_left)

/-- An ultrafilter on `α` is finer than `Filter.cofinite` if and only if it is not principal at any
point of `α`. -/
theorem le_cofinite_iff_forall_ne_pure {ω : Ultrafilter α} :
    (ω : Filter α) ≤ cofinite ↔ ∀ a, ω ≠ pure a := by
  refine ⟨fun h a ha ↦ ?_, fun h ↦ ω.le_cofinite_or_eq_pure.resolve_right fun ⟨a, ha⟩ ↦ h a ha⟩
  have hmem : ({a}ᶜ : Set α) ∈ (ω : Filter α) := h (mem_cofinite.2 (by simp))
  simp [ha] at hmem

/-- An ultrafilter on `ℕ` is finer than `Filter.atTop` if and only if it is not principal at any
natural number. -/
theorem le_atTop_iff_forall_ne_pure {ω : Ultrafilter ℕ} :
    (ω : Filter ℕ) ≤ atTop ↔ ∀ n, ω ≠ pure n := by
  rw [← Nat.cofinite_eq_atTop, le_cofinite_iff_forall_ne_pure]

end Ultrafilter
