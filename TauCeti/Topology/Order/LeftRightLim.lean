/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Order
public import Mathlib.Topology.Order.LeftRightLim

/-!
# One-sided limits under homeomorphisms, reflection, and right convergence

Mathlib's `Function.leftLim f a` is the limit of `f` strictly to the left of `a`, with the
fallback value `f a` when `a` is isolated on the left or no such limit exists, and
`Function.rightLim` is its mirror image. This file records how both behave under post-composition
with a homeomorphism, under the reflection `t ↦ -t` of an ordered additive group, along a right
limit in a regular space, and under upper bounds on `(-∞, t]` or `(-∞, T]`. All identities hold
unconditionally: the fallback cases match and no càdlàg hypothesis is required.

## Main results

* `Homeomorph.leftLim_comp` and `Homeomorph.rightLim_comp`: one-sided limits commute with
  post-composition by a homeomorphism.
* `TauCeti.leftLim_comp_neg` and `TauCeti.rightLim_comp_neg`: reflecting the variable exchanges
  the left and right limits.
* `Filter.Tendsto.leftLim_nhdsGT`: if `f` converges from the right at `x` in a regular space, its
  strict left limit also converges from the right to the same limit.
* `TauCeti.leftLim_le_of_forall_le` and `TauCeti.upperBounds_image_Iic_subset_leftLim`: upper bounds
  on `(-∞, t]` or `(-∞, T]` are preserved by `Function.leftLim` in any preorder with closed lower
  rays.
-/

public section

open Filter Topology Function

variable {α β γ : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [TopologicalSpace β] [TopologicalSpace γ] [T2Space γ]

namespace Homeomorph

/-- **The left limit commutes with a homeomorphism**: `leftLim (e ∘ f) a = e (leftLim f a)`,
including when the left limit of `f` does not exist and both sides take the fallback value. -/
theorem leftLim_comp (e : β ≃ₜ γ) (f : α → β) (a : α) :
    leftLim (fun x => e (f x)) a = e (leftLim f a) := by
  have : T2Space β := e.isEmbedding.t2Space
  rcases eq_or_neBot (𝓝[<] a) with h | h
  · rw [leftLim_eq_of_eq_bot _ h, leftLim_eq_of_eq_bot _ h]
  by_cases hex : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)
  · obtain ⟨y, hy⟩ := hex
    rw [leftLim_eq_of_tendsto hy]
    exact leftLim_eq_of_tendsto ((e.continuous.tendsto y).comp hy)
  · rw [leftLim_eq_of_not_tendsto _ hex, leftLim_eq_of_not_tendsto]
    rintro ⟨z, hz⟩
    exact hex ⟨e.symm z, by
      simpa [Function.comp_def] using (e.symm.continuous.tendsto z).comp hz⟩

/-- **The right limit commutes with a homeomorphism**: `rightLim (e ∘ f) a = e (rightLim f a)`,
including when the right limit of `f` does not exist and both sides take the fallback value. -/
theorem rightLim_comp (e : β ≃ₜ γ) (f : α → β) (a : α) :
    rightLim (fun x => e (f x)) a = e (rightLim f a) := by
  have : T2Space β := e.isEmbedding.t2Space
  rcases eq_or_neBot (𝓝[>] a) with h | h
  · rw [rightLim_eq_of_eq_bot _ h, rightLim_eq_of_eq_bot _ h]
  by_cases hex : ∃ y, Tendsto f (𝓝[>] a) (𝓝 y)
  · obtain ⟨y, hy⟩ := hex
    rw [rightLim_eq_of_tendsto hy]
    exact rightLim_eq_of_tendsto ((e.continuous.tendsto y).comp hy)
  · rw [rightLim_eq_of_not_tendsto _ hex, rightLim_eq_of_not_tendsto]
    rintro ⟨z, hz⟩
    exact hex ⟨e.symm z, by
      simpa [Function.comp_def] using (e.symm.continuous.tendsto z).comp hz⟩

end Homeomorph

namespace TauCeti

variable {H : Type*} [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H] [TopologicalSpace H]
  [OrderTopology H] [ContinuousNeg H] [T2Space β]

/-- **Reflection exchanges the one-sided limits**: the left limit of `t ↦ f (-t)` at `a` is the
right limit of `f` at `-a`, including in the fallback cases. -/
theorem leftLim_comp_neg (f : H → β) (a : H) :
    leftLim (fun t => f (-t)) a = rightLim f (-a) := by
  have hmap : map Neg.neg (𝓝[<] a) = 𝓝[>] (-a) := Filter.neg_nhdsLT
  have htend (y : β) :
      Tendsto (fun t => f (-t)) (𝓝[<] a) (𝓝 y) ↔ Tendsto f (𝓝[>] (-a)) (𝓝 y) := by
    rw [← hmap, tendsto_map'_iff]
    rfl
  rcases eq_or_neBot (𝓝[<] a) with h | h
  · have h' : 𝓝[>] (-a) = ⊥ := by rw [← hmap, h, map_bot]
    rw [leftLim_eq_of_eq_bot _ h, rightLim_eq_of_eq_bot _ h']
  have : (𝓝[>] (-a)).NeBot := hmap ▸ h.map _
  by_cases hex : ∃ y, Tendsto f (𝓝[>] (-a)) (𝓝 y)
  · obtain ⟨y, hy⟩ := hex
    rw [rightLim_eq_of_tendsto hy, leftLim_eq_of_tendsto ((htend y).mpr hy)]
  · rw [rightLim_eq_of_not_tendsto _ hex, leftLim_eq_of_not_tendsto]
    exact fun ⟨y, hy⟩ => hex ⟨y, (htend y).mp hy⟩

/-- **Reflection exchanges the one-sided limits**: the right limit of `t ↦ f (-t)` at `a` is the
left limit of `f` at `-a`, including in the fallback cases. -/
theorem rightLim_comp_neg (f : H → β) (a : H) :
    rightLim (fun t => f (-t)) a = leftLim f (-a) := by
  simpa only [neg_neg] using (leftLim_comp_neg (fun t => f (-t)) (-a)).symm

end TauCeti

section RightConvergence

open Set

/-- Along times approaching `x` strictly from the right, if `f` converges to `y` in a regular
space, then its strict left limit `f.leftLim` also converges to `y`. -/
theorem Filter.Tendsto.leftLim_nhdsGT {X Y : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [TopologicalSpace Y] [RegularSpace Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝[>] x) (𝓝 y)) :
    Tendsto f.leftLim (𝓝[>] x) (𝓝 y) := by
  rcases eq_or_neBot (𝓝[>] x) with hbot | _
  · simp [hbot]
  apply (closed_nhds_basis y).tendsto_right_iff.2
  rintro V ⟨hV_mem, hV_closed⟩
  obtain ⟨b, hb⟩ : (Ioi x).Nonempty := nonempty_of_mem (self_mem_nhdsWithin (a := x))
  obtain ⟨u, hxu, hu⟩ : ∃ u, x < u ∧ Ioo x u ⊆ {t | f t ∈ V} := by
    have hpre := (closed_nhds_basis y).tendsto_right_iff.1 h V ⟨hV_mem, hV_closed⟩
    simpa using (mem_nhdsGT_iff_exists_Ioo_subset' hb).1 hpre
  filter_upwards [Ioo_mem_nhdsGT hxu] with r hr
  rcases eq_or_neBot (𝓝[<] r) with hr_bot | _
  · simpa [leftLim_eq_of_eq_bot f hr_bot] using hu hr
  by_cases hr_lim : ∃ l, Tendsto f (𝓝[<] r) (𝓝 l)
  · apply hV_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto hr_lim)
    filter_upwards [Ioo_mem_nhdsLT hr.1] with s hs
    exact hu ⟨hs.1, hs.2.trans hr.2⟩
  · simpa [leftLim_eq_of_not_tendsto f hr_lim] using hu hr

namespace TauCeti

/-- An upper bound on `g` over `(-∞, t]` is preserved by its strict left limit at `t`, in any
preorder with closed lower rays. No càdlàg hypothesis is required. -/
theorem leftLim_le_of_forall_le {X α : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [Preorder α] [TopologicalSpace α] [ClosedIicTopology α]
    {g : X → α} {t : X} {c : α} (hg : ∀ s ≤ t, g s ≤ c) :
    g.leftLim t ≤ c :=
  isClosed_Iic.mem_of_mapClusterPt (mapClusterPt_leftLim g t) <|
    eventually_nhdsWithin_of_forall hg

/-- Every upper bound of `g` on `(-∞, T]` is also an upper bound of `g.leftLim` on `(-∞, T]`, in
any preorder with closed lower rays. No càdlàg hypothesis is required. -/
theorem upperBounds_image_Iic_subset_leftLim {X α : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [Preorder α] [TopologicalSpace α] [ClosedIicTopology α]
    (g : X → α) (T : X) :
    upperBounds (g '' Iic T) ⊆ upperBounds (g.leftLim '' Iic T) := by
  rintro c hc _ ⟨t, ht, rfl⟩
  exact leftLim_le_of_forall_le fun s hs => hc ⟨s, hs.trans ht, rfl⟩

end TauCeti

end RightConvergence
