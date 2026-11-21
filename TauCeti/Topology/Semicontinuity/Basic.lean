/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Basic properties of semicontinuous functions

This file collects general results about upper and lower semicontinuous functions:

* A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s`, for an arbitrary `G : Set X → β` with values in a
  complete linear order, is lower semicontinuous (`TauCeti.lowerSemicontinuous_iSup_nhds`): a strict
  lower bound witnessed by a neighbourhood of `x` is witnessed by the same set at every point of its
  interior. Lower envelopes and lower and upper Γ-limits are of this form.
* A lower semicontinuous subadditive function `A` with values in `ℝ≥0∞` and `A 0 = 0`, such as a
  lower semicontinuous extended seminorm, satisfies the triangle inequality for convergent series:
  `A (∑ f) ≤ ∑' b, A (f b)` (`LowerSemicontinuous.le_tsum_of_hasSum`). No continuity of `A` is
  needed, because the bound on the partial sums passes to their limit through the closed sublevel
  set.
* In the same way, a bound `g (u i) ≤ c + ε i` along a family `u`, with errors `ε i` tending to
  `0`, passes to every cluster point of `u` (`MapClusterPt.le_of_eventually_le_add`).
* For a product-valued function `f : α → ∀ i, β i` into linearly ordered codomains that locally
  takes finitely many values, coordinatewise upper semicontinuity forces `f x' ≤ f x` eventually
  near `x` without any ordering on the index type `ι`
  (`TauCeti.eventually_le_of_upperSemicontinuousWithinAt`,
  `TauCeti.eventually_le_of_upperSemicontinuousAt`), and dually for lower semicontinuity
  (`TauCeti.eventually_ge_of_lowerSemicontinuousWithinAt`,
  `TauCeti.eventually_ge_of_lowerSemicontinuousAt`). Consequently, post-composing such a family
  with any monotone map into a preorder preserves upper and lower semicontinuity at all four scopes
  (`Monotone.upperSemicontinuousWithinAt_comp_of_locally_finite_image`,
  `Monotone.upperSemicontinuousAt_comp_of_locally_finite_image`,
  `Monotone.upperSemicontinuousOn_comp_of_locally_finite_image`,
  `Monotone.upperSemicontinuous_comp_of_locally_finite_image`,
  `Monotone.lowerSemicontinuousWithinAt_comp_of_locally_finite_image`,
  `Monotone.lowerSemicontinuousAt_comp_of_locally_finite_image`,
  `Monotone.lowerSemicontinuousOn_comp_of_locally_finite_image`,
  `Monotone.lowerSemicontinuous_comp_of_locally_finite_image`). In particular, for a well-ordered
  index type `ι`, composing with `Pi.toLex` yields semicontinuity into `Lex (∀ i, β i)` directly
  via `Pi.toLex_monotone.<scope>_comp_of_locally_finite_image hf hfin`.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *$\mathbb{Q}$-universal
  desingularization*, Asian J. Math. 15 (2011), 229–250, §6.1 (for the locally finite
  product-valued semicontinuity criterion).
-/

public section

open Topology

namespace TauCeti

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β]

/-- A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s` is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_nhds (G : Set X → β) :
    LowerSemicontinuous fun x ↦ ⨆ s ∈ 𝓝 x, G s := by
  intro x c hc
  obtain ⟨s, hcs⟩ := lt_iSup_iff.1 hc
  obtain ⟨hs, hcs⟩ := lt_iSup_iff.1 hcs
  filter_upwards [eventually_mem_nhds_iff.2 hs] with y hy
  exact hcs.trans_le (le_iSup₂_of_le s hy le_rfl)

end TauCeti

open scoped ENNReal

namespace LowerSemicontinuous

variable {E β : Type*} [AddCommMonoid E] [TopologicalSpace E] {A : E → ℝ≥0∞}

/-- A lower semicontinuous subadditive function with values in `ℝ≥0∞` vanishing at zero bounds
the sum of a convergent series by the sum of its values on the terms. -/
theorem le_tsum_of_hasSum (hA : LowerSemicontinuous A) (h0 : A 0 = 0)
    (hadd : ∀ x y, A (x + y) ≤ A x + A y) {f : β → E} {s : E} (hf : HasSum f s) :
    A s ≤ ∑' b, A (f b) :=
  (hA.isClosed_preimage _).mem_of_tendsto hf <| Filter.Eventually.of_forall fun t ↦
    (Finset.le_sum_of_subadditive A h0.le hadd t f).trans (sum_le_tsum t)

end LowerSemicontinuous

namespace MapClusterPt

open Filter

variable {X β ι : Type*} [TopologicalSpace X] [AddCommGroup β] [LinearOrder β]
  [IsOrderedAddMonoid β] [DenselyOrdered β] [TopologicalSpace β] [OrderTopology β]

/-- **Bounds with vanishing errors pass to cluster points.** If a lower semicontinuous `g`
satisfies `g (u i) ≤ c + ε i` eventually along `l`, with errors `ε i` tending to `0`, then
`g x ≤ c` at every cluster point `x` of `u` along `l`. -/
theorem le_of_eventually_le_add {l : Filter ι} {u : ι → X} {x : X} (hx : MapClusterPt x l u)
    {g : X → β} (hg : LowerSemicontinuous g) {c : β} {ε : ι → β} (hε : Tendsto ε l (𝓝 0))
    (hu : ∀ᶠ i in l, g (u i) ≤ c + ε i) : g x ≤ c := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ (hg.isClosed_preimage (c + δ)).mem_of_mapClusterPt hx ?_
  filter_upwards [hu, hε.eventually (eventually_le_nhds hδ)] with i hi hεi
  exact hi.trans (add_le_add_right hεi c)

end MapClusterPt

section FiniteRange

open Filter Set

namespace TauCeti

section Eventually

variable {α ι : Type*} {β : ι → Type*} [TopologicalSpace α] [∀ i, LinearOrder (β i)]

/-- If each coordinate of `f` is upper semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `f x' ≤ f x` eventually in `𝓝[s] x`. -/
theorem eventually_le_of_upperSemicontinuousWithinAt {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝[s] x, f x' ≤ f x := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  obtain ⟨u, hu, hufin⟩ := hfin
  have hV : {v ∈ f '' u | ¬ v ≤ f x}.Finite := hufin.subset (sep_subset _ _)
  have hex : ∃ᶠ x' in 𝓝[s] x, ∃ v ∈ {v ∈ f '' u | ¬ v ≤ f x}, f x' = v :=
    (hnot.and_eventually hu).mono fun x' ⟨hnotle, hx'⟩ ↦ ⟨f x', ⟨⟨x', hx', rfl⟩, hnotle⟩, rfl⟩
  obtain ⟨v, ⟨-, hnotle⟩, hvfreq⟩ := hV.frequently_exists.mp hex
  exact hnotle fun i ↦
    (hf i).frequently (v i) (hvfreq.mono fun _ hx' ↦ (congr_fun hx' i).symm.le)

/-- If each coordinate of `f` is upper semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `f x' ≤ f x` eventually in `𝓝 x`. -/
theorem eventually_le_of_upperSemicontinuousAt {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, UpperSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝 x, f x' ≤ f x := by
  rw [← nhdsWithin_univ]
  refine eventually_le_of_upperSemicontinuousWithinAt
    (fun i ↦ (hf i).upperSemicontinuousWithinAt univ) ?_
  rwa [nhdsWithin_univ]

/-- If each coordinate of `f` is lower semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `f x ≤ f x'` eventually in `𝓝[s] x`. -/
theorem eventually_ge_of_lowerSemicontinuousWithinAt {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝[s] x, f x ≤ f x' := by
  let f' : α → ∀ i, (β i)ᵒᵈ := fun a i ↦ OrderDual.toDual (f a i)
  have hf' : ∀ i, UpperSemicontinuousWithinAt (f' · i) s x := fun i y hy ↦
    (hf i (OrderDual.ofDual y) (OrderDual.toDual_lt.mp hy)).mono
      fun _ hx' ↦ OrderDual.toDual_lt.mpr hx'
  have hfin' : ∃ u ∈ 𝓝[s] x, (f' '' u).Finite := by
    obtain ⟨u, hu, hufin⟩ := hfin
    refine ⟨u, hu, ?_⟩
    rw [← Set.image_image (fun v i ↦ OrderDual.toDual (v i)) f u]
    exact hufin.image _
  exact (eventually_le_of_upperSemicontinuousWithinAt hf' hfin').mono
    fun _ hx' i ↦ OrderDual.toDual_le_toDual.mp (hx' i)

/-- If each coordinate of `f` is lower semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `f x ≤ f x'` eventually in `𝓝 x`. -/
theorem eventually_ge_of_lowerSemicontinuousAt {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, LowerSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝 x, f x ≤ f x' := by
  rw [← nhdsWithin_univ]
  refine eventually_ge_of_lowerSemicontinuousWithinAt
    (fun i ↦ (hf i).lowerSemicontinuousWithinAt univ) ?_
  rwa [nhdsWithin_univ]

end Eventually

end TauCeti

section MonotoneComp

variable {α ι γ : Type*} {β : ι → Type*} [TopologicalSpace α] [∀ i, LinearOrder (β i)]
  [Preorder γ]

/-- Post-composing a coordinatewise upper semicontinuous locally finite family with a monotone map
preserves `UpperSemicontinuousWithinAt`. -/
theorem Monotone.upperSemicontinuousWithinAt_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousWithinAt (fun x' ↦ g (f x')) s x := fun _ hy ↦
  (TauCeti.eventually_le_of_upperSemicontinuousWithinAt hf hfin).mono
    fun _ hx' ↦ (hg hx').trans_lt hy

/-- Post-composing a coordinatewise upper semicontinuous locally finite family with a monotone map
preserves `UpperSemicontinuousAt`. -/
theorem Monotone.upperSemicontinuousAt_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, UpperSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuousAt (fun x' ↦ g (f x')) x := fun _ hy ↦
  (TauCeti.eventually_le_of_upperSemicontinuousAt hf hfin).mono
    fun _ hx' ↦ (hg hx').trans_lt hy

/-- Post-composing a coordinatewise upper semicontinuous locally finite family with a monotone map
preserves `UpperSemicontinuousOn`. -/
theorem Monotone.upperSemicontinuousOn_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, UpperSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousOn (fun x' ↦ g (f x')) s :=
  fun x hx ↦
    hg.upperSemicontinuousWithinAt_comp_of_locally_finite_image (fun i ↦ hf i x hx) (hfin x hx)

/-- Post-composing a coordinatewise upper semicontinuous locally finite family with a monotone map
preserves `UpperSemicontinuous`. -/
theorem Monotone.upperSemicontinuous_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i}
    (hf : ∀ i, UpperSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuous (fun x' ↦ g (f x')) :=
  fun x ↦ hg.upperSemicontinuousAt_comp_of_locally_finite_image (fun i ↦ hf i x) (hfin x)

/-- Post-composing a coordinatewise lower semicontinuous locally finite family with a monotone map
preserves `LowerSemicontinuousWithinAt`. -/
theorem Monotone.lowerSemicontinuousWithinAt_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousWithinAt (fun x' ↦ g (f x')) s x := fun _ hy ↦
  (TauCeti.eventually_ge_of_lowerSemicontinuousWithinAt hf hfin).mono
    fun _ hx' ↦ hy.trans_le (hg hx')

/-- Post-composing a coordinatewise lower semicontinuous locally finite family with a monotone map
preserves `LowerSemicontinuousAt`. -/
theorem Monotone.lowerSemicontinuousAt_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, LowerSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuousAt (fun x' ↦ g (f x')) x := fun _ hy ↦
  (TauCeti.eventually_ge_of_lowerSemicontinuousAt hf hfin).mono
    fun _ hx' ↦ hy.trans_le (hg hx')

/-- Post-composing a coordinatewise lower semicontinuous locally finite family with a monotone map
preserves `LowerSemicontinuousOn`. -/
theorem Monotone.lowerSemicontinuousOn_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, LowerSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousOn (fun x' ↦ g (f x')) s :=
  fun x hx ↦
    hg.lowerSemicontinuousWithinAt_comp_of_locally_finite_image (fun i ↦ hf i x hx) (hfin x hx)

/-- Post-composing a coordinatewise lower semicontinuous locally finite family with a monotone map
preserves `LowerSemicontinuous`. -/
theorem Monotone.lowerSemicontinuous_comp_of_locally_finite_image {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i}
    (hf : ∀ i, LowerSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuous (fun x' ↦ g (f x')) :=
  fun x ↦ hg.lowerSemicontinuousAt_comp_of_locally_finite_image (fun i ↦ hf i x) (hfin x)

end MonotoneComp

end FiniteRange
