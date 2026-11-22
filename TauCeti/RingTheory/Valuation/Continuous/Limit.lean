/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# Passage of continuous valuation bounds to limits

Let `v : Valuation A Γ₀` be a continuous valuation (`Valuation.IsContinuous`). By
`Valuation.IsContinuous.isClosed_ge` and `Valuation.IsContinuous.isClosed_le` (in
`TauCeti.RingTheory.Valuation.Continuous.Basic`), attained superlevel sets `{a | v b ≤ v a}` are
closed with no compatibility between the topology and the ring operations, and under
`[SeparatelyContinuousAdd A]` closed balls `{a | v a ≤ γ}` are closed for *every* `γ : Γ₀`,
attained or not.

Passing to topological limits along a nontrivial filter therefore preserves:
* attained lower bounds `v b ≤ v (f i)` (`Valuation.IsContinuous.ge_of_tendsto`), needing only a
  topology on `A`;
* upper bounds `v (f i) ≤ γ` for arbitrary `γ : Γ₀` (`Valuation.IsContinuous.le_of_tendsto`) —
  covering genuinely unattained thresholds `γ ∈ Γ₀ \ Set.range v` and applying directly to
  `γ = max (v x) (v y)` without case-splitting on `le_total (v x) (v y)` (including `γ = 0`, where
  `IsContinuous.isOpen_le`'s `v b ≠ 0` hypothesis fails), as needed when pulling continuous
  valuations back along limit constructions such as the tilt of a uniform Tate ring;
* eventually constant values `v (f i) = γ` (`Valuation.IsContinuous.eq_of_tendsto`).

## Main results

* `Valuation.IsContinuous.ge_of_tendsto` : preservation of attained lower bounds under limits,
  needing only a topology on `A`.
* `Valuation.IsContinuous.le_of_tendsto` and `Valuation.IsContinuous.eq_of_tendsto` : preservation
  of arbitrary upper bounds and eventually constant values under limits under
  `[SeparatelyContinuousAdd A]`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.7 and Remark 7.8.
-/

public section

namespace Valuation

open Filter Topology

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **Attained lower bounds pass to limits.** If `f` converges to `x` along a nontrivial filter and
`v b ≤ v (f i)` eventually, then `v b ≤ v x`. -/
theorem IsContinuous.ge_of_tendsto {v : Valuation A Γ₀} (hv : v.IsContinuous) {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → A} {x b : A} (hf : Tendsto f l (𝓝 x))
    (hle : ∀ᶠ i in l, v b ≤ v (f i)) : v b ≤ v x :=
  (hv.isClosed_ge b).mem_of_tendsto hf hle

section SeparatelyContinuousAdd

variable [SeparatelyContinuousAdd A]

/-- **Upper bounds pass to limits.** If `f` converges to `x` along a nontrivial filter and
`v (f i) ≤ γ` eventually, then `v x ≤ γ`. The bound `γ` may be any element of `Γ₀`. -/
theorem IsContinuous.le_of_tendsto {v : Valuation A Γ₀} (hv : v.IsContinuous) {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → A} {x : A} {γ : Γ₀} (hf : Tendsto f l (𝓝 x))
    (hle : ∀ᶠ i in l, v (f i) ≤ γ) : v x ≤ γ :=
  (hv.isClosed_le γ).mem_of_tendsto hf hle

/-- **Eventually constant values pass to limits.** If `f` converges to `x` along a nontrivial
filter and `v (f i) = γ` eventually, then `v x = γ`. -/
theorem IsContinuous.eq_of_tendsto {v : Valuation A Γ₀} (hv : v.IsContinuous) {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → A} {x : A} {γ : Γ₀} (hf : Tendsto f l (𝓝 x))
    (heq : ∀ᶠ i in l, v (f i) = γ) : v x = γ := by
  obtain ⟨i₀, rfl⟩ := heq.exists
  exact le_antisymm (hv.le_of_tendsto hf (heq.mono fun _ h ↦ h.le))
    (hv.ge_of_tendsto hf (heq.mono fun _ h ↦ h.ge))

end SeparatelyContinuousAdd

end Valuation
