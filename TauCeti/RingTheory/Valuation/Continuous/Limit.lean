/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# Closedness of valuation bounds and passage to limits

Let `v : Valuation A Γ₀` be a continuous valuation (`Valuation.IsContinuous`). While `{a | v a < γ}`
is only guaranteed to be open at *attained* thresholds `γ = v b` (see the module docstring of
`TauCeti.RingTheory.Valuation.Continuous.Basic`), the opposite strict inequality behaves uniformly
across the entire codomain `Γ₀` as soon as addition is separately continuous: any `x` with
`γ < v x` satisfies `v x ≠ 0`, so `v` is locally constant at `x` (`IsContinuous.eventually_eq`).

Consequently:
* `{a | v b ≤ v a}` is closed for every `b : A`, with no compatibility between the topology and the
  ring operations (`Valuation.IsContinuous.isClosed_ge`);
* under `[SeparatelyContinuousAdd A]`, `{a | γ < v a}` is open and `{a | v a ≤ γ}` is closed for
  *every* `γ : Γ₀`, attained or not (`Valuation.IsContinuous.isOpen_gt`,
  `Valuation.IsContinuous.isClosed_le`).

Passing to topological limits along a nontrivial filter then preserves upper bounds `v (f i) ≤ γ`
for arbitrary `γ : Γ₀` (`Valuation.IsContinuous.le_of_tendsto`) — in particular at
`γ = max (v x) (v y)`, which need not be attained when `v x = 0` and `v y = 0` or in general before
case-splitting, and which underlies pulling continuous valuations back along limit constructions
such as the tilt of a uniform Tate ring — as well as attained lower bounds `v b ≤ v (f i)`
(`Valuation.IsContinuous.ge_of_tendsto`).

## Main results

* `Valuation.IsContinuous.isClosed_ge` and `Valuation.IsContinuous.ge_of_tendsto` : closedness of
  `{a | v b ≤ v a}` and preservation of attained lower bounds under limits, needing only a topology
  on `A`.
* `Valuation.IsContinuous.isOpen_gt` and `Valuation.IsContinuous.isClosed_le` : openness of
  `{a | γ < v a}` and closedness of `{a | v a ≤ γ}` for arbitrary `γ : Γ₀` under
  `[SeparatelyContinuousAdd A]`.
* `Valuation.IsContinuous.le_of_tendsto` and `Valuation.IsContinuous.eq_of_tendsto` : preservation
  of arbitrary upper bounds and attained values under limits.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.7 and Remark 7.8.
-/

public section

namespace Valuation

open Filter Set Topology

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **Attained superlevel sets of a continuous valuation are closed.** For every `b : A`, the set
`{a | v b ≤ v a}` is the complement of the defining open `{a | v a < v b}`, so no compatibility
between the topology and the ring operations is required. -/
theorem IsContinuous.isClosed_ge {v : Valuation A Γ₀} (hv : v.IsContinuous) (b : A) :
    IsClosed {a : A | v b ≤ v a} := by
  have hcompl : ({a : A | v a < v b} : Set A)ᶜ = {a : A | v b ≤ v a} := by
    ext a
    simp
  exact hcompl ▸ (isContinuous_def.mp hv b).isClosed_compl

/-- **Attained lower bounds pass to limits.** If `f` converges to `x` along a nontrivial filter and
`v b ≤ v (f i)` eventually, then `v b ≤ v x`. -/
theorem IsContinuous.ge_of_tendsto {v : Valuation A Γ₀} (hv : v.IsContinuous) {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → A} {x b : A} (hf : Tendsto f l (𝓝 x))
    (hle : ∀ᶠ i in l, v b ≤ v (f i)) : v b ≤ v x :=
  (hv.isClosed_ge b).mem_of_tendsto hf hle

section SeparatelyContinuousAdd

variable [SeparatelyContinuousAdd A]

/-- **Strict superlevel sets `{a | γ < v a}` are open for every `γ : Γ₀`**, whether or not `γ` lies
in the value group: `γ < v x` forces `v x ≠ 0`, and off its support `v` is locally constant
(`IsContinuous.eventually_eq`). -/
theorem IsContinuous.isOpen_gt {v : Valuation A Γ₀} (hv : v.IsContinuous) (γ : Γ₀) :
    IsOpen {a : A | γ < v a} := by
  refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  have hx0 : v x ≠ 0 := ne_of_gt (zero_le.trans_lt hx)
  filter_upwards [hv.eventually_eq hx0] with y hy
  exact hy.symm ▸ hx

/-- **Closed balls `{a | v a ≤ γ}` are closed for every `γ : Γ₀`.** For `γ = 0` this recovers
closedness of the support (`IsContinuous.isClosed_supp`, without needing commutativity of `A`). -/
theorem IsContinuous.isClosed_le {v : Valuation A Γ₀} (hv : v.IsContinuous) (γ : Γ₀) :
    IsClosed {a : A | v a ≤ γ} := by
  have hcompl : ({a : A | γ < v a} : Set A)ᶜ = {a : A | v a ≤ γ} := by
    ext a
    simp
  exact hcompl ▸ (hv.isOpen_gt γ).isClosed_compl

/-- **Upper bounds pass to limits.** If `f` converges to `x` along a nontrivial filter and
`v (f i) ≤ γ` eventually, then `v x ≤ γ`. The bound `γ` may be any element of `Γ₀`. -/
theorem IsContinuous.le_of_tendsto {v : Valuation A Γ₀} (hv : v.IsContinuous) {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → A} {x : A} {γ : Γ₀} (hf : Tendsto f l (𝓝 x))
    (hle : ∀ᶠ i in l, v (f i) ≤ γ) : v x ≤ γ :=
  (hv.isClosed_le γ).mem_of_tendsto hf hle

/-- **Attained values pass to limits.** If `f` converges to `x` along a nontrivial filter and
`v (f i) = v b` eventually, then `v x = v b`. -/
theorem IsContinuous.eq_of_tendsto {v : Valuation A Γ₀} (hv : v.IsContinuous) {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → A} {x b : A} (hf : Tendsto f l (𝓝 x))
    (heq : ∀ᶠ i in l, v (f i) = v b) : v x = v b :=
  le_antisymm (hv.le_of_tendsto hf (heq.mono fun _ h ↦ h.le))
    (hv.ge_of_tendsto hf (heq.mono fun _ h ↦ h.ge))

end SeparatelyContinuousAdd

end Valuation
