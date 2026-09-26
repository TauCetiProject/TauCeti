/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Order.BigOperators.Sum.Slack

/-!
# Lower bounds that saturate a limit of the sum are limits

Let `f i` be a finite family of functions into a linearly ordered field. If every `f i` is
eventually above each value below `c i`, so that `c i` is a lower bound for its lower limit, and
the sum `∑ i, f i` is eventually below each value above `∑ i, c i`, then every `f i` tends to
`c i`: the lower bounds of the other members leave room for no more than `c i` in the sum.

The two hypotheses are the two halves of `tendsto_order`, the lower half for each member and the
upper half for the sum. No boundedness is assumed, so the statement avoids the side conditions of
`Filter.liminf` and `Filter.limsup`.

This is how a one-sided estimate becomes an asymptotic: an argument that exhibits enough mass in
each member of a finite partition, and cannot see that there is no more, still determines every
member once the total is known.

The analogous Dirichlet-density squeeze is
`NumberField.Set.hasDirichletDensity_of_squeeze`.

## Main results

* `TauCeti.tendsto_of_forall_eventually_lt_of_eventually_sum_lt`: lower bounds on the members of
  a finite family whose sum is bounded above by the sum of the bounds are limits.
-/

public section

namespace TauCeti

open Filter Topology

/-- **Lower bounds that saturate the sum are limits.** Let `f i`, for `i ∈ s`, be functions into a
linearly ordered field with the order topology. If for every `i ∈ s` each value below `c i` is
eventually exceeded by `f i`, and each value above `∑ i ∈ s, c i` eventually exceeds
`∑ i ∈ s, f i`, then `f i₀` tends to `c i₀` for every `i₀ ∈ s`.

The hypotheses are the lower half of `tendsto_order` for each member and the upper half for the
sum; the upper half for a member is manufactured from the other members' lower bounds. -/
theorem tendsto_of_forall_eventually_lt_of_eventually_sum_lt {ι α 𝕜 : Type*} [Field 𝕜]
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    {l : Filter α} {s : Finset ι} {f : ι → α → 𝕜} {c : ι → 𝕜}
    (hlow : ∀ i ∈ s, ∀ b < c i, ∀ᶠ x in l, b < f i x)
    (hsum : ∀ b > ∑ i ∈ s, c i, ∀ᶠ x in l, ∑ i ∈ s, f i x < b) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    Tendsto (f i₀) l (𝓝 (c i₀)) := by
  classical
  refine tendsto_order.2 ⟨hlow i₀ hi₀, fun a ha ↦ ?_⟩
  -- Share the room `a - c i₀` between the sum and the `#s - 1` other members.
  set η := (a - c i₀) / s.card
  have hcard : (0 : 𝕜) < s.card := by exact_mod_cast Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hη : 0 < η := div_pos (sub_pos.mpr ha) hcard
  have hoth : ∀ᶠ x in l, ∀ i ∈ s.erase i₀, c i - η < f i x :=
    (eventually_all_finset _).2 fun i hi ↦
      hlow i (Finset.mem_of_mem_erase hi) _ (sub_lt_self _ hη)
  filter_upwards [hsum _ (lt_add_of_pos_right _ hη), hoth] with x hx hx'
  have hrest := Finset.sum_sub_le_sum_of_forall_sub_le (fun i hi ↦ (hx' i hi).le) le_rfl
  rw [← Finset.add_sum_erase _ _ hi₀, ← Finset.add_sum_erase s c hi₀] at hx
  rw [nsmul_eq_mul, Finset.card_erase_of_mem hi₀,
    Nat.cast_pred (Finset.card_pos.mpr ⟨i₀, hi₀⟩)] at hrest
  -- The other members use up `(#s - 1) η` of the room and the sum the last `η`.
  have hηa : ((s.card : 𝕜) - 1) * η = a - c i₀ - η := by
    rw [sub_mul, mul_div_cancel₀ _ hcard.ne', one_mul]
  linarith

end TauCeti
