/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Cofinite.Lift
public import Mathlib.Topology.Basic

/-!
# Lifting a convergent family along a surjection

A family `g : ι → N` converges to `n₀` along the cofinite filter when all but finitely many of its
members lie in any given neighbourhood of `n₀`. This file shows that a surjection which carries the
neighbourhood filter of `m₀` into that of `n₀` lifts such a family to one converging to `m₀`: the
lift can be chosen convergent, not merely made to exist.

**Openness is not the hypothesis, and would not suffice on its own.** `IsOpenMap φ` puts the image
of a neighbourhood of `m₀` around `φ m₀`, which is a neighbourhood of `n₀` only when `φ m₀ = n₀`.
The hypothesis used here is `𝓝 n₀ ≤ Filter.map φ (𝓝 m₀)`, which is exactly what the proof consumes;
a zero-preserving open surjection — an `A`-linear map, say — is one way to supply it, and that is
the form `TauCeti.Huber` uses it in.

That the lifts exist pointwise is only surjectivity. The content is that they can be chosen
*uniformly enough to still converge*, and this genuinely needs a construction: choosing a preimage
of `g α` for each `α` independently can leave the lifts spread out even when the `g α` collapse to
`n₀`. The fix is to choose the preimage of `g α` from a neighbourhood whose index grows with `α`,
so that convergence is forced by the choice rather than hoped for.

## Main results

* `exists_lift_tendsto_cofinite_nhds`: the lifting statement.

## Implementation notes

The proof applies `TauCeti.exists_lift_eventually_mem_cofinite` to an antitone basis of `𝓝 m₀`,
supplied by `Filter.exists_antitone_basis`. The filter inequality gives the required image
condition for each basis member. No algebraic structure is used.
-/

namespace TauCeti

open Filter Topology Set

public section

variable {ι : Type*} [Countable ι] {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- **A convergent family lifts to a convergent family.** If `φ` is surjective and carries the
neighbourhood filter of `m₀` into that of `n₀`, then any family tending to `n₀` cofinitely has a
`φ`-preimage family tending to `m₀` cofinitely.

Pointwise lifting is surjectivity alone; the statement is that a *single* choice of lifts can be
made to converge. Note that `IsOpenMap φ` supplies the filter hypothesis only together with
`φ m₀ = n₀`; openness by itself places the images around `φ m₀`, not around `n₀`.

**Two countability hypotheses are essential**, and both are instance arguments rather than
explicit ones. `[(𝓝 m₀).IsCountablyGenerated]` is what produces the antitone basis the lifts are
drawn from, and `[Countable ι]` — from the variable block — is what supplies the injection
`ι ↪ ℕ` that caps the construction. Neither is bookkeeping: without the first there is no
sequence of neighbourhoods to index, and without the second the cap has nothing to grow along. -/
theorem exists_lift_tendsto_cofinite_nhds {m₀ : M} {n₀ : N} [(𝓝 m₀).IsCountablyGenerated]
    (φ : M → N) (hsurj : Function.Surjective φ) (hmap : 𝓝 n₀ ≤ Filter.map φ (𝓝 m₀))
    (g : ι → N) (hg : Tendsto g (Filter.cofinite : Filter ι) (𝓝 n₀)) :
    ∃ f : ι → M, (∀ α, φ (f α) = g α) ∧ Tendsto f (Filter.cofinite : Filter ι) (𝓝 m₀) := by
  obtain ⟨V, hV⟩ := (𝓝 m₀).exists_antitone_basis
  have hVmem : ∀ i, φ '' V i ∈ 𝓝 n₀ := fun i ↦ hmap (Filter.image_mem_map (hV.mem i))
  obtain ⟨f, hf, hbound⟩ := exists_lift_eventually_mem_cofinite φ hsurj
    (fun i _ ↦ V i) (fun _ ↦ hV.antitone) g (fun i ↦ hg.eventually_mem (hVmem i))
  exact ⟨f, hf, hV.toHasBasis.tendsto_right_iff.mpr fun i _ ↦ hbound i⟩

end

end TauCeti
