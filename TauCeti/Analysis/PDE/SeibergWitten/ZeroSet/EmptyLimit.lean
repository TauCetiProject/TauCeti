/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Limit
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# An empty limit zero set forces the twisting line bundle to be trivial

Consider solutions of the Seiberg–Witten equations on a closed symplectic four-manifold `X` at
parameters `rᵢ → ∞`, twisted by a line bundle `E`, with normalized spinors `χᵢ = αᵢ u₀ + βᵢ`, where
`αᵢ` is a section of `E`, `sᵢ = |αᵢ|²` and zero sets `Zᵢ = αᵢ⁻¹(0)`. Along a subsequence the zero
sets converge in the Hausdorff distance to a closed set `Z`, the support of the limiting curve
(`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Limit`). This file treats the case where the limit is
empty.

When `X` is compact and `Z = ∅`, the compact-set vacuum
`TauCeti.SeibergWitten.eventually_forall_lt_of_tendsto` applies with `K = X`, so for every `σ < 1`
eventually `σ < sᵢ` on all of `X`. With `σ = 0`, eventually `αᵢ` vanishes nowhere
(`TauCeti.SeibergWitten.eventually_forall_ne_zero_of_tendsto_bot`), so it trivializes the line
bundle `E` (`TauCeti.SeibergWitten.exists_trivialization_baseSet_eq_univ_of_tendsto_bot`): `E` has
a linear trivialization over the whole of `X`, given by `αᵢ` through
`TauCeti.VectorBundle.sectionTrivialization`. This is a statement about the actual topological line
bundle, including its torsion: the vanishing of the real Chern class, which is all that weak
convergence of the curvature currents to zero detects, would not suffice.

Contrapositively, if `E` has no linear trivialization over `X`, for instance if `c₁(E)` is a
nonzero torsion class, then no such sequence of solutions has an empty limit zero set.

As in `TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Limit`, the analytic input is Taubes's off-zero
bound `w₊ ≤ (C / r) w₊ + C / r + C exp (-c R / h)`, `w₊ = max (1 - |α|²) 0`, taken as a hypothesis,
and the statements hold along an arbitrary filter, for instance along a subsequence.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Bundle Filter Real Set TopologicalSpace Topology

namespace TauCeti.SeibergWitten

variable {X : Type*} [MetricSpace X] [CompactSpace X] {ι : Type*} {l : Filter ι}
  {s : ι → X → ℝ} {Z : ι → Closeds X} {r h : ι → ℝ}

variable {E : X → Type*} {α : ι → ∀ x, E x}

/-- **An empty limit zero set forces the sections to vanish nowhere.** Let `α i` be sections of a
bundle `E` over a compact metric space `X`, and `s i` real functions with `s i x ≤ 0` wherever
`α i x = 0`, such as `s i x = ‖α i x‖ ^ 2`. Let closed sets `Z i` converge in the Hausdorff distance
to the empty set along `l`, while `r i → ∞` and `h i → 0⁺`, and let `c > 0`. If eventually the
off-zero bound `max (1 - s i x) 0 ≤ (C / r i) max (1 - s i x) 0 + C / r i + C exp (-c R / h i)`
holds at every point `x`, for every radius `R ≥ c₀ h i` of an open ball about `x` missing `Z i`,
then eventually `α i` vanishes nowhere. -/
theorem eventually_forall_ne_zero_of_tendsto_bot [∀ x, Zero (E x)] (C c c₀ : ℝ) (hc : 0 < c)
    (hr : Tendsto r l atTop) (hh : Tendsto h l (𝓝 0)) (hZ : Tendsto Z l (𝓝 ⊥))
    (hh₀ : ∀ᶠ i in l, 0 < h i)
    (hbound : ∀ᶠ i in l, ∀ x, ∀ R, c₀ * h i ≤ R → (∀ z ∈ Z i, R ≤ dist x z) →
      max (1 - s i x) 0 ≤ C / r i * max (1 - s i x) 0 + C / r i + C * exp (-(c * R / h i)))
    (hα : ∀ i x, α i x = 0 → s i x ≤ 0) :
    ∀ᶠ i in l, ∀ x, α i x ≠ 0 := by
  -- The limit is empty, so the compact-set vacuum applies on all of `X`, with `σ = 0`.
  have hK : Disjoint (univ : Set X) ((⊥ : Closeds X) : Set X) := by simp
  filter_upwards [eventually_forall_lt_of_tendsto C c c₀ hc zero_lt_one hr hh hZ isCompact_univ
    hK hh₀ (hbound.mono fun i hi x _ ↦ hi x)] with i hi x hx
  exact (hi x (mem_univ x)).not_ge (hα i x hx)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace 𝕜 E)] [FiberBundle 𝕜 E]
  [VectorBundle 𝕜 𝕜 E]

/-- **The empty-limit vacuum forces the line bundle to be trivial.** Let `α i` be continuous
sections of a line bundle `E` over a compact metric space `X`, and `s i` real functions with
`s i x ≤ 0` wherever `α i x = 0`, such as `s i x = ‖α i x‖ ^ 2`. If the closed sets `Z i` converge
to the empty set along a nontrivial filter and the off-zero bound of
`TauCeti.SeibergWitten.eventually_forall_ne_zero_of_tendsto_bot` holds, then `E` has a linear
trivialization over the whole of `X`. -/
theorem exists_trivialization_baseSet_eq_univ_of_tendsto_bot [l.NeBot] (C c c₀ : ℝ) (hc : 0 < c)
    (hr : Tendsto r l atTop) (hh : Tendsto h l (𝓝 0)) (hZ : Tendsto Z l (𝓝 ⊥))
    (hh₀ : ∀ᶠ i in l, 0 < h i)
    (hbound : ∀ᶠ i in l, ∀ x, ∀ R, c₀ * h i ≤ R → (∀ z ∈ Z i, R ≤ dist x z) →
      max (1 - s i x) 0 ≤ C / r i * max (1 - s i x) 0 + C / r i + C * exp (-(c * R / h i)))
    (hα : ∀ i x, α i x = 0 → s i x ≤ 0)
    (hαc : ∀ i, Continuous fun x ↦ TotalSpace.mk' 𝕜 x (α i x)) :
    ∃ e : Trivialization 𝕜 (π 𝕜 E), e.IsLinear 𝕜 ∧ e.baseSet = univ := by
  obtain ⟨i, hi⟩ := (eventually_forall_ne_zero_of_tendsto_bot C c c₀ hc hr hh hZ hh₀ hbound
    hα).exists
  exact VectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_continuous_forall_ne_zero.2
    ⟨α i, hαc i, hi⟩

end TauCeti.SeibergWitten
