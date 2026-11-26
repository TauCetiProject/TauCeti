/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import TauCeti.Analysis.Complex.QuasiPeriodic.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Complex.QuasiPeriodic.CauchyRiemann
import TauCeti.Topology.Covering.Periodic

/-!
# Unbranched covers of a torus in its normal model lie on the zero section

Let `C` be an embedded pseudoholomorphic torus in a symplectic four-manifold, a square-zero class
orthogonal to the canonical class, and write `C = ℂ ⧸ Λ` for a lattice `Λ`. Over the universal
cover `ℂ` of `C`, in a `Λ`-periodic unitary frame of the normal line, the normal Cauchy–Riemann
operator of `C` reads `D v = ∂bar v + ν v + μ conj v`, and the graph of a map `v : ℂ → ℂ` is
holomorphic for the normal model structure `J_N` exactly when `D v = 0`
(`TauCeti.isJHolomorphic_graph_normalModelStructure_iff`).

In Taubes's analysis of Seiberg–Witten solutions concentrating along `C` with a multiplicity, the
limit is a holomorphic cycle in the total space of the normal bundle. Each of its components that
is not contained in a fibre is an embedded torus whose projection to `C` is an unbranched covering
(`FiniteHolomorphicMap.isCoveringMap_and_genus_eq_one_and_singularity_eq_zero`). Lifted to the
universal cover, such a component is a set `E ⊆ ℂ × ℂ`, invariant under the deck translations by
`Λ`, whose projection to the base `ℂ` is a covering map with finite fibres, and which near each of
its points is the graph of a local solution of `D v = 0`.

The torus `C` is *nondegenerate on its finite covers* when, for every subgroup `L' ≤ Λ` of finite
index, the operator `D` pulled back to the covering torus `ℂ ⧸ L'` has no kernel: every
`L'`-periodic solution of `D v = 0` vanishes. This file shows that under this condition the
component lies on the zero section `C` (`TauCeti.snd_eq_zero_of_isCoveringMap`).

Indeed, since `ℂ` is simply connected, `E` is the union of the graphs of global continuous
sections, one through each of its points
(`IsCoveringMap.exists_continuous_forall_prodMk_mem`). Each section solves `D v = 0`, as it agrees
near every point with a local solution. There are finitely many sections, and the deck
translations permute them, so each one is periodic for a subgroup `L'` of finite index of `Λ`
(`IsCoveringMap.exists_relIndex_ne_zero_forall_add_eq`): it is a solution on the covering torus
`ℂ ⧸ L'`, a normal section of `C` pulled back to that cover. By nondegeneracy it vanishes.

The condition holds for the flat normal structure `D = ∂bar + c` with a constant `c` whose
holonomy has infinite order
(`TauCeti.eq_zero_of_conjWirtingerDeriv_add_mul_eq_zero_of_irrational`), which gives the
unconditional statement in that case (`TauCeti.snd_eq_zero_of_isCoveringMap_of_irrational`).

## Main results

* `TauCeti.snd_eq_zero_of_isCoveringMap`: a deck-invariant curve covering the torus without
  branching, locally the graph of solutions of `D v = 0`, lies on the zero section when `D` has
  no nonzero periodic solution on any finite covering torus.
* `TauCeti.snd_eq_zero_of_isCoveringMap_of_irrational`: the same for `D = ∂bar + c` with
  holonomy of infinite order, with no further hypothesis on `D`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (nondegeneracy of square-zero tori on their finite covers).
-/

public section

open Filter Topology ComplexConjugate Real

namespace TauCeti

variable {ν μ : ℂ → ℂ} {E : Set (ℂ × ℂ)}

/-- A continuous map whose graph lies in `E` solves `D v = 0` at every point, if `E` is near each
of its points contained in the graph of a local solution. -/
private theorem differentiableAt_and_conjWirtingerDeriv_add_add_eq_zero
    (hloc : ∀ q ∈ E, ∃ v : ℂ → ℂ, DifferentiableAt ℝ v q.1 ∧
      conjWirtingerDeriv v q.1 1 + ν q.1 * v q.1 + μ q.1 * conj (v q.1) = 0 ∧
      ∀ᶠ p in 𝓝 q, p ∈ E → p.2 = v p.1)
    {g : ℂ → ℂ} (hg : Continuous g) (hgE : ∀ z, (z, g z) ∈ E) (z₀ : ℂ) :
    DifferentiableAt ℝ g z₀ ∧
      conjWirtingerDeriv g z₀ 1 + ν z₀ * g z₀ + μ z₀ * conj (g z₀) = 0 := by
  obtain ⟨v, hv, heq, hEv⟩ := hloc _ (hgE z₀)
  -- Near `z₀` the graph of `g` stays in the region where `E` is the graph of `v`.
  have hgv : g =ᶠ[𝓝 z₀] v := by
    filter_upwards [((continuous_id.prodMk hg).tendsto z₀).eventually hEv] with z hz
    exact hz (hgE z)
  refine ⟨hv.congr_of_eventuallyEq hgv, ?_⟩
  rw [hgv.conjWirtingerDeriv_eq, hgv.self_of_nhds]
  exact heq

/-- **Unbranched covers of a nondegenerate torus lie on the zero section.** Let `E ⊆ ℂ × ℂ` be
invariant under the translations of the base by a subgroup `Λ`, with a finite fibre, such that
the projection of `E` to the base is a covering map and, near each of its points, `E` is
contained in the graph of a local solution of `D v = ∂bar v + ν v + μ conj v = 0`. Suppose that
for every subgroup `L' ≤ Λ` of finite index, every `L'`-periodic solution of `D v = 0` on `ℂ`
vanishes. Then every point of `E` lies on the zero section. -/
theorem snd_eq_zero_of_isCoveringMap (hE : IsCoveringMap fun q : E ↦ (q : ℂ × ℂ).1)
    {Λ : AddSubgroup ℂ} (hΛ : ∀ ω ∈ Λ, ∀ q ∈ E, (q.1 + ω, q.2) ∈ E) {z₀ : ℂ}
    (hfin : {w | (z₀, w) ∈ E}.Finite)
    (hloc : ∀ q ∈ E, ∃ v : ℂ → ℂ, DifferentiableAt ℝ v q.1 ∧
      conjWirtingerDeriv v q.1 1 + ν q.1 * v q.1 + μ q.1 * conj (v q.1) = 0 ∧
      ∀ᶠ p in 𝓝 q, p ∈ E → p.2 = v p.1)
    (hgap : ∀ L' : AddSubgroup ℂ, L' ≤ Λ → L'.relIndex Λ ≠ 0 → ∀ v : ℂ → ℂ,
      Differentiable ℝ v → (∀ z, conjWirtingerDeriv v z 1 + ν z * v z + μ z * conj (v z) = 0) →
      (∀ ω ∈ L', ∀ z, v (z + ω) = v z) → v = 0)
    {q : ℂ × ℂ} (hq : q ∈ E) : q.2 = 0 := by
  -- The point `q` lies on the graph of a global section `g`, periodic for some `L'`.
  obtain ⟨g, hg, hgE, hgq⟩ := hE.exists_continuous_forall_prodMk_mem hq
  obtain ⟨L', hL', hidx, hper⟩ := hE.exists_relIndex_ne_zero_forall_add_eq hΛ hfin hg hgE
  have hsol := differentiableAt_and_conjWirtingerDeriv_add_add_eq_zero hloc hg hgE
  rw [← hgq, hgap L' hL' hidx g (fun z ↦ (hsol z).1) (fun z ↦ (hsol z).2) hper, Pi.zero_apply]

/-- **Unbranched covers of a torus with irrational flat normal line lie on the zero section.** Let
`L ⊆ ℂ` be a lattice and let the normal operator be `D v = ∂bar v + c v` with a constant `c` such
that `Im (c conj ω₀) / π` is irrational for some `ω₀ ∈ L`. Let `E ⊆ ℂ × ℂ` be invariant under the
translations of the base by `L`, with a finite fibre, such that the projection of `E` to the base
is a covering map and, near each of its points, `E` is contained in the graph of a local solution
of `D v = 0`. Then every point of `E` lies on the zero section. -/
theorem snd_eq_zero_of_isCoveringMap_of_irrational {L : Submodule ℤ ℂ} [DiscreteTopology L]
    [IsZLattice ℝ L] {c ω₀ : ℂ} (hω₀L : ω₀ ∈ L) (hω₀ : Irrational ((c * conj ω₀).im / π))
    (hE : IsCoveringMap fun q : E ↦ (q : ℂ × ℂ).1) (hL : ∀ ω ∈ L, ∀ q ∈ E, (q.1 + ω, q.2) ∈ E)
    {z₀ : ℂ} (hfin : {w | (z₀, w) ∈ E}.Finite)
    (hloc : ∀ q ∈ E, ∃ v : ℂ → ℂ, DifferentiableAt ℝ v q.1 ∧
      conjWirtingerDeriv v q.1 1 + c * v q.1 = 0 ∧ ∀ᶠ p in 𝓝 q, p ∈ E → p.2 = v p.1)
    {q : ℂ × ℂ} (hq : q ∈ E) : q.2 = 0 :=
  snd_eq_zero_of_isCoveringMap (ν := fun _ ↦ c) (μ := 0) (Λ := L.toAddSubgroup) hE hL hfin
    (by simpa using hloc)
    (fun _ hL' hidx _ hv heq hper ↦
      eq_zero_of_conjWirtingerDeriv_add_mul_eq_zero_of_irrational hω₀L hω₀ hL' hidx hv
        (by simpa using heq) hper)
    hq

end TauCeti
