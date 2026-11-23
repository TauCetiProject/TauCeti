/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Invariant functions on a quotient covering

Let a countable group `G` act on a Lindelöf Borel space `M`, and let `q : M → N` be a quotient
covering map for this action (`IsQuotientCoveringMap q G`), such as the orbit projection of a free
action of a finite group by homeomorphisms. Let `μ` be a measure on `M` for which every
translation `x ↦ g • x` is quasi-measure-preserving. A function `f` on `M` is almost everywhere
`G`-invariant, `f (g • x) = f x` for almost every `x` and each `g`, exactly when it agrees almost
everywhere with `u ∘ q` for a strongly measurable function `u` on `N`.

One direction is immediate, since `q (g • x) = q x`. Conversely, `q` has a measurable section `s`
(`IsLocalHomeomorph.exists_measurable_rightInverse`); the point `s (q x)` lies in the orbit of
`x`, so `u = f ∘ s` works once `f` is replaced by a strongly measurable representative.

If moreover `μ.map q = C • ν` with `0 < C < ∞`, then the normalized pullback
`Lᵖ(ν) → Lᵖ(μ)`, `u ↦ C ^ (-1/p) • u ∘ q`, is a linear isometry
(`MeasureTheory.Lp.normalizedCompOfMapEqSmul`), and its range is exactly the subspace of
`G`-invariant elements of `Lᵖ(μ)`. For a closed Riemannian manifold `M` and a free isometric action,
`C = |G|` and `ν` is the Riemannian volume of the quotient; for `p = 2` the normalized pullback is
then a unitary map from `L²(M / G)` onto the `G`-invariant subspace of `L²(M)`.

## Main results

* `IsQuotientCoveringMap.exists_stronglyMeasurable_ae_eq_comp_iff`: a function is almost everywhere
  invariant exactly when it factors almost everywhere through `q`.
* `IsQuotientCoveringMap.mem_range_normalizedCompOfMapEqSmul_iff`: the range of the normalized
  pullback on `Lᵖ` is the subspace of invariant elements.

## References

* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Lemma 16, p. 159.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace IsQuotientCoveringMap

variable {M N E G : Type*} [TopologicalSpace M] [MeasurableSpace M] [TopologicalSpace N]
  [MeasurableSpace N] [Group G] [MulAction G M] {q : M → N} {μ : Measure M}

/-- **Invariant functions factor through a quotient covering.** If every translation by `G` is
quasi-measure-preserving for `μ`, then a function on `M` is almost everywhere `G`-invariant exactly
when it agrees almost everywhere with `u ∘ q` for a strongly measurable `u`. -/
theorem exists_stronglyMeasurable_ae_eq_comp_iff [BorelSpace M] [LindelofSpace M]
    [BorelSpace N] [Countable G] [TopologicalSpace E] (hq : IsQuotientCoveringMap q G)
    (hG : ∀ g : G, QuasiMeasurePreserving (g • ·) μ μ) {f : M → E}
    (hf : AEStronglyMeasurable f μ) :
    (∃ u : N → E, StronglyMeasurable u ∧ f =ᵐ[μ] u ∘ q) ↔
      ∀ g : G, (fun x ↦ f (g • x)) =ᵐ[μ] f := by
  refine ⟨fun ⟨u, _, hu⟩ g ↦ ?_, fun hinv ↦ ?_⟩
  · filter_upwards [(hG g).ae_eq_comp hu, hu] with x hgx hx
    simp only [Function.comp_apply, hq.map_smul] at hgx hx
    rw [hgx, hx]
  obtain ⟨s, hs, hqs⟩ := hq.isLocalHomeomorph.exists_measurable_rightInverse hq.surjective
  -- The strongly measurable representative `hf.mk f` is still almost everywhere invariant.
  have hinv' : ∀ᵐ x ∂μ, ∀ g : G, hf.mk f (g • x) = hf.mk f x := by
    refine ae_all_iff.2 fun g ↦ ?_
    filter_upwards [(hG g).ae_eq_comp hf.ae_eq_mk, hinv g, hf.ae_eq_mk] with x hgx hx hmk
    simp only [Function.comp_apply] at hgx
    rw [← hgx, hx, hmk]
  refine ⟨hf.mk f ∘ s, hf.stronglyMeasurable_mk.comp_measurable hs, ?_⟩
  filter_upwards [hf.ae_eq_mk, hinv'] with x hx hinvx
  -- The section sends `q x` into the orbit of `x`.
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.1 (hqs (q x))
  simp only [Function.comp_apply, ← hg, hinvx, hx]

/-- **The normalized pullback onto invariants.** Let `μ.map q = C • ν` with `0 < C < ∞`, and let
every translation by `G` be quasi-measure-preserving for `μ`. Then `h ∈ Lᵖ(μ)` lies in the range of
the normalized pullback `u ↦ C ^ (-1/p) • u ∘ q` from `Lᵖ(ν)` exactly when it is `G`-invariant. -/
theorem mem_range_normalizedCompOfMapEqSmul_iff [BorelSpace M] [LindelofSpace M]
    [BorelSpace N] [Countable G] {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {ν : Measure N}
    {C : ℝ≥0∞} (hq : IsQuotientCoveringMap q G)
    (hG : ∀ g : G, QuasiMeasurePreserving (g • ·) μ μ) (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hmap : μ.map q = C • ν) (h : Lp E p μ) :
    h ∈ Set.range (Lp.normalizedCompOfMapEqSmul 𝕜 hq.continuous.aemeasurable hC₀ hC hmap) ↔
      ∀ g : G, (fun x ↦ h (g • x)) =ᵐ[μ] h := by
  rw [Lp.mem_range_normalizedCompOfMapEqSmul_iff,
    hq.exists_stronglyMeasurable_ae_eq_comp_iff hG (Lp.aestronglyMeasurable h)]

end IsQuotientCoveringMap
