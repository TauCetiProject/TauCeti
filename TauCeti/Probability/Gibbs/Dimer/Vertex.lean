/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Dimer.Basic

/-!
# The vertex form of the dimer Gibbs property

Let `Λ` be a finite set of vertices and `F = E(Λ)` the edges with both endpoints in `Λ`
(`SimpleGraph.insideEdges`). A configuration `ω` matches `Λ` inside `Λ`
(`SimpleGraph.IsMatchedIn`) when every vertex of `Λ` lies in an edge of `F` of value `true`.

For a dimer configuration `ω` matching `Λ` inside `Λ`, the edges leaving `Λ` have value `false`,
so the completion set of `ω` at `F` consists of the gluings to `ω` of the perfect matchings of the
subgraph induced on `Λ`
(`SimpleGraph.IsDimerConfiguration.isDimerConfiguration_updateFinset_insideEdges_iff`), and the
partition function `Z^w_F(ω)` is the same for all such `ω`
(`SimpleGraph.dimerPartitionFunction_insideEdges_congr`): it is the partition function of the
dimer model on `Λ`.

**Vertex form** (`SimpleGraph.IsDimerGibbs.measure_eq_of_isMatchedIn`): for a dimer Gibbs measure
`μ` with positive weights, conditionally on the configuration off `F` (on a finite set `E ∖ F`,
where `E` contains every edge sharing a vertex with an edge of `F`) and on all vertices of `Λ` being
matched inside `Λ`, the configuration on `F` has the Boltzmann law: for every dimer configuration
`ω` matching `Λ` inside `Λ`,
`μ[ω]_E = w(ω ∩ F) / Z^w_F(ω) · μ([ω]_{E ∖ F} ∩ {Λ matched inside Λ})`.
The event that `Λ` is matched inside contains `[ω]_{E ∖ F}` up to a `μ`-null set
(`SimpleGraph.IsDimerGibbs.measure_inter_setOf_isMatchedIn`), so this is the cylinder identity
summed over the completion set
(`SimpleGraph.IsDimerGibbs.ofReal_mul_measure_setOf_forall_mem_notMem_eq`).

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Definition 13.4.
-/

public section

open MeasureTheory Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **The partition function inside `Λ` does not depend on the outside.** Two dimer configurations
matching every vertex of `Λ` inside `Λ` have the same partition function on the edges inside
`Λ`. -/
theorem dimerPartitionFunction_insideEdges_congr (w : G.edgeSet → ℝ) {Λ : Finset V}
    {ω₁ ω₂ : G.edgeSet → Bool} (h₁ : G.IsDimerConfiguration ω₁) (h₂ : G.IsDimerConfiguration ω₂)
    (hΛ₁ : G.IsMatchedIn Λ ω₁) (hΛ₂ : G.IsMatchedIn Λ ω₂) :
    G.dimerPartitionFunction w (G.insideEdges Λ) ω₁ =
      G.dimerPartitionFunction w (G.insideEdges Λ) ω₂ :=
  dimerPartitionFunction_congr_of_isDimerConfiguration w _ h₁ h₂ fun _ he hef =>
    h₁.eq_of_isMatchedIn h₂ hΛ₁ hΛ₂ he hef

variable {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)}

/-- Let `ω` be a dimer configuration matching every vertex of `Λ` inside `Λ`, and `E` a set
containing every edge sharing a vertex with an edge inside `Λ`. Under a dimer Gibbs measure, the
configurations agreeing with `ω` on `E` off the edges inside `Λ` almost surely match `Λ` inside
`Λ`. -/
theorem IsDimerGibbs.measure_inter_setOf_isMatchedIn (hμ : G.IsDimerGibbs w μ) {Λ : Finset V}
    {E : Finset G.edgeSet}
    (hE : ∀ e ∈ G.insideEdges Λ, ∀ e' : G.edgeSet,
      (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E)
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) (hΛ : G.IsMatchedIn Λ ω) :
    μ ({η | ∀ e ∈ E, e ∉ G.insideEdges Λ → η e = ω e} ∩ {η | G.IsMatchedIn Λ η}) =
      μ {η | ∀ e ∈ E, e ∉ G.insideEdges Λ → η e = ω e} := by
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hμ.ae_isDimerConfiguration] with η hη
  classical
  refine ⟨fun h => h.1, fun h => ⟨h, isMatchedIn_iff_subset.2 fun v hv => ?_⟩⟩
  obtain ⟨⟨f, hf, hvf⟩, hout⟩ := hω.mem_dimerCoveredVertices_iff.1 (isMatchedIn_iff_subset.1 hΛ hv)
  refine hη.mem_dimerCoveredVertices_iff.2 ⟨⟨f, hf, hvf⟩, fun e he hηe hve => ?_⟩
  exact hout e he (h e (hE f hf e ⟨v, hvf, hve⟩) he ▸ hηe) hve

/-- **The vertex form of the dimer Gibbs property.** Let `μ` be dimer Gibbs for a positive weight
`w`, `Λ` a finite set of vertices, and `E` a finite set containing every edge sharing a vertex with
an edge inside `Λ`. For every dimer configuration `ω` matching `Λ` inside `Λ`,
`μ[ω]_E = w(ω ∩ E(Λ)) / Z^w_{E(Λ)}(ω) · μ([ω]_{E ∖ E(Λ)} ∩ {Λ is matched inside Λ})`: conditionally
on the configuration outside `Λ` and on all vertices of `Λ` being matched inside `Λ`, the law on
the edges inside `Λ` is the Boltzmann law of the perfect matchings of `Λ`, whose partition function
does not depend on `ω` (`SimpleGraph.dimerPartitionFunction_insideEdges_congr`). -/
theorem IsDimerGibbs.measure_eq_of_isMatchedIn (hw : ∀ e, 0 < w e) (hμ : G.IsDimerGibbs w μ)
    {Λ : Finset V} {E : Finset G.edgeSet}
    (hE : ∀ e ∈ G.insideEdges Λ, ∀ e' : G.edgeSet,
      (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E)
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) (hΛ : G.IsMatchedIn Λ ω) :
    μ {η | ∀ e ∈ E, η e = ω e} =
      ENNReal.ofReal (G.dimerWeight w (G.insideEdges Λ) ω /
          G.dimerPartitionFunction w (G.insideEdges Λ) ω) *
        μ ({η | ∀ e ∈ E, e ∉ G.insideEdges Λ → η e = ω e} ∩ {η | G.IsMatchedIn Λ η}) := by
  rw [hμ.measure_inter_setOf_isMatchedIn hE hω hΛ,
    hμ.ofReal_mul_measure_setOf_forall_mem_notMem_eq hw hE hω]

end SimpleGraph
