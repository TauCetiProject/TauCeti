/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Complete
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CountableSeminorms
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The compact derivative topology on bundle sections is completely metrizable

Let `V` be a smooth vector bundle with Banach model fibre `F` over a boundaryless manifold `M`
modelled on a locally compact normed space over `ℝ` or `ℂ`. Its `C^n` sections, for finite or
smooth regularity `n`, carry the compact derivative topology `ContMDiffSection.frameTopology` of
any covering system of smooth frames, which does not depend on the covering system
(`ContMDiffSection.frameTopology_eq_of_covers`). For instance the `C^k` vector fields on `M` are
the `C^k` sections of its tangent bundle.

This file proves that for a second-countable base this topology is completely metrizable
(`ContMDiffSection.isCompletelyMetrizableSpace_frameTopology`), hence a Baire space
(`ContMDiffSection.baireSpace_frameTopology`): a countable intersection of open dense sets of
sections is dense. This is the parameter space of the genericity theorems for vector fields and
other sections on a manifold that need not be compact, such as the Kupka–Smale theorem, where a
property is shown to hold on a countable intersection of open dense sets of fields, one for each
compact window of a countable exhaustion of the base. On a noncompact base the space is not
normable, so the Baire property cannot come from a Banach space structure.

The proof assembles three existing facts. A countable covering frame system with sigma-compact
domains gives a metrizable topology
(`ContMDiffSection.metrizableSpace_frameTopology_of_sigmaCompactDomains`); the space is complete
for the uniform structure of this topological additive group
(`ContMDiffSection.completeSpace_frameTopology`); and a metrizable topological additive group has
a countably generated uniformity, so it carries a complete compatible metric. On a
second-countable base every covering frame system has a countable subcover, whose domains are
open in a locally compact second-countable space and hence sigma-compact, and the subcover
induces the same topology.

## Main results

* `ContMDiffSection.isCompletelyMetrizableSpace_frameTopology_of_countable`: for a countable
  covering frame system with sigma-compact domains, the sections form a completely metrizable
  space.
* `ContMDiffSection.isCompletelyMetrizableSpace_frameTopology`: on a second-countable base, the
  same for every covering frame system.
* `ContMDiffSection.baireSpace_frameTopology`: on a second-countable base, the sections form a
  Baire space.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §4, where the spaces of `C^r` maps are
  shown to be Baire spaces.
* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2, for the Baire spaces of vector fields in the Kupka–Smale theorem.
-/

public section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M] [ENat.LEInfty n]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- **Sections are completely metrizable, for a countable frame cover.** For a countable covering
system of smooth frames with sigma-compact domains, the `C^n` sections of a vector bundle with
Banach model fibre, for finite or smooth regularity `n`, form a completely metrizable space in the
compact derivative topology. -/
theorem isCompletelyMetrizableSpace_frameTopology_of_countable [Countable ι]
    [∀ i, SigmaCompactSpace (U i)] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsCompletelyMetrizableSpace Cₛ^n⟮I; F, V⟯ := by
  let _ := frameUniformSpace (I := I) (n := n) e U hU
  have := isUniformAddGroup_frameUniformSpace (I := I) (n := n) e U hU
  have := completeSpace_frameTopology (I := I) (n := n) e U hU hcover
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  have := metrizableSpace_frameTopology_of_sigmaCompactDomains (I := I) (n := n) e U hU hcover
  have : (uniformity Cₛ^n⟮I; F, V⟯).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  infer_instance

/-- **Sections are completely metrizable.** Over a second-countable boundaryless manifold
modelled on a locally compact space over `ℝ` or `ℂ`, the `C^n` sections of a vector bundle with
Banach model fibre, for finite or smooth regularity `n`, form a completely metrizable space in the
compact derivative topology of any covering system of smooth frames. -/
theorem isCompletelyMetrizableSpace_frameTopology [SecondCountableTopology M]
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsCompletelyMetrizableSpace Cₛ^n⟮I; F, V⟯ := by
  -- Pass to a countable subcover, which induces the same topology.
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable (fun i ↦ (U i : Set M)) fun i ↦ (U i).isOpen
  have := hT.to_subtype
  have hcover' : ∀ x, ∃ j : T, x ∈ U j := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    have hx : x ∈ ⋃ i ∈ T, (U i : Set M) := hTU ▸ mem_iUnion.2 ⟨i, hi⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
    exact ⟨⟨j, hj⟩, hxj⟩
  -- The frame domains are open in a locally compact second-countable space.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have (j : T) : SigmaCompactSpace (U j) :=
    have := (U j).isOpen.locallyCompactSpace
    inferInstance
  rw [frameTopology_eq_of_covers (I := I) (n := n) e U hU hcover (fun j : T ↦ e j)
    (fun j ↦ U j) (fun j ↦ hU j) hcover']
  exact isCompletelyMetrizableSpace_frameTopology_of_countable (I := I) (n := n)
    (fun j : T ↦ e j) (fun j ↦ U j) (fun j ↦ hU j) hcover'

/-- **Sections form a Baire space.** Over a second-countable boundaryless manifold modelled on a
locally compact space over `ℝ` or `ℂ`, the `C^n` sections of a vector bundle with Banach model
fibre, for finite or smooth regularity `n`, form a Baire space in the compact derivative topology
of any covering system of smooth frames: a countable intersection of open dense sets of sections
is dense. -/
theorem baireSpace_frameTopology [SecondCountableTopology M] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    BaireSpace Cₛ^n⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have := isCompletelyMetrizableSpace_frameTopology (I := I) (n := n) e U hU hcover
  infer_instance

end ContMDiffSection
