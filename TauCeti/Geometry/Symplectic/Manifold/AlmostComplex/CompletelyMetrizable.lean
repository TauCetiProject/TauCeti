/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Topology
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Section.Complete
import TauCeti.Geometry.Manifold.VectorBundle.Section.CountableSeminorms

/-!
# Complete metrizability of spaces of smooth almost complex structures

Let `M` be a manifold without boundary whose model space is locally compact, and let `V` be a
smooth vector bundle over `M` with complete fibre model. For countably many covering frames on
sigma-compact domains, the space of smooth sections of `V` with the compact derivative topology
`ContMDiffSection.frameTopology` is complete and metrizable, hence completely metrizable. On a
Lindelöf manifold over a second countable model this holds for every covering frame system, since
the topology does not depend on the frames.

The smooth almost complex structures on a Lindelöf manifold without boundary and with
finite-dimensional model, with the `C^∞` topology
`TauCeti.SmoothAlmostComplexStructure.frameTopology` of a covering frame system, are a closed
subspace of the smooth sections of `End(TM)`, so they form a completely metrizable space and a
Baire space. For a smooth two-form `ω`, tameness is a `G_δ` condition and invariance a closed
condition in this topology (`TauCeti.SmoothTwoForm.isGδ_setOf_tames_frameTopology`,
`TauCeti.SmoothTwoForm.isClosed_setOf_invariant_frameTopology`), so the spaces of smooth `ω`-tame
and of smooth `ω`-compatible almost complex structures are also completely metrizable and Baire
spaces. These are the parameter spaces of the genericity theorems of pseudoholomorphic curve
theory.

## Main declarations

* `ContMDiffSection.isCompletelyMetrizableSpace_frameTopology_of_sigmaCompactDomains`,
  `ContMDiffSection.isCompletelyMetrizableSpace_frameTopology`: smooth sections of a vector bundle
  form a completely metrizable space.
* `TauCeti.SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology`,
  `TauCeti.SmoothAlmostComplexStructure.baireSpace_frameTopology`: on a Lindelöf manifold without
  boundary and with finite-dimensional model, the smooth almost complex structures form a
  completely metrizable space and a Baire space.
* `TauCeti.SmoothTwoForm.baireSpace_tames_frameTopology`,
  `TauCeti.SmoothTwoForm.baireSpace_compatible_frameTopology`: on such a manifold, the smooth tame
  and the smooth compatible structures form Baire spaces.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.2.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] [I.Boundaryless] [CompleteSpace F]
  [ENat.LEInfty n]

/-- For countably many covering frames on sigma-compact domains, over a manifold without boundary
with locally compact model, the smooth sections of a vector bundle with complete fibre model form
a completely metrizable space for the compact derivative topology. -/
theorem isCompletelyMetrizableSpace_frameTopology_of_sigmaCompactDomains [Countable ι]
    [∀ i, SigmaCompactSpace (U i)] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsCompletelyMetrizableSpace Cₛ^n⟮I; F, V⟯ := by
  let _ := frameUniformSpace (I := I) (n := n) e U hU
  have := isUniformAddGroup_frameUniformSpace (I := I) (n := n) e U hU
  have := completeSpace_frameTopology (I := I) (n := n) e U hU hcover
  have := metrizableSpace_frameTopology_of_sigmaCompactDomains (I := I) (n := n) e U hU hcover
  have := IsUniformAddGroup.uniformity_countably_generated (α := Cₛ^n⟮I; F, V⟯)
  infer_instance

/-- On a locally compact Lindelöf manifold without boundary over a second countable model space,
with locally compact model, the smooth sections of a vector bundle with complete fibre model form
a completely metrizable space for the compact derivative topology of any covering frame
system. -/
theorem isCompletelyMetrizableSpace_frameTopology [SecondCountableTopology H]
    [LocallyCompactSpace M] [LindelofSpace M] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsCompletelyMetrizableSpace Cₛ^n⟮I; F, V⟯ := by
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_lindelof H M
  let e' (x : M) := trivializationAt F V x
  let U' (x : M) : Opens M := ⟨(e' x).baseSet, (e' x).open_baseSet⟩
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable (fun x ↦ (U' x : Set M)) fun x ↦ (U' x).isOpen
  have := hT.to_subtype
  have hcover' (x : M) : ∃ i : T, x ∈ U' i := by
    have hx : x ∈ ⋃ y, (U' y : Set M) :=
      mem_iUnion.2 ⟨x, FiberBundle.mem_baseSet_trivializationAt _ _ x⟩
    rw [← hTU] at hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
    exact ⟨⟨y, hy⟩, hxy⟩
  have (i : T) : SigmaCompactSpace (U' i) := by
    have := (U' i).isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
    infer_instance
  have h := isCompletelyMetrizableSpace_frameTopology_of_sigmaCompactDomains (I := I) (n := n)
    (fun i : T ↦ e' i) (fun i ↦ U' i) (fun _ ↦ subset_rfl) hcover'
  rwa [frameTopology_eq_of_covers e U hU hcover (fun i : T ↦ e' i) (fun i ↦ U' i)
    (fun _ ↦ subset_rfl) hcover']

end ContMDiffSection

namespace TauCeti

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {ι : Type*}
  (e : ι → Trivialization (E →L[ℝ] E)
    (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [LindelofSpace M]

namespace SmoothAlmostComplexStructure

/-- On a Lindelöf manifold without boundary and with finite-dimensional model, the smooth almost
complex structures with the `C^∞` topology of any covering frame system form a completely
metrizable space. -/
theorem isCompletelyMetrizableSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    IsCompletelyMetrizableSpace (SmoothAlmostComplexStructure I M) := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  have := ContMDiffSection.isCompletelyMetrizableSpace_frameTopology (I := I) (n := ∞) e U hU
    hcover
  exact (isClosedEmbedding_toEndomorphism_frameTopology e U hU hcover).IsCompletelyMetrizableSpace

/-- On a Lindelöf manifold without boundary and with finite-dimensional model, the smooth almost
complex structures with the `C^∞` topology of any covering frame system form a Baire space. -/
theorem baireSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    BaireSpace (SmoothAlmostComplexStructure I M) := by
  let _ := frameTopology e U hU
  have := isCompletelyMetrizableSpace_frameTopology e U hU hcover
  infer_instance

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

/-- On a Lindelöf manifold without boundary and with finite-dimensional model, the smooth almost
complex structures tamed by a smooth two-form, with the `C^∞` topology of any covering frame
system, form a completely metrizable space. -/
theorem isCompletelyMetrizableSpace_tames_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsCompletelyMetrizableSpace {J : SmoothAlmostComplexStructure I M // form.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology e U hU hcover
  exact (isGδ_setOf_tames_frameTopology e U hU hcover form).isCompletelyMetrizableSpace

/-- On a Lindelöf manifold without boundary and with finite-dimensional model, the smooth almost
complex structures compatible with a smooth two-form, with the `C^∞` topology of any covering
frame system, form a completely metrizable space. -/
theorem isCompletelyMetrizableSpace_compatible_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsCompletelyMetrizableSpace {J : SmoothAlmostComplexStructure I M // form.Compatible J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology e U hU hcover
  have hset : {J : SmoothAlmostComplexStructure I M | form.Compatible J} =
      {J | form.Tames J} ∩ {J | form.Invariant J} := by
    ext J
    exact ⟨fun h ↦ ⟨h.tames, h.invariant⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  have hG : IsGδ {J : SmoothAlmostComplexStructure I M | form.Compatible J} := by
    rw [hset]
    exact (isGδ_setOf_tames_frameTopology e U hU hcover form).inter
      (isClosed_setOf_invariant_frameTopology e U hU hcover form).isGδ
  exact hG.isCompletelyMetrizableSpace

/-- On a Lindelöf manifold without boundary and with finite-dimensional model, the smooth almost
complex structures tamed by a smooth two-form, with the `C^∞` topology of any covering frame
system, form a Baire space. -/
theorem baireSpace_tames_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    BaireSpace {J : SmoothAlmostComplexStructure I M // form.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := isCompletelyMetrizableSpace_tames_frameTopology e U hU hcover form
  infer_instance

/-- On a Lindelöf manifold without boundary and with finite-dimensional model, the smooth almost
complex structures compatible with a smooth two-form, with the `C^∞` topology of any covering
frame system, form a Baire space. -/
theorem baireSpace_compatible_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    BaireSpace {J : SmoothAlmostComplexStructure I M // form.Compatible J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := isCompletelyMetrizableSpace_compatible_frameTopology e U hU hcover form
  infer_instance

end SmoothTwoForm

end TauCeti
