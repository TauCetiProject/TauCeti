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
import TauCeti.Geometry.Manifold.VectorBundle.Section.CompletelyMetrizable

/-!
# Complete metrizability of spaces of smooth almost complex structures

The smooth almost complex structures on a Lindelöf manifold with finite-dimensional model, with
the `C^∞` topology `TauCeti.SmoothAlmostComplexStructure.frameTopology` of a covering frame
system, are a closed subspace of the smooth sections of `End(TM)`, which form a completely
metrizable space
(`ContMDiffSection.isCompletelyMetrizableSpace_frameTopology`). So they form a completely
metrizable space and a Baire space. For a smooth two-form `ω`, tameness is a `G_δ` condition and
invariance a closed condition in this topology
(`TauCeti.SmoothTwoForm.isGδ_setOf_tames_frameTopology`,
`TauCeti.SmoothTwoForm.isClosed_setOf_invariant_frameTopology`), so the spaces of smooth `ω`-tame
and of smooth `ω`-compatible almost complex structures are also completely metrizable and Baire
spaces. These are the parameter spaces of the genericity theorems of pseudoholomorphic curve
theory.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology`,
  `TauCeti.SmoothAlmostComplexStructure.baireSpace_frameTopology`: on a Lindelöf manifold with
  finite-dimensional model, the smooth almost complex structures form a completely metrizable
  space and a Baire space.
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

variable [FiniteDimensional ℝ E] [LindelofSpace M]

namespace SmoothAlmostComplexStructure

/-- On a Lindelöf manifold with finite-dimensional model, the smooth almost complex structures with
the `C^∞` topology of any covering frame system form a completely metrizable space. -/
theorem isCompletelyMetrizableSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    IsCompletelyMetrizableSpace (SmoothAlmostComplexStructure I M) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  have := ContMDiffSection.isCompletelyMetrizableSpace_frameTopology (I := I) (n := ∞) e U hU
    hcover
  exact (isClosedEmbedding_toEndomorphism_frameTopology e U hU hcover).IsCompletelyMetrizableSpace

/-- On a Lindelöf manifold with finite-dimensional model, the smooth almost complex structures with
the `C^∞` topology of any covering frame system form a Baire space. -/
theorem baireSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    BaireSpace (SmoothAlmostComplexStructure I M) := by
  let _ := frameTopology e U hU
  have := isCompletelyMetrizableSpace_frameTopology e U hU hcover
  infer_instance

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

/-- On a Lindelöf manifold with finite-dimensional model, the smooth almost complex structures
tamed by a smooth two-form, with the `C^∞` topology of any covering frame system, form a completely
metrizable space. -/
theorem isCompletelyMetrizableSpace_tames_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsCompletelyMetrizableSpace {J : SmoothAlmostComplexStructure I M // form.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology e U hU hcover
  exact (isGδ_setOf_tames_frameTopology e U hU hcover form).isCompletelyMetrizableSpace

/-- On a Lindelöf manifold with finite-dimensional model, the smooth almost complex structures
compatible with a smooth two-form, with the `C^∞` topology of any covering frame system, form a
completely metrizable space. -/
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

/-- On a Lindelöf manifold with finite-dimensional model, the smooth almost complex structures
tamed by a smooth two-form, with the `C^∞` topology of any covering frame system, form a Baire
space. -/
theorem baireSpace_tames_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    BaireSpace {J : SmoothAlmostComplexStructure I M // form.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := isCompletelyMetrizableSpace_tames_frameTopology e U hU hcover form
  infer_instance

/-- On a Lindelöf manifold with finite-dimensional model, the smooth almost complex structures
compatible with a smooth two-form, with the `C^∞` topology of any covering frame system, form a
Baire space. -/
theorem baireSpace_compatible_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    BaireSpace {J : SmoothAlmostComplexStructure I M // form.Compatible J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := isCompletelyMetrizableSpace_compatible_frameTopology e U hU hcover form
  infer_instance

end SmoothTwoForm

end TauCeti
