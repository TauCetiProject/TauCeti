/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.LaurentCover.Module
public import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.Topology.Algebra.Module.TensorProduct
import TauCeti.Analysis.Normed.Group.Quotient

/-!
# Strictness of the finite-module Laurent sequence

The augmented two-piece Laurent sequence for a finite module over an affinoid algebra is
strictly exact. Its augmentation is a closed embedding and its differential, second
restriction minus first restriction, is an open quotient map. Thus compatible local sections
glue continuously, not merely algebraically.

We allow complete Hausdorff topological modules with countably generated additive
uniformities, nonarchimedean additive topologies, and continuous coefficient-algebra actions.
The finite-module topology
theorem identifies these topologies with the canonical module topologies. In particular,
the results apply to compatible complete ultrametric module norms, without requiring equality
of chosen norms, projectivity, or reducedness. Apply
`TauCeti.exists_complete_norm_of_module_finite` separately to the module and its three Laurent
scalar extensions to obtain such norms; `isClosedEmbedding_moduleAugmentation` and
`isOpenQuotientMap_moduleDiff` then supply strictness.

The tensors are algebraic scalar extensions by the Laurent coordinate algebras, not completed
tensors of arbitrary Banach modules. No topology is imposed on infinitely generated modules.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§3.7.2 and 8.2.1–8.2.2.
-/

public section

namespace TauCeti.LaurentCover

open TensorProduct Topology
open scoped Uniformity

variable {K A : Type*} [NontriviallyNormedField K]
    [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)

local notation "L(" f ")" =>
  LaurentFraction (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → _)
local notation "G(" f ")" =>
  LaurentFraction (Fin.elim0 : Fin 0 → _) (fun _ : Fin 1 ↦ f)
local notation "O(" f ")" =>
  LaurentFraction (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f)

section Augmentation

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M] [BaireSpace M]
    [ContinuousSMul A M]
    [TopologicalSpace (L(f) ⊗[A] M)] [ContinuousAdd (L(f) ⊗[A] M)]
    [ContinuousSMul L(f) (L(f) ⊗[A] M)]
    [TopologicalSpace (G(f) ⊗[A] M)] [ContinuousAdd (G(f) ⊗[A] M)]
    [ContinuousSMul G(f) (G(f) ⊗[A] M)]

/-- The finite-module Laurent augmentation is continuous for compatible Baire topologies
when the coefficient algebra is a Tate ring. -/
theorem continuous_moduleAugmentation [Huber.IsTateRing A] :
    Continuous (moduleAugmentation M f) := by
  have : IsModuleTopology A M := Huber.IsTateRing.isModuleTopology
  have : ContinuousSMul A (L(f) ⊗[A] M) := IsScalarTower.continuousSMul L(f)
  have : ContinuousSMul A (G(f) ⊗[A] M) := IsScalarTower.continuousSMul G(f)
  exact IsModuleTopology.continuous_of_linearMap (moduleAugmentation M f)

end Augmentation

variable [IsUltrametricDist K] [CompleteSpace K]

section Differential

variable [TopologicalSpace (L(f) ⊗[A] M)] [IsTopologicalAddGroup (L(f) ⊗[A] M)]
    [T2Space (L(f) ⊗[A] M)] [BaireSpace (L(f) ⊗[A] M)]
    [ContinuousSMul L(f) (L(f) ⊗[A] M)]
    [TopologicalSpace (G(f) ⊗[A] M)] [IsTopologicalAddGroup (G(f) ⊗[A] M)]
    [T2Space (G(f) ⊗[A] M)] [BaireSpace (G(f) ⊗[A] M)]
    [ContinuousSMul G(f) (G(f) ⊗[A] M)]
    [TopologicalSpace (O(f) ⊗[A] M)] [IsTopologicalAddGroup (O(f) ⊗[A] M)]
    [ContinuousSMul O(f) (O(f) ⊗[A] M)]

/-- The finite-module Laurent differential is continuous when the two source modules carry
compatible Hausdorff Baire topologies. No bound on the norm of `f` is required. -/
theorem continuous_moduleDiff (hA : IsAffinoidAlgebra K A) :
    Continuous (moduleDiff M f) := by
  have := hA.isRestricted_subring.isClosed_ideal
    (laurentFractionIdeal (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A))
  have := hA.isRestricted_subring.isClosed_ideal
    (laurentFractionIdeal (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f))
  have := hA.isRestricted_subring.isClosed_ideal
    (laurentFractionIdeal (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f))
  let : Huber.IsTateRing L(f) := Huber.IsTateRing.of_normedAlgebra K L(f)
  let : Huber.IsTateRing G(f) := Huber.IsTateRing.of_normedAlgebra K G(f)
  have : IsModuleTopology L(f) (L(f) ⊗[A] M) :=
    Huber.IsTateRing.isModuleTopology (A := L(f)) (M := L(f) ⊗[A] M)
  have : IsModuleTopology G(f) (G(f) ⊗[A] M) :=
    Huber.IsTateRing.isModuleTopology (A := G(f)) (M := G(f) ⊗[A] M)
  have hO := LaurentFraction.isAffinoidAlgebra hA (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f)
  have := (LaurentFraction.isAffinoidAlgebra hA
    (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A)).isNoetherianRing
  have := (LaurentFraction.isAffinoidAlgebra hA
    (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f)).isNoetherianRing
  have hle := hO.continuous_algHom (K := K) (A := O(f)) (B := L(f))
    ((leToOverlap f).restrictScalars K)
  have hge := hO.continuous_algHom (K := K) (A := O(f)) (B := G(f))
    ((geToOverlap f).restrictScalars K)
  exact ((((geToOverlap f).continuous_rTensor (M := M) hge).comp continuous_snd).sub
    (((leToOverlap f).continuous_rTensor (M := M) hle).comp continuous_fst)).congr
      fun z ↦ (moduleDiff_apply M f z.1 z.2).symm

end Differential

section Strictness

variable [UniformSpace (L(f) ⊗[A] M)] [IsTopologicalAddGroup (L(f) ⊗[A] M)]
    [CompleteSpace (L(f) ⊗[A] M)] [(𝓤 (L(f) ⊗[A] M)).IsCountablyGenerated]
    [T2Space (L(f) ⊗[A] M)]
    [ContinuousSMul L(f) (L(f) ⊗[A] M)]
    [UniformSpace (G(f) ⊗[A] M)] [IsTopologicalAddGroup (G(f) ⊗[A] M)]
    [CompleteSpace (G(f) ⊗[A] M)] [(𝓤 (G(f) ⊗[A] M)).IsCountablyGenerated]
    [T2Space (G(f) ⊗[A] M)]
    [ContinuousSMul G(f) (G(f) ⊗[A] M)]
    [TopologicalSpace (O(f) ⊗[A] M)] [IsTopologicalAddGroup (O(f) ⊗[A] M)]
    [T2Space (O(f) ⊗[A] M)] [ContinuousSMul O(f) (O(f) ⊗[A] M)]

/-- **Closedness and strictness of the Laurent augmentation.** A finite module is identified
topologically with the closed space of compatible pairs on the two Laurent pieces. -/
theorem isClosedEmbedding_moduleAugmentation
    [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M] [(𝓤 M).IsCountablyGenerated]
    [T2Space M] [NonarchimedeanAddGroup M] [ContinuousSMul A M]
    (hA : IsAffinoidAlgebra K A) : IsClosedEmbedding (moduleAugmentation M f) := by
  let : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  have : ContinuousSMul A (L(f) ⊗[A] M) := IsScalarTower.continuousSMul L(f)
  have : ContinuousSMul A (G(f) ⊗[A] M) := IsScalarTower.continuousSMul G(f)
  have hc := continuous_moduleAugmentation M f
  have hrange : Set.range (moduleAugmentation M f) = (moduleDiff M f).ker := by
    ext z
    exact ((exact_moduleAugmentation_moduleDiff M f) z).symm
  have hclosed : IsClosed (Set.range (moduleAugmentation M f)) := by
    rw [hrange]
    exact isClosed_singleton.preimage (continuous_moduleDiff M f hA)
  exact ⟨isEmbedding_iff_isStrictMap_injective.mpr
    ⟨(moduleAugmentation M f).isStrictMap_of_isClosed_range_of_isTateRing
      hc.continuousAt hclosed, moduleAugmentation_injective M hA f⟩, hclosed⟩

omit [IsTopologicalAddGroup (L(f) ⊗[A] M)] [IsTopologicalAddGroup (G(f) ⊗[A] M)] in
/-- **Strictness of the Laurent differential.** The overlap module carries the quotient
topology for the difference of restrictions, including when some pieces are zero. -/
theorem isOpenQuotientMap_moduleDiff
    [IsUniformAddGroup (L(f) ⊗[A] M)] [NonarchimedeanAddGroup (L(f) ⊗[A] M)]
    [IsUniformAddGroup (G(f) ⊗[A] M)] [NonarchimedeanAddGroup (G(f) ⊗[A] M)]
    [BaireSpace (O(f) ⊗[A] M)]
    (hA : IsAffinoidAlgebra K A) : IsOpenQuotientMap (moduleDiff M f) := by
  let : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  have : ContinuousSMul A (L(f) ⊗[A] M) := IsScalarTower.continuousSMul L(f)
  have : ContinuousSMul A (G(f) ⊗[A] M) := IsScalarTower.continuousSMul G(f)
  have : ContinuousSMul A (O(f) ⊗[A] M) := IsScalarTower.continuousSMul O(f)
  have hc := continuous_moduleDiff M f hA
  exact ⟨moduleDiff_surjective M f, hc,
    (moduleDiff M f).isOpenMap_of_isTateRing
      (moduleDiff_surjective M f) hc.continuousAt⟩

end Strictness

end TauCeti.LaurentCover
