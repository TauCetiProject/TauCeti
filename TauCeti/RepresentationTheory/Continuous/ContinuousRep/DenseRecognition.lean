/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic
public import TauCeti.RepresentationTheory.Semisimplification
import TauCeti.RepresentationTheory.BrauerNesbitt
import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Charpoly

/-!
# Recognition of continuous representations on a dense subset

Two finite-dimensional continuous representations over different coefficient fields can be
compared by mapping their characteristic polynomials to a common Hausdorff field.

* `TauCeti.ContinuousRep.nonempty_equiv_baseChange_semisimplification_iff_charpoly_map_eq_of_dense`:
  agreement on a dense subset characterizes equivalence of the semisimplifications after
  scalar extension. This combines `TauCeti.ContinuousRep.charpoly_eq_of_dense` with
  `Representation.nonempty_equiv_semisimplification_iff_charpoly_eq`.
* `TauCeti.ContinuousRep.nonempty_iso_baseChange_iff_charpoly_map_eq_of_dense`:
  if the scalar extensions are semisimple, the same test characterizes continuous isomorphism,
  using the equivalence of each semisimple representation with its semisimplification.

See Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
pseudorepresentations of group algebras*, Example 2.31.
-/

public section

open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {Γ E₁ E₂ E V₁ V₂ : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [Field E₁] [TopologicalSpace E₁] [Field E₂] [TopologicalSpace E₂]
  [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E] [Algebra E₁ E] [Algebra E₂ E]
  [AddCommGroup V₁] [Module E₁ V₁] [FiniteDimensional E₁ V₁]
  [TopologicalSpace V₁] [IsModuleTopology E₁ V₁]
  [AddCommGroup V₂] [Module E₂ V₂] [FiniteDimensional E₂ V₂]
  [TopologicalSpace V₂] [IsModuleTopology E₂ V₂]

/-- For continuous representations over topological fields with continuous embeddings into a common
Hausdorff topological field `E`, the mapped characteristic polynomials agree on a dense subset
if and only if the semisimplifications after extending to `E` are equivariantly
linearly equivalent. -/
theorem nonempty_equiv_baseChange_semisimplification_iff_charpoly_map_eq_of_dense
    {ρ : ContinuousRep Γ E₁ V₁} {σ : ContinuousRep Γ E₂ V₂}
    (h₁ : Continuous (algebraMap E₁ E)) (h₂ : Continuous (algebraMap E₂ E))
    {s : Set Γ} (hs : Dense s) :
    Nonempty ((ρ.toRepresentation.baseChange E).semisimplification.Equiv
      (σ.toRepresentation.baseChange E).semisimplification) ↔
      ∀ g ∈ s, (ρ g).charpoly.map (algebraMap E₁ E) = (σ g).charpoly.map (algebraMap E₂ E) := by
  let : TopologicalSpace (E ⊗[E₁] V₁) := moduleTopology E _
  let : TopologicalSpace (E ⊗[E₂] V₂) := moduleTopology E _
  have : IsModuleTopology E (E ⊗[E₁] V₁) := ⟨rfl⟩
  have : IsModuleTopology E (E ⊗[E₂] V₂) := ⟨rfl⟩
  have : ContinuousSMul E₁ E := continuousSMul_of_algebraMap _ _ h₁
  have : ContinuousSMul E₂ E := continuousSMul_of_algebraMap _ _ h₂
  rw [← toRepresentation_baseChange, ← toRepresentation_baseChange,
    Representation.nonempty_equiv_semisimplification_iff_charpoly_eq]
  simp only [coe_toRepresentation, ← ρ.charpoly_baseChange_apply E, ← σ.charpoly_baseChange_apply E]
  exact ⟨fun h g _ ↦ h g, (ρ.baseChange E).charpoly_eq_of_dense (σ.baseChange E) hs⟩

/-- Two continuous representations with semisimple scalar extensions to a common Hausdorff
topological field are continuously isomorphic after scalar extension if and only if their
mapped characteristic polynomials agree on a dense subset. -/
theorem nonempty_iso_baseChange_iff_charpoly_map_eq_of_dense
    [ContinuousSMul E₁ E] [ContinuousSMul E₂ E]
    [TopologicalSpace (E ⊗[E₁] V₁)] [IsModuleTopology E (E ⊗[E₁] V₁)]
    [TopologicalSpace (E ⊗[E₂] V₂)] [IsModuleTopology E (E ⊗[E₂] V₂)]
    {ρ : ContinuousRep Γ E₁ V₁} {σ : ContinuousRep Γ E₂ V₂}
    [(ρ.baseChange E).toRepresentation.IsSemisimpleRepresentation]
    [(σ.baseChange E).toRepresentation.IsSemisimpleRepresentation]
    {s : Set Γ} (hs : Dense s) :
    Nonempty (Iso (ρ.baseChange E) (σ.baseChange E)) ↔
      ∀ g ∈ s, (ρ g).charpoly.map (algebraMap E₁ E) = (σ g).charpoly.map (algebraMap E₂ E) := by
  refine ⟨fun ⟨e⟩ g _ ↦ ?_, fun h ↦ ?_⟩
  · rw [← ρ.charpoly_baseChange_apply E, ← σ.charpoly_baseChange_apply E]
    exact e.charpoly_apply_eq g
  · have hss := (nonempty_equiv_baseChange_semisimplification_iff_charpoly_map_eq_of_dense
      (continuous_algebraMap E₁ E) (continuous_algebraMap E₂ E) hs).mpr h
    rw [← toRepresentation_baseChange, ← toRepresentation_baseChange] at hss
    obtain ⟨ess⟩ := hss
    obtain ⟨eρ⟩ := (ρ.baseChange E).toRepresentation.nonempty_equiv_semisimplification_iff.mpr
      inferInstance
    obtain ⟨eσ⟩ := (σ.baseChange E).toRepresentation.nonempty_equiv_semisimplification_iff.mpr
      inferInstance
    exact ⟨Iso.ofEquiv ((eρ.symm.trans ess).trans eσ)⟩

end TauCeti.ContinuousRep
