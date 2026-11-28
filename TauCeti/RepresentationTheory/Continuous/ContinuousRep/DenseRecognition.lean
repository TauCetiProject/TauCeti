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

* `TauCeti.ContinuousRep.nonempty_equiv_semisimplification_baseChange_iff_charpoly_map_eq_of_dense`:
  agreement on a dense subset characterizes equivalence of the semisimplifications after
  scalar extension. This combines `TauCeti.ContinuousRep.charpoly_eq_of_dense` with
  `Representation.nonempty_equiv_semisimplification_iff_charpoly_eq`.
* `TauCeti.ContinuousRep.nonempty_equiv_baseChange_iff_charpoly_map_eq_of_dense`:
  if the scalar extensions are semisimple, the same test characterizes their equivalence,
  using `Representation.nonempty_equiv_iff_charpoly_eq_of_isSemisimpleRepresentation`.

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

/-- For continuous representations with continuous coefficient embeddings into a common Hausdorff
topological field `E`, the mapped characteristic polynomials agree on a dense subset
if and only if the semisimplifications after extending to `E` are equivariantly
linearly equivalent. -/
theorem nonempty_equiv_semisimplification_baseChange_iff_charpoly_map_eq_of_dense
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

/-- For continuous representations with continuous coefficient embeddings into a common Hausdorff
topological field, semisimple scalar extensions are equivariantly linearly equivalent if and only
if the mapped characteristic polynomials agree on a dense subset. -/
theorem nonempty_equiv_baseChange_iff_charpoly_map_eq_of_dense
    {ρ : ContinuousRep Γ E₁ V₁} {σ : ContinuousRep Γ E₂ V₂}
    [(ρ.toRepresentation.baseChange E).IsSemisimpleRepresentation]
    [(σ.toRepresentation.baseChange E).IsSemisimpleRepresentation]
    (h₁ : Continuous (algebraMap E₁ E)) (h₂ : Continuous (algebraMap E₂ E))
    {s : Set Γ} (hs : Dense s) :
    Nonempty ((ρ.toRepresentation.baseChange E).Equiv (σ.toRepresentation.baseChange E)) ↔
      ∀ g ∈ s, (ρ g).charpoly.map (algebraMap E₁ E) = (σ g).charpoly.map (algebraMap E₂ E) := by
  rw [Representation.nonempty_equiv_iff_charpoly_eq_of_isSemisimpleRepresentation,
    ← Representation.nonempty_equiv_semisimplification_iff_charpoly_eq]
  exact nonempty_equiv_semisimplification_baseChange_iff_charpoly_map_eq_of_dense h₁ h₂ hs

end TauCeti.ContinuousRep
