/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.IsotypicProjection
public import TauCeti.RepresentationTheory.Compact.StrongIntegrated
public import TauCeti.RepresentationTheory.Continuous.StronglyContinuous
import TauCeti.RepresentationTheory.Compact.GFiniteDensity

/-!
# Isotypic projectors on Banach representations of compact groups

Let `π` be a strongly continuous representation of a compact group `G` on a Banach space `V` over
`ℝ` or `ℂ`: every orbit `g ↦ π g v` is continuous, while `g ↦ π g` need not be continuous in the
operator norm. For a finite-dimensional continuous irreducible `σ` over an algebraically closed
field, the kernel `dim(σ) · conj(χ_σ)` of `ContRepresentation.isotypicKernel` acts on `V` through
the strong integrated operator `ContRepresentation.strongIntegratedOperator`, giving the
**isotypic projector** `e_σ = π(dim(σ) · conj(χ_σ))`, a continuous self-intertwiner of `π`. On an
operator-norm continuous representation, in particular a finite-dimensional one, it is the
finite-dimensional `ContRepresentation.isotypicProjector`. It is idempotent, and `e_σ ∘ e_τ = 0`
for inequivalent irreducibles `σ`, `τ`: both identities hold on each `G`-finite vector, where
`e_σ` is the finite-dimensional projector of a finite-dimensional subrepresentation containing it,
and the `G`-finite vectors are dense (`ContRepresentation.continuousLinearMap_ext_of_isGFinite`).

## Main definitions

* `ContRepresentation.banachIsotypicProjector π hπ σ hσ`: the isotypic projector `e_σ`, a
  continuous self-intertwiner of `π`.

## Main results

* `ContRepresentation.banachIsotypicProjector_eq_isotypicProjector`: on an operator-norm
  continuous representation `e_σ` is `isotypicProjector`.
* `ContRepresentation.banachIsotypicProjector_apply_of_mem`: on a finite-dimensional
  subrepresentation `e_σ` is the isotypic projector of the restricted representation.
* `ContRepresentation.banachIsotypicProjector_idempotent`: `e_σ` is idempotent.
* `ContRepresentation.banachIsotypicProjector_comp_of_not_equiv`: `e_σ ∘ e_τ = 0` for
  inequivalent irreducibles `σ` and `τ`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III.
* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §4.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped MonoidAlgebra

namespace ContRepresentation

variable {k G V : Type*} [RCLike k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace k V] [NormedSpace ℝ V] [SMulCommClass ℝ k V]

/-! ### The isotypic projector -/

variable [CompleteSpace V] (π : ContRepresentation k G V) (hπ : ∀ v, Continuous fun g ↦ π g v)
  {W W' : Type*} [NormedAddCommGroup W] [NormedSpace k W] [FiniteDimensional k W]
  [NormedAddCommGroup W'] [NormedSpace k W'] [FiniteDimensional k W']

/-- The **isotypic projector** `e_σ = ∫ g, dim(σ) conj(χ_σ g) • π g` of a strongly continuous
Banach representation of a compact group, for a finite-dimensional continuous representation `σ`,
as a continuous self-intertwiner. For `σ` irreducible over an algebraically closed field it is
idempotent (`banachIsotypicProjector_idempotent`). -/
def banachIsotypicProjector (σ : ContRepresentation k G W) (hσ : Continuous σ) :
    ContIntertwiningMap π π where
  __ := strongIntegratedOperator π hπ (isotypicKernel σ hσ)
  isIntertwining' := strongIntegratedOperator_comp π hπ (isotypicKernel_conj σ hσ)

/-- The continuous linear map underlying `e_σ` is the strong integrated operator of the
isotypic kernel. -/
@[simp]
theorem toContinuousLinearMap_banachIsotypicProjector (σ : ContRepresentation k G W)
    (hσ : Continuous σ) :
    (banachIsotypicProjector π hπ σ hσ).toContinuousLinearMap =
      strongIntegratedOperator π hπ (isotypicKernel σ hσ) :=
  (rfl)

/-- The defining integral formula for `e_σ`. -/
theorem banachIsotypicProjector_apply (σ : ContRepresentation k G W) (hσ : Continuous σ) (v : V) :
    banachIsotypicProjector π hπ σ hσ v = ∫ g, isotypicKernel σ hσ g • π g v ∂haarProb G :=
  strongIntegratedOperator_apply π hπ _ v

/-- On a representation continuous in the operator norm, for instance a finite-dimensional
continuous one, `e_σ` is the isotypic projector `isotypicProjector`. -/
theorem banachIsotypicProjector_eq_isotypicProjector (hπ' : Continuous π)
    (σ : ContRepresentation k G W) (hσ : Continuous σ) :
    banachIsotypicProjector π hπ σ hσ = isotypicProjector π hπ' σ hσ := by
  ext v
  simp [strongIntegratedOperator_eq_integratedOperator π hπ hπ']

/-- On a finite-dimensional subrepresentation, for instance the span of the orbit of a `G`-finite
vector, `e_σ` is the finite-dimensional isotypic projector of the restricted representation. -/
theorem banachIsotypicProjector_apply_of_mem (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (S : Subrepresentation π.toRepresentation)
    [FiniteDimensional k S.toSubmodule] {v : V} (hv : v ∈ S.toSubmodule) :
    banachIsotypicProjector π hπ σ hσ v =
      (isotypicProjector (π.subrepresentation S.toSubmodule
          fun g _ hu ↦ S.apply_mem_toSubmodule g hu)
        (continuous_subrepresentation_of_finiteDimensional hπ) σ hσ ⟨v, hv⟩ : V) := by
  have h := congrArg (fun T : S.toSubmodule →L[k] V ↦ T ⟨v, hv⟩)
    (comp_strongIntegratedOperator _ (continuous_subrepresentation_apply hπ) π hπ
      (subrepresentationInclusion π S) (isotypicKernel σ hσ))
  simp only [ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_apply,
    subrepresentationInclusion_apply, strongIntegratedOperator_apply] at h
  simpa [banachIsotypicProjector_apply, isotypicProjector_apply] using h.symm

variable [IsAlgClosed k]

/-- **`e_σ` is idempotent** for an irreducible `σ`. -/
@[simp]
theorem banachIsotypicProjector_idempotent (σ : ContRepresentation k G W) (hσ : Continuous σ)
    (hirr : Representation.IsIrreducible σ.toRepresentation) :
    (banachIsotypicProjector π hπ σ hσ).comp (banachIsotypicProjector π hπ σ hσ) =
      banachIsotypicProjector π hπ σ hσ := by
  refine ContIntertwiningMap.toContinuousLinearMap_injective
    (continuousLinearMap_ext_of_isGFinite π hπ fun v hv ↦ ?_)
  obtain ⟨S, _, hvS⟩ := (π.toRepresentation.isGFinite_iff_exists_subrepresentation v).1 hv
  let ρ := π.subrepresentation S.toSubmodule fun g _ hu ↦ S.apply_mem_toSubmodule g hu
  have hρ : Continuous ρ := continuous_subrepresentation_of_finiteDimensional hπ
  have hP := congrArg (fun T ↦ (T ⟨v, hvS⟩ : V)) (isotypicProjector_idempotent ρ hρ σ hσ hirr)
  simp only [ContIntertwiningMap.toContinuousLinearMap_comp, ContinuousLinearMap.comp_apply,
    ContIntertwiningMap.toContinuousLinearMap_apply] at hP ⊢
  rw [banachIsotypicProjector_apply_of_mem π hπ σ hσ S hvS,
    banachIsotypicProjector_apply_of_mem π hπ σ hσ S (Subtype.property _)]
  exact hP

/-- **Orthogonality.** For inequivalent irreducibles `σ` and `τ`, `e_σ ∘ e_τ = 0`. -/
theorem banachIsotypicProjector_comp_of_not_equiv (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (hσirr : Representation.IsIrreducible σ.toRepresentation)
    (τ : ContRepresentation k G W') (hτ : Continuous τ)
    (hτirr : Representation.IsIrreducible τ.toRepresentation)
    (hne : IsEmpty (τ.toRepresentation.asModule ≃ₗ[k[G]] σ.toRepresentation.asModule)) :
    (banachIsotypicProjector π hπ σ hσ).comp (banachIsotypicProjector π hπ τ hτ) = 0 := by
  refine ContIntertwiningMap.toContinuousLinearMap_injective
    (continuousLinearMap_ext_of_isGFinite π hπ fun v hv ↦ ?_)
  obtain ⟨S, _, hvS⟩ := (π.toRepresentation.isGFinite_iff_exists_subrepresentation v).1 hv
  let ρ := π.subrepresentation S.toSubmodule fun g _ hu ↦ S.apply_mem_toSubmodule g hu
  have hρ : Continuous ρ := continuous_subrepresentation_of_finiteDimensional hπ
  let w := isotypicProjector ρ hρ τ hτ ⟨v, hvS⟩
  have h0 := isotypicProjector_apply_of_mem_isotypicComponent_of_not_equiv ρ hρ σ hσ hσirr τ
    hτirr hne w (isotypicProjector_apply_mem_isotypicComponent ρ hρ τ hτ hτirr _)
  simp only [ContIntertwiningMap.toContinuousLinearMap_comp, ContinuousLinearMap.comp_apply,
    ContIntertwiningMap.toContinuousLinearMap_apply, ContIntertwiningMap.toContinuousLinearMap_zero,
    zero_apply]
  rw [banachIsotypicProjector_apply_of_mem π hπ τ hτ S hvS,
    banachIsotypicProjector_apply_of_mem π hπ σ hσ S w.property]
  exact congrArg Subtype.val h0

end ContRepresentation
