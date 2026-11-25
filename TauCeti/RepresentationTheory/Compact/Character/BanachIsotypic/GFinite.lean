/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.BanachIsotypic.Basic
public import TauCeti.RepresentationTheory.GFinite
public import TauCeti.RepresentationTheory.Compact.PeterWeyl
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Continuous.Intertwining

/-!
# Isotypic projectors produce `G`-finite vectors

Let `π` be a strongly continuous representation of a compact group `G` on a Banach space `V` over
`ℝ` or `ℂ`, and `σ` a finite-dimensional continuous representation. Every output `e_σ v` of the
isotypic projector `ContRepresentation.banachIsotypicProjector` is `G`-finite. Indeed
`π h (e_σ v) = π(f(h⁻¹ ·)) v` for the isotypic kernel `f = dim(σ) · conj(χ_σ)`, and the left
translates of `f` span a finite-dimensional subspace of `C(G, k)`
(`ContRepresentation.finiteDimensional_span_range_isotypicKernel_comp_mulLeft`).

Consequently the ranges of the projectors lie in `gFiniteSubmodule`, and for a family of pairwise
inequivalent irreducibles over an algebraically closed field they are independent, since the
projectors are idempotent and pairwise orthogonal. This is the first half of the decomposition of
the `G`-finite vectors as the algebraic direct sum of the isotypic ranges.

## Main definitions

* `ContRepresentation.banachIsotypicRange π hπ σ hσ`: the isotypic part `V(σ)`, the range of
  `e_σ`.

## Main results

* `ContRepresentation.isGFinite_banachIsotypicProjector_apply`: `e_σ v` is `G`-finite.
* `ContRepresentation.banachIsotypicRange_le_gFiniteSubmodule`: the isotypic part `V(σ)`, the
  range of `e_σ`, consists of `G`-finite vectors.
* `ContRepresentation.iSupIndep_banachIsotypicRange`: for pairwise inequivalent irreducible models
  the isotypic parts are independent.
* `ContRepresentation.iSupIndep_banachIsotypicRange_of_isIrrepSkeleton`: in particular for a
  skeleton of the unitary dual.
* `ContRepresentation.iSup_banachIsotypicRange_le_gFiniteSubmodule`: their sum lies in the
  `G`-finite vectors.

## References

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
  {W : Type*} [NormedAddCommGroup W] [NormedSpace k W] [FiniteDimensional k W]

variable [CompleteSpace V] (π : ContRepresentation k G V) (hπ : ∀ v, Continuous fun g ↦ π g v)

/-- **Isotypic projections are `G`-finite.** For a finite-dimensional continuous representation
`σ`, every output `e_σ v` of the isotypic projector is `G`-finite: its translates
`π h (e_σ v) = π(f(h⁻¹ ·)) v` are images of the left translates of the isotypic kernel `f`, which
span a finite-dimensional space. -/
theorem isGFinite_banachIsotypicProjector_apply (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (v : V) :
    π.toRepresentation.IsGFinite (banachIsotypicProjector π hπ σ hσ v) := by
  have := finiteDimensional_span_range_isotypicKernel_comp_mulLeft σ hσ
  refine Representation.IsGFinite.of_apply_eq
    ((ContinuousLinearMap.apply k V v).toLinearMap ∘ₗ strongIntegratedOperatorₗ π hπ)
    (u := fun h : G ↦ (isotypicKernel σ hσ).comp (ContinuousMap.mulLeft h⁻¹)) fun h ↦ ?_
  rw [← ContIntertwiningMap.toContinuousLinearMap_apply,
    toContinuousLinearMap_banachIsotypicProjector]
  simp only [LinearMap.coe_comp, Function.comp_apply, strongIntegratedOperatorₗ_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply]
  exact apply_strongIntegratedOperator π hπ _ h v

/-- The **isotypic part** `V(σ)`: the range of the isotypic projector `e_σ`. For `σ` irreducible
over an algebraically closed field it is the set of vectors fixed by `e_σ`
(`mem_banachIsotypicRange_iff_apply_eq_self`). -/
def banachIsotypicRange (σ : ContRepresentation k G W) (hσ : Continuous σ) : Submodule k V :=
  LinearMap.range (banachIsotypicProjector π hπ σ hσ).toContinuousLinearMap.toLinearMap

/-- Membership in the isotypic part: being an output of `e_σ`. -/
@[simp]
theorem mem_banachIsotypicRange (σ : ContRepresentation k G W) (hσ : Continuous σ) {v : V} :
    v ∈ banachIsotypicRange π hπ σ hσ ↔ ∃ w, banachIsotypicProjector π hπ σ hσ w = v := by
  rw [banachIsotypicRange, LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe, ContIntertwiningMap.toContinuousLinearMap_apply]

/-- Every output of `e_σ` lies in the isotypic part. -/
theorem banachIsotypicProjector_apply_mem_banachIsotypicRange (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (v : V) :
    banachIsotypicProjector π hπ σ hσ v ∈ banachIsotypicRange π hπ σ hσ :=
  (mem_banachIsotypicRange π hπ σ hσ).2 ⟨v, rfl⟩

/-- For `σ` irreducible over an algebraically closed field, the isotypic part is the set of vectors
fixed by `e_σ`. -/
theorem mem_banachIsotypicRange_iff_apply_eq_self [IsAlgClosed k] (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (hirr : Representation.IsIrreducible σ.toRepresentation) {v : V} :
    v ∈ banachIsotypicRange π hπ σ hσ ↔ banachIsotypicProjector π hπ σ hσ v = v := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ hv ▸ banachIsotypicProjector_apply_mem_banachIsotypicRange
    π hπ σ hσ v⟩
  obtain ⟨w, rfl⟩ := (mem_banachIsotypicRange π hπ σ hσ).1 hv
  exact banachIsotypicProjector_apply_apply π hπ σ hσ hirr w

/-- The isotypic part `V(σ)` consists of `G`-finite vectors. -/
theorem banachIsotypicRange_le_gFiniteSubmodule (σ : ContRepresentation k G W)
    (hσ : Continuous σ) :
    banachIsotypicRange π hπ σ hσ ≤ π.toRepresentation.gFiniteSubmodule := by
  intro _ hv
  obtain ⟨v, rfl⟩ := (mem_banachIsotypicRange π hπ σ hσ).1 hv
  exact (Representation.mem_gFiniteSubmodule _).2
    (isGFinite_banachIsotypicProjector_apply π hπ σ hσ v)

/-- The sum of the isotypic parts of a family of models consists of `G`-finite vectors. -/
theorem iSup_banachIsotypicRange_le_gFiniteSubmodule {ι : Type*}
    (models : ι → IrrepModel k G) :
    ⨆ i, banachIsotypicRange π hπ (models i).rep (models i).continuous_rep ≤
      π.toRepresentation.gFiniteSubmodule :=
  iSup_le fun _ ↦ banachIsotypicRange_le_gFiniteSubmodule π hπ _ _

/-- **The isotypic parts are independent.** For a family of irreducible models over an
algebraically closed field which are pairwise inequivalent as `k[G]`-modules, the isotypic parts
are independent: `e_i` fixes its own part and kills the part of every other `e_j`. -/
theorem iSupIndep_banachIsotypicRange [IsAlgClosed k] {ι : Type*}
    (models : ι → IrrepModel k G)
    (hne : Pairwise fun i j ↦ IsEmpty ((models i).rep.toRepresentation.asModule ≃ₗ[k[G]]
      (models j).rep.toRepresentation.asModule)) :
    iSupIndep fun i ↦ banachIsotypicRange π hπ (models i).rep (models i).continuous_rep := by
  refine iSupIndep_def.2 fun i ↦ Submodule.disjoint_def.2 fun x hx hx' ↦ ?_
  have hle : ⨆ j, ⨆ (_ : j ≠ i), banachIsotypicRange π hπ (models j).rep
      (models j).continuous_rep ≤ LinearMap.ker (banachIsotypicProjector π hπ (models i).rep
        (models i).continuous_rep).toContinuousLinearMap.toLinearMap :=
    iSup₂_le fun j hji ↦ by
      intro _ hz
      obtain ⟨z, rfl⟩ := (mem_banachIsotypicRange π hπ _ _).1 hz
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        ContIntertwiningMap.toContinuousLinearMap_apply]
      exact banachIsotypicProjector_apply_apply_of_not_equiv π hπ (models i).rep
        (models i).continuous_rep (models i).isIrreducible (models j).rep
        (models j).continuous_rep (models j).isIrreducible (hne hji) z
  rw [← (mem_banachIsotypicRange_iff_apply_eq_self π hπ _ _ (models i).isIrreducible).1 hx]
  exact hle hx'

/-- The isotypic parts of a skeleton of the unitary dual are independent. -/
theorem iSupIndep_banachIsotypicRange_of_isIrrepSkeleton [IsAlgClosed k] {ι : Type*}
    {models : ι → IrrepModel k G} (h : IsIrrepSkeleton models) :
    iSupIndep fun i ↦ banachIsotypicRange π hπ (models i).rep (models i).continuous_rep :=
  iSupIndep_banachIsotypicRange π hπ models fun _ _ hij ↦ ⟨fun e ↦
    (h.pairwise_isEmpty_equiv hij).false <| Classical.choice <|
      _root_.ContRepresentation.nonempty_equiv_iff.2 <|
        TauCeti.Representation.nonempty_equiv_iff.2 ⟨e⟩⟩

end ContRepresentation
