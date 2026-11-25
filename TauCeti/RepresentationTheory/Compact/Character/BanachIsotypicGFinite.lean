/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.BanachIsotypicProjection
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
translates of `f` lie in the span of the conjugated matrix entries of `σ` in a basis, a
finite-dimensional subspace of `C(G, k)`.

Consequently the ranges of the projectors lie in `gFiniteSubmodule`, and for a family of pairwise
inequivalent irreducibles over an algebraically closed field they are independent, since the
projectors are idempotent and pairwise orthogonal. This is the first half of the decomposition of
the `G`-finite vectors as the algebraic direct sum of the isotypic ranges.

## Main definitions

* `ContRepresentation.banachIsotypicRange π hπ σ hσ`: the isotypic part `V(σ)`, the range of
  `e_σ`.

## Main results

* `ContRepresentation.finiteDimensional_span_range_isotypicKernel_comp_mulLeft`: the left
  translates of the isotypic kernel span a finite-dimensional space.
* `ContRepresentation.banachIsotypicProjector_apply_isGFinite`: `e_σ v` is `G`-finite.
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

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The left translates `g ↦ f (h⁻¹ * g)` of the isotypic kernel `f = dim(σ) · conj(χ_σ)` span a
finite-dimensional subspace of `C(G, k)`: each is a combination of the conjugated matrix entries
of `σ` in a basis of its carrier. -/
theorem finiteDimensional_span_range_isotypicKernel_comp_mulLeft
    (σ : ContRepresentation k G W) (hσ : Continuous σ) :
    FiniteDimensional k (Submodule.span k (Set.range fun h : G ↦
      (isotypicKernel σ hσ).comp (ContinuousMap.mulLeft h⁻¹))) := by
  let b := Module.finBasis k W
  let u : Fin (Module.finrank k W) × Fin (Module.finrank k W) → C(G, k) := fun p ↦
    ⟨fun g ↦ star (b.repr (σ g (b p.2)) p.1),
      Continuous.star (f := fun g ↦ b.repr (σ g (b p.2)) p.1)
        (((b.coord p.1).continuous_of_finiteDimensional).comp
          (hσ.clm_apply continuous_const))⟩
  have := FiniteDimensional.span_of_finite k (Set.finite_range u)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span k (Set.range u)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  have hu : (isotypicKernel σ hσ).comp (ContinuousMap.mulLeft h⁻¹) =
      ∑ p, ((Module.finrank k W : k) * star (b.repr (σ h⁻¹ (b p.1)) p.2)) • u p := by
    ext g
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft, isotypicKernel_apply,
      character_apply, map_mul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ContinuousMap.coe_mk, u]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace, star_sum, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.toLinearMap_mul, LinearMap.toMatrix_mul, Matrix.diag_apply,
      Matrix.mul_apply, star_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [LinearMap.toMatrix_apply, mul_comm]
  change (isotypicKernel σ hσ).comp (ContinuousMap.mulLeft h⁻¹) ∈ _
  rw [hu]
  exact Submodule.sum_mem _ fun p _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

variable [CompleteSpace V] (π : ContRepresentation k G V) (hπ : ∀ v, Continuous fun g ↦ π g v)

/-- **Isotypic projections are `G`-finite.** For a finite-dimensional continuous representation
`σ`, every output `e_σ v` of the isotypic projector is `G`-finite: its translates
`π h (e_σ v) = π(f(h⁻¹ ·)) v` are images of the left translates of the isotypic kernel `f`, which
span a finite-dimensional space. -/
theorem banachIsotypicProjector_apply_isGFinite (σ : ContRepresentation k G W)
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
(`mem_banachIsotypicRange_iff`). -/
def banachIsotypicRange (σ : ContRepresentation k G W) (hσ : Continuous σ) : Submodule k V :=
  LinearMap.range (banachIsotypicProjector π hπ σ hσ).toContinuousLinearMap.toLinearMap

/-- Membership in the isotypic part: being an output of `e_σ`. -/
theorem mem_banachIsotypicRange (σ : ContRepresentation k G W) (hσ : Continuous σ) {v : V} :
    v ∈ banachIsotypicRange π hπ σ hσ ↔ ∃ w, banachIsotypicProjector π hπ σ hσ w = v :=
  (Iff.rfl)

/-- Every output of `e_σ` lies in the isotypic part. -/
theorem banachIsotypicProjector_apply_mem_banachIsotypicRange (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (v : V) :
    banachIsotypicProjector π hπ σ hσ v ∈ banachIsotypicRange π hπ σ hσ :=
  (mem_banachIsotypicRange π hπ σ hσ).2 ⟨v, rfl⟩

/-- For `σ` irreducible over an algebraically closed field, the isotypic part is the set of vectors
fixed by `e_σ`. -/
theorem mem_banachIsotypicRange_iff [IsAlgClosed k] (σ : ContRepresentation k G W)
    (hσ : Continuous σ) (hirr : Representation.IsIrreducible σ.toRepresentation) {v : V} :
    v ∈ banachIsotypicRange π hπ σ hσ ↔ banachIsotypicProjector π hπ σ hσ v = v := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ hv ▸ banachIsotypicProjector_apply_mem_banachIsotypicRange
    π hπ σ hσ v⟩
  obtain ⟨w, rfl⟩ := (mem_banachIsotypicRange π hπ σ hσ).1 hv
  exact congrArg (fun T : ContIntertwiningMap π π ↦ T w)
    (banachIsotypicProjector_idempotent π hπ σ hσ hirr)

/-- The isotypic part `V(σ)` consists of `G`-finite vectors. -/
theorem banachIsotypicRange_le_gFiniteSubmodule (σ : ContRepresentation k G W)
    (hσ : Continuous σ) :
    banachIsotypicRange π hπ σ hσ ≤ π.toRepresentation.gFiniteSubmodule := by
  rintro _ ⟨v, rfl⟩
  exact (Representation.mem_gFiniteSubmodule _).2
    (banachIsotypicProjector_apply_isGFinite π hπ σ hσ v)

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
      rintro _ ⟨z, rfl⟩
      exact congrArg (fun T : ContIntertwiningMap π π ↦ T z)
        (banachIsotypicProjector_comp_of_not_equiv π hπ (models i).rep (models i).continuous_rep
          (models i).isIrreducible (models j).rep (models j).continuous_rep
          (models j).isIrreducible (hne hji))
  rw [← (mem_banachIsotypicRange_iff π hπ _ _ (models i).isIrreducible).1 hx]
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
