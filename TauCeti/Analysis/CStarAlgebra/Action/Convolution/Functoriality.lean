/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.FullSeminorm

/-!
# Contractive functoriality of twisted convolution

An equivariant coefficient homomorphism acts contractively on the compact-support convolution
algebra in the L¹ norm. Its extension to the twisted L¹ completion is a continuous nonunital
star-algebra homomorphism. These extensions preserve identities and composition, and commute
with integrated covariant representations.

The coefficient map also decreases the full seminorm, when both coefficient algebras use the
same universe for the indexing family of covariant representations. This estimate supplies the
continuity needed to extend the convolution map to the full crossed-product completion.
It does not assert independence of that indexing universe.

No unitality, nondegeneracy, separability or global σ-finiteness is assumed. The L¹ norm estimate
only needs finiteness of the measure on compact sets; left invariance supplies multiplication on
the completions. The star law uses a Borel measurable space, and the full-seminorm estimate
uses Haar measure.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for functoriality via pullback of
covariant representations and extension of the compact-support convolution maps.
-/

public section

noncomputable section

open MeasureTheory UniformSpace UniformSpace.Completion

namespace TauCeti.CStarAction.Hom

variable {G A B C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}
  (φ : Hom α β) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- Equivariant coefficient maps decrease the L¹ norm of convolution coefficients. -/
theorem norm_convolutionMap_le (f : ConvolutionAlgebra α μ) :
    ‖φ.convolutionMap μ f‖ ≤ ‖f‖ := by
  simp only [ConvolutionAlgebra.norm_eq_integral_norm]
  refine integral_mono (φ.convolutionMap μ f).ofConv.integrable.norm f.ofConv.integrable.norm ?_
  intro s
  simpa only [convolutionMap_apply] using
    NonUnitalStarAlgHom.norm_apply_le φ (f.ofConv s)

/-- The compact-support convolution map as a continuous linear map for the L¹ norms. -/
def convolutionMapCLM : ConvolutionAlgebra α μ →L[ℂ] ConvolutionAlgebra β μ :=
  (φ.convolutionMap μ : ConvolutionAlgebra α μ →ₗ[ℂ] ConvolutionAlgebra β μ).mkContinuous
    1 fun f => by simpa using φ.norm_convolutionMap_le μ f

@[simp]
theorem convolutionMapCLM_apply (f : ConvolutionAlgebra α μ) :
    φ.convolutionMapCLM μ f = φ.convolutionMap μ f :=
  (rfl)

variable [BorelSpace G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The equivariant convolution map on the twisted L¹ completions. -/
def convolutionMapL1 :
    Completion (ConvolutionAlgebra α μ) →⋆ₙₐ[ℂ] Completion (ConvolutionAlgebra β μ) where
  toFun := (toComplL.comp (φ.convolutionMapCLM μ)).fromCompletion
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f g => simp only [← Completion.coe_mul',
        ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.comp_apply,
        coe_toComplL, convolutionMapCLM_apply, map_mul]
  map_star' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f => simp only [← Completion.coe_star,
        ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.comp_apply,
        coe_toComplL, convolutionMapCLM_apply, map_star]

/-- The L¹ map extends the pointwise coefficient map on compact-support functions. -/
@[simp]
theorem convolutionMapL1_coe (f : ConvolutionAlgebra α μ) :
    φ.convolutionMapL1 μ f = (φ.convolutionMap μ f : Completion (ConvolutionAlgebra β μ)) := by
  simp [convolutionMapL1]

/-- The extended convolution map is continuous. -/
@[fun_prop]
theorem continuous_convolutionMapL1 : Continuous (φ.convolutionMapL1 μ) :=
  (toComplL.comp (φ.convolutionMapCLM μ)).fromCompletion.continuous

/-- Equivariant coefficient maps decrease the norm on the twisted L¹ completions. -/
theorem norm_convolutionMapL1_le (x : Completion (ConvolutionAlgebra α μ)) :
    ‖φ.convolutionMapL1 μ x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih f => simpa using φ.norm_convolutionMap_le μ f

/-- The identity coefficient map induces the identity on the L¹ completion. -/
@[simp]
theorem convolutionMapL1_id :
    (Hom.id α).convolutionMapL1 μ =
      NonUnitalStarAlgHom.id ℂ (Completion (ConvolutionAlgebra α μ)) := by
  ext x
  simp only [NonUnitalStarAlgHom.coe_id, id_eq]
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

/-- The L¹ extensions preserve composition of equivariant coefficient maps. -/
@[simp]
theorem convolutionMapL1_comp (ψ : Hom β γ) :
    (ψ.comp φ).convolutionMapL1 μ = (ψ.convolutionMapL1 μ).comp (φ.convolutionMapL1 μ) := by
  ext x
  simp only [NonUnitalStarAlgHom.comp_apply]
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

end TauCeti.CStarAction.Hom

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A B H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}
  (P : CovariantRepresentation β H) (φ : Hom α β) (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] [BorelSpace G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Pullback and integration commute on the twisted L¹ completions. -/
theorem integratedOperatorL1_comap (x : Completion (ConvolutionAlgebra α μ)) :
    (P.comap φ).integratedOperatorL1 μ x =
      P.integratedOperatorL1 μ (φ.convolutionMapL1 μ x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simpa using P.integratedOperator_comap φ μ f

end TauCeti.CStarAction.CovariantRepresentation

namespace TauCeti.CStarAction.Hom

universe u v

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B} (φ : Hom α β)
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Equivariant coefficient maps decrease the full seminorm, using the same indexing universe
for the source and target covariant representations. -/
theorem fullSeminorm_convolutionMap_le (f : ConvolutionAlgebra α μ) :
    ConvolutionAlgebra.fullSeminorm β μ (φ.convolutionMap μ f) ≤
      ConvolutionAlgebra.fullSeminorm α μ f := by
  refine (ConvolutionAlgebra.fullSeminorm_le_iff (apply_nonneg _ f)).2 fun H _ _ _ P => ?_
  simpa only [CovariantRepresentation.integratedStarAlgHom_apply,
    ← CovariantRepresentation.integratedOperator_comap] using
    ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm (P.comap φ) f

end TauCeti.CStarAction.Hom
