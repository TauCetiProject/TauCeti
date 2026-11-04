/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Functoriality
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.FullSeminorm

/-!
# Pullback of covariant representations

A covariant pair for a coefficient algebra pulls back along an equivariant homomorphism.
The group representation stays the same, and the coefficient representation is composed with
the homomorphism. Vector integration identifies its integrated form with the original integrated
form applied to the induced map of compact-support convolution algebras. This is the
representation-level compatibility needed to extend coefficient maps to full crossed products.
The same compatibility holds on the twisted L¹ completions.

The coefficient map also decreases the full seminorm, when both coefficient algebras use the
same universe for the indexing family of covariant representations. This estimate supplies the
continuity needed to extend the convolution map to the full crossed-product completion.
It does not assert independence of that indexing universe.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2. The integrated
form is Tau Ceti's `CovariantRepresentation.integratedOperator`, defined by vector integration.
-/

public section

noncomputable section

open MeasureTheory UniformSpace

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A B C H : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}

/-- Pull back a covariant representation along an equivariant coefficient homomorphism. -/
def comap (P : CovariantRepresentation β H) (φ : Hom α β) : CovariantRepresentation α H where
  coefficient := P.coefficient.comp φ.toNonUnitalStarAlgHom
  group := P.group
  isUnitary := P.isUnitary
  continuous_orbit := P.continuous_orbit
  covariance g a v := by
    simpa only [NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom, φ.map_action]
      using P.covariance g (φ a) v

@[simp]
theorem comap_coefficient (P : CovariantRepresentation β H) (φ : Hom α β) :
    (P.comap φ).coefficient = P.coefficient.comp φ.toNonUnitalStarAlgHom :=
  (rfl)

@[simp]
theorem comap_group (P : CovariantRepresentation β H) (φ : Hom α β) :
    (P.comap φ).group = P.group :=
  (rfl)

/-- Pullback along the identity recovers the original covariant representation. -/
@[simp]
theorem comap_id (P : CovariantRepresentation α H) : P.comap (Hom.id α) = P := by
  apply CovariantRepresentation.ext
  · ext a v
    simp
  · simp

/-- Successive pullbacks agree with pullback along the composite coefficient map. -/
@[simp]
theorem comap_comp (P : CovariantRepresentation γ H) (ψ : Hom β γ) (φ : Hom α β) :
    (P.comap ψ).comap φ = P.comap (ψ.comp φ) := by
  apply CovariantRepresentation.ext
  · ext a v
    simp
  · simp

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G]

/-- Pullback of a covariant pair agrees with the induced convolution map under vector
integration. -/
theorem integratedOperator_comap (P : CovariantRepresentation β H) (φ : Hom α β)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : ConvolutionAlgebra α μ) :
    (P.comap φ).integratedOperator μ f.ofConv =
      P.integratedOperator μ (φ.convolutionMap μ f).ofConv := by
  ext v
  simp only [integratedOperator_apply, comap_coefficient, comap_group,
    NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom, Hom.convolutionMap_apply]

end TauCeti.CStarAction.CovariantRepresentation

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
