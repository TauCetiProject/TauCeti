/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.Hom

/-!
# Equivariant maps of twisted convolution algebras

An equivariant coefficient homomorphism induces a nonunital star-algebra homomorphism
between the compact-support twisted convolution algebras, by pointwise application.
These maps preserve identities and composition, and are injective whenever the coefficient
homomorphism is injective. They supply the dense-algebra maps for crossed-product functoriality.

The measure need only be finite on compact sets for compatibility with convolution. Left
invariance supplies associativity; no unitality, nondegeneracy, separability, or
global σ-finiteness is needed.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported CStarAlgebra

namespace TauCeti.CStarAction.Hom

variable {G A B C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}

section Convolution

variable [MeasurableSpace G] [OpensMeasurableSpace G]

/-- Pointwise application of an equivariant coefficient homomorphism commutes with twisted
convolution. -/
theorem map_convolution (φ : Hom α β) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f g : C_c(G, A)) (s : G) :
    φ (α.convolution μ f g s) = ∫ r, φ (f r) * β r (φ (g (r⁻¹ * s))) ∂μ := by
  let L : A →L[ℂ] B :=
    { toLinearMap := (φ : A →ₗ[ℂ] B), cont := map_continuous _ }
  have hL (a : A) : L a = φ a := rfl
  have hint : Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
    (by fun_prop : Continuous fun r => f r * α r (g (r⁻¹ * s))).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  rw [convolution_apply]
  exact (L.integral_comp_comm hint).symm.trans (by simp only [hL, map_mul, map_action])

end Convolution

variable [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

/-- The map of compact-support twisted convolution algebras induced by an equivariant
coefficient homomorphism. -/
def convolutionMap (φ : Hom α β) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] :
    ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] ConvolutionAlgebra β μ where
  toFun f := .toConv (f.ofConv.compLeft ⟨φ, map_continuous φ.toNonUnitalStarAlgHom⟩)
  map_zero' := by
    apply ConvolutionAlgebra.ext
    ext s
    simp [CompactlySupportedContinuousMap.compLeft_apply
      (g := ⟨φ, map_continuous φ⟩) (map_zero φ)]
  map_add' f g := by
    apply ConvolutionAlgebra.ext
    ext s
    simp [CompactlySupportedContinuousMap.compLeft_apply
      (g := ⟨φ, map_continuous φ⟩) (map_zero φ)]
  map_smul' c f := by
    apply ConvolutionAlgebra.ext
    ext s
    simp [CompactlySupportedContinuousMap.compLeft_apply
      (g := ⟨φ, map_continuous φ⟩) (map_zero φ)]
  map_mul' f g := by
    apply ConvolutionAlgebra.ext
    ext s
    simp only [ConvolutionAlgebra.ofConv_mul,
      CompactlySupportedContinuousMap.compLeft_apply
      (g := ⟨φ, map_continuous φ⟩) (map_zero φ), ContinuousMap.coe_mk]
    rw [map_convolution, convolution_apply]
    simp only [CompactlySupportedContinuousMap.compLeft_apply
      (g := ⟨φ, map_continuous φ⟩) (map_zero φ), ContinuousMap.coe_mk]
  map_star' f := by
    apply ConvolutionAlgebra.ext
    ext s
    simp only [ConvolutionAlgebra.ofConv_star, twistedInvolution_apply,
      CompactlySupportedContinuousMap.compLeft_apply
        (g := ⟨φ, map_continuous φ⟩) (map_zero φ), ContinuousMap.coe_mk,
      map_smul, map_action, map_star]

variable {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-- The induced map applies the coefficient homomorphism at each group element. -/
@[simp]
theorem convolutionMap_apply (φ : Hom α β) (f : ConvolutionAlgebra α μ) (s : G) :
    (φ.convolutionMap μ f).ofConv s = φ (f.ofConv s) :=
  CompactlySupportedContinuousMap.compLeft_apply
    (g := ⟨φ, map_continuous φ⟩) (map_zero φ) _ _

/-- The identity coefficient map induces the identity convolution map. -/
@[simp]
theorem convolutionMap_id :
    (Hom.id α).convolutionMap μ = NonUnitalStarAlgHom.id ℂ (ConvolutionAlgebra α μ) := by
  ext f s
  simp

/-- Induced convolution maps preserve composition of equivariant coefficient maps. -/
@[simp]
theorem convolutionMap_comp (ψ : Hom β γ) (φ : Hom α β) :
    (ψ.comp φ).convolutionMap μ = (ψ.convolutionMap μ).comp (φ.convolutionMap μ) := by
  ext f s
  simp

/-- A faithful coefficient map induces a faithful map of compact-support convolution algebras. -/
theorem convolutionMap_injective (φ : Hom α β) (hφ : Function.Injective φ) :
    Function.Injective (φ.convolutionMap μ) := by
  intro f g h
  apply ConvolutionAlgebra.ext
  ext s
  apply hφ
  simpa using congrArg (fun k : ConvolutionAlgebra β μ => k.ofConv s) h

end TauCeti.CStarAction.Hom
