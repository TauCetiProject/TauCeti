/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Functoriality
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1

/-!
# Bochner `Lᵖ` equivariant functoriality

This file extends `TauCeti.Analysis.CStarAlgebra.Action.Convolution.Functoriality` and
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1` with Bochner `Lᵖ` functoriality:

* `TauCeti.CStarAction.Hom.mapLp`: contractive functoriality `Lp A p μ →L[ℂ] Lp B p μ` of an
  equivariant homomorphism, intertwining `actionLp`, `translateLp`, `convolutionLp`,
  `convolutionMapL1`, and `twistedInvolutionL1`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §§2.5, 3.2.
-/

public section

noncomputable section

open Filter Function MeasureTheory Topology UniformSpace
open scoped CompactlySupported CStarAlgebra ENNReal NNReal

namespace TauCeti.CStarAction

/-! ### Equivariant functoriality on Bochner `Lᵖ` -/

namespace Hom

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}

section MapLp

variable [MeasurableSpace G] (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pointwise application of an equivariant C⋆-algebra homomorphism `φ : Hom α β` on `Lp A p μ`,
as a contractive continuous linear map `Lp A p μ →L[ℂ] Lp B p μ`. -/
def mapLp (φ : Hom α β) : Lp A p μ →L[ℂ] Lp B p μ :=
  φ.toNonUnitalStarAlgHom.toContinuousLinearMap.compLpL p μ

variable {μ p}

/-- `Hom.mapLp` is composition on `Lp` with `φ.toNonUnitalStarAlgHom.toContinuousLinearMap`. -/
theorem mapLp_eq_compLpL (φ : Hom α β) :
    φ.mapLp μ p = φ.toNonUnitalStarAlgHom.toContinuousLinearMap.compLpL p μ :=
  (rfl)

/-- Pointwise almost-everywhere formula for `Hom.mapLp`. -/
theorem coeFn_mapLp (φ : Hom α β) (u : Lp A p μ) : φ.mapLp μ p u =ᵐ[μ] fun s => φ (u s) := by
  simpa only [mapLp_eq_compLpL, NonUnitalStarAlgHom.coe_toContinuousLinearMap,
    coe_toNonUnitalStarAlgHom] using
    φ.toNonUnitalStarAlgHom.toContinuousLinearMap.coeFn_compLpL (p := p) (μ := μ) u

/-- `Hom.mapLp` is a contraction: `‖φ.mapLp μ p‖ ≤ 1`. -/
theorem norm_mapLp_le (φ : Hom α β) : ‖φ.mapLp μ p‖ ≤ 1 := by
  rw [mapLp_eq_compLpL]
  exact (φ.toNonUnitalStarAlgHom.toContinuousLinearMap.norm_compLpL_le (p := p) (μ := μ)).trans
    φ.toNonUnitalStarAlgHom.norm_toContinuousLinearMap_le

/-- The identity equivariant homomorphism induces the identity on `Lp A p μ`. -/
@[simp]
theorem mapLp_id : (Hom.id α).mapLp μ p = ContinuousLinearMap.id ℂ (Lp A p μ) := by
  rw [mapLp_eq_compLpL]
  have hid : (Hom.id α).toNonUnitalStarAlgHom.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ A := by ext a; simp
  rw [hid, ContinuousLinearMap.id_compLpL]

/-- `Hom.mapLp` preserves composition of equivariant homomorphisms. -/
@[simp]
theorem mapLp_comp (ψ : Hom β γ) (φ : Hom α β) :
    (ψ.comp φ).mapLp μ p = (ψ.mapLp μ p).comp (φ.mapLp μ p) := by
  rw [mapLp_eq_compLpL, mapLp_eq_compLpL, mapLp_eq_compLpL,
    ContinuousLinearMap.compLpL_comp_compLpL]
  congr 1; ext a; simp

/-- `Hom.mapLp` intertwines the pointwise action `actionLp`. -/
theorem mapLp_actionLp (φ : Hom α β) (r : G) (u : Lp A p μ) :
    φ.mapLp μ p (α.actionLp μ p r u) = β.actionLp μ p r (φ.mapLp μ p u) := by
  refine Lp.ext ?_
  filter_upwards [φ.coeFn_mapLp (α.actionLp μ p r u), α.coeFn_actionLp r u,
    β.coeFn_actionLp r (φ.mapLp μ p u), φ.coeFn_mapLp u] with s h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- `Hom.mapLp` intertwines twisted left translation `translateLp`. -/
theorem mapLp_translateLp [MeasurableMul G] [μ.IsMulLeftInvariant] (φ : Hom α β) (r : G)
    (u : Lp A p μ) :
    φ.mapLp μ p (α.translateLp μ p r u) = β.translateLp μ p r (φ.mapLp μ p u) := by
  refine Lp.ext ?_
  filter_upwards [φ.coeFn_mapLp (α.translateLp μ p r u), α.coeFn_translateLp r u,
    β.coeFn_translateLp r (φ.mapLp μ p u),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae (φ.coeFn_mapLp u)]
    with s h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- `Hom.mapLp` intertwines twisted Bochner convolution `convolutionLp`. -/
theorem mapLp_convolutionLp [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] (hp : p ≠ ∞) (φ : Hom α β)
    (h : Lp A 1 μ) (f : Lp A p μ) :
    φ.mapLp μ p (α.convolutionLp μ p hp h f) =
      β.convolutionLp μ p hp (φ.mapLp μ 1 h) (φ.mapLp μ p f) := by
  rw [α.convolutionLp_apply,
    ← (φ.mapLp μ p).integral_comp_comm
      (α.integrable_compLp_mul_translateLp μ hp (L1.integrable_coeFn h) f),
    β.convolutionLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [φ.coeFn_mapLp h] with y hy
  rw [hy, ← φ.mapLp_translateLp y f, mapLp_eq_compLpL, ContinuousLinearMap.compLpL_apply,
    ContinuousLinearMap.compLp_compLp, ContinuousLinearMap.compLpL_apply,
    ContinuousLinearMap.compLp_compLp]
  congr 1; ext a; simp

end MapLp

section Completion

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] (φ : Hom α β)
  (μ : Measure G)

/-- `toL1` intertwines `Hom.convolutionMap` with `Hom.mapLp`. -/
@[simp]
theorem toL1_convolutionMap [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (f : ConvolutionAlgebra α μ) :
    ConvolutionAlgebra.toL1 (φ.convolutionMap μ f) = φ.mapLp μ 1 (ConvolutionAlgebra.toL1 f) := by
  refine Lp.ext ?_
  filter_upwards [ConvolutionAlgebra.coeFn_toL1 (φ.convolutionMap μ f),
    φ.coeFn_mapLp (ConvolutionAlgebra.toL1 f), ConvolutionAlgebra.coeFn_toL1 f] with s h₁ h₂ h₃
  simp [h₁, h₂, h₃]

end Completion

section CompletionL1

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (φ : Hom α β) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- `toL1FromCompletion` intertwines `Hom.convolutionMapL1` with `Hom.mapLp`. -/
@[simp]
theorem toL1FromCompletion_convolutionMapL1 (x : Completion (ConvolutionAlgebra α μ)) :
    ConvolutionAlgebra.toL1FromCompletion β μ (φ.convolutionMapL1 μ x) =
      φ.mapLp μ 1 (ConvolutionAlgebra.toL1FromCompletion α μ x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

variable [μ.InnerRegularCompactLTTop]

/-- `completionEquivL1` intertwines `Hom.convolutionMapL1` with `Hom.mapLp`. -/
@[simp]
theorem completionEquivL1_convolutionMapL1 (x : Completion (ConvolutionAlgebra α μ)) :
    ConvolutionAlgebra.completionEquivL1 β μ (φ.convolutionMapL1 μ x) =
      φ.mapLp μ 1 (ConvolutionAlgebra.completionEquivL1 α μ x) := by
  rw [← ConvolutionAlgebra.toL1FromCompletion_eq_completionEquivL1,
    ← ConvolutionAlgebra.toL1FromCompletion_eq_completionEquivL1,
    φ.toL1FromCompletion_convolutionMapL1 μ x]

/-- The inverse of `completionEquivL1` intertwines `Hom.mapLp` with `Hom.convolutionMapL1`. -/
@[simp]
theorem completionEquivL1_symm_mapLp (u : Lp A 1 μ) :
    (ConvolutionAlgebra.completionEquivL1 β μ).symm (φ.mapLp μ 1 u) =
      φ.convolutionMapL1 μ ((ConvolutionAlgebra.completionEquivL1 α μ).symm u) :=
  (ConvolutionAlgebra.completionEquivL1 β μ).injective <| by simp

/-- `Hom.mapLp` intertwines the twisted involution `twistedInvolutionL1`. -/
theorem mapLp_twistedInvolutionL1 (u : Lp A 1 μ) :
    φ.mapLp μ 1 (α.twistedInvolutionL1 μ u) = β.twistedInvolutionL1 μ (φ.mapLp μ 1 u) := by
  rw [← LinearIsometryEquiv.apply_symm_apply (ConvolutionAlgebra.completionEquivL1 α μ) u,
    ← ConvolutionAlgebra.completionEquivL1_star, ← φ.completionEquivL1_convolutionMapL1,
    map_star, ConvolutionAlgebra.completionEquivL1_star,
    φ.completionEquivL1_convolutionMapL1, LinearIsometryEquiv.apply_symm_apply]

end CompletionL1

end Hom

end TauCeti.CStarAction
