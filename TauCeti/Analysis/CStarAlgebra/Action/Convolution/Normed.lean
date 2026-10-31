/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The L¹ norm on the twisted convolution algebra

Equip `CStarAction.ConvolutionAlgebra α μ` with the seminorm `∫ s, ‖f s‖ ∂μ`, by pulling back
the norm of the Bochner `L¹` space. For a left-invariant measure the convolution estimate makes
this a nonunital seminormed ring. If every nonempty open set has positive measure, as for Haar
measure, it is a nonunital normed ring: continuous functions that agree almost everywhere agree
everywhere. The scalar action makes it a complex normed space. For a left-invariant measure the
twisted involution is an L¹ isometry, `‖f*‖₁ = ‖f‖₁`, because the modular weight in
`f*(s) = c(s) • α s (star (f s⁻¹))` is the density of the inverted Haar measure.

These structures give the compact-support convolution algebra its L¹ topology, used for extending
bounded integrated representations and completing the algebra. The map `toL1` records its
realization in the ordinary coefficient-valued Bochner space; `toL1LI` is its linear isometric
version. Multiplication in that Bochner space is not the pointwise product.

The completion `UniformSpace.Completion (ConvolutionAlgebra α μ)` is the twisted L¹ Banach
⋆-algebra, Williams's `L¹(G, A)`. The instances of `TauCeti.Analysis.Normed.Ring.Completion`,
`TauCeti.Topology.Algebra.UniformRing` and `TauCeti.Analysis.CStarAlgebra.Completion` make it a
complete nonunital normed ring and ⋆-ring with isometric star. The canonical map from the compactly
supported functions has dense image; it is an embedding when every nonempty open set has positive
measure, so that the L¹ seminorm is a norm.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction.ConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G] [OpensMeasurableSpace G]
  {α : CStarAction G A} {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-- Realize a compactly supported convolution coefficient as a Bochner L¹ class. -/
def toL1 : ConvolutionAlgebra α μ →ₗ[ℂ] Lp A 1 μ where
  toFun f := f.ofConv.integrable.toL1 f.ofConv
  map_add' f g := by
    simpa only [ofConv_add, CompactlySupportedContinuousMap.coe_add] using
      Integrable.toL1_add (f.ofConv : G → A) (g.ofConv : G → A)
        f.ofConv.integrable g.ofConv.integrable
  map_smul' c f := by
    simpa only [ofConv_smul, CompactlySupportedContinuousMap.coe_smul, RingHom.id_apply] using
      Integrable.toL1_smul' (f.ofConv : G → A) f.ofConv.integrable c

/-- The L¹ class of a convolution coefficient is represented by its underlying function. -/
theorem coeFn_toL1 (f : ConvolutionAlgebra α μ) : toL1 f =ᵐ[μ] f.ofConv :=
  f.ofConv.integrable.coeFn_toL1

/-- The convolution algebra carries the L¹ seminorm, even for measures without full support. -/
instance : SeminormedAddCommGroup (ConvolutionAlgebra α μ) :=
  .induced _ _ (toL1 (α := α) (μ := μ)).toAddMonoidHom

/-- The L¹ seminorm is compatible with the complex scalar action. -/
instance : NormedSpace ℂ (ConvolutionAlgebra α μ) :=
  .induced ℂ _ _ (toL1 (α := α) (μ := μ))

/-- The norm of a convolution coefficient is its integral norm. -/
theorem norm_eq_integral_norm (f : ConvolutionAlgebra α μ) : ‖f‖ = ∫ s, ‖f.ofConv s‖ ∂μ := by
  exact (L1.norm_eq_integral_norm (toL1 f)).trans
    (integral_congr_ae ((coeFn_toL1 f).fun_comp norm))

@[simp]
theorem norm_toConv (f : C_c(G, A)) :
    ‖(toConv f : ConvolutionAlgebra α μ)‖ = ∫ s, ‖f s‖ ∂μ :=
  norm_eq_integral_norm _

variable (α μ) in
/-- The linear isometry from the convolution algebra with its L¹ seminorm to Bochner L¹. -/
def toL1LI : ConvolutionAlgebra α μ →ₗᵢ[ℂ] Lp A 1 μ where
  __ := toL1
  norm_map' _ := (rfl)

@[simp]
theorem toL1LI_apply (f : ConvolutionAlgebra α μ) : toL1LI α μ f = toL1 f :=
  (rfl)

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Twisted convolution is submultiplicative for the L¹ seminorm. -/
instance : NonUnitalSeminormedRing (ConvolutionAlgebra α μ) where
  __ : SeminormedAddCommGroup (ConvolutionAlgebra α μ) := inferInstance
  __ : NonUnitalRing (ConvolutionAlgebra α μ) := inferInstance
  norm_mul_le f g := by
    simpa only [norm_eq_integral_norm, ofConv_mul] using
      α.integral_norm_convolution_le μ f.ofConv g.ofConv

end Multiplication

section FullSupport

variable [μ.IsOpenPosMeasure]

/-- Full support of the measure makes the realization of continuous coefficients injective. -/
theorem toL1_injective : Function.Injective (toL1 (α := α) (μ := μ)) := by
  intro f g h
  apply ext
  exact CompactlySupportedContinuousMap.ext fun s => congrFun
    (Measure.eq_of_ae_eq ((coeFn_toL1 f).symm.trans (h ▸ coeFn_toL1 g))
      f.ofConv.continuous g.ofConv.continuous) s

/-- For a full-support measure the L¹ seminorm separates convolution coefficients. -/
instance : NormedAddCommGroup (ConvolutionAlgebra α μ) :=
  .ofSeparation fun f hf => toL1_injective <| by
    rw [map_zero]
    exact norm_eq_zero.1 (((toL1LI α μ).norm_map f).trans hf)

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- For Haar measure the twisted convolution algebra is a nonunital normed ring. -/
instance : NonUnitalNormedRing (ConvolutionAlgebra α μ) where
  __ : NonUnitalSeminormedRing (ConvolutionAlgebra α μ) := inferInstance
  __ : NormedAddCommGroup (ConvolutionAlgebra α μ) := inferInstance

end FullSupport

section Star

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsMulLeftInvariant]

/-- For a left-invariant measure the twisted involution is an isometry for the L¹ seminorm,
`‖f*‖₁ = ‖f‖₁`: the modular weight in `f*(s) = c(s) • α s (star (f s⁻¹))` is exactly the density
of the inverted Haar measure. -/
theorem norm_star (f : ConvolutionAlgebra α μ) : ‖star f‖ = ‖f‖ := by
  simp only [norm_eq_integral_norm, ofConv_star, norm_twistedInvolution_apply]
  -- On compactly supported continuous integrands `μ` is a multiple of a Haar measure, for which
  -- this is the inversion formula.
  have hc : Continuous fun s => (Measure.modularCharacter s : ℝ) * ‖f.ofConv s⁻¹‖ :=
    (NNReal.continuous_coe.comp continuous_modularCharacter).mul
      (f.ofConv.continuous.comp continuous_inv).norm
  have hcs : HasCompactSupport fun s => (Measure.modularCharacter s : ℝ) * ‖f.ofConv s⁻¹‖ :=
    (f.ofConv.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).norm.mul_left
  rw [Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ Measure.haar hc hcs,
    Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (f := fun s => ‖f.ofConv s‖)
      μ Measure.haar f.ofConv.continuous.norm f.ofConv.hasCompactSupport.norm,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simpa only [smul_eq_mul] using congrArg _ (integral_modularCharacter_smul_inv_eq_self
    (μ := Measure.haar) (f := fun s => ‖f.ofConv s‖) f.ofConv.continuous.norm
    f.ofConv.hasCompactSupport.norm)

/-- For a left-invariant measure the twisted convolution algebra is a seminormed ⋆-algebra. Its
completion `UniformSpace.Completion (ConvolutionAlgebra α μ)` is the twisted L¹ Banach
⋆-algebra. -/
instance : NormedStarGroup (ConvolutionAlgebra α μ) :=
  ⟨fun f => (norm_star f).le⟩

end Star

end TauCeti.CStarAction.ConvolutionAlgebra
