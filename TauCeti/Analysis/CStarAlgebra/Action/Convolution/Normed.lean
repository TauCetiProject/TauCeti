/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported
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
  [MeasurableSpace G]

section OpensMeasurable

variable [OpensMeasurableSpace G] {α : CStarAction G A} {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

/-- Realize a compactly supported convolution coefficient as a Bochner L¹ class. -/
abbrev toL1 : ConvolutionAlgebra α μ →ₗ[ℂ] Lp A 1 μ :=
  CompactlySupportedL1.toL1 ℂ

/-- The L¹ class of a convolution coefficient is represented by its underlying function. -/
theorem coeFn_toL1 (f : ConvolutionAlgebra α μ) : toL1 f =ᵐ[μ] f.ofConv :=
  CompactlySupportedL1.coeFn_toL1 ℂ f

/-- The norm of a convolution coefficient is its integral norm. -/
theorem norm_eq_integral_norm (f : ConvolutionAlgebra α μ) : ‖f‖ = ∫ s, ‖f.ofConv s‖ ∂μ :=
  CompactlySupportedL1.norm_eq_integral_norm f

theorem norm_toConv (f : C_c(G, A)) :
    ‖(toConv f : ConvolutionAlgebra α μ)‖ = ∫ s, ‖f s‖ ∂μ :=
  CompactlySupportedL1.norm_toConv f

/-- The `L¹` norm of an elementary function is `(∫ |φ|) * ‖e‖`. -/
@[simp]
theorem norm_smulRight (φ : C_c(G, ℝ)) (e : A) :
    ‖(smulRight φ e : ConvolutionAlgebra α μ)‖ = (∫ s, |φ s| ∂μ) * ‖e‖ := by
  simp [norm_eq_integral_norm, norm_smul, integral_mul_const]

variable (α μ) in
/-- The linear isometry from the convolution algebra with its L¹ seminorm to Bochner L¹. -/
abbrev toL1LI : ConvolutionAlgebra α μ →ₗᵢ[ℂ] Lp A 1 μ :=
  CompactlySupportedL1.toL1LI α A μ ℂ

theorem toL1LI_apply (f : ConvolutionAlgebra α μ) : toL1LI α μ f = toL1 f :=
  CompactlySupportedL1.toL1LI_apply ℂ f

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Twisted convolution is submultiplicative for the L¹ seminorm. -/
instance : NonUnitalSeminormedRing (ConvolutionAlgebra α μ) where
  __ : SeminormedAddCommGroup (ConvolutionAlgebra α μ) := inferInstance
  __ : NonUnitalRing (ConvolutionAlgebra α μ) := inferInstance
  norm_mul_le := CompactlySupportedL1.norm_mul_le_of (fun f g => α.convolution μ f g) ofConv_mul
    (fun f g => α.integral_norm_convolution_le μ f g)

end Multiplication

section FullSupport

variable [μ.IsOpenPosMeasure]

/-- Full support of the measure makes the realization of continuous coefficients injective. -/
theorem toL1_injective : Function.Injective (toL1 (α := α) (μ := μ)) :=
  CompactlySupportedL1.toL1_injective ℂ

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- For Haar measure the twisted convolution algebra is a nonunital normed ring. -/
instance : NonUnitalNormedRing (ConvolutionAlgebra α μ) where
  __ : NonUnitalSeminormedRing (ConvolutionAlgebra α μ) := inferInstance
  __ : NormedAddCommGroup (ConvolutionAlgebra α μ) := inferInstance

end FullSupport

end OpensMeasurable

section Star

variable {α : CStarAction G A} {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsMulLeftInvariant]

/-- For a left-invariant measure the twisted involution is an isometry for the L¹ seminorm,
`‖f*‖₁ = ‖f‖₁`: the modular weight in `f*(s) = c(s) • α s (star (f s⁻¹))` is exactly the density
of the inverted Haar measure. -/
theorem norm_star (f : ConvolutionAlgebra α μ) : ‖star f‖ = ‖f‖ :=
  CompactlySupportedL1.norm_star_of α.twistedInvolution ofConv_star
    (α.integral_norm_twistedInvolution μ) f

/-- For a left-invariant measure the twisted convolution algebra is a seminormed ⋆-algebra. Its
completion `UniformSpace.Completion (ConvolutionAlgebra α μ)` is the twisted L¹ Banach
⋆-algebra. -/
instance : NormedStarGroup (ConvolutionAlgebra α μ) :=
  CompactlySupportedL1.normedStarGroupOf α.twistedInvolution ofConv_star
    (α.integral_norm_twistedInvolution μ)

end Star

end TauCeti.CStarAction.ConvolutionAlgebra
