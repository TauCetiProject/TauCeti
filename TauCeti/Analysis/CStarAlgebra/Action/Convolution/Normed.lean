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

`TauCeti.CompactlySupportedL1` supplies `ConvolutionAlgebra α μ` with the `L¹` seminorm
`∫ s, ‖f.toFun s‖ ∂μ` (`SeminormedAddCommGroup`, `NormedSpace`), the realization
`CompactlySupportedL1.toL1` and linear isometry `CompactlySupportedL1.toL1LI` into Bochner
`Lp A 1 μ`, and separation (`NormedAddCommGroup`) when every nonempty open set has positive
measure.

This file adds the algebraic norm bounds and star-isometry structure for `ConvolutionAlgebra α μ`:
for a left-invariant measure the convolution estimate makes it a `NonUnitalSeminormedRing` (and a
`NonUnitalNormedRing` for full-support measures), and the twisted involution is an `L¹` isometry
(`norm_star`, `NormedStarGroup`), because the modular weight in `f*(s) = c(s) • α s (star (f s⁻¹))`
is the density of the inverted Haar measure.

The completion `UniformSpace.Completion (ConvolutionAlgebra α μ)` is the twisted L¹ Banach
⋆-algebra, Williams's `L¹(G, A)`. The instances of `TauCeti.Analysis.Normed.Ring.Completion`,
`TauCeti.Topology.Algebra.UniformRing` and `TauCeti.Analysis.CStarAlgebra.Completion` make it a
complete nonunital normed ring and ⋆-ring with isometric star.

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

/-- The `L¹` norm of an elementary function is `(∫ |φ|) * ‖e‖`. -/
@[simp]
theorem norm_smulRight (φ : C_c(G, ℝ)) (e : A) :
    ‖(smulRight φ e : ConvolutionAlgebra α μ)‖ = (∫ s, |φ s| ∂μ) * ‖e‖ := by
  simp [CompactlySupportedL1.norm_eq_integral_norm, norm_smul, integral_mul_const]

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

variable [μ.IsOpenPosMeasure] [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

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
