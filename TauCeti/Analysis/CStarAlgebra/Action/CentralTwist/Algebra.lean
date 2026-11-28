/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Convolution

/-!
# The cocycle-twisted convolution ⋆-algebra and its L¹ norm

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A`, a
normalized continuous central multiplier cocycle `ω : CentralCocycle α`, and a measure `μ` on `G`,
`TwistedConvolutionAlgebra ω μ` is an abbreviation for `CompactlySupportedL1 ω A μ`, wrapping
`C_c(G, A)` with `ω.convolution μ`, `ω.involution`, and the Bochner `L¹` seminorm `∫ s, ‖f s‖ ∂μ`.
When `G` is locally compact and Borel and `μ` is left-invariant and finite on compact sets,
`TwistedConvolutionAlgebra ω μ` is a complex `StarRing` and `NormedStarGroup` whose uniform
completion `UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)` is the cocycle-twisted `L¹`
Banach ⋆-algebra `L¹(G, A, α, ω)`. When `G` is a weakly locally compact `R₁` Borel space and `μ` is
finite on compact sets and inner regular for compact sets on sets of finite measure,
`CompactlySupportedL1.completionEquivL1` identifies this completion isometrically with Bochner
`Lp A 1 μ`. At `ω = 1`, `untwistStarAlgEquiv` identifies the two compact-support convolution
algebras `TwistedConvolutionAlgebra 1 μ` and `ConvolutionAlgebra α μ` isometrically as complex
`⋆`-algebras (under `LocallyCompactSpace`); without local compactness, `untwistRingEquiv` provides
the underlying isometric `ℂ`-linear ring equivalence.

## Main definitions

* `TauCeti.CStarAction.TwistedConvolutionAlgebra`: the `ω`-twisted convolution ⋆-algebra on
  `C_c(G, A)` with its `L¹` topology.
* `TauCeti.CStarAction.TwistedConvolutionAlgebra.untwistRingEquiv`: isometric `ℂ`-linear ring
  equivalence `TwistedConvolutionAlgebra (1 : CentralCocycle α) μ ≃+* ConvolutionAlgebra α μ`
  without local compactness.
* `TauCeti.CStarAction.TwistedConvolutionAlgebra.untwistStarAlgEquiv`: isometric ⋆-algebra
  equivalence
  `TwistedConvolutionAlgebra (1 : CentralCocycle α) μ ≃⋆ₐ[ℂ] ConvolutionAlgebra α μ`.

## References

* J. Packer and I. Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc. Cambridge
  Philos. Soc. 106 (1989), 293–311, Section 2.
* D. P. Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A] [MeasurableSpace G]

/-- The `ω`-twisted convolution ⋆-algebra of `(A, G, α, ω)` with respect to `μ`: compactly
supported continuous functions `G → A` equipped with `ω.convolution μ`, `ω.involution`, and the
Bochner `L¹` seminorm. -/
abbrev TwistedConvolutionAlgebra {α : CStarAction G A} (ω : CentralCocycle α)
    (μ : Measure G) : Type _ :=
  CompactlySupportedL1 ω A μ

namespace TwistedConvolutionAlgebra

variable {α : CStarAction G A} {ω : CentralCocycle α} {μ : Measure G}

/-! ### Cocycle-twisted convolution product -/

section Mul

variable [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

instance : Mul (TwistedConvolutionAlgebra ω μ) where
  mul f g := CompactlySupportedL1.ofFun (ω.convolution μ f.toFun g.toFun)

@[simp] theorem toFun_mul (f g : TwistedConvolutionAlgebra ω μ) :
    (f * g).toFun = ω.convolution μ f.toFun g.toFun := (rfl)

@[simp] theorem ofFun_convolution (f g : C_c(G, A)) :
    (CompactlySupportedL1.ofFun (ω.convolution μ f g) : TwistedConvolutionAlgebra ω μ) =
      CompactlySupportedL1.ofFun f * CompactlySupportedL1.ofFun g := (rfl)

instance : NonUnitalNonAssocRing (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.nonUnitalNonAssocRingOf (fun f g => ω.convolution μ f g) toFun_mul
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ => by simp) (fun _ => by simp)

instance :
    IsScalarTower ℂ (TwistedConvolutionAlgebra ω μ) (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.isScalarTowerOf (fun f g => ω.convolution μ f g) toFun_mul
    fun _ _ _ => by simp

instance :
    SMulCommClass ℂ (TwistedConvolutionAlgebra ω μ) (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.smulCommClassOf (fun f g => ω.convolution μ f g) toFun_mul
    fun _ _ _ => by simp

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

instance instNonUnitalRing : NonUnitalRing (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.nonUnitalRingOf (fun f g => ω.convolution μ f g) toFun_mul
    fun _ _ _ => by simp [CentralCocycle.convolution_assoc]

end Mul

/-! ### Cocycle-twisted involution -/

section Star

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

instance : Star (TwistedConvolutionAlgebra ω μ) where
  star f := CompactlySupportedL1.ofFun (ω.involution f.toFun)

@[simp] theorem toFun_star (f : TwistedConvolutionAlgebra ω μ) :
    (star f).toFun = ω.involution f.toFun := (rfl)

@[simp] theorem ofFun_involution (f : C_c(G, A)) :
    (CompactlySupportedL1.ofFun (ω.involution f) : TwistedConvolutionAlgebra ω μ) =
      star (CompactlySupportedL1.ofFun f) := (rfl)

instance : InvolutiveStar (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.involutiveStarOf ω.involution toFun_star fun _ => by simp

instance : StarModule ℂ (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.starModuleOf ω.involution toFun_star fun _ _ => by simp

variable [OpensMeasurableSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant]

instance instStarRing : StarRing (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.starRingOf (fun f g => ω.convolution μ f g) ω.involution toFun_mul
    toFun_star CompactlySupportedL1.toFun_add (fun _ _ => by simp) fun _ _ => by
      simp [CentralCocycle.involution_convolution]

end Star

/-! ### Bochner L¹ seminorm and norm -/

section Normed

variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

instance : NonUnitalSeminormedRing (TwistedConvolutionAlgebra ω μ) where
  __ : SeminormedAddCommGroup (TwistedConvolutionAlgebra ω μ) := inferInstance
  __ : NonUnitalRing (TwistedConvolutionAlgebra ω μ) := inferInstance
  norm_mul_le := CompactlySupportedL1.norm_mul_le_of (fun f g => ω.convolution μ f g) toFun_mul
    (fun f g => ω.integral_norm_convolution_le μ f g)

end Multiplication

section FullSupport

variable [μ.IsOpenPosMeasure] [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

instance : NonUnitalNormedRing (TwistedConvolutionAlgebra ω μ) where
  __ : NonUnitalSeminormedRing (TwistedConvolutionAlgebra ω μ) := inferInstance
  __ : NormedAddCommGroup (TwistedConvolutionAlgebra ω μ) := inferInstance

end FullSupport

end Normed

section NormedStar

variable [IsFiniteMeasureOnCompacts μ] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [BorelSpace G] [μ.IsMulLeftInvariant]

/-- For a left-invariant Borel measure finite on compact sets on a locally compact topological
group, `TwistedConvolutionAlgebra ω μ` is a seminormed ⋆-algebra (`‖star f‖ = ‖f‖` by Mathlib's
generic `norm_star`). -/
instance : NormedStarGroup (TwistedConvolutionAlgebra ω μ) :=
  CompactlySupportedL1.normedStarGroupOf ω.involution toFun_star (ω.integral_norm_involution μ)

end NormedStar

/-! ### Comparison with the untwisted convolution algebra at `ω = 1` -/

section Untwisted

variable (α μ) [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

/-- For the trivial cocycle `1 : CentralCocycle α`, `TwistedConvolutionAlgebra 1 μ` is canonically
and isometrically isomorphic as a nonunital ring (and `ℂ`-linearly, via `untwistRingEquiv_smul`)
to `ConvolutionAlgebra α μ`, without requiring local compactness. -/
def untwistRingEquiv :
    TwistedConvolutionAlgebra (1 : CentralCocycle α) μ ≃+* ConvolutionAlgebra α μ where
  toFun f := CompactlySupportedL1.ofFun f.toFun
  invFun f := CompactlySupportedL1.ofFun f.toFun
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by ext1; simp
  map_mul' _ _ := by ext1; simp

@[simp] theorem toFun_untwistRingEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (untwistRingEquiv α μ f).toFun = f.toFun := (rfl)

@[simp] theorem toFun_untwistRingEquiv_symm (f : ConvolutionAlgebra α μ) :
    ((untwistRingEquiv α μ).symm f).toFun = f.toFun := (rfl)

@[simp] theorem untwistRingEquiv_smul (c : ℂ)
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    untwistRingEquiv α μ (c • f) = c • untwistRingEquiv α μ f := by
  ext1; simp

@[simp] theorem untwistRingEquiv_symm_smul (c : ℂ) (f : ConvolutionAlgebra α μ) :
    (untwistRingEquiv α μ).symm (c • f) = c • (untwistRingEquiv α μ).symm f := by
  ext1; simp

@[simp] theorem norm_untwistRingEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    ‖untwistRingEquiv α μ f‖ = ‖f‖ := by
  simp [CompactlySupportedL1.norm_eq_integral_norm, toFun_untwistRingEquiv]

@[simp] theorem norm_untwistRingEquiv_symm (f : ConvolutionAlgebra α μ) :
    ‖(untwistRingEquiv α μ).symm f‖ = ‖f‖ := by
  simp [CompactlySupportedL1.norm_eq_integral_norm, toFun_untwistRingEquiv_symm]

section LocallyCompact

variable [LocallyCompactSpace G]

/-- For the trivial cocycle `1 : CentralCocycle α` over a locally compact group,
`untwistRingEquiv` upgrades to an isometric complex nonunital ⋆-algebra equivalence
`TwistedConvolutionAlgebra 1 μ ≃⋆ₐ[ℂ] ConvolutionAlgebra α μ`. -/
def untwistStarAlgEquiv :
    TwistedConvolutionAlgebra (1 : CentralCocycle α) μ ≃⋆ₐ[ℂ]
      ConvolutionAlgebra α μ where
  __ := untwistRingEquiv α μ
  map_smul' := untwistRingEquiv_smul α μ
  map_star' _ := by ext1; simp

@[simp] theorem toRingEquiv_untwistStarAlgEquiv :
    (untwistStarAlgEquiv α μ).toRingEquiv = untwistRingEquiv α μ := (rfl)

@[simp] theorem toFun_untwistStarAlgEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (untwistStarAlgEquiv α μ f).toFun = f.toFun := (rfl)

@[simp] theorem toFun_untwistStarAlgEquiv_symm (f : ConvolutionAlgebra α μ) :
    ((untwistStarAlgEquiv α μ).symm f).toFun = f.toFun := (rfl)

@[simp] theorem norm_untwistStarAlgEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    ‖untwistStarAlgEquiv α μ f‖ = ‖f‖ :=
  norm_untwistRingEquiv α μ f

@[simp] theorem norm_untwistStarAlgEquiv_symm (f : ConvolutionAlgebra α μ) :
    ‖(untwistStarAlgEquiv α μ).symm f‖ = ‖f‖ :=
  norm_untwistRingEquiv_symm α μ f

end LocallyCompact

end Untwisted

end TwistedConvolutionAlgebra

end TauCeti.CStarAction
