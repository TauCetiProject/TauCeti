/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Convolution
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact

/-!
# The cocycle-twisted convolution ⋆-algebra and its L¹ norm

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A`, a
normalized continuous central multiplier cocycle `ω : CentralCocycle α`, and a measure `μ` on `G`,
`TwistedConvolutionAlgebra ω μ` wraps `C_c(G, A)` with `ω.convolution μ`, `ω.involution`,
and the Bochner `L¹` seminorm `∫ s, ‖f s‖ ∂μ`. When `G` is locally compact and Borel and `μ` is
left-invariant, `TwistedConvolutionAlgebra ω μ` is a complex `StarRing` and `NormedStarGroup`
whose uniform completion `UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)` is the
cocycle-twisted `L¹` Banach ⋆-algebra `L¹(G, A, α, ω)`. When `G` is weakly locally compact and `μ`
is inner regular on finite-measure sets, `TwistedConvolutionAlgebra.completionEquivL1` identifies
this completion isometrically with Bochner `Lp A 1 μ`. At `ω = 1`, `untwistStarAlgEquiv` identifies
it isometrically with `ConvolutionAlgebra α μ`.

## Main definitions

* `TauCeti.CStarAction.TwistedConvolutionAlgebra`: the `ω`-twisted convolution ⋆-algebra on
  `C_c(G, A)` with its `L¹` topology.
* `TauCeti.CStarAction.TwistedConvolutionAlgebra.toL1`, `toL1LI`: linear and linear-isometric
  realizations in Bochner `Lp A 1 μ`.
* `TauCeti.CStarAction.TwistedConvolutionAlgebra.completionEquivL1`: identification of the
  twisted `L¹` completion `UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)` with Bochner
  `Lp A 1 μ`.
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
structure TwistedConvolutionAlgebra {α : CStarAction G A} (ω : CentralCocycle α)
    (μ : Measure G) where
  /-- Regard a compactly supported function as an element of the twisted convolution algebra. -/
  toConv ::
  /-- The compactly supported function underlying an element of the twisted convolution algebra. -/
  ofConv : C_c(G, A)

namespace TwistedConvolutionAlgebra

variable {α : CStarAction G A} {ω : CentralCocycle α} {μ : Measure G}

@[simp] theorem ofConv_toConv (f : C_c(G, A)) :
    (toConv f : TwistedConvolutionAlgebra ω μ).ofConv = f := (rfl)

@[simp] theorem toConv_ofConv (f : TwistedConvolutionAlgebra ω μ) : toConv f.ofConv = f := (rfl)

theorem ofConv_injective :
    Function.Injective (ofConv : TwistedConvolutionAlgebra ω μ → C_c(G, A)) :=
  fun f g h => by rw [← toConv_ofConv f, h, toConv_ofConv]

theorem toConv_injective :
    Function.Injective (toConv : C_c(G, A) → TwistedConvolutionAlgebra ω μ) :=
  fun f g h => by rw [← ofConv_toConv (ω := ω) (μ := μ) f, h, ofConv_toConv]

@[ext] theorem ext {f g : TwistedConvolutionAlgebra ω μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

variable (ω μ) in
/-- `ofConv` and `toConv` as an equivalence with `C_c(G, A)`. -/
def equiv : TwistedConvolutionAlgebra ω μ ≃ C_c(G, A) :=
  ⟨ofConv, toConv, fun _ => rfl, fun _ => rfl⟩

@[simp] theorem equiv_apply (f : TwistedConvolutionAlgebra ω μ) :
    equiv ω μ f = f.ofConv := (rfl)

@[simp] theorem equiv_symm_apply (f : C_c(G, A)) : (equiv ω μ).symm f = toConv f := (rfl)

instance : AddCommGroup (TwistedConvolutionAlgebra ω μ) := (equiv ω μ).addCommGroup

variable (ω μ) in
/-- `ofConv` as an additive equivalence with `C_c(G, A)`. -/
def addEquiv : TwistedConvolutionAlgebra ω μ ≃+ C_c(G, A) :=
  { equiv ω μ with map_add' _ _ := rfl }

@[simp] theorem addEquiv_apply (f : TwistedConvolutionAlgebra ω μ) :
    addEquiv ω μ f = f.ofConv := (rfl)

@[simp] theorem addEquiv_symm_apply (f : C_c(G, A)) : (addEquiv ω μ).symm f = toConv f := (rfl)

instance : Module ℂ (TwistedConvolutionAlgebra ω μ) := (addEquiv ω μ).module ℂ

@[simp] theorem ofConv_zero : (0 : TwistedConvolutionAlgebra ω μ).ofConv = 0 := (rfl)
@[simp] theorem ofConv_add (f g : TwistedConvolutionAlgebra ω μ) :
    (f + g).ofConv = f.ofConv + g.ofConv := (rfl)
@[simp] theorem ofConv_neg (f : TwistedConvolutionAlgebra ω μ) : (-f).ofConv = -f.ofConv := (rfl)
@[simp] theorem ofConv_sub (f g : TwistedConvolutionAlgebra ω μ) :
    (f - g).ofConv = f.ofConv - g.ofConv := (rfl)
@[simp] theorem ofConv_smul (c : ℂ) (f : TwistedConvolutionAlgebra ω μ) :
    (c • f).ofConv = c • f.ofConv := (rfl)

@[simp] theorem toConv_zero : (toConv 0 : TwistedConvolutionAlgebra ω μ) = 0 := (rfl)
@[simp] theorem toConv_add (f g : C_c(G, A)) :
    (toConv (f + g) : TwistedConvolutionAlgebra ω μ) = toConv f + toConv g := (rfl)
@[simp] theorem toConv_neg (f : C_c(G, A)) :
    (toConv (-f) : TwistedConvolutionAlgebra ω μ) = -toConv f := (rfl)
@[simp] theorem toConv_sub (f g : C_c(G, A)) :
    (toConv (f - g) : TwistedConvolutionAlgebra ω μ) = toConv f - toConv g := (rfl)
@[simp] theorem toConv_smul (c : ℂ) (f : C_c(G, A)) :
    (toConv (c • f) : TwistedConvolutionAlgebra ω μ) = c • toConv f := (rfl)

variable (ω μ) in
/-- `ofConv` as a complex linear equivalence with `C_c(G, A)`. -/
def linearEquiv : TwistedConvolutionAlgebra ω μ ≃ₗ[ℂ] C_c(G, A) :=
  { addEquiv ω μ with map_smul' _ _ := rfl }

@[simp] theorem linearEquiv_apply (f : TwistedConvolutionAlgebra ω μ) :
    linearEquiv ω μ f = f.ofConv := (rfl)

@[simp] theorem linearEquiv_symm_apply (f : C_c(G, A)) :
    (linearEquiv ω μ).symm f = toConv f := (rfl)

/-! ### Cocycle-twisted convolution product -/

section Mul

variable [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

instance : Mul (TwistedConvolutionAlgebra ω μ) where
  mul f g := toConv (ω.convolution μ f.ofConv g.ofConv)

@[simp] theorem ofConv_mul (f g : TwistedConvolutionAlgebra ω μ) :
    (f * g).ofConv = ω.convolution μ f.ofConv g.ofConv := (rfl)

@[simp] theorem toConv_convolution (f g : C_c(G, A)) :
    (toConv (ω.convolution μ f g) : TwistedConvolutionAlgebra ω μ) =
      toConv f * toConv g := (rfl)

instance : NonUnitalNonAssocRing (TwistedConvolutionAlgebra ω μ) where
  left_distrib _ _ _ := by ext1; simp
  right_distrib _ _ _ := by ext1; simp
  zero_mul _ := by ext1; simp
  mul_zero _ := by ext1; simp

instance :
    IsScalarTower ℂ (TwistedConvolutionAlgebra ω μ) (TwistedConvolutionAlgebra ω μ) where
  smul_assoc _ _ _ := by ext1; simp

instance :
    SMulCommClass ℂ (TwistedConvolutionAlgebra ω μ) (TwistedConvolutionAlgebra ω μ) where
  smul_comm _ _ _ := by ext1; simp

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

instance instNonUnitalRing : NonUnitalRing (TwistedConvolutionAlgebra ω μ) where
  mul_assoc _ _ _ := by ext1; simp [CentralCocycle.convolution_assoc]

end Mul

/-! ### Cocycle-twisted involution -/

section Star

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

instance : Star (TwistedConvolutionAlgebra ω μ) where
  star f := toConv (ω.involution f.ofConv)

@[simp] theorem ofConv_star (f : TwistedConvolutionAlgebra ω μ) :
    (star f).ofConv = ω.involution f.ofConv := (rfl)

@[simp] theorem toConv_involution (f : C_c(G, A)) :
    (toConv (ω.involution f) : TwistedConvolutionAlgebra ω μ) = star (toConv f) := (rfl)

instance : InvolutiveStar (TwistedConvolutionAlgebra ω μ) where
  star_involutive _ := by ext1; simp

instance : StarModule ℂ (TwistedConvolutionAlgebra ω μ) where
  star_smul _ _ := by ext1; simp

variable [OpensMeasurableSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant]

instance instStarRing : StarRing (TwistedConvolutionAlgebra ω μ) where
  star_mul _ _ := by ext1; simp [CentralCocycle.involution_convolution]
  star_add _ _ := by ext1; simp

end Star

/-! ### Bochner L¹ seminorm and norm -/

section Normed

variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

/-- Realize a compactly supported twisted convolution coefficient as a Bochner `L¹` class. -/
def toL1 : TwistedConvolutionAlgebra ω μ →ₗ[ℂ] Lp A 1 μ :=
  (CompactlySupportedContinuousMap.toLp 1 μ ℂ).comp (linearEquiv ω μ).toLinearMap

/-- The `L¹` class of a twisted convolution coefficient is represented by its underlying
function. -/
theorem coeFn_toL1 (f : TwistedConvolutionAlgebra ω μ) : toL1 f =ᵐ[μ] f.ofConv := by
  simpa [toL1] using CompactlySupportedContinuousMap.coeFn_toLp ℂ f.ofConv

instance : SeminormedAddCommGroup (TwistedConvolutionAlgebra ω μ) :=
  .induced _ _ (toL1 (ω := ω) (μ := μ)).toAddMonoidHom

instance : NormedSpace ℂ (TwistedConvolutionAlgebra ω μ) :=
  .induced ℂ _ _ (toL1 (ω := ω) (μ := μ))

theorem norm_def (f : TwistedConvolutionAlgebra ω μ) : ‖f‖ = ‖toL1 f‖ := (rfl)

/-- The norm of a twisted convolution coefficient is its `L¹` integral norm. -/
theorem norm_eq_integral_norm (f : TwistedConvolutionAlgebra ω μ) :
    ‖f‖ = ∫ s, ‖f.ofConv s‖ ∂μ :=
  (L1.norm_eq_integral_norm (toL1 f)).trans <| integral_congr_ae <|
    (coeFn_toL1 f).fun_comp norm

@[simp] theorem norm_toConv (f : C_c(G, A)) :
    ‖(toConv f : TwistedConvolutionAlgebra ω μ)‖ = ∫ s, ‖f s‖ ∂μ :=
  norm_eq_integral_norm _

variable (ω μ) in
/-- The linear isometry from the twisted convolution algebra with its `L¹` seminorm to Bochner
`L¹`. -/
def toL1LI : TwistedConvolutionAlgebra ω μ →ₗᵢ[ℂ] Lp A 1 μ :=
  { toL1 with norm_map' _ := rfl }

@[simp] theorem toL1LI_apply (f : TwistedConvolutionAlgebra ω μ) :
    toL1LI ω μ f = toL1 f := (rfl)

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

instance : NonUnitalSeminormedRing (TwistedConvolutionAlgebra ω μ) where
  __ : SeminormedAddCommGroup (TwistedConvolutionAlgebra ω μ) := inferInstance
  __ : NonUnitalRing (TwistedConvolutionAlgebra ω μ) := inferInstance
  norm_mul_le f g := by
    simpa only [norm_eq_integral_norm, ofConv_mul] using
      ω.integral_norm_convolution_le μ f.ofConv g.ofConv

end Multiplication

section FullSupport

variable [μ.IsOpenPosMeasure]

/-- Full support of `μ` makes `toL1` injective on continuous coefficients. -/
theorem toL1_injective : Function.Injective (toL1 (ω := ω) (μ := μ)) :=
  (CompactlySupportedContinuousMap.toLp_injective 1 μ ℂ).comp (linearEquiv ω μ).injective

instance : NormedAddCommGroup (TwistedConvolutionAlgebra ω μ) :=
  .ofSeparation fun f hf => toL1_injective <| by
    rw [map_zero]; exact norm_eq_zero.1 (((toL1LI ω μ).norm_map f).trans hf)

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

instance : NonUnitalNormedRing (TwistedConvolutionAlgebra ω μ) where
  __ : NonUnitalSeminormedRing (TwistedConvolutionAlgebra ω μ) := inferInstance
  __ : NormedAddCommGroup (TwistedConvolutionAlgebra ω μ) := inferInstance

end FullSupport

end Normed

section NormedStar

variable [IsFiniteMeasureOnCompacts μ] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [BorelSpace G] [μ.IsMulLeftInvariant]

/-- For a left-invariant measure, the `ω`-twisted involution is an `L¹` isometry:
`‖star f‖ = ‖f‖`. -/
theorem norm_star (f : TwistedConvolutionAlgebra ω μ) : ‖star f‖ = ‖f‖ := by
  rw [norm_eq_integral_norm, ofConv_star, ω.integral_norm_involution μ f.ofConv,
    norm_eq_integral_norm]

instance : NormedStarGroup (TwistedConvolutionAlgebra ω μ) := ⟨fun f => (norm_star f).le⟩

end NormedStar

section CompletionEquiv

/-- `TwistedConvolutionAlgebra.toL1` realizes a compactly supported coefficient via
`CompactlySupportedContinuousMap.toLp`. -/
theorem toL1_eq_toLp [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (f : TwistedConvolutionAlgebra ω μ) :
    toL1 f = CompactlySupportedContinuousMap.toLp 1 μ ℂ f.ofConv :=
  Lp.ext ((coeFn_toL1 f).trans (CompactlySupportedContinuousMap.coeFn_toLp ℂ f.ofConv).symm)

variable [R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]

/-- The compact-support twisted convolution algebra has dense image in `Lp A 1 μ` for any
measure finite on compact sets and inner regular on sets of finite measure. -/
theorem denseRange_toL1 : DenseRange (toL1 (ω := ω) (μ := μ)) := by
  refine (CompactlySupportedContinuousMap.denseRange_toLp ENNReal.one_ne_top μ ℂ).mono ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨toConv f, toL1_eq_toLp (toConv f)⟩

/-- `toL1LI` has dense range in `Lp A 1 μ`. -/
theorem denseRange_toL1LI : DenseRange (toL1LI ω μ) :=
  (funext toL1LI_apply : ⇑(toL1LI ω μ) = ⇑(toL1 (ω := ω) (μ := μ))) ▸ denseRange_toL1

variable (ω μ) in
/-- **Identification of the cocycle-twisted `L¹` completion with Bochner `L¹`**: the canonical
inclusion `toL1` extends to a complex linear isometric equivalence between
`UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)` and `Lp A 1 μ`. -/
def completionEquivL1 : Completion (TwistedConvolutionAlgebra ω μ) ≃ₗᵢ[ℂ] Lp A 1 μ :=
  (toL1LI ω μ).fromCompletionEquivOfDenseRange denseRange_toL1LI

@[simp] theorem completionEquivL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    completionEquivL1 ω μ f = toL1 f := by
  rw [completionEquivL1,
    (toL1LI ω μ).fromCompletionEquivOfDenseRange_coe denseRange_toL1LI f, toL1LI_apply]

@[simp] theorem completionEquivL1_symm_toL1 (f : TwistedConvolutionAlgebra ω μ) :
    (completionEquivL1 ω μ).symm (toL1 f) = f := by
  rw [completionEquivL1, ← toL1LI_apply (ω := ω) (μ := μ),
    (toL1LI ω μ).fromCompletionEquivOfDenseRange_symm_apply denseRange_toL1LI f]

@[simp] theorem completionEquivL1_symm_toLp (f : C_c(G, A)) :
    (completionEquivL1 ω μ).symm (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      ((toConv f : TwistedConvolutionAlgebra ω μ) :
        Completion (TwistedConvolutionAlgebra ω μ)) := by
  rw [← toL1_eq_toLp, completionEquivL1_symm_toL1]

end CompletionEquiv

/-! ### Comparison with the untwisted convolution algebra at `ω = 1` -/

section Untwisted

variable (α μ) [IsTopologicalGroup G] [LocallyCompactSpace G] [OpensMeasurableSpace G]
  [IsFiniteMeasureOnCompacts μ]

/-- For the trivial cocycle `1 : CentralCocycle α`, `TwistedConvolutionAlgebra 1 μ` is canonically
and isometrically isomorphic as a complex nonunital ⋆-algebra to `ConvolutionAlgebra α μ`. -/
def untwistStarAlgEquiv :
    TwistedConvolutionAlgebra (1 : CentralCocycle α) μ ≃⋆ₐ[ℂ]
      ConvolutionAlgebra α μ where
  toFun f := ConvolutionAlgebra.toConv f.ofConv
  invFun f := toConv f.ofConv
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by ext1; simp
  map_mul' _ _ := by ext1; simp
  map_smul' _ _ := by ext1; simp
  map_star' _ := by ext1; simp

@[simp] theorem ofConv_untwistStarAlgEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (untwistStarAlgEquiv α μ f).ofConv = f.ofConv := (rfl)

@[simp] theorem ofConv_untwistStarAlgEquiv_symm (f : ConvolutionAlgebra α μ) :
    ((untwistStarAlgEquiv α μ).symm f).ofConv = f.ofConv := (rfl)

@[simp] theorem norm_untwistStarAlgEquiv
    (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    ‖untwistStarAlgEquiv α μ f‖ = ‖f‖ := by
  rw [ConvolutionAlgebra.norm_eq_integral_norm, ofConv_untwistStarAlgEquiv, norm_eq_integral_norm]

end Untwisted

end TwistedConvolutionAlgebra

end TauCeti.CStarAction
