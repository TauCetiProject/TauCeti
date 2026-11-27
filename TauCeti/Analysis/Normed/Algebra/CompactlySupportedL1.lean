/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact

/-!
# Tagged `L¹` spaces of compactly supported continuous functions

This file provides a shared wrapper `TauCeti.CompactlySupportedL1 tag E μ` around `C_c(X, E)`
tagged by an arbitrary parameter `tag : ι` and a measure `μ : Measure X`. Tagging separates
distinct algebraic structures (such as untwisted and cocycle-twisted convolution algebras) that
share the same underlying function space `C_c(X, E)` and the same Bochner `L¹` seminorm.

We develop once for all tagged spaces:
* the wrapper equivalence, `AddCommGroup`, and `Module 𝕜` API (`ofFun`, `toFun`, `equiv`,
  `addEquiv`, `linearEquiv`);
* the Bochner `L¹` seminorm (`SeminormedAddCommGroup`, `NormedSpace`), realization `toL1` and
  linear isometry `toL1LI` into `Lp E 1 μ`, separation (`NormedAddCommGroup`) for full-support
  measures, and the isometric identification `completionEquivL1` of
  `UniformSpace.Completion (CompactlySupportedL1 tag E μ)` with `Lp E 1 μ` on weakly locally
  compact `R₁` spaces;
* builder helpers (`nonUnitalNonAssocRingOf`, `nonUnitalRingOf`, `norm_mul_le_of`, `starRingOf`,
  `normedStarGroupOf`, …) turning convolution and involution laws on `C_c(X, E)` into algebraic
  and normed structures on `CompactlySupportedL1 tag E μ`;
* `CompactlySupportedL1.liftCLM`, bundling a `𝕜`-linear map on `C_c(X, E)` with an `L¹` bound
  `‖Φ f‖ ≤ C * ∫ s, ‖f s‖ ∂μ` into a bounded linear map `CompactlySupportedL1 tag E μ →L[𝕜] B`
  of operator norm at most `C` (`norm_liftCLM_le`, contractive when `C ≤ 1`).
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported

namespace TauCeti

/-- A wrapper around `C_c(X, E)` tagged by `tag : ι` and a measure `μ : Measure X`, allowing
distinct algebraic structures on compactly supported continuous functions to share the Bochner
`L¹` seminorm and completion identification. -/
structure CompactlySupportedL1 {ι : Type*} (tag : ι) {X : Type*} (E : Type*)
    [TopologicalSpace X] [MeasurableSpace X] [Zero E] [TopologicalSpace E] (μ : Measure X) where
  /-- Regard a compactly supported continuous function as an element of the tagged `L¹` space. -/
  ofFun ::
  /-- The compactly supported continuous function underlying an element of the tagged `L¹`
  space. -/
  toFun : C_c(X, E)

namespace CompactlySupportedL1

section Wrapper

variable {ι : Type*} {tag : ι} {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [Zero E] [TopologicalSpace E] {μ : Measure X}

@[simp]
theorem toFun_ofFun (f : C_c(X, E)) :
    (ofFun f : CompactlySupportedL1 tag E μ).toFun = f :=
  (rfl)

@[simp]
theorem ofFun_toFun (f : CompactlySupportedL1 tag E μ) : ofFun f.toFun = f :=
  (rfl)

theorem toFun_injective :
    Function.Injective (toFun : CompactlySupportedL1 tag E μ → C_c(X, E)) :=
  fun f g h => by rw [← ofFun_toFun f, h, ofFun_toFun]

theorem ofFun_injective :
    Function.Injective (ofFun : C_c(X, E) → CompactlySupportedL1 tag E μ) :=
  fun f g h => by rw [← toFun_ofFun (tag := tag) (E := E) (μ := μ) f, h, toFun_ofFun]

@[ext]
theorem ext {f g : CompactlySupportedL1 tag E μ} (h : f.toFun = g.toFun) : f = g :=
  toFun_injective h

variable (tag E μ) in
/-- `CompactlySupportedL1.toFun` and `CompactlySupportedL1.ofFun` as an equivalence. -/
def equiv : CompactlySupportedL1 tag E μ ≃ C_c(X, E) where
  toFun := toFun
  invFun := ofFun
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (f : CompactlySupportedL1 tag E μ) : equiv tag E μ f = f.toFun :=
  (rfl)

@[simp]
theorem equiv_symm_apply (f : C_c(X, E)) : (equiv tag E μ).symm f = ofFun f :=
  (rfl)

end Wrapper

section AddCommGroup

variable {ι : Type*} {tag : ι} {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] {μ : Measure X}

instance : AddCommGroup (CompactlySupportedL1 tag E μ) :=
  (equiv tag E μ).addCommGroup

variable (tag E μ) in
/-- `CompactlySupportedL1.toFun` as an additive equivalence with `C_c(X, E)`. -/
def addEquiv : CompactlySupportedL1 tag E μ ≃+ C_c(X, E) where
  __ := equiv tag E μ
  map_add' _ _ := (rfl)

@[simp]
theorem addEquiv_apply (f : CompactlySupportedL1 tag E μ) : addEquiv tag E μ f = f.toFun :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply (f : C_c(X, E)) : (addEquiv tag E μ).symm f = ofFun f :=
  (rfl)

@[simp]
theorem toFun_zero : (0 : CompactlySupportedL1 tag E μ).toFun = 0 :=
  (rfl)

@[simp]
theorem toFun_add (f g : CompactlySupportedL1 tag E μ) : (f + g).toFun = f.toFun + g.toFun :=
  (rfl)

@[simp]
theorem toFun_neg (f : CompactlySupportedL1 tag E μ) : (-f).toFun = -f.toFun :=
  (rfl)

@[simp]
theorem toFun_sub (f g : CompactlySupportedL1 tag E μ) : (f - g).toFun = f.toFun - g.toFun :=
  (rfl)

@[simp]
theorem ofFun_zero : (ofFun 0 : CompactlySupportedL1 tag E μ) = 0 :=
  (rfl)

@[simp]
theorem ofFun_add (f g : C_c(X, E)) :
    (ofFun (f + g) : CompactlySupportedL1 tag E μ) = ofFun f + ofFun g :=
  (rfl)

@[simp]
theorem ofFun_neg (f : C_c(X, E)) : (ofFun (-f) : CompactlySupportedL1 tag E μ) = -ofFun f :=
  (rfl)

@[simp]
theorem ofFun_sub (f g : C_c(X, E)) :
    (ofFun (f - g) : CompactlySupportedL1 tag E μ) = ofFun f - ofFun g :=
  (rfl)

section Module

variable {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]

instance : Module 𝕜 (CompactlySupportedL1 tag E μ) :=
  (addEquiv tag E μ).module 𝕜

@[simp]
theorem toFun_smul (c : 𝕜) (f : CompactlySupportedL1 tag E μ) : (c • f).toFun = c • f.toFun :=
  (rfl)

@[simp]
theorem ofFun_smul (c : 𝕜) (f : C_c(X, E)) :
    (ofFun (c • f) : CompactlySupportedL1 tag E μ) = c • ofFun f :=
  (rfl)

variable (tag E μ 𝕜) in
/-- `CompactlySupportedL1.toFun` as a `𝕜`-linear equivalence with `C_c(X, E)`. -/
def linearEquiv : CompactlySupportedL1 tag E μ ≃ₗ[𝕜] C_c(X, E) where
  __ := addEquiv tag E μ
  map_smul' _ _ := (rfl)

@[simp]
theorem linearEquiv_apply (f : CompactlySupportedL1 tag E μ) : linearEquiv tag E μ 𝕜 f = f.toFun :=
  (rfl)

@[simp]
theorem linearEquiv_symm_apply (f : C_c(X, E)) : (linearEquiv tag E μ 𝕜).symm f = ofFun f :=
  (rfl)

end Module

end AddCommGroup

section L1Norm

variable {ι : Type*} {tag : ι} {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
  [IsFiniteMeasureOnCompacts μ]

/-- Realize a compactly supported function in `CompactlySupportedL1 tag E μ` as a Bochner `L¹`
class without fixing a scalar ring. -/
def toL1AddMonoidHom : CompactlySupportedL1 tag E μ →+ Lp E 1 μ where
  toFun f := (f.toFun.memLp 1 μ).toLp f.toFun
  map_zero' := by
    simpa only [toFun_zero, CompactlySupportedContinuousMap.coe_zero] using
      MemLp.toLp_zero (p := 1) (μ := μ) (E := E) _
  map_add' f g := by
    simpa only [toFun_add, CompactlySupportedContinuousMap.coe_add] using
      MemLp.toLp_add (f.toFun.memLp 1 μ) (g.toFun.memLp 1 μ)

instance : SeminormedAddCommGroup (CompactlySupportedL1 tag E μ) :=
  .induced _ _ (toL1AddMonoidHom (tag := tag) (E := E) (μ := μ))

/-- Realize a compactly supported function in `CompactlySupportedL1 tag E μ` as a `𝕜`-linear map
into Bochner `Lp E 1 μ`. -/
def toL1 (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    CompactlySupportedL1 tag E μ →ₗ[𝕜] Lp E 1 μ :=
  (CompactlySupportedContinuousMap.toLp 1 μ 𝕜).comp (linearEquiv tag E μ 𝕜).toLinearMap

/-- The `L¹` class of an element of `CompactlySupportedL1` is represented a.e. by its underlying
function. -/
theorem coeFn_toL1 (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : CompactlySupportedL1 tag E μ) : toL1 𝕜 f =ᵐ[μ] f.toFun := by
  simpa [toL1] using CompactlySupportedContinuousMap.coeFn_toLp 𝕜 f.toFun

private theorem toL1_eq_toL1AddMonoidHom (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (f : CompactlySupportedL1 tag E μ) :
    toL1 𝕜 f = toL1AddMonoidHom f :=
  Lp.ext ((coeFn_toL1 𝕜 f).trans (f.toFun.memLp 1 μ).coeFn_toLp.symm)

/-- The `L¹` seminorm of `f : CompactlySupportedL1 tag E μ` is `‖toL1 𝕜 f‖`. -/
theorem norm_def (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : CompactlySupportedL1 tag E μ) : ‖f‖ = ‖toL1 𝕜 f‖ :=
  congrArg norm (toL1_eq_toL1AddMonoidHom 𝕜 f).symm

instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] :
    NormedSpace 𝕜 (CompactlySupportedL1 tag E μ) where
  norm_smul_le c f := by
    rw [norm_def 𝕜, norm_def 𝕜, map_smul]
    exact norm_smul_le c (toL1 𝕜 f)

/-- The norm of `f : CompactlySupportedL1 tag E μ` is its integral norm `∫ s, ‖f.toFun s‖ ∂μ`. -/
theorem norm_eq_integral_norm (f : CompactlySupportedL1 tag E μ) :
    ‖f‖ = ∫ s, ‖f.toFun s‖ ∂μ :=
  (L1.norm_eq_integral_norm (toL1AddMonoidHom f)).trans <|
    integral_congr_ae <| (f.toFun.memLp 1 μ).coeFn_toLp.fun_comp norm

@[simp]
theorem norm_ofFun (f : C_c(X, E)) :
    ‖(ofFun f : CompactlySupportedL1 tag E μ)‖ = ∫ s, ‖f s‖ ∂μ :=
  norm_eq_integral_norm _

variable (tag E μ) in
/-- The linear isometry from `CompactlySupportedL1 tag E μ` with its `L¹` seminorm to Bochner
`Lp E 1 μ`. -/
def toL1LI (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    CompactlySupportedL1 tag E μ →ₗᵢ[𝕜] Lp E 1 μ where
  __ := toL1 𝕜
  norm_map' f := (norm_def 𝕜 f).symm

@[simp]
theorem toL1LI_apply (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : CompactlySupportedL1 tag E μ) : toL1LI tag E μ 𝕜 f = toL1 𝕜 f :=
  (rfl)

/-- `toL1 𝕜` realizes a compactly supported element via `CompactlySupportedContinuousMap.toLp`. -/
theorem toL1_eq_toLp (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : CompactlySupportedL1 tag E μ) :
    toL1 𝕜 f = CompactlySupportedContinuousMap.toLp 1 μ 𝕜 f.toFun :=
  (rfl)

section FullSupport

variable [μ.IsOpenPosMeasure]

/-- Full support of `μ` makes `toL1AddMonoidHom` injective on continuous coefficients. -/
theorem toL1AddMonoidHom_injective :
    Function.Injective (toL1AddMonoidHom (tag := tag) (E := E) (μ := μ)) := by
  intro f g hfg
  ext1
  apply DFunLike.coe_injective
  exact Measure.eq_of_ae_eq
    ((f.toFun.memLp 1 μ).coeFn_toLp.symm.trans
      ((Lp.ext_iff.1 hfg).trans (g.toFun.memLp 1 μ).coeFn_toLp))
    f.toFun.continuous g.toFun.continuous

/-- Full support of `μ` makes `toL1 𝕜` injective on continuous coefficients. -/
theorem toL1_injective (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    Function.Injective (toL1 (tag := tag) (E := E) (μ := μ) 𝕜) :=
  fun f g h => toL1AddMonoidHom_injective <|
    (toL1_eq_toL1AddMonoidHom 𝕜 f).symm.trans (h.trans (toL1_eq_toL1AddMonoidHom 𝕜 g))

/-- For a full-support measure the `L¹` seminorm separates continuous coefficients. -/
instance : NormedAddCommGroup (CompactlySupportedL1 tag E μ) :=
  .ofSeparation fun f hf => toL1AddMonoidHom_injective <| by
    rw [map_zero]
    exact norm_eq_zero.1 hf

end FullSupport

section CompletionEquiv

variable [R1Space X] [WeaklyLocallyCompactSpace X] [BorelSpace X] [NormedSpace ℝ E]
  [μ.InnerRegularCompactLTTop] (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- `CompactlySupportedL1` has dense image in `Lp E 1 μ` for any measure finite on compact sets
and inner regular on sets of finite measure. -/
theorem denseRange_toL1 : DenseRange (toL1 (tag := tag) (E := E) (μ := μ) 𝕜) := by
  refine (CompactlySupportedContinuousMap.denseRange_toLp ENNReal.one_ne_top μ 𝕜).mono ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨ofFun f, rfl⟩

/-- `toL1LI` has dense range in `Lp E 1 μ`. -/
theorem denseRange_toL1LI : DenseRange (toL1LI tag E μ 𝕜) :=
  denseRange_toL1 𝕜

section Complete

variable [CompleteSpace E]

variable (tag E μ) in
/-- **Identification of the abstract `L¹` completion with Bochner `L¹`**: `toL1` extends to a
`𝕜`-linear isometric equivalence between `UniformSpace.Completion (CompactlySupportedL1 tag E μ)`
and `Lp E 1 μ`. -/
def completionEquivL1 : Completion (CompactlySupportedL1 tag E μ) ≃ₗᵢ[𝕜] Lp E 1 μ :=
  (LinearEquiv.refl 𝕜 _).extendOfIsometry Completion.toComplₗᵢ.toLinearMap (toL1 𝕜)
    Completion.denseRange_coe (denseRange_toL1 𝕜) (by simp [norm_def 𝕜])

@[simp]
theorem completionEquivL1_coe (f : CompactlySupportedL1 tag E μ) :
    completionEquivL1 tag E μ 𝕜 f = toL1 𝕜 f :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

@[simp]
theorem completionEquivL1_symm_toL1 (f : CompactlySupportedL1 tag E μ) :
    (completionEquivL1 tag E μ 𝕜).symm (toL1 𝕜 f) = f :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ f

@[simp]
theorem completionEquivL1_symm_toLp (f : C_c(X, E)) :
    (completionEquivL1 tag E μ 𝕜).symm (CompactlySupportedContinuousMap.toLp 1 μ 𝕜 f) =
      ((ofFun f : CompactlySupportedL1 tag E μ) : Completion (CompactlySupportedL1 tag E μ)) := by
  rw [← toL1_eq_toLp 𝕜 (ofFun f), completionEquivL1_symm_toL1]

end Complete

end CompletionEquiv

end L1Norm

section AlgebraBuilders

variable {ι : Type*} {tag : ι} {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] {μ : Measure X}

/-- Construct `NonUnitalNonAssocRing` on `CompactlySupportedL1 tag E μ` from the corresponding laws
on underlying functions `C_c(X, E)`. -/
@[expose, instance_reducible]
def nonUnitalNonAssocRingOf [Mul (CompactlySupportedL1 tag E μ)]
    (conv : C_c(X, E) → C_c(X, E) → C_c(X, E))
    (h_mul : ∀ f g : CompactlySupportedL1 tag E μ, (f * g).toFun = conv f.toFun g.toFun)
    (h_add_left : ∀ f g h : C_c(X, E), conv f (g + h) = conv f g + conv f h)
    (h_add_right : ∀ f g h : C_c(X, E), conv (f + g) h = conv f h + conv g h)
    (h_zero_left : ∀ f : C_c(X, E), conv 0 f = 0)
    (h_zero_right : ∀ f : C_c(X, E), conv f 0 = 0) :
    NonUnitalNonAssocRing (CompactlySupportedL1 tag E μ) where
  left_distrib f g h := by ext1; simp [h_mul, h_add_left]
  right_distrib f g h := by ext1; simp [h_mul, h_add_right]
  zero_mul f := by ext1; simp [h_mul, h_zero_left]
  mul_zero f := by ext1; simp [h_mul, h_zero_right]

/-- Construct `IsScalarTower 𝕜` on `CompactlySupportedL1 tag E μ` from left equivariance of
`conv`. -/
theorem isScalarTowerOf {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
    [Mul (CompactlySupportedL1 tag E μ)] (conv : C_c(X, E) → C_c(X, E) → C_c(X, E))
    (h_mul : ∀ f g : CompactlySupportedL1 tag E μ, (f * g).toFun = conv f.toFun g.toFun)
    (h_smul_left : ∀ (c : 𝕜) (f g : C_c(X, E)), conv (c • f) g = c • conv f g) :
    IsScalarTower 𝕜 (CompactlySupportedL1 tag E μ) (CompactlySupportedL1 tag E μ) where
  smul_assoc c f g := by ext1; simp [h_mul, h_smul_left]

/-- Construct `SMulCommClass 𝕜` on `CompactlySupportedL1 tag E μ` from right equivariance of
`conv`. -/
theorem smulCommClassOf {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
    [Mul (CompactlySupportedL1 tag E μ)] (conv : C_c(X, E) → C_c(X, E) → C_c(X, E))
    (h_mul : ∀ f g : CompactlySupportedL1 tag E μ, (f * g).toFun = conv f.toFun g.toFun)
    (h_smul_right : ∀ (c : 𝕜) (f g : C_c(X, E)), conv f (c • g) = c • conv f g) :
    SMulCommClass 𝕜 (CompactlySupportedL1 tag E μ) (CompactlySupportedL1 tag E μ) where
  smul_comm c f g := by ext1; simp [h_mul, h_smul_right]

/-- Construct `NonUnitalRing` on `CompactlySupportedL1 tag E μ` from associativity of `conv`. -/
@[expose, instance_reducible]
def nonUnitalRingOf [NonUnitalNonAssocRing (CompactlySupportedL1 tag E μ)]
    (conv : C_c(X, E) → C_c(X, E) → C_c(X, E))
    (h_mul : ∀ f g : CompactlySupportedL1 tag E μ, (f * g).toFun = conv f.toFun g.toFun)
    (h_assoc : ∀ f g h : C_c(X, E), conv (conv f g) h = conv f (conv g h)) :
    NonUnitalRing (CompactlySupportedL1 tag E μ) where
  mul_assoc f g h := by ext1; simp [h_mul, h_assoc]

/-- Construct `InvolutiveStar` on `CompactlySupportedL1 tag E μ` from involutivity on
`C_c(X, E)`. -/
@[expose, instance_reducible]
def involutiveStarOf [Star (CompactlySupportedL1 tag E μ)] (inv : C_c(X, E) → C_c(X, E))
    (h_star : ∀ f : CompactlySupportedL1 tag E μ, (star f).toFun = inv f.toFun)
    (h_inv : ∀ f : C_c(X, E), inv (inv f) = f) :
    InvolutiveStar (CompactlySupportedL1 tag E μ) where
  star_involutive f := by ext1; simp [h_star, h_inv]

/-- Construct `StarModule 𝕜` on `CompactlySupportedL1 tag E μ` from conjugate-linearity of
`inv`. -/
theorem starModuleOf {𝕜 : Type*} [Semiring 𝕜] [Star 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
    [Star (CompactlySupportedL1 tag E μ)] (inv : C_c(X, E) → C_c(X, E))
    (h_star : ∀ f : CompactlySupportedL1 tag E μ, (star f).toFun = inv f.toFun)
    (h_smul : ∀ (c : 𝕜) (f : C_c(X, E)), inv (c • f) = star c • inv f) :
    StarModule 𝕜 (CompactlySupportedL1 tag E μ) where
  star_smul c f := by ext1; simp [h_star, h_smul]

/-- Construct `StarRing` on `CompactlySupportedL1 tag E μ` from additivity and anti-multiplicativity
of `inv` with respect to `conv`. -/
@[expose, instance_reducible]
def starRingOf [NonUnitalNonAssocSemiring (CompactlySupportedL1 tag E μ)]
    [InvolutiveStar (CompactlySupportedL1 tag E μ)]
    (conv : C_c(X, E) → C_c(X, E) → C_c(X, E)) (inv : C_c(X, E) → C_c(X, E))
    (h_mul : ∀ f g : CompactlySupportedL1 tag E μ, (f * g).toFun = conv f.toFun g.toFun)
    (h_star : ∀ f : CompactlySupportedL1 tag E μ, (star f).toFun = inv f.toFun)
    (h_add_toFun : ∀ f g : CompactlySupportedL1 tag E μ, (f + g).toFun = f.toFun + g.toFun)
    (h_add : ∀ f g : C_c(X, E), inv (f + g) = inv f + inv g)
    (h_star_mul : ∀ f g : C_c(X, E), inv (conv f g) = conv (inv g) (inv f)) :
    StarRing (CompactlySupportedL1 tag E μ) where
  star_mul f g := by ext1; simp [h_mul, h_star, h_star_mul]
  star_add f g := by ext1; simp [h_star, h_add_toFun, h_add]

end AlgebraBuilders

section NormedBuilders

variable {ι : Type*} {tag : ι} {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
  [IsFiniteMeasureOnCompacts μ]

/-- Derive `L¹` submultiplicativity `‖f * g‖ ≤ ‖f‖ * ‖g‖` on `CompactlySupportedL1 tag E μ` from
the corresponding integral bound on `C_c(X, E)`. -/
theorem norm_mul_le_of [Mul (CompactlySupportedL1 tag E μ)]
    (conv : C_c(X, E) → C_c(X, E) → C_c(X, E))
    (h_mul : ∀ f g : CompactlySupportedL1 tag E μ, (f * g).toFun = conv f.toFun g.toFun)
    (h_norm_mul : ∀ f g : C_c(X, E),
      ∫ s, ‖conv f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ)
    (f g : CompactlySupportedL1 tag E μ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  simpa only [norm_eq_integral_norm, h_mul] using h_norm_mul f.toFun g.toFun

/-- An `L¹`-norm-preserving involution `inv` on `C_c(X, E)` makes `star` an `L¹` isometry on
`CompactlySupportedL1 tag E μ`. -/
theorem norm_star_of [Star (CompactlySupportedL1 tag E μ)] (inv : C_c(X, E) → C_c(X, E))
    (h_star : ∀ f : CompactlySupportedL1 tag E μ, (star f).toFun = inv f.toFun)
    (h_norm_star : ∀ f : C_c(X, E), ∫ s, ‖inv f s‖ ∂μ = ∫ s, ‖f s‖ ∂μ)
    (f : CompactlySupportedL1 tag E μ) :
    ‖star f‖ = ‖f‖ := by
  rw [norm_eq_integral_norm, h_star, h_norm_star, norm_eq_integral_norm]

/-- Construct `NormedStarGroup` on `CompactlySupportedL1 tag E μ` from an `L¹`-norm-preserving
involution on `C_c(X, E)`. -/
theorem normedStarGroupOf [StarAddMonoid (CompactlySupportedL1 tag E μ)]
    (inv : C_c(X, E) → C_c(X, E))
    (h_star : ∀ f : CompactlySupportedL1 tag E μ, (star f).toFun = inv f.toFun)
    (h_norm_star : ∀ f : C_c(X, E), ∫ s, ‖inv f s‖ ∂μ = ∫ s, ‖f s‖ ∂μ) :
    NormedStarGroup (CompactlySupportedL1 tag E μ) :=
  ⟨fun f => (norm_star_of inv h_star h_norm_star f).le⟩

end NormedBuilders

section LiftCLM

variable {ι : Type*} {tag : ι} {X E 𝕜 B : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [SeminormedAddCommGroup B] [NormedSpace 𝕜 B]

/-- Bundle a `𝕜`-linear map `Φ : C_c(X, E) →ₗ[𝕜] B` satisfying an `L¹` bound `‖Φ f‖ ≤ C * ‖f‖₁`
as a continuous linear map on `CompactlySupportedL1 tag E μ`. -/
def liftCLM (Φ : C_c(X, E) →ₗ[𝕜] B) (C : ℝ)
    (hΦ : ∀ f : C_c(X, E), ‖Φ f‖ ≤ C * ∫ s, ‖f s‖ ∂μ) :
    CompactlySupportedL1 tag E μ →L[𝕜] B :=
  (Φ.comp (linearEquiv tag E μ 𝕜).toLinearMap).mkContinuous C fun f => by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, linearEquiv_apply,
      norm_eq_integral_norm] using hΦ f.toFun

@[simp]
theorem liftCLM_apply (Φ : C_c(X, E) →ₗ[𝕜] B) {C : ℝ}
    (hΦ : ∀ f : C_c(X, E), ‖Φ f‖ ≤ C * ∫ s, ‖f s‖ ∂μ)
    (f : CompactlySupportedL1 tag E μ) :
    liftCLM (tag := tag) (E := E) (μ := μ) Φ C hΦ f = Φ f.toFun :=
  (rfl)

theorem norm_liftCLM_le (Φ : C_c(X, E) →ₗ[𝕜] B) {C : ℝ} (hC : 0 ≤ C)
    (hΦ : ∀ f : C_c(X, E), ‖Φ f‖ ≤ C * ∫ s, ‖f s‖ ∂μ) :
    ‖liftCLM (tag := tag) (E := E) (μ := μ) Φ C hΦ‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end LiftCLM

end CompactlySupportedL1

end TauCeti
