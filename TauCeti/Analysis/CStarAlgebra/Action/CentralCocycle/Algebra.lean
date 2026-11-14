/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralCocycle.Convolution
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed

/-!
# The cocycle-twisted convolution ⋆-algebra and its L¹ norm

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A`, a normalized
continuous central multiplier cocycle `ω : CentralCocycle α`, and a measure `μ` on `G`, the type
`TwistedConvolutionAlgebra ω μ` wraps `C_c(G, A)` and equips it with the `ω`-twisted convolution
`ω.twistedConvolution μ`, the `ω`-twisted involution `ω.twistedInvolution`, and the Bochner `L¹`
seminorm `∫ s, ‖f s‖ ∂μ`.

* For any measure finite on compact sets, `TwistedConvolutionAlgebra ω μ` is a complex nonunital,
  possibly nonassociative ring with `SeminormedAddCommGroup` and `NormedSpace ℂ`.
* When `μ` is left-invariant, it is an associative `NonUnitalSeminormedRing` (and a
  `NonUnitalNormedRing` when `[μ.IsOpenPosMeasure]`).
* When `G` is locally compact and Borel, `ω.twistedInvolution` makes it a `StarRing` and
  `NormedStarGroup` (`‖star f‖ = ‖f‖`). Its uniform completion
  `UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)` is the cocycle-twisted `L¹` Banach
  ⋆-algebra `L¹(G, A, α, ω)` via the completion instances in
  `TauCeti.Analysis.Normed.Ring.Completion` and `TauCeti.Analysis.CStarAlgebra.Completion`.
* At the trivial cocycle `1 : CentralCocycle α`, `untwistStarAlgEquiv` identifies
  `TwistedConvolutionAlgebra 1 μ` isometrically as a complex ⋆-algebra with
  `ConvolutionAlgebra α μ`.

## Main definitions

* `TauCeti.CStarAction.TwistedConvolutionAlgebra`: the `ω`-twisted convolution ⋆-algebra on
  `C_c(G, A)` with its `L¹` topology.
* `TauCeti.CStarAction.TwistedConvolutionAlgebra.toL1` and `toL1LI`: the linear and linear-isometric
  realizations in Bochner `Lp A 1 μ`.
* `TauCeti.CStarAction.TwistedConvolutionAlgebra.untwistStarAlgEquiv`: the isometric ⋆-algebra
  equivalence `TwistedConvolutionAlgebra (1 : CentralCocycle α) μ ≃⋆ₐ[ℂ] ConvolutionAlgebra α μ`.

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc.
  Cambridge Philos. Soc. 106 (1989), 293–311, Section 2.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G]

/-- The `ω`-twisted convolution ⋆-algebra of `(A, G, α, ω)` with respect to `μ`: compactly
supported continuous functions `G → A` equipped with `ω.twistedConvolution μ`,
`ω.twistedInvolution`, and the Bochner `L¹` seminorm. Use `toConv` and `ofConv` to pass to and from
`C_c(G, A)`. -/
structure TwistedConvolutionAlgebra {α : CStarAction G A} (ω : CentralCocycle α)
    (μ : Measure G) where
  /-- Regard a compactly supported function as an element of the twisted convolution algebra. -/
  toConv ::
  /-- The compactly supported function underlying an element of the twisted convolution algebra. -/
  ofConv : C_c(G, A)

namespace TwistedConvolutionAlgebra

variable {α : CStarAction G A} {ω : CentralCocycle α} {μ : Measure G}

@[simp]
theorem ofConv_toConv (f : C_c(G, A)) :
    (toConv f : TwistedConvolutionAlgebra ω μ).ofConv = f :=
  (rfl)

@[simp]
theorem toConv_ofConv (f : TwistedConvolutionAlgebra ω μ) : toConv f.ofConv = f :=
  (rfl)

theorem ofConv_injective :
    Function.Injective (ofConv : TwistedConvolutionAlgebra ω μ → C_c(G, A)) :=
  fun f g h => by rw [← toConv_ofConv f, h, toConv_ofConv]

theorem toConv_injective :
    Function.Injective (toConv : C_c(G, A) → TwistedConvolutionAlgebra ω μ) :=
  fun f g h => by rw [← ofConv_toConv (ω := ω) (μ := μ) f, h, ofConv_toConv]

@[ext]
theorem ext {f g : TwistedConvolutionAlgebra ω μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

variable (ω μ) in
/-- `ofConv` and `toConv` as an equivalence with `C_c(G, A)`. -/
def equiv : TwistedConvolutionAlgebra ω μ ≃ C_c(G, A) where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (f : TwistedConvolutionAlgebra ω μ) : equiv ω μ f = f.ofConv :=
  (rfl)

@[simp]
theorem equiv_symm_apply (f : C_c(G, A)) : (equiv ω μ).symm f = toConv f :=
  (rfl)

instance : AddCommGroup (TwistedConvolutionAlgebra ω μ) :=
  (equiv ω μ).addCommGroup

variable (ω μ) in
/-- `ofConv` as an additive equivalence with `C_c(G, A)`. -/
def addEquiv : TwistedConvolutionAlgebra ω μ ≃+ C_c(G, A) where
  __ := equiv ω μ
  map_add' _ _ := (rfl)

@[simp]
theorem addEquiv_apply (f : TwistedConvolutionAlgebra ω μ) : addEquiv ω μ f = f.ofConv :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply (f : C_c(G, A)) : (addEquiv ω μ).symm f = toConv f :=
  (rfl)

instance : Module ℂ (TwistedConvolutionAlgebra ω μ) :=
  (addEquiv ω μ).module ℂ

@[simp]
theorem ofConv_zero : (0 : TwistedConvolutionAlgebra ω μ).ofConv = 0 :=
  (rfl)

@[simp]
theorem ofConv_add (f g : TwistedConvolutionAlgebra ω μ) :
    (f + g).ofConv = f.ofConv + g.ofConv :=
  (rfl)

@[simp]
theorem ofConv_neg (f : TwistedConvolutionAlgebra ω μ) : (-f).ofConv = -f.ofConv :=
  (rfl)

@[simp]
theorem ofConv_sub (f g : TwistedConvolutionAlgebra ω μ) :
    (f - g).ofConv = f.ofConv - g.ofConv :=
  (rfl)

@[simp]
theorem ofConv_smul (c : ℂ) (f : TwistedConvolutionAlgebra ω μ) :
    (c • f).ofConv = c • f.ofConv :=
  (rfl)

@[simp]
theorem toConv_zero : (toConv 0 : TwistedConvolutionAlgebra ω μ) = 0 :=
  (rfl)

@[simp]
theorem toConv_add (f g : C_c(G, A)) :
    (toConv (f + g) : TwistedConvolutionAlgebra ω μ) = toConv f + toConv g :=
  (rfl)

@[simp]
theorem toConv_neg (f : C_c(G, A)) :
    (toConv (-f) : TwistedConvolutionAlgebra ω μ) = -toConv f :=
  (rfl)

@[simp]
theorem toConv_sub (f g : C_c(G, A)) :
    (toConv (f - g) : TwistedConvolutionAlgebra ω μ) = toConv f - toConv g :=
  (rfl)

@[simp]
theorem toConv_smul (c : ℂ) (f : C_c(G, A)) :
    (toConv (c • f) : TwistedConvolutionAlgebra ω μ) = c • toConv f :=
  (rfl)

variable (ω μ) in
/-- `ofConv` as a complex linear equivalence with `C_c(G, A)`. -/
def linearEquiv : TwistedConvolutionAlgebra ω μ ≃ₗ[ℂ] C_c(G, A) where
  __ := equiv ω μ
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem linearEquiv_apply (f : TwistedConvolutionAlgebra ω μ) :
    linearEquiv ω μ f = f.ofConv :=
  (rfl)

@[simp]
theorem linearEquiv_symm_apply (f : C_c(G, A)) :
    (linearEquiv ω μ).symm f = toConv f :=
  (rfl)

/-! ### Cocycle-twisted convolution product -/

section Mul

variable [IsTopologicalGroup G] [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

instance : Mul (TwistedConvolutionAlgebra ω μ) where
  mul f g := toConv (ω.twistedConvolution μ f.ofConv g.ofConv)

@[simp]
theorem ofConv_mul (f g : TwistedConvolutionAlgebra ω μ) :
    (f * g).ofConv = ω.twistedConvolution μ f.ofConv g.ofConv :=
  (rfl)

@[simp]
theorem toConv_twistedConvolution (f g : C_c(G, A)) :
    (toConv (ω.twistedConvolution μ f g) : TwistedConvolutionAlgebra ω μ) =
      toConv f * toConv g :=
  (rfl)

instance : NonUnitalNonAssocRing (TwistedConvolutionAlgebra ω μ) where
  left_distrib f g h := by ext1; simp
  right_distrib f g h := by ext1; simp
  zero_mul f := by ext1; simp
  mul_zero f := by ext1; simp

instance : IsScalarTower ℂ (TwistedConvolutionAlgebra ω μ) (TwistedConvolutionAlgebra ω μ) where
  smul_assoc c f g := by ext1; simp

instance : SMulCommClass ℂ (TwistedConvolutionAlgebra ω μ) (TwistedConvolutionAlgebra ω μ) where
  smul_comm c f g := by ext1; simp

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

instance instNonUnitalRing : NonUnitalRing (TwistedConvolutionAlgebra ω μ) where
  mul_assoc f g h := by ext1; simp [CentralCocycle.twistedConvolution_assoc]

end Mul

/-! ### Cocycle-twisted involution -/

section Star

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

instance : Star (TwistedConvolutionAlgebra ω μ) where
  star f := toConv (ω.twistedInvolution f.ofConv)

@[simp]
theorem ofConv_star (f : TwistedConvolutionAlgebra ω μ) :
    (star f).ofConv = ω.twistedInvolution f.ofConv :=
  (rfl)

@[simp]
theorem toConv_twistedInvolution (f : C_c(G, A)) :
    (toConv (ω.twistedInvolution f) : TwistedConvolutionAlgebra ω μ) = star (toConv f) :=
  (rfl)

instance : InvolutiveStar (TwistedConvolutionAlgebra ω μ) where
  star_involutive f := by ext1; simp

instance : StarModule ℂ (TwistedConvolutionAlgebra ω μ) where
  star_smul c f := by ext1; simp

variable [OpensMeasurableSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant]

instance instStarRing : StarRing (TwistedConvolutionAlgebra ω μ) where
  star_mul f g := by ext1; simp [CentralCocycle.twistedInvolution_twistedConvolution]
  star_add f g := by ext1; simp

end Star

/-! ### Bochner L¹ seminorm and norm -/

section Normed

variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]

/-- Realize a compactly supported twisted convolution coefficient as a Bochner `L¹` class. -/
def toL1 : TwistedConvolutionAlgebra ω μ →ₗ[ℂ] Lp A 1 μ :=
  (ConvolutionAlgebra.toL1 (α := α) (μ := μ)).comp
    ((ConvolutionAlgebra.linearEquiv α μ).symm.toLinearMap.comp (linearEquiv ω μ).toLinearMap)

theorem toL1_eq (f : TwistedConvolutionAlgebra ω μ) :
    toL1 f =
      ConvolutionAlgebra.toL1 (ConvolutionAlgebra.toConv f.ofConv : ConvolutionAlgebra α μ) := by
  simp [toL1]

/-- The `L¹` class of a twisted convolution coefficient is represented by its underlying
function. -/
theorem coeFn_toL1 (f : TwistedConvolutionAlgebra ω μ) : toL1 f =ᵐ[μ] f.ofConv := by
  rw [toL1_eq]
  exact ConvolutionAlgebra.coeFn_toL1 (ConvolutionAlgebra.toConv f.ofConv)

/-- The twisted convolution algebra carries the `L¹` seminorm. -/
instance : SeminormedAddCommGroup (TwistedConvolutionAlgebra ω μ) :=
  .induced _ _ (toL1 (ω := ω) (μ := μ)).toAddMonoidHom

/-- The `L¹` seminorm is compatible with the complex scalar action. -/
instance : NormedSpace ℂ (TwistedConvolutionAlgebra ω μ) :=
  .induced ℂ _ _ (toL1 (ω := ω) (μ := μ))

theorem norm_def (f : TwistedConvolutionAlgebra ω μ) : ‖f‖ = ‖toL1 f‖ :=
  (rfl)

/-- The norm of a twisted convolution coefficient is its `L¹` integral norm. -/
theorem norm_eq_integral_norm (f : TwistedConvolutionAlgebra ω μ) :
    ‖f‖ = ∫ s, ‖f.ofConv s‖ ∂μ := by
  rw [norm_def, toL1_eq]
  exact (L1.norm_eq_integral_norm _).trans
    (integral_congr_ae
      ((ConvolutionAlgebra.coeFn_toL1 (ConvolutionAlgebra.toConv f.ofConv)).fun_comp norm))

@[simp]
theorem norm_toConv (f : C_c(G, A)) :
    ‖(toConv f : TwistedConvolutionAlgebra ω μ)‖ = ∫ s, ‖f s‖ ∂μ :=
  norm_eq_integral_norm _

variable (ω μ) in
/-- The linear isometry from the twisted convolution algebra with its `L¹` seminorm to Bochner
`L¹`. -/
def toL1LI : TwistedConvolutionAlgebra ω μ →ₗᵢ[ℂ] Lp A 1 μ where
  __ := toL1
  norm_map' _ := (rfl)

@[simp]
theorem toL1LI_apply (f : TwistedConvolutionAlgebra ω μ) : toL1LI ω μ f = toL1 f :=
  (rfl)

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- `ω`-twisted convolution is submultiplicative for the `L¹` seminorm. -/
instance : NonUnitalSeminormedRing (TwistedConvolutionAlgebra ω μ) where
  __ : SeminormedAddCommGroup (TwistedConvolutionAlgebra ω μ) := inferInstance
  __ : NonUnitalRing (TwistedConvolutionAlgebra ω μ) := inferInstance
  norm_mul_le f g := by
    simpa only [norm_eq_integral_norm, ofConv_mul] using
      ω.integral_norm_twistedConvolution_le μ f.ofConv g.ofConv

end Multiplication

section FullSupport

variable [μ.IsOpenPosMeasure]

/-- Full support of `μ` makes `toL1` injective on continuous coefficients. -/
theorem toL1_injective : Function.Injective (toL1 (ω := ω) (μ := μ)) := by
  intro f g h
  rw [toL1_eq, toL1_eq] at h
  ext1
  simpa using congrArg ConvolutionAlgebra.ofConv (ConvolutionAlgebra.toL1_injective h)

/-- For a full-support measure the `L¹` seminorm separates twisted convolution coefficients. -/
instance : NormedAddCommGroup (TwistedConvolutionAlgebra ω μ) :=
  .ofSeparation fun f hf => toL1_injective <| by
    rw [map_zero]
    exact norm_eq_zero.1 (((toL1LI ω μ).norm_map f).trans hf)

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- For a full-support left-invariant measure, `TwistedConvolutionAlgebra ω μ` is a nonunital
normed ring. -/
instance : NonUnitalNormedRing (TwistedConvolutionAlgebra ω μ) where
  __ : NonUnitalSeminormedRing (TwistedConvolutionAlgebra ω μ) := inferInstance
  __ : NormedAddCommGroup (TwistedConvolutionAlgebra ω μ) := inferInstance

end FullSupport

end Normed

section NormedStar

variable [IsFiniteMeasureOnCompacts μ] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [BorelSpace G] [μ.IsMulLeftInvariant]

/-- For a left-invariant measure, the `ω`-twisted involution is an `L¹` isometry: `‖star f‖ = ‖f‖`.
Pointwise unitarity of `ω(s, s⁻¹)*` reduces the integrand norm directly to the untwisted
`ConvolutionAlgebra.norm_star`. -/
theorem norm_star (f : TwistedConvolutionAlgebra ω μ) : ‖star f‖ = ‖f‖ := by
  calc ‖star f‖
      = ∫ s, ‖ω.twistedInvolution f.ofConv s‖ ∂μ := by
        rw [norm_eq_integral_norm, ofConv_star]
    _ = ∫ s, ‖α.twistedInvolution f.ofConv s‖ ∂μ := by
        simp only [CentralCocycle.norm_twistedInvolution_apply,
          CStarAction.norm_twistedInvolution_apply]
    _ = ‖star (ConvolutionAlgebra.toConv f.ofConv : ConvolutionAlgebra α μ)‖ := by
        rw [ConvolutionAlgebra.norm_eq_integral_norm, ConvolutionAlgebra.ofConv_star,
          ConvolutionAlgebra.ofConv_toConv]
    _ = ‖(ConvolutionAlgebra.toConv f.ofConv : ConvolutionAlgebra α μ)‖ :=
        ConvolutionAlgebra.norm_star _
    _ = ‖f‖ := by rw [ConvolutionAlgebra.norm_toConv, norm_eq_integral_norm]

instance : NormedStarGroup (TwistedConvolutionAlgebra ω μ) :=
  ⟨fun f => (norm_star f).le⟩

end NormedStar

/-! ### Comparison with the untwisted convolution algebra at `ω = 1` -/

section Untwisted

variable (α μ) [IsTopologicalGroup G] [LocallyCompactSpace G] [OpensMeasurableSpace G]
  [IsFiniteMeasureOnCompacts μ]

/-- For the trivial cocycle `1 : CentralCocycle α`, `TwistedConvolutionAlgebra 1 μ` is canonically
and isometrically isomorphic as a complex nonunital ⋆-algebra to `ConvolutionAlgebra α μ`. -/
def untwistStarAlgEquiv :
    TwistedConvolutionAlgebra (1 : CentralCocycle α) μ ≃⋆ₐ[ℂ] ConvolutionAlgebra α μ where
  toFun f := ConvolutionAlgebra.toConv f.ofConv
  invFun f := toConv f.ofConv
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' f g := by ext1; simp
  map_mul' f g := by ext1; simp
  map_smul' c f := by ext1; simp
  map_star' f := by ext1; simp

@[simp]
theorem ofConv_untwistStarAlgEquiv (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    (untwistStarAlgEquiv α μ f).ofConv = f.ofConv :=
  (rfl)

@[simp]
theorem ofConv_untwistStarAlgEquiv_symm (f : ConvolutionAlgebra α μ) :
    ((untwistStarAlgEquiv α μ).symm f).ofConv = f.ofConv :=
  (rfl)

@[simp]
theorem norm_untwistStarAlgEquiv (f : TwistedConvolutionAlgebra (1 : CentralCocycle α) μ) :
    ‖untwistStarAlgEquiv α μ f‖ = ‖f‖ := by
  rw [ConvolutionAlgebra.norm_eq_integral_norm, ofConv_untwistStarAlgEquiv, norm_eq_integral_norm]

end Untwisted

end TwistedConvolutionAlgebra

end TauCeti.CStarAction
