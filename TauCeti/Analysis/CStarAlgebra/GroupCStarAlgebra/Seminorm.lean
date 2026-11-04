/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import TauCeti.MeasureTheory.Group.Convolution.Support
public import TauCeti.MeasureTheory.Group.ModularCharacter
public import TauCeti.MeasureTheory.Integral.Bochner.Set
public import TauCeti.RepresentationTheory.Continuous.Integrated.Basic
public import TauCeti.RepresentationTheory.Continuous.LeftRegular
public import TauCeti.RepresentationTheory.Continuous.Unitary.StronglyContinuous
import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Multiplier
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star

/-!
# Group convolution algebras, integrated unitary representations and the full group C⋆-seminorm

Let `G : Type u` be a locally compact group and `μ` a left Haar measure on `G`. The *group
convolution algebra* `GroupConvolutionAlgebra G μ` is the space `C_c(G, ℂ)` of compactly supported
continuous complex-valued functions on `G`, equipped with the convolution product

`(f * g) s = ∫ r, f r * g (r⁻¹ * s) ∂μ`,

the modular-weighted involution `f⋆ s = c(s) • conj (f s⁻¹)` (where `c` is Mathlib's modular
character, the inverse of Williams's and Folland's modular function `Δ`), and the `L¹(μ)` norm
`‖f‖ = ∫ s, ‖f s‖ ∂μ`. Left translation `(r • f) s = f (r⁻¹ * s)` acts by `L¹` linear isometries
with continuous orbits.

Every strongly continuous unitary representation `U : ContRepresentation ℂ G H` on a complex
Hilbert space `H` integrates to a bounded linear map
`ContRepresentation.IsUnitary.integratedOperator` on `C_c(G, ℂ)` via the Hilbert-space vector
integral

`U(f) v = ∫ g, f g • U g v ∂μ`,

which becomes a nonunital ⋆-algebra homomorphism `ContRepresentation.IsUnitary.integratedStarAlgHom`
on `GroupConvolutionAlgebra G μ`, bounded by the `L¹` norm and turning left translation into left
multiplication by `U r`. On `L²(G, ℂ)`, the integrated left regular representation is injective
whenever `μ` is inner regular for compact sets on sets of finite measure.

The *full* (or *universal*) *group C⋆-seminorm* `GroupConvolutionAlgebra.fullSeminorm G μ` is

`‖f‖ᵤ = sup ‖U(f)‖`,

ranging over strongly continuous unitary representations on Hilbert spaces in `Type u`. It is a
submultiplicative, star-invariant seminorm dominated by the `L¹` norm and satisfying the
C⋆-identity `‖f⋆ * f‖ᵤ = ‖f‖ᵤ * ‖f‖ᵤ`. Its completion is the full group C⋆-algebra `C⋆(G)`.

No Hausdorff, separability, second-countability or σ-finiteness assumption is imposed where not
needed.

## Main definitions

* `TauCeti.GroupConvolutionAlgebra`: the convolution ⋆-algebra on `C_c(G, ℂ)` with its `L¹` norm.
* `TauCeti.GroupConvolutionAlgebra.translateLIE`: left translation `(r • f) s = f (r⁻¹ * s)` as an
  `L¹` linear isometric equivalence.
* `ContRepresentation.IsUnitary.integratedOperator` and
  `ContRepresentation.IsUnitary.integratedStarAlgHom`: the Hilbert-space vector-integrated form of
  a strongly continuous unitary representation.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm`: the universal group C⋆-seminorm `‖·‖ᵤ`.

## Main statements

* `MeasureTheory.Measure.injective_integratedOperator_leftRegular`: the integrated left regular
  representation on `L²(G, ℂ)` is injective.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm_mul_le`,
  `TauCeti.GroupConvolutionAlgebra.fullSeminorm_star` and
  `TauCeti.GroupConvolutionAlgebra.fullSeminorm_star_mul_self`: the full group seminorm is a
  C⋆-seminorm.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm_eq_zero_iff`: the full group seminorm is definite
  for every left Haar measure.

## References

* Jacques Dixmier, *C*-Algebras*, §13.9 (group C*-algebras of locally compact groups).
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.5, §3.2 and §7.1.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* The twisted-action counterparts `TauCeti.CStarAction.ConvolutionAlgebra` and
  `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm` in
  `TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra` and
  `TauCeti.Analysis.CStarAlgebra.Action.Covariant.FullSeminorm`, which supply the underlying
  associativity, left-regular injectivity and C*-seminorm patterns.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Function
open scoped CompactlySupported Pointwise InnerProductSpace ENNReal

namespace TauCeti

/-- The group convolution ⋆-algebra on `C_c(G, ℂ)` with respect to a measure `μ`: compactly
supported continuous complex-valued functions on `G`, with convolution as product, the
modular-weighted involution as star, and the `L¹(μ)` norm. Use `GroupConvolutionAlgebra.toConv`
and `GroupConvolutionAlgebra.ofConv` to pass to and from `C_c(G, ℂ)`, whose own product and star
are pointwise. -/
structure GroupConvolutionAlgebra (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (μ : Measure G) where
  /-- Regard a compactly supported continuous function as an element of the group convolution
  algebra. -/
  toConv ::
  /-- The compactly supported continuous function underlying an element of the group convolution
  algebra. -/
  ofConv : C_c(G, ℂ)

namespace GroupConvolutionAlgebra

section Basic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}

@[simp]
theorem ofConv_toConv (f : C_c(G, ℂ)) : (toConv f : GroupConvolutionAlgebra G μ).ofConv = f :=
  (rfl)

@[simp]
theorem toConv_ofConv (f : GroupConvolutionAlgebra G μ) : toConv f.ofConv = f :=
  (rfl)

theorem ofConv_injective : Function.Injective (ofConv : GroupConvolutionAlgebra G μ → C_c(G, ℂ)) :=
  fun f g h => by rw [← toConv_ofConv f, h, toConv_ofConv]

theorem toConv_injective : Function.Injective (toConv : C_c(G, ℂ) → GroupConvolutionAlgebra G μ) :=
  fun f g h => by rw [← ofConv_toConv (μ := μ) f, h, ofConv_toConv]

@[ext]
theorem ext {f g : GroupConvolutionAlgebra G μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

variable (G μ) in
/-- `GroupConvolutionAlgebra.ofConv` and `GroupConvolutionAlgebra.toConv` as an equivalence. -/
def equiv : GroupConvolutionAlgebra G μ ≃ C_c(G, ℂ) where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (f : GroupConvolutionAlgebra G μ) : equiv G μ f = f.ofConv :=
  (rfl)

@[simp]
theorem equiv_symm_apply (f : C_c(G, ℂ)) : (equiv G μ).symm f = toConv f :=
  (rfl)

instance : AddCommGroup (GroupConvolutionAlgebra G μ) :=
  (equiv G μ).addCommGroup

variable (G μ) in
/-- `GroupConvolutionAlgebra.ofConv` as an additive equivalence with `C_c(G, ℂ)`. -/
def addEquiv : GroupConvolutionAlgebra G μ ≃+ C_c(G, ℂ) where
  __ := equiv G μ
  map_add' _ _ := (rfl)

@[simp]
theorem addEquiv_apply (f : GroupConvolutionAlgebra G μ) : addEquiv G μ f = f.ofConv :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply (f : C_c(G, ℂ)) : (addEquiv G μ).symm f = toConv f :=
  (rfl)

instance : Module ℂ (GroupConvolutionAlgebra G μ) :=
  (addEquiv G μ).module ℂ

@[simp]
theorem ofConv_zero : (0 : GroupConvolutionAlgebra G μ).ofConv = 0 :=
  (rfl)

@[simp]
theorem ofConv_add (f g : GroupConvolutionAlgebra G μ) : (f + g).ofConv = f.ofConv + g.ofConv :=
  (rfl)

@[simp]
theorem ofConv_neg (f : GroupConvolutionAlgebra G μ) : (-f).ofConv = -f.ofConv :=
  (rfl)

@[simp]
theorem ofConv_sub (f g : GroupConvolutionAlgebra G μ) : (f - g).ofConv = f.ofConv - g.ofConv :=
  (rfl)

@[simp]
theorem ofConv_smul (c : ℂ) (f : GroupConvolutionAlgebra G μ) : (c • f).ofConv = c • f.ofConv :=
  (rfl)

@[simp]
theorem toConv_zero : (toConv 0 : GroupConvolutionAlgebra G μ) = 0 :=
  (rfl)

@[simp]
theorem toConv_add (f g : C_c(G, ℂ)) :
    (toConv (f + g) : GroupConvolutionAlgebra G μ) = toConv f + toConv g :=
  (rfl)

@[simp]
theorem toConv_neg (f : C_c(G, ℂ)) : (toConv (-f) : GroupConvolutionAlgebra G μ) = -toConv f :=
  (rfl)

@[simp]
theorem toConv_sub (f g : C_c(G, ℂ)) :
    (toConv (f - g) : GroupConvolutionAlgebra G μ) = toConv f - toConv g :=
  (rfl)

@[simp]
theorem toConv_smul (c : ℂ) (f : C_c(G, ℂ)) :
    (toConv (c • f) : GroupConvolutionAlgebra G μ) = c • toConv f :=
  (rfl)

variable (G μ) in
/-- `GroupConvolutionAlgebra.ofConv` as a complex linear equivalence with `C_c(G, ℂ)`. -/
def linearEquiv : GroupConvolutionAlgebra G μ ≃ₗ[ℂ] C_c(G, ℂ) where
  __ := equiv G μ
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem linearEquiv_apply (f : GroupConvolutionAlgebra G μ) : linearEquiv G μ f = f.ofConv :=
  (rfl)

@[simp]
theorem linearEquiv_symm_apply (f : C_c(G, ℂ)) : (linearEquiv G μ).symm f = toConv f :=
  (rfl)

end Basic

/-! ### Convolution product -/

section Mul

section Support

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem mem_support_of_mul_ne_zero (f g : C_c(G, ℂ)) {s r : G}
    (hsr : f r * g (r⁻¹ * s) ≠ 0) : r ∈ support f ∧ r⁻¹ * s ∈ support g :=
  ⟨mem_support.2 fun hf => hsr (by simp [hf]), mem_support.2 fun hg => hsr (by simp [hg])⟩

private theorem mem_tsupport_of_mul_ne_zero (f g : C_c(G, ℂ)) {s r : G}
    (hsr : f r * g (r⁻¹ * s) ≠ 0) : r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
  (mem_support_of_mul_ne_zero f g hsr).imp (subset_tsupport _ ·) (subset_tsupport _ ·)

private theorem continuous_mul_integrand [IsTopologicalGroup G] (f g : C_c(G, ℂ)) :
    Continuous (uncurry fun s r => f r * g (r⁻¹ * s)) := by
  rw [uncurry_def]
  fun_prop

end Support

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-- The convolution integrand `r ↦ f r * g (r⁻¹ * s)` is integrable on `G`. -/
theorem integrable_mul_integrand (f g : C_c(G, ℂ)) (s : G) :
    Integrable (fun r => f r * g (r⁻¹ * s)) μ :=
  ((continuous_mul_integrand f g).comp (.prodMk_right s)).integrable_of_hasCompactSupport
    (f.hasCompactSupport.mono' fun _ hr => (mem_tsupport_of_mul_ne_zero f g hr).1)

instance : Mul (GroupConvolutionAlgebra G μ) where
  mul f g := toConv
    { toFun s := ∫ r, f.ofConv r * g.ofConv (r⁻¹ * s) ∂μ
      continuous_toFun := continuous_integral_of_compact_support μ f.ofConv.hasCompactSupport
        (by rw [uncurry_def]; fun_prop)
        fun _ _ h => subset_tsupport _ (mem_support.2 fun hf => h (by simp [hf]))
      hasCompactSupport' := hasCompactSupport_integral_of_inv_mul_mem μ f.ofConv.hasCompactSupport
        g.ofConv.hasCompactSupport fun _ _ h =>
          ⟨subset_tsupport _ (mem_support.2 fun hf => h (by simp [hf])),
           subset_tsupport _ (mem_support.2 fun hg => h (by simp [hg]))⟩ }

/-- The convolution product in `GroupConvolutionAlgebra G μ` is given by
`(f * g) s = ∫ r, f r * g (r⁻¹ * s) ∂μ`. -/
@[simp]
theorem ofConv_mul_apply (f g : GroupConvolutionAlgebra G μ) (s : G) :
    (f * g).ofConv s = ∫ r, f.ofConv r * g.ofConv (r⁻¹ * s) ∂μ :=
  (rfl)

private theorem ofConv_mul_eq_trivial_convolution (f g : GroupConvolutionAlgebra G μ) :
    (f * g).ofConv =
      (CStarAction.trivial (G := G) (A := ℂ)).convolution μ f.ofConv g.ofConv := by
  ext s
  simp

/-- A convolution product is supported in the product of the supports. -/
theorem support_ofConv_mul_subset (f g : GroupConvolutionAlgebra G μ) :
    support (f * g).ofConv ⊆ support f.ofConv * support g.ofConv :=
  support_integral_subset_mul μ fun _ _ => mem_support_of_mul_ne_zero f.ofConv g.ofConv

instance : NonUnitalNonAssocRing (GroupConvolutionAlgebra G μ) where
  left_distrib f g h := by
    apply ext; ext s
    simp only [ofConv_mul_apply, ofConv_add, CompactlySupportedContinuousMap.add_apply, mul_add]
    exact integral_add (integrable_mul_integrand f.ofConv g.ofConv s)
      (integrable_mul_integrand f.ofConv h.ofConv s)
  right_distrib f g h := by
    apply ext; ext s
    simp only [ofConv_mul_apply, ofConv_add, CompactlySupportedContinuousMap.add_apply, add_mul]
    exact integral_add (integrable_mul_integrand f.ofConv h.ofConv s)
      (integrable_mul_integrand g.ofConv h.ofConv s)
  zero_mul f := by apply ext; ext s; simp
  mul_zero f := by apply ext; ext s; simp

instance : IsScalarTower ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ) where
  smul_assoc c f g := by
    rw [smul_eq_mul, smul_eq_mul]
    apply ext; ext s
    simp only [ofConv_mul_apply, ofConv_smul, CompactlySupportedContinuousMap.coe_smul,
      Pi.smul_apply, smul_mul_assoc]
    exact integral_smul c _

instance : SMulCommClass ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ) where
  smul_comm c f g := by
    rw [smul_eq_mul, smul_eq_mul]
    apply ext; ext s
    simp only [ofConv_mul_apply, ofConv_smul, CompactlySupportedContinuousMap.coe_smul,
      Pi.smul_apply, mul_smul_comm]
    exact (integral_smul c _).symm

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

instance : NonUnitalRing (GroupConvolutionAlgebra G μ) where
  mul_assoc f g h := by
    apply ext
    simp only [ofConv_mul_eq_trivial_convolution, CStarAction.convolution_assoc]

end Mul

/-! ### Modular-weighted involution -/

section Star

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] {μ : Measure G}

instance : Star (GroupConvolutionAlgebra G μ) where
  star f := toConv
    { toFun s := (Measure.modularCharacter s : ℝ) • star (f.ofConv s⁻¹)
      continuous_toFun :=
        (NNReal.continuous_coe.comp continuous_modularCharacter).smul
          (f.ofConv.continuous.comp continuous_inv).star
      hasCompactSupport' :=
        (f.ofConv.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mono fun s hs hz =>
          hs <| by
            have hz' : f.ofConv s⁻¹ = 0 := hz
            simp [hz'] }

/-- The involution on `GroupConvolutionAlgebra G μ` is given by
`f⋆ s = c(s) • conj (f s⁻¹)`, where `c` is Mathlib's modular character. -/
@[simp]
theorem ofConv_star_apply (f : GroupConvolutionAlgebra G μ) (s : G) :
    (star f).ofConv s = (Measure.modularCharacter s : ℝ) • star (f.ofConv s⁻¹) :=
  (rfl)

private theorem ofConv_star_eq_trivial_twistedInvolution (f : GroupConvolutionAlgebra G μ) :
    (star f).ofConv = (CStarAction.trivial (G := G) (A := ℂ)).twistedInvolution f.ofConv := by
  ext s
  simp [CStarAction.twistedInvolution_apply]

instance : InvolutiveStar (GroupConvolutionAlgebra G μ) where
  star_involutive f := by
    apply ext
    simp only [ofConv_star_eq_trivial_twistedInvolution,
      CStarAction.twistedInvolution_twistedInvolution]

instance : StarModule ℂ (GroupConvolutionAlgebra G μ) where
  star_smul c f := by
    apply ext; ext s
    simp only [ofConv_star_apply, ofConv_smul, CompactlySupportedContinuousMap.smul_apply,
      star_smul]
    exact smul_comm _ _ _

variable [OpensMeasurableSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant]

instance : StarRing (GroupConvolutionAlgebra G μ) where
  star_mul f g := by
    apply ext
    simp only [ofConv_star_eq_trivial_twistedInvolution, ofConv_mul_eq_trivial_convolution,
      CStarAction.twistedInvolution_convolution]
  star_add f g := by
    apply ext; ext s
    simp only [ofConv_star_apply, ofConv_add, CompactlySupportedContinuousMap.add_apply,
      star_add, smul_add]

end Star

/-! ### The `L¹` norm and left translation -/

section Normed

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-- Realize an element of the group convolution algebra as an `L¹` equivalence class. -/
def toL1 : GroupConvolutionAlgebra G μ →ₗ[ℂ] Lp ℂ 1 μ where
  toFun f := f.ofConv.integrable.toL1 f.ofConv
  map_add' f g := by
    simpa only [ofConv_add, CompactlySupportedContinuousMap.coe_add] using
      Integrable.toL1_add (f.ofConv : G → ℂ) (g.ofConv : G → ℂ)
        f.ofConv.integrable g.ofConv.integrable
  map_smul' c f := by
    simpa only [ofConv_smul, CompactlySupportedContinuousMap.coe_smul, RingHom.id_apply] using
      Integrable.toL1_smul' (f.ofConv : G → ℂ) f.ofConv.integrable c

/-- The `L¹` class of a group convolution element is represented by its underlying function. -/
theorem coeFn_toL1 (f : GroupConvolutionAlgebra G μ) : toL1 f =ᵐ[μ] f.ofConv :=
  f.ofConv.integrable.coeFn_toL1

instance : SeminormedAddCommGroup (GroupConvolutionAlgebra G μ) :=
  .induced _ _ (toL1 (G := G) (μ := μ)).toAddMonoidHom

instance : NormedSpace ℂ (GroupConvolutionAlgebra G μ) :=
  .induced ℂ _ _ (toL1 (G := G) (μ := μ))

/-- The norm on `GroupConvolutionAlgebra G μ` is the `L¹(μ)` integral norm. -/
theorem norm_eq_integral_norm (f : GroupConvolutionAlgebra G μ) : ‖f‖ = ∫ s, ‖f.ofConv s‖ ∂μ :=
  (L1.norm_eq_integral_norm (toL1 f)).trans
    (integral_congr_ae ((coeFn_toL1 f).fun_comp norm))

@[simp]
theorem norm_toConv (f : C_c(G, ℂ)) :
    ‖(toConv f : GroupConvolutionAlgebra G μ)‖ = ∫ s, ‖f s‖ ∂μ :=
  norm_eq_integral_norm _

variable (G μ) in
/-- The linear isometry from the group convolution algebra with its `L¹` seminorm into
`L¹(G, μ)`. -/
def toL1LI : GroupConvolutionAlgebra G μ →ₗᵢ[ℂ] Lp ℂ 1 μ where
  __ := toL1
  norm_map' _ := (rfl)

@[simp]
theorem toL1LI_apply (f : GroupConvolutionAlgebra G μ) : toL1LI G μ f = toL1 f :=
  (rfl)

section MulNorm

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

instance : NonUnitalSeminormedRing (GroupConvolutionAlgebra G μ) where
  __ : SeminormedAddCommGroup (GroupConvolutionAlgebra G μ) := inferInstance
  __ : NonUnitalRing (GroupConvolutionAlgebra G μ) := inferInstance
  norm_mul_le f g := by
    rw [norm_eq_integral_norm, norm_eq_integral_norm, norm_eq_integral_norm,
      ofConv_mul_eq_trivial_convolution]
    exact (CStarAction.trivial (G := G) (A := ℂ)).integral_norm_convolution_le μ f.ofConv g.ofConv

end MulNorm

section OpenPos

variable [μ.IsOpenPosMeasure]

theorem toL1_injective : Function.Injective (toL1 (G := G) (μ := μ)) := by
  intro f g h
  apply ext
  exact CompactlySupportedContinuousMap.ext fun s => congrFun
    (Measure.eq_of_ae_eq ((coeFn_toL1 f).symm.trans (h ▸ coeFn_toL1 g))
      f.ofConv.continuous g.ofConv.continuous) s

instance : NormedAddCommGroup (GroupConvolutionAlgebra G μ) :=
  .ofSeparation fun f hf => toL1_injective <| by
    rw [map_zero]
    exact norm_eq_zero.1 (((toL1LI G μ).norm_map f).trans hf)

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

instance : NonUnitalNormedRing (GroupConvolutionAlgebra G μ) where
  __ : NonUnitalSeminormedRing (GroupConvolutionAlgebra G μ) := inferInstance
  __ : NormedAddCommGroup (GroupConvolutionAlgebra G μ) := inferInstance

end OpenPos

section StarNorm

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsMulLeftInvariant]

/-- The modular-weighted involution is isometric for the `L¹` seminorm. -/
theorem norm_star (f : GroupConvolutionAlgebra G μ) : ‖star f‖ = ‖f‖ := by
  rw [norm_eq_integral_norm, norm_eq_integral_norm, ofConv_star_eq_trivial_twistedInvolution]
  simpa only [CStarAction.ConvolutionAlgebra.norm_eq_integral_norm,
    CStarAction.ConvolutionAlgebra.ofConv_star] using
    CStarAction.ConvolutionAlgebra.norm_star
      (α := CStarAction.trivial (G := G) (A := ℂ)) (μ := μ) ⟨f.ofConv⟩

instance : NormedStarGroup (GroupConvolutionAlgebra G μ) where
  norm_star_le f := (norm_star f).le

end StarNorm

section Translate

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Left translation `(r • f) s = f (r * s)` of a compactly supported function before bundling. -/
private def mulLeftAux (r : G) (f : C_c(G, ℂ)) : C_c(G, ℂ) where
  toFun s := f (r * s)
  continuous_toFun := f.continuous.comp (continuous_const.mul continuous_id)
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft r)

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] in
private theorem mulLeftAux_apply (r : G) (f : C_c(G, ℂ)) (s : G) :
    mulLeftAux r f s = f (r * s) :=
  rfl

/-- Left translation `(r • f) s = f (r⁻¹ * s)`, bundled as a linear isometric equivalence on
`GroupConvolutionAlgebra G μ` for the `L¹` seminorm. -/
def translateLIE (r : G) : GroupConvolutionAlgebra G μ ≃ₗᵢ[ℂ] GroupConvolutionAlgebra G μ where
  toFun f := toConv (mulLeftAux r⁻¹ f.ofConv)
  invFun f := toConv (mulLeftAux r f.ofConv)
  left_inv f := by apply ext; ext s; simp [mulLeftAux_apply]
  right_inv f := by apply ext; ext s; simp [mulLeftAux_apply]
  map_add' f g := by apply ext; ext s; rfl
  map_smul' c f := by apply ext; ext s; rfl
  norm_map' f := by
    rw [norm_toConv, norm_eq_integral_norm]
    exact integral_mul_left_eq_self (μ := μ) (fun s => ‖f.ofConv s‖) r⁻¹

@[simp]
theorem ofConv_translateLIE_apply (r : G) (f : GroupConvolutionAlgebra G μ) (s : G) :
    (translateLIE r f).ofConv s = f.ofConv (r⁻¹ * s) :=
  (rfl)

@[simp]
theorem ofConv_translateLIE_symm_apply (r : G) (f : GroupConvolutionAlgebra G μ) (s : G) :
    ((translateLIE r).symm f).ofConv s = f.ofConv (r * s) :=
  (rfl)

private theorem ofConv_translateLIE_eq_trivial_translate (r : G)
    (f : GroupConvolutionAlgebra G μ) :
    (translateLIE r f).ofConv = (CStarAction.trivial (G := G) (A := ℂ)).translate r f.ofConv := by
  ext s
  simp

@[simp]
theorem translateLIE_one : translateLIE (G := G) (μ := μ) 1 = 1 := by
  ext f : 1
  apply ext; ext s
  simp

theorem translateLIE_symm (r : G) :
    (translateLIE (G := G) (μ := μ) r).symm = translateLIE r⁻¹ := by
  ext f : 1
  apply ext; ext s
  simp

@[simp]
theorem translateLIE_inv_translateLIE (r : G) (f : GroupConvolutionAlgebra G μ) :
    translateLIE r⁻¹ (translateLIE r f) = f := by
  rw [← translateLIE_symm]
  exact LinearIsometryEquiv.symm_apply_apply _ _

@[simp]
theorem translateLIE_translateLIE_inv (r : G) (f : GroupConvolutionAlgebra G μ) :
    translateLIE r (translateLIE r⁻¹ f) = f := by
  rw [← translateLIE_symm]
  exact LinearIsometryEquiv.apply_symm_apply _ _

/-- Left translations form a left group action on `GroupConvolutionAlgebra G μ`. -/
theorem translateLIE_mul (r t : G) :
    translateLIE (G := G) (μ := μ) (r * t) = translateLIE r * translateLIE t := by
  ext f : 1
  apply ext; ext s
  simp [mul_assoc]

/-- Left translation is a left multiplier of convolution: `(r • f) * g = r • (f * g)`. -/
theorem translateLIE_apply_mul (r : G) (f g : GroupConvolutionAlgebra G μ) :
    translateLIE r (f * g) = translateLIE r f * g := by
  apply ext
  simp only [ofConv_mul_eq_trivial_convolution, ofConv_translateLIE_eq_trivial_translate,
    CStarAction.translate_convolution]

/-- Group orbits of compactly supported functions are continuous in the `L¹` topology. -/
theorem continuous_translateLIE [LocallyCompactSpace G] (f : GroupConvolutionAlgebra G μ) :
    Continuous fun r : G => translateLIE r f := by
  let e : CStarAction.ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ ≃ₗᵢ[ℂ]
      GroupConvolutionAlgebra G μ :=
    { toFun := fun g => toConv g.ofConv
      invFun := fun g => ⟨g.ofConv⟩
      left_inv := fun g => CStarAction.ConvolutionAlgebra.ext rfl
      right_inv := fun g => ext rfl
      map_add' := fun _ _ => by apply ext; ext s; simp
      map_smul' := fun _ _ => by apply ext; ext s; simp
      norm_map' := fun g => (norm_toConv g.ofConv).trans
        (CStarAction.ConvolutionAlgebra.norm_eq_integral_norm g).symm }
  have heq : (fun r : G => translateLIE r f) =
      fun r => e (CStarAction.ConvolutionAlgebra.translateLIE
        (α := CStarAction.trivial (G := G) (A := ℂ)) (μ := μ) r ⟨f.ofConv⟩) := by
    funext r
    apply ext
    ext s
    simp [e]
  rw [heq]
  exact e.continuous.comp
    (CStarAction.ConvolutionAlgebra.continuous_translateLIE
      (α := CStarAction.trivial (G := G) (A := ℂ)) (μ := μ) ⟨f.ofConv⟩)

end Translate

end Normed

end GroupConvolutionAlgebra

end TauCeti

/-! ### Integrated forms of strongly continuous unitary representations -/

namespace ContRepresentation.IsUnitary

open TauCeti

section Integrand

variable {G H : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The vector integrand `g ↦ f g • U g v` of a strongly continuous representation is
continuous. -/
@[fun_prop]
theorem continuous_integrand {U : ContRepresentation ℂ G H}
    (hcont : ∀ v, Continuous fun g => U g v) (f : C_c(G, ℂ)) (v : H) :
    Continuous fun g => f g • U g v :=
  f.continuous.smul (hcont v)

/-- The vector integrand `g ↦ f g • U g v` has compact support. -/
theorem hasCompactSupport_integrand (U : ContRepresentation ℂ G H) (f : C_c(G, ℂ)) (v : H) :
    HasCompactSupport fun g => f g • U g v :=
  f.hasCompactSupport.smul_right

/-- The vector integrand `g ↦ f g • U g v` is Bochner integrable. -/
theorem integrable_integrand [MeasurableSpace G] [OpensMeasurableSpace G]
    {U : ContRepresentation ℂ G H} (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : C_c(G, ℂ)) (v : H) :
    Integrable (fun g => f g • U g v) μ :=
  (continuous_integrand hcont f v).integrable_of_hasCompactSupport
    (hasCompactSupport_integrand U f v)

end Integrand

section FiniteMeasure

variable {G H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem norm_integral_integrand_le {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : C_c(G, ℂ)) (v : H) :
    ‖∫ g, f g • U g v ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  calc ‖∫ g, f g • U g v ∂μ‖ ≤ ∫ g, ‖f g‖ * ‖v‖ ∂μ :=
        norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun g => by
          rw [norm_smul, hU.norm_map])
    _ = (∫ g, ‖f g‖ ∂μ) * ‖v‖ := integral_mul_const _ _

/-- The integrated form of a strongly continuous unitary representation on `C_c(G, ℂ)`, defined by
the Hilbert-space vector integral `U(f) v = ∫ g, f g • U g v ∂μ`. -/
def integratedOperator {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] :
    C_c(G, ℂ) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun f := LinearMap.mkContinuous
    { toFun v := ∫ g, f g • U g v ∂μ
      map_add' v w := by
        simp_rw [map_add, smul_add]
        exact integral_add (integrable_integrand hcont μ f v) (integrable_integrand hcont μ f w)
      map_smul' c v := by
        simp_rw [map_smul, smul_comm _ c]
        exact integral_smul c _ }
    (∫ g, ‖f g‖ ∂μ) (hU.norm_integral_integrand_le μ f)
  map_add' f g := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.add_apply, add_smul,
      add_apply]
    exact integral_add (integrable_integrand hcont μ f v) (integrable_integrand hcont μ g v)
  map_smul' c f := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.smul_apply,
      smul_eq_mul, mul_smul, RingHom.id_apply, smul_apply]
    exact integral_smul c _

/-- The defining vector formula `U(f) v = ∫ g, f g • U g v ∂μ` for the integrated operator. -/
theorem integratedOperator_apply {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(G, ℂ)) (v : H) :
    hU.integratedOperator hcont μ f v = ∫ g, f g • U g v ∂μ :=
  (rfl)

/-- The operator norm of `U(f)` is bounded by the `L¹(μ)` norm of `f`. -/
theorem norm_integratedOperator_le {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(G, ℂ)) :
    ‖hU.integratedOperator hcont μ f‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
    (hU.norm_integral_integrand_le μ f)

variable [CompleteSpace H]

/-- View a strongly continuous unitary group representation as a covariant pair for the trivial
action on `ℂ` with unital scalar coefficients. -/
private def toTrivialCovariant {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) :
    CStarAction.CovariantRepresentation (CStarAction.trivial (G := G) (A := ℂ)) H where
  coefficient := (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
  group := U
  isUnitary := hU
  continuous_orbit := hcont
  covariance g z v := by simp [Algebra.algebraMap_eq_smul_one]

private theorem integratedOperator_eq_toTrivialCovariant {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : C_c(G, ℂ)) :
    hU.integratedOperator hcont μ f = (hU.toTrivialCovariant hcont).integratedOperator μ f := by
  ext v
  simp [integratedOperator_apply, toTrivialCovariant,
    CStarAction.CovariantRepresentation.integratedOperator_apply, Algebra.algebraMap_eq_smul_one]

/-- Matrix coefficients of the integrated operator are integrals of scalar matrix coefficients:
`⟪w, U(f) v⟫ = ∫ g, f g * ⟪w, U g v⟫ ∂μ`. -/
theorem inner_integratedOperator_apply {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(G, ℂ)) (w v : H) :
    ⟪w, hU.integratedOperator hcont μ f v⟫_ℂ = ∫ g, f g * ⟪w, U g v⟫_ℂ ∂μ := by
  rw [integratedOperator_apply, ← integral_inner (integrable_integrand hcont μ f v) w]
  simp_rw [inner_smul_right]

/-- The integrated operators of a strongly continuous unitary representation span a dense
subspace of `H` for any measure finite on compact sets and positive on nonempty open sets. -/
theorem dense_span_integratedOperator [LocallyCompactSpace G] [R1Space G]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] :
    Dense (Submodule.span ℂ (⋃ f : C_c(G, ℂ), Set.range (hU.integratedOperator hcont μ f)) :
      Set H) := by
  simp_rw [hU.integratedOperator_eq_toTrivialCovariant hcont μ]
  rw [CStarAction.CovariantRepresentation.dense_span_integratedOperator_iff]
  exact NonUnitalStarAlgHom.isNondegenerate_of_map_one (B := ℂ)
    (map_one (StarAlgHom.ofId ℂ (H →L[ℂ] H)))

end FiniteMeasure

section ScalarComparison

variable {G H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Transport the measurable space from `G` to `Additive G`. -/
@[reducible] local instance : MeasurableSpace (Additive G) := ‹MeasurableSpace G›
local instance : R1Space (Additive G) := ‹R1Space G›
local instance : BorelSpace (Additive G) := ‹BorelSpace G›

/-- The compactly supported integrated operator agrees with
`ContRepresentation.integratedOperatorL1` after transporting `G` to `Additive G`. -/
theorem integratedOperator_eq_integratedOperatorL1 {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] (f : C_c(G, ℂ)) :
    letI : Measure.InnerRegularCompactLTTop (α := Additive G) μ :=
      inferInstanceAs (Measure.InnerRegularCompactLTTop (α := G) μ)
    hU.integratedOperator hcont μ f =
      (U.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).integratedOperatorL1
        (G := Additive G) (fun v => hcont v)
        (hU.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le
        (μ : Measure (Additive G))
        (Integrable.toL1 (α := Additive G) (f : Additive G → ℂ) f.integrable) := by
  let : Measure.InnerRegularCompactLTTop (α := Additive G) μ :=
    inferInstanceAs (Measure.InnerRegularCompactLTTop (α := G) μ)
  rw [integratedOperator_eq_toTrivialCovariant]
  simpa [toTrivialCovariant] using
    (hU.toTrivialCovariant hcont).integratedOperator_eq_coefficient_mul_integratedOperatorL1
      μ f f 1 (fun g => by simp)

end ScalarComparison

section Convolution

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The integrated form turns convolution into operator multiplication:
`U(f * g) = U(f) * U(g)`. -/
@[simp]
theorem integratedOperator_mul {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (f g : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (f * g).ofConv =
      hU.integratedOperator hcont μ f.ofConv * hU.integratedOperator hcont μ g.ofConv := by
  have hfg : (f * g).ofConv =
      (CStarAction.trivial (G := G) (A := ℂ)).convolution μ f.ofConv g.ofConv := by
    ext s; simp
  simp only [integratedOperator_eq_toTrivialCovariant, hfg,
    CStarAction.CovariantRepresentation.integratedOperator_convolution]

/-- The integrated form turns left translation into left multiplication by `U r`:
`U(r • f) = U r * U(f)`. -/
@[simp]
theorem integratedOperator_translateLIE {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (r : G) (f : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (GroupConvolutionAlgebra.translateLIE r f).ofConv =
      U r * hU.integratedOperator hcont μ f.ofConv := by
  have hrf : (GroupConvolutionAlgebra.translateLIE r f).ofConv =
      (CStarAction.trivial (G := G) (A := ℂ)).translate r f.ofConv := by
    ext s; simp
  simp only [integratedOperator_eq_toTrivialCovariant, hrf,
    CStarAction.CovariantRepresentation.integratedOperator_translate]
  rfl

end Convolution

section Star

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The integrated form sends the modular-weighted involution to the operator adjoint:
`U(f⋆) = U(f)⋆`. -/
@[simp]
theorem integratedOperator_star {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (star f).ofConv =
      star (hU.integratedOperator hcont μ f.ofConv) := by
  have hf : (star f).ofConv =
      (CStarAction.trivial (G := G) (A := ℂ)).twistedInvolution f.ofConv := by
    ext s
    simp [CStarAction.twistedInvolution_apply]
  simp only [integratedOperator_eq_toTrivialCovariant, hf,
    CStarAction.CovariantRepresentation.integratedOperator_twistedInvolution]

/-- The integrated form of a strongly continuous unitary representation as a nonunital complex
⋆-algebra homomorphism out of `GroupConvolutionAlgebra G μ`. -/
def integratedStarAlgHom {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    GroupConvolutionAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun f := hU.integratedOperator hcont μ f.ofConv
  map_zero' := by simp
  map_add' f g := by simp
  map_mul' f g := hU.integratedOperator_mul hcont μ f g
  map_smul' c f := by simp
  map_star' f := hU.integratedOperator_star hcont μ f

@[simp]
theorem integratedStarAlgHom_apply {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont μ f = hU.integratedOperator hcont μ f.ofConv :=
  (rfl)

/-- The integrated ⋆-homomorphism is contractive for the `L¹` norm. -/
theorem norm_integratedStarAlgHom_le_norm {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    ‖hU.integratedStarAlgHom hcont μ f‖ ≤ ‖f‖ := by
  simpa only [integratedStarAlgHom_apply, GroupConvolutionAlgebra.norm_eq_integral_norm] using
    hU.norm_integratedOperator_le hcont μ f.ofConv

/-- The integrated ⋆-homomorphism turns left translation into left multiplication by `U r`. -/
theorem integratedStarAlgHom_translateLIE {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (r : G) (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont μ (GroupConvolutionAlgebra.translateLIE r f) =
      U r * hU.integratedStarAlgHom hcont μ f :=
  hU.integratedOperator_translateLIE hcont μ r f

omit [LocallyCompactSpace G] [CompleteSpace H] in
/-- Integrating a strongly continuous unitary representation against any left-invariant measure
`μ'` finite on compact sets rescales the integral against a Haar measure `ν` by
`Measure.haarScalarFactor μ' ν`. -/
theorem integratedOperator_eq_haarScalarFactor_smul {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant]
    (ν : Measure G) [ν.IsHaarMeasure] (f : C_c(G, ℂ)) :
    hU.integratedOperator hcont μ' f =
      (Measure.haarScalarFactor μ' ν : ℝ) • hU.integratedOperator hcont ν f := by
  ext v
  simp only [integratedOperator_apply, smul_apply]
  exact TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul μ' ν
    (continuous_integrand hcont f v) (hasCompactSupport_integrand U f v)

end Star

section CommGroup

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On an abelian group, every operator `U r` commutes with every integrated operator `U(f)`. -/
theorem commute_integratedOperator [OpensMeasurableSpace G] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (r : G) (f : C_c(G, ℂ)) :
    Commute (U r) (hU.integratedOperator hcont μ f) := by
  ext v
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    integratedOperator_apply, integratedOperator_apply,
    ← (U r).integral_comp_comm (integrable_integrand hcont μ f v)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only
  rw [map_smul]
  exact congrArg (f g • ·) (congr($(map_mul U r g) v).symm.trans <|
    by rw [mul_comm r g, map_mul]; rfl)

/-- On an abelian group, integrated operators of a strongly continuous unitary representation
commute with each other. -/
theorem integratedOperator_commute [OpensMeasurableSpace G] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f g : C_c(G, ℂ)) :
    Commute (hU.integratedOperator hcont μ f) (hU.integratedOperator hcont μ g) := by
  ext v
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    integratedOperator_apply hU hcont μ g,
    ← (hU.integratedOperator hcont μ f).integral_comp_comm (integrable_integrand hcont μ g v),
    integratedOperator_apply hU hcont μ g]
  refine integral_congr_ae (.of_forall fun r => ?_)
  dsimp only
  rw [map_smul]
  exact congrArg (g r • ·) congr($((hU.commute_integratedOperator hcont μ r f).symm.eq) v)

/-- On an abelian group, the integrated ⋆-homomorphism has commutative range. -/
theorem integratedStarAlgHom_commute [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [μ.IsHaarMeasure] (f g : GroupConvolutionAlgebra G μ) :
    Commute (hU.integratedStarAlgHom hcont μ f) (hU.integratedStarAlgHom hcont μ g) :=
  hU.integratedOperator_commute hcont μ f.ofConv g.ofConv

end CommGroup

end ContRepresentation.IsUnitary

/-! ### Injectivity of the integrated left regular representation -/

namespace MeasureTheory.Measure

/-- The integrated left regular representation of `G` on `L²(G, ℂ)` is injective on `C_c(G, ℂ)`
for any left-invariant locally finite measure that is positive on nonempty open sets and inner
regular for compact sets on sets of finite measure. -/
theorem injective_integratedOperator_leftRegular {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] :
    Function.Injective
      ((μ.isUnitary_leftRegular (𝕜 := ℂ) (E := ℂ)).integratedOperator
        (μ.continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top) μ) := by
  let ρ : ℂ →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ) := (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom
  have hρ : Function.Injective ρ := fun z w h => by
    simpa [ρ, Algebra.algebraMap_eq_smul_one] using congr($h (1 : ℂ))
  have heq : (μ.isUnitary_leftRegular (𝕜 := ℂ) (E := ℂ)).integratedOperator
      (μ.continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top) μ =
      (TauCeti.CStarAction.CovariantRepresentation.regular
        (TauCeti.CStarAction.trivial (G := G) (A := ℂ)) ρ μ).integratedOperator μ := by
    ext1 f; ext1 ξ
    rw [ContRepresentation.IsUnitary.integratedOperator_apply,
      TauCeti.CStarAction.CovariantRepresentation.integratedOperator_apply]
    refine congrArg (integral (G := Lp ℂ 2 μ) μ) (funext fun s => ?_)
    rw [TauCeti.CStarAction.CovariantRepresentation.regular_group]
    apply Lp.ext_iff.2
    filter_upwards [Lp.coeFn_smul (f s) (μ.leftRegular ℂ ℂ 2 s ξ),
      TauCeti.CStarAction.CovariantRepresentation.coeFn_regular_coefficient
        (TauCeti.CStarAction.trivial (G := G) (A := ℂ)) ρ μ (f s)
        (μ.leftRegular ℂ ℂ 2 s ξ)] with r h₁ h₂
    rw [h₁, h₂]
    simp [ρ, Algebra.algebraMap_eq_smul_one]
  rw [heq]
  exact TauCeti.CStarAction.CovariantRepresentation.injective_integratedOperator_regular hρ

end MeasureTheory.Measure

/-! ### The universal group C⋆-seminorm -/

namespace TauCeti.GroupConvolutionAlgebra

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

variable (G μ) in
/-- The seminorms `f ↦ ‖U(f)‖` of the integrated forms of strongly continuous unitary
representations of `G` on Hilbert spaces in `Type u`. -/
private def integratedSeminorms : Set (Seminorm ℂ (GroupConvolutionAlgebra G μ)) :=
  {p | ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v),
      p = (normSeminorm ℂ (H →L[ℂ] H)).comp
        (hU.integratedStarAlgHom hcont μ : GroupConvolutionAlgebra G μ →ₗ[ℂ] (H →L[ℂ] H))}

private theorem bddAbove_integratedSeminorms : BddAbove (integratedSeminorms G μ) :=
  ⟨normSeminorm ℂ _, by
    rintro _ ⟨H, _, _, _, U, hU, hcont, rfl⟩ f
    exact hU.norm_integratedStarAlgHom_le_norm hcont μ f⟩

variable (G μ) in
/-- The universal (or full) group C⋆-seminorm `‖f‖ᵤ = sup ‖U(f)‖` on `GroupConvolutionAlgebra G μ`,
ranging over all strongly continuous unitary representations of `G` on Hilbert spaces in `Type u`.
Its completion is the full group C⋆-algebra `FullGroupCStarAlgebra G μ`. -/
def fullSeminorm : Seminorm ℂ (GroupConvolutionAlgebra G μ) :=
  sSup (integratedSeminorms G μ)

/-- The universal group C⋆-seminorm at `f` is the supremum of `‖U(f)‖` over strongly continuous
unitary representations on Hilbert spaces in `Type u`. -/
theorem fullSeminorm_apply (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ f =
      sSup {r | ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v),
          ‖hU.integratedStarAlgHom hcont μ f‖ = r} := by
  rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms, iSup]
  congr 1
  ext r
  simp [integratedSeminorms]

/-- The integrated form of every strongly continuous unitary representation on a Hilbert space in
`Type u` is bounded by the full group C⋆-seminorm. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (f : GroupConvolutionAlgebra G μ) :
    ‖hU.integratedStarAlgHom hcont μ f‖ ≤ fullSeminorm G μ f :=
  le_csSup bddAbove_integratedSeminorms
    ⟨H, inferInstance, inferInstance, inferInstance, U, hU, hcont, rfl⟩ f

/-- The full group C⋆-seminorm is the least nonnegative bound for all integrated forms of strongly
continuous unitary representations on Hilbert spaces in `Type u`. -/
theorem fullSeminorm_le_iff {f : GroupConvolutionAlgebra G μ} {c : ℝ} (hc : 0 ≤ c) :
    fullSeminorm G μ f ≤ c ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v),
          ‖hU.integratedStarAlgHom hcont μ f‖ ≤ c :=
  ⟨fun h _ _ _ _ _ hU hcont => (norm_integratedStarAlgHom_le_fullSeminorm hU hcont f).trans h,
    fun h => by
      rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms]
      exact Real.iSup_le (fun ⟨_, H, _, _, _, U, hU, hcont, hp⟩ => hp ▸ h H U hU hcont) hc⟩

/-- The full group C⋆-seminorm is bounded by the `L¹(μ)` norm. -/
theorem fullSeminorm_le_norm (f : GroupConvolutionAlgebra G μ) : fullSeminorm G μ f ≤ ‖f‖ :=
  (fullSeminorm_le_iff (norm_nonneg f)).2 fun _ _ _ _ _ hU hcont =>
    hU.norm_integratedStarAlgHom_le_norm hcont μ f

/-- The full group C⋆-seminorm is submultiplicative for convolution. -/
theorem fullSeminorm_mul_le (f g : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (f * g) ≤ fullSeminorm G μ f * fullSeminorm G μ g := by
  refine (fullSeminorm_le_iff (mul_nonneg (apply_nonneg _ f) (apply_nonneg _ g))).2
    fun _ _ _ _ _ hU hcont => ?_
  rw [map_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_integratedStarAlgHom_le_fullSeminorm hU hcont f)
    (norm_integratedStarAlgHom_le_fullSeminorm hU hcont g) (norm_nonneg _) (apply_nonneg _ f))

/-- The full group C⋆-seminorm is invariant under the modular-weighted involution. -/
@[simp]
theorem fullSeminorm_star (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (star f) = fullSeminorm G μ f := by
  have key (g : GroupConvolutionAlgebra G μ) : fullSeminorm G μ (star g) ≤ fullSeminorm G μ g := by
    refine (fullSeminorm_le_iff (apply_nonneg _ g)).2 fun _ _ _ _ _ hU hcont => ?_
    rw [map_star, _root_.norm_star]
    exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  exact le_antisymm (key f) (by simpa using key (star f))

/-- The full group C⋆-seminorm satisfies the C⋆-identity `‖f⋆ * f‖ᵤ = ‖f‖ᵤ * ‖f‖ᵤ`. -/
theorem fullSeminorm_star_mul_self (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (star f * f) = fullSeminorm G μ f * fullSeminorm G μ f := by
  refine le_antisymm ((fullSeminorm_mul_le _ _).trans_eq (by rw [fullSeminorm_star])) ?_
  have hsqrt : fullSeminorm G μ f ≤ √(fullSeminorm G μ (star f * f)) := by
    refine (fullSeminorm_le_iff (Real.sqrt_nonneg _)).2 fun _ _ _ _ _ hU hcont => ?_
    refine Real.le_sqrt_of_sq_le ?_
    rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
    exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont _
  calc fullSeminorm G μ f * fullSeminorm G μ f
      ≤ √(fullSeminorm G μ (star f * f)) * √(fullSeminorm G μ (star f * f)) :=
        mul_le_mul hsqrt hsqrt (apply_nonneg _ f) (Real.sqrt_nonneg _)
    _ = fullSeminorm G μ (star f * f) := Real.mul_self_sqrt (apply_nonneg _ _)

/-- For every left Haar measure `μ`, the full group C⋆-seminorm is definite: integrating the left
regular representation of `(Measure.haar : Measure G)` against `μ` rescales its injective
`Measure.haar`-integrated operator by the positive factor `Measure.haarScalarFactor μ Measure.haar`,
and is bounded by `fullSeminorm G μ`. -/
@[simp]
theorem fullSeminorm_eq_zero_iff {f : GroupConvolutionAlgebra G μ} :
    fullSeminorm G μ f = 0 ↔ f = 0 := by
  refine ⟨fun hf => ext ?_, fun hf => hf ▸ map_zero _⟩
  have hU := (Measure.haar : Measure G).isUnitary_leftRegular (𝕜 := ℂ) (E := ℂ)
  have hcont := (Measure.haar : Measure G).continuous_leftRegular_apply
    (𝕜 := ℂ) (E := ℂ) 2 ENNReal.ofNat_ne_top
  have hzero : hU.integratedOperator hcont μ f.ofConv = 0 := by
    rw [← hU.integratedStarAlgHom_apply, ← norm_le_zero_iff, ← hf]
    exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont f
  rw [hU.integratedOperator_eq_haarScalarFactor_smul hcont μ Measure.haar] at hzero
  have hhaar := (smul_eq_zero.1 hzero).resolve_left <|
    NNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ Measure.haar).ne'
  exact (Measure.haar : Measure G).injective_integratedOperator_leftRegular
    (by simpa only [ofConv_zero, map_zero] using hhaar)

/-- Left translation preserves the full group C⋆-seminorm. -/
@[simp]
theorem fullSeminorm_translateLIE (r : G) (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (translateLIE r f) = fullSeminorm G μ f := by
  have h (t : G) (g : GroupConvolutionAlgebra G μ) :
      fullSeminorm G μ (translateLIE t g) ≤ fullSeminorm G μ g := by
    refine (fullSeminorm_le_iff (apply_nonneg _ _)).2 fun _ _ _ _ _ hU hcont => ?_
    rw [hU.integratedStarAlgHom_translateLIE, CStarRing.norm_mem_unitary_mul _ (hU.mem_unitary t)]
    exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  exact le_antisymm (h r f) (by simpa using h r⁻¹ (translateLIE r f))

/-- Group orbits of compactly supported elements are continuous in the full group C⋆-seminorm. -/
theorem tendsto_fullSeminorm_translateLIE_sub (f : GroupConvolutionAlgebra G μ) (r : G) :
    Tendsto (fun t => fullSeminorm G μ (translateLIE t f - translateLIE r f)) (𝓝 r) (𝓝 0) :=
  squeeze_zero (fun _ => apply_nonneg _ _) (fun _ => fullSeminorm_le_norm _)
    (tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_translateLIE f).tendsto r))

end TauCeti.GroupConvolutionAlgebra

end
