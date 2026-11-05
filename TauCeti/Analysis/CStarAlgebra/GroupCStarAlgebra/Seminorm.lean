/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Translate
public import TauCeti.RepresentationTheory.Continuous.Integrated.CompactlySupported
import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Multiplier
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star

/-!
# Group convolution algebras, integrated unitary representations and the full group C⋆-seminorm

For a locally compact group `G : Type u` and a left Haar measure `μ`, `GroupConvolutionAlgebra G μ`
equips `C_c(G, ℂ)` with convolution `(f * g) s = ∫ r, f r * g (r⁻¹ * s) ∂μ`, the modular-weighted
involution `f⋆ s = c(s) • conj (f s⁻¹)` (`c = Measure.modularCharacter`), and the `L¹(μ)` norm,
realizing the trivial-action specialization of `CStarAction`. Left translation `(r • f) s =
f (r⁻¹ * s)` acts by `L¹` linear isometries with continuous orbits.

Integrating a strongly continuous unitary representation `U : ContRepresentation ℂ G H` yields an
`L¹`-contractive nonunital ⋆-homomorphism `ContRepresentation.IsUnitary.integratedStarAlgHom` on
`GroupConvolutionAlgebra G μ`. Taking `‖f‖ᵤ = sup ‖U(f)‖` over `H : Type u` defines the definite
C⋆-seminorm `GroupConvolutionAlgebra.fullSeminorm G μ` for every left Haar measure `μ`.

## Main definitions

* `TauCeti.GroupConvolutionAlgebra`: the convolution ⋆-algebra on `C_c(G, ℂ)` with its `L¹` norm.
* `TauCeti.GroupConvolutionAlgebra.translateLIE`: left translation as an `L¹` linear isometry.
* `ContRepresentation.IsUnitary.integratedStarAlgHom`: the integrated nonunital ⋆-homomorphism on
  `GroupConvolutionAlgebra G μ`.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm`: the universal group C⋆-seminorm `‖·‖ᵤ`.

## Main statements

* `ContRepresentation.IsUnitary.integratedOperator_mul` and
  `ContRepresentation.IsUnitary.integratedOperator_star`: multiplicativity and ⋆-compatibility.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm_star_mul_self` and
  `TauCeti.GroupConvolutionAlgebra.fullSeminorm_eq_zero_iff`: the C⋆-identity and definiteness.

## References

* Kenneth R. Davidson, *C*-Algebras by Example*, Chapter VII.
* Jacques Dixmier, *C*-Algebras*, §13.9.
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.5, §3.2 and §7.1.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Function
open scoped CompactlySupported Pointwise InnerProductSpace ENNReal

namespace TauCeti

/-- The group convolution ⋆-algebra on `C_c(G, ℂ)` with respect to a measure `μ`, with convolution
as product, the modular-weighted involution as star, and the `L¹(μ)` norm. -/
structure GroupConvolutionAlgebra (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (μ : Measure G) where
  /-- Regard a compactly supported continuous function as a group convolution algebra element. -/
  toConv ::
  /-- Extract the underlying compactly supported continuous function. -/
  ofConv : C_c(G, ℂ)

namespace GroupConvolutionAlgebra

section Basic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}

@[simp] theorem ofConv_toConv (f : C_c(G, ℂ)) :
    (toConv f : GroupConvolutionAlgebra G μ).ofConv = f := (rfl)
@[simp] theorem toConv_ofConv (f : GroupConvolutionAlgebra G μ) : toConv f.ofConv = f := (rfl)

theorem ofConv_injective : Function.Injective (ofConv : GroupConvolutionAlgebra G μ → C_c(G, ℂ)) :=
  fun f _ h => by rw [← toConv_ofConv f, h, toConv_ofConv]
theorem toConv_injective : Function.Injective (toConv : C_c(G, ℂ) → GroupConvolutionAlgebra G μ) :=
  fun f _ h => by rw [← ofConv_toConv (μ := μ) f, h, ofConv_toConv]

@[ext] theorem ext {f g : GroupConvolutionAlgebra G μ} (h : f.ofConv = g.ofConv) : f = g :=
  ofConv_injective h

instance : AddCommGroup (GroupConvolutionAlgebra G μ) :=
  (⟨ofConv, toConv, fun _ => rfl, fun _ => rfl⟩ :
    GroupConvolutionAlgebra G μ ≃ C_c(G, ℂ)).addCommGroup
instance : Module ℂ (GroupConvolutionAlgebra G μ) :=
  (⟨⟨ofConv, toConv, fun _ => rfl, fun _ => rfl⟩, fun _ _ => rfl⟩ :
    GroupConvolutionAlgebra G μ ≃+ C_c(G, ℂ)).module ℂ

@[simp] theorem ofConv_zero : (0 : GroupConvolutionAlgebra G μ).ofConv = 0 := (rfl)
@[simp] theorem ofConv_add (f g : GroupConvolutionAlgebra G μ) :
    (f + g).ofConv = f.ofConv + g.ofConv := (rfl)
@[simp] theorem ofConv_neg (f : GroupConvolutionAlgebra G μ) : (-f).ofConv = -f.ofConv := (rfl)
@[simp] theorem ofConv_sub (f g : GroupConvolutionAlgebra G μ) :
    (f - g).ofConv = f.ofConv - g.ofConv := (rfl)
@[simp] theorem ofConv_smul (c : ℂ) (f : GroupConvolutionAlgebra G μ) :
    (c • f).ofConv = c • f.ofConv := (rfl)
@[simp] theorem toConv_zero : (toConv 0 : GroupConvolutionAlgebra G μ) = 0 := (rfl)
@[simp] theorem toConv_add (f g : C_c(G, ℂ)) :
    (toConv (f + g) : GroupConvolutionAlgebra G μ) = toConv f + toConv g := (rfl)
@[simp] theorem toConv_neg (f : C_c(G, ℂ)) :
    (toConv (-f) : GroupConvolutionAlgebra G μ) = -toConv f := (rfl)
@[simp] theorem toConv_sub (f g : C_c(G, ℂ)) :
    (toConv (f - g) : GroupConvolutionAlgebra G μ) = toConv f - toConv g := (rfl)
@[simp] theorem toConv_smul (c : ℂ) (f : C_c(G, ℂ)) :
    (toConv (c • f) : GroupConvolutionAlgebra G μ) = c • toConv f := (rfl)

end Basic

/-! ### Convolution product and involution -/

section Mul

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-- The convolution integrand `r ↦ f r * g (r⁻¹ * s)` is integrable on `G`. -/
theorem integrable_mul_integrand (f g : C_c(G, ℂ)) (s : G) :
    Integrable (fun r => f r * g (r⁻¹ * s)) μ := by
  simpa using (CStarAction.trivial (G := G) (A := ℂ)).integrable_integrand f g μ s

instance : Mul (GroupConvolutionAlgebra G μ) where
  mul f g := toConv ((CStarAction.trivial (G := G) (A := ℂ)).convolution μ f.ofConv g.ofConv)

theorem ofConv_mul (f g : GroupConvolutionAlgebra G μ) :
    (f * g).ofConv =
      (CStarAction.trivial (G := G) (A := ℂ)).convolution μ f.ofConv g.ofConv := (rfl)
@[simp] theorem ofConv_mul_apply (f g : GroupConvolutionAlgebra G μ) (s : G) :
    (f * g).ofConv s = ∫ r, f.ofConv r * g.ofConv (r⁻¹ * s) ∂μ := by simp [ofConv_mul]

/-- A convolution product is supported in the product of the supports. -/
theorem support_ofConv_mul_subset (f g : GroupConvolutionAlgebra G μ) :
    support (f * g).ofConv ⊆ support f.ofConv * support g.ofConv :=
  (CStarAction.trivial (G := G) (A := ℂ)).support_convolution_subset μ f.ofConv g.ofConv

instance : NonUnitalNonAssocRing (GroupConvolutionAlgebra G μ) where
  left_distrib _ g h := ext (map_add _ g.ofConv h.ofConv)
  right_distrib f g h := ext (LinearMap.map_add₂ _ f.ofConv g.ofConv h.ofConv)
  zero_mul g := ext (LinearMap.map_zero₂ _ g.ofConv)
  mul_zero _ := ext (map_zero _)

instance : IsScalarTower ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ) where
  smul_assoc c f g := ext (LinearMap.map_smul₂ _ c f.ofConv g.ofConv)
instance : SMulCommClass ℂ (GroupConvolutionAlgebra G μ) (GroupConvolutionAlgebra G μ) where
  smul_comm c f g :=
    ext (map_smul ((CStarAction.trivial (G := G) (A := ℂ)).convolution μ f.ofConv) c g.ofConv).symm
instance [MeasurableMul G] [μ.IsMulLeftInvariant] :
    NonUnitalRing (GroupConvolutionAlgebra G μ) where
  mul_assoc f g h :=
    ext ((CStarAction.trivial (G := G) (A := ℂ)).convolution_assoc μ f.ofConv g.ofConv h.ofConv)

end Mul

section Star

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] {μ : Measure G}

instance : Star (GroupConvolutionAlgebra G μ) where
  star f := toConv ((CStarAction.trivial (G := G) (A := ℂ)).twistedInvolution f.ofConv)

theorem ofConv_star (f : GroupConvolutionAlgebra G μ) :
    (star f).ofConv = (CStarAction.trivial (G := G) (A := ℂ)).twistedInvolution f.ofConv := (rfl)
@[simp] theorem ofConv_star_apply (f : GroupConvolutionAlgebra G μ) (s : G) :
    (star f).ofConv s = (Measure.modularCharacter s : ℝ) • star (f.ofConv s⁻¹) := by
  rw [ofConv_star, CStarAction.twistedInvolution_apply, CStarAction.trivial_apply, Complex.coe_smul]

instance : InvolutiveStar (GroupConvolutionAlgebra G μ) where
  star_involutive f :=
    ext ((CStarAction.trivial (G := G) (A := ℂ)).twistedInvolution_twistedInvolution f.ofConv)
instance : StarModule ℂ (GroupConvolutionAlgebra G μ) where
  star_smul c f := ext (map_smulₛₗ _ c f.ofConv)

variable [OpensMeasurableSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant]

instance : StarRing (GroupConvolutionAlgebra G μ) where
  star_mul f g := ext (CStarAction.twistedInvolution_convolution _ μ f.ofConv g.ofConv)
  star_add f g := ext (map_add _ f.ofConv g.ofConv)

end Star

/-! ### The `L¹` norm and left translation -/

section Normed

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-- Realize an element of the group convolution algebra as an `L¹(G, μ)` equivalence class. -/
def toL1 : GroupConvolutionAlgebra G μ →ₗ[ℂ] Lp ℂ 1 μ where
  toFun f := f.ofConv.integrable.toL1 f.ofConv
  map_add' f g := by
    simpa only [ofConv_add, CompactlySupportedContinuousMap.coe_add] using
      Integrable.toL1_add _ _ f.ofConv.integrable g.ofConv.integrable
  map_smul' c f := by
    simpa only [ofConv_smul, CompactlySupportedContinuousMap.coe_smul, RingHom.id_apply] using
      Integrable.toL1_smul' _ f.ofConv.integrable c

/-- A representative of `toL1 f` agrees almost everywhere with `f.ofConv`. -/
theorem coeFn_toL1 (f : GroupConvolutionAlgebra G μ) : toL1 f =ᵐ[μ] f.ofConv :=
  f.ofConv.integrable.coeFn_toL1

instance : SeminormedAddCommGroup (GroupConvolutionAlgebra G μ) :=
  .induced _ _ (toL1 (G := G) (μ := μ)).toAddMonoidHom
instance : NormedSpace ℂ (GroupConvolutionAlgebra G μ) := .induced ℂ _ _ (toL1 (G := G) (μ := μ))

/-- The norm on `GroupConvolutionAlgebra G μ` is the `L¹(μ)` integral norm. -/
theorem norm_eq_integral_norm (f : GroupConvolutionAlgebra G μ) : ‖f‖ = ∫ s, ‖f.ofConv s‖ ∂μ :=
  (L1.norm_eq_integral_norm (toL1 f)).trans (integral_congr_ae ((coeFn_toL1 f).fun_comp norm))
@[simp] theorem norm_toConv (f : C_c(G, ℂ)) :
    ‖(toConv f : GroupConvolutionAlgebra G μ)‖ = ∫ s, ‖f s‖ ∂μ := norm_eq_integral_norm _

variable (G μ) in
/-- The linear isometry from `GroupConvolutionAlgebra G μ` into `L¹(G, μ)`. -/
def toL1LI : GroupConvolutionAlgebra G μ →ₗᵢ[ℂ] Lp ℂ 1 μ := { toL1 with norm_map' _ := (rfl) }
@[simp] theorem toL1LI_apply (f : GroupConvolutionAlgebra G μ) : toL1LI G μ f = toL1 f := (rfl)

instance [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant] :
    NonUnitalSeminormedRing (GroupConvolutionAlgebra G μ) where
  __ : SeminormedAddCommGroup (GroupConvolutionAlgebra G μ) := inferInstance
  __ : NonUnitalRing (GroupConvolutionAlgebra G μ) := inferInstance
  norm_mul_le f g := by
    simp only [norm_eq_integral_norm, ofConv_mul]
    exact (CStarAction.trivial (G := G) (A := ℂ)).integral_norm_convolution_le μ f.ofConv g.ofConv

section OpenPos

variable [μ.IsOpenPosMeasure]

/-- On an open-positive measure, `toL1` is injective. -/
theorem toL1_injective : Function.Injective (toL1 (G := G) (μ := μ)) := fun f g h =>
  ext <| CompactlySupportedContinuousMap.ext fun s => congrFun
    (Measure.eq_of_ae_eq ((coeFn_toL1 f).symm.trans (h ▸ coeFn_toL1 g))
      f.ofConv.continuous g.ofConv.continuous) s

instance : NormedAddCommGroup (GroupConvolutionAlgebra G μ) :=
  .ofSeparation fun f hf => toL1_injective <| by
    rw [map_zero]; exact norm_eq_zero.1 (((toL1LI G μ).norm_map f).trans hf)
instance [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant] :
    NonUnitalNormedRing (GroupConvolutionAlgebra G μ) where
  __ : NonUnitalSeminormedRing (GroupConvolutionAlgebra G μ) := inferInstance
  __ : NormedAddCommGroup (GroupConvolutionAlgebra G μ) := inferInstance

end OpenPos

section StarNorm

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsMulLeftInvariant]

/-- The modular-weighted involution is isometric for the `L¹(μ)` norm. -/
theorem norm_star (f : GroupConvolutionAlgebra G μ) : ‖star f‖ = ‖f‖ := by
  rw [norm_eq_integral_norm, norm_eq_integral_norm, ofConv_star]
  simpa only [CStarAction.ConvolutionAlgebra.norm_eq_integral_norm,
    CStarAction.ConvolutionAlgebra.ofConv_star] using
    CStarAction.ConvolutionAlgebra.norm_star (α := CStarAction.trivial) (μ := μ) ⟨f.ofConv⟩

instance : NormedStarGroup (GroupConvolutionAlgebra G μ) := ⟨fun f => (norm_star f).le⟩

end StarNorm

section Translate

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Left translation `(r • f) s = f (r⁻¹ * s)` as an `L¹` linear isometric equivalence. -/
def translateLIE (r : G) : GroupConvolutionAlgebra G μ ≃ₗᵢ[ℂ] GroupConvolutionAlgebra G μ where
  toFun f := toConv ((CStarAction.trivial (G := G) (A := ℂ)).translate r f.ofConv)
  invFun f := toConv ((CStarAction.trivial (G := G) (A := ℂ)).translate r⁻¹ f.ofConv)
  left_inv f := ext <| by
    rw [ofConv_toConv, ← CStarAction.translate_mul, inv_mul_cancel, CStarAction.translate_one]
  right_inv f := ext <| by
    rw [ofConv_toConv, ← CStarAction.translate_mul, mul_inv_cancel, CStarAction.translate_one]
  map_add' f g := ext (map_add _ f.ofConv g.ofConv)
  map_smul' c f := ext (map_smul _ c f.ofConv)
  norm_map' f := (norm_toConv _).trans <| by
    simp only [CStarAction.translate_apply, CStarAction.trivial_apply, norm_eq_integral_norm]
    exact integral_mul_left_eq_self (μ := μ) (fun s => ‖f.ofConv s‖) r⁻¹

theorem ofConv_translateLIE (r : G) (f : GroupConvolutionAlgebra G μ) :
    (translateLIE r f).ofConv = (CStarAction.trivial (G := G) (A := ℂ)).translate r f.ofConv :=
  (rfl)
@[simp] theorem ofConv_translateLIE_apply (r : G) (f : GroupConvolutionAlgebra G μ) (s : G) :
    (translateLIE r f).ofConv s = f.ofConv (r⁻¹ * s) := by simp [ofConv_translateLIE]
@[simp] theorem ofConv_translateLIE_symm_apply (r : G) (f : GroupConvolutionAlgebra G μ) (s : G) :
    ((translateLIE r).symm f).ofConv s = f.ofConv (r * s) := by
  change ((CStarAction.trivial (G := G) (A := ℂ)).translate r⁻¹ f.ofConv) s = f.ofConv (r * s)
  simp

@[simp] theorem translateLIE_one : translateLIE (G := G) (μ := μ) 1 = 1 := by
  ext f : 1; apply ext; ext s; simp
theorem translateLIE_symm (r : G) :
    (translateLIE (G := G) (μ := μ) r).symm = translateLIE r⁻¹ := by
  ext f : 1; apply ext; ext s; simp
theorem translateLIE_mul (r t : G) :
    translateLIE (G := G) (μ := μ) (r * t) = translateLIE r * translateLIE t := by
  ext f : 1; apply ext; ext s; simp [mul_assoc]

/-- Left translation associates with convolution on the left: `(r • f) * g = r • (f * g)`. -/
theorem translateLIE_apply_mul (r : G) (f g : GroupConvolutionAlgebra G μ) :
    translateLIE r (f * g) = translateLIE r f * g :=
  ext <| by simp [ofConv_mul, ofConv_translateLIE, CStarAction.translate_convolution]

/-- Group orbits of compactly supported functions are continuous in the `L¹` topology. -/
theorem continuous_translateLIE [LocallyCompactSpace G] (f : GroupConvolutionAlgebra G μ) :
    Continuous fun r : G => translateLIE r f := by
  refine continuous_iff_continuousAt.2 fun r₀ => tendsto_iff_norm_sub_tendsto_zero.2 <|
    (tendsto_iff_norm_sub_tendsto_zero.1
      ((CStarAction.ConvolutionAlgebra.continuous_translateLIE
        (α := CStarAction.trivial (G := G) (A := ℂ)) (μ := μ) ⟨f.ofConv⟩).tendsto r₀)).congr
      fun r => ?_
  simp only [norm_eq_integral_norm, CStarAction.ConvolutionAlgebra.norm_eq_integral_norm]
  congr 1 with s; simp

end Translate
end Normed
end GroupConvolutionAlgebra
end TauCeti

/-! ### Integrated ⋆-homomorphisms on the group convolution algebra -/

namespace ContRepresentation.IsUnitary

open TauCeti

section Convolution

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a left-invariant measure, the integrated form turns convolution into composition. -/
@[simp] theorem integratedOperator_mul {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (f g : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (f * g).ofConv =
      hU.integratedOperator hcont μ f.ofConv * hU.integratedOperator hcont μ g.ofConv := by
  rw [GroupConvolutionAlgebra.ofConv_mul, ← hU.integratedOperator_toTrivialCovariant hcont μ,
    CStarAction.CovariantRepresentation.integratedOperator_convolution,
    hU.integratedOperator_toTrivialCovariant, hU.integratedOperator_toTrivialCovariant]

/-- Left translation of `f` corresponds to left multiplication of `U(f)` by `U r`. -/
@[simp] theorem integratedOperator_translateLIE {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (r : G) (f : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (GroupConvolutionAlgebra.translateLIE r f).ofConv =
      U r * hU.integratedOperator hcont μ f.ofConv := by
  rw [GroupConvolutionAlgebra.ofConv_translateLIE,
    ← hU.integratedOperator_toTrivialCovariant hcont μ,
    CStarAction.CovariantRepresentation.integratedOperator_translate,
    toTrivialCovariant_group, hU.integratedOperator_toTrivialCovariant]

end Convolution

section Star

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Against a left Haar measure, the integrated form intertwines the modular-weighted involution
with the Hilbert-space adjoint. -/
@[simp] theorem integratedOperator_star {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (star f).ofConv =
      star (hU.integratedOperator hcont μ f.ofConv) := by
  rw [GroupConvolutionAlgebra.ofConv_star, ← hU.integratedOperator_toTrivialCovariant hcont μ,
    CStarAction.CovariantRepresentation.integratedOperator_twistedInvolution,
    hU.integratedOperator_toTrivialCovariant]

/-- The integrated form of a strongly continuous unitary representation as a nonunital complex
⋆-algebra homomorphism out of `GroupConvolutionAlgebra G μ`. -/
def integratedStarAlgHom {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    GroupConvolutionAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun f := hU.integratedOperator hcont μ f.ofConv
  map_zero' := by simp
  map_add' _ _ := by simp
  map_mul' := hU.integratedOperator_mul hcont μ
  map_smul' _ _ := by simp
  map_star' := hU.integratedOperator_star hcont μ

@[simp] theorem integratedStarAlgHom_apply {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont μ f = hU.integratedOperator hcont μ f.ofConv := (rfl)

/-- Every integrated unitary representation is `L¹`-contractive. -/
theorem norm_integratedStarAlgHom_le_norm {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) : ‖hU.integratedStarAlgHom hcont μ f‖ ≤ ‖f‖ := by
  simpa only [integratedStarAlgHom_apply, GroupConvolutionAlgebra.norm_eq_integral_norm] using
    hU.norm_integratedOperator_le hcont μ f.ofConv

theorem integratedStarAlgHom_translateLIE {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (r : G) (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont μ (GroupConvolutionAlgebra.translateLIE r f) =
      U r * hU.integratedStarAlgHom hcont μ f :=
  hU.integratedOperator_translateLIE hcont μ r f

end Star

section CommGroup

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Over a commutative group, the integrated ⋆-homomorphism has commuting values. -/
theorem integratedStarAlgHom_commute {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f g : GroupConvolutionAlgebra G μ) :
    Commute (hU.integratedStarAlgHom hcont μ f) (hU.integratedStarAlgHom hcont μ g) :=
  hU.integratedOperator_commute hcont μ f.ofConv g.ofConv

end CommGroup
end ContRepresentation.IsUnitary

/-! ### The universal group C⋆-seminorm -/

namespace TauCeti.GroupConvolutionAlgebra

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

variable (G μ) in
private def integratedSeminorms : Set (Seminorm ℂ (GroupConvolutionAlgebra G μ)) :=
  {p | ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v),
      p = (normSeminorm ℂ (H →L[ℂ] H)).comp
        (hU.integratedStarAlgHom hcont μ : GroupConvolutionAlgebra G μ →ₗ[ℂ] (H →L[ℂ] H))}

private theorem bddAbove_integratedSeminorms : BddAbove (integratedSeminorms G μ) :=
  ⟨normSeminorm ℂ _, fun _ ⟨_, _, _, _, _, hU, hcont, hp⟩ f =>
    hp ▸ hU.norm_integratedStarAlgHom_le_norm hcont μ f⟩

variable (G μ) in
/-- The universal (or full) group C⋆-seminorm `‖f‖ᵤ = sup ‖U(f)‖` on `GroupConvolutionAlgebra G μ`,
ranging over strongly continuous unitary representations of `G` on Hilbert spaces in `Type u`. -/
def fullSeminorm : Seminorm ℂ (GroupConvolutionAlgebra G μ) := sSup (integratedSeminorms G μ)

/-- Pointwise formula for `fullSeminorm` as the supremum of integrated operator norms. -/
theorem fullSeminorm_apply (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ f =
      sSup {r | ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v), ‖hU.integratedStarAlgHom hcont μ f‖ = r} := by
  rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms, iSup]
  congr 1; ext r; simp [integratedSeminorms]

/-- Every integrated unitary representation on `H : Type u` is bounded by `fullSeminorm`. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (f : GroupConvolutionAlgebra G μ) :
    ‖hU.integratedStarAlgHom hcont μ f‖ ≤ fullSeminorm G μ f :=
  le_csSup bddAbove_integratedSeminorms
    ⟨H, inferInstance, inferInstance, inferInstance, U, hU, hcont, rfl⟩ f

/-- `fullSeminorm G μ f` is the least nonnegative upper bound for all integrated operator norms. -/
theorem fullSeminorm_le_iff {f : GroupConvolutionAlgebra G μ} {c : ℝ} (hc : 0 ≤ c) :
    fullSeminorm G μ f ≤ c ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v), ‖hU.integratedStarAlgHom hcont μ f‖ ≤ c :=
  ⟨fun h _ _ _ _ _ hU hcont => (norm_integratedStarAlgHom_le_fullSeminorm hU hcont f).trans h,
    fun h => by
      rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms]
      exact Real.iSup_le (fun ⟨_, H, _, _, _, U, hU, hcont, hp⟩ => hp ▸ h H U hU hcont) hc⟩

/-- The full group C⋆-seminorm is dominated by the `L¹(μ)` norm. -/
theorem fullSeminorm_le_norm (f : GroupConvolutionAlgebra G μ) : fullSeminorm G μ f ≤ ‖f‖ :=
  (fullSeminorm_le_iff (norm_nonneg f)).2 fun _ _ _ _ _ hU hcont =>
    hU.norm_integratedStarAlgHom_le_norm hcont μ f

/-- The full group C⋆-seminorm is submultiplicative for convolution. -/
theorem fullSeminorm_mul_le (f g : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (f * g) ≤ fullSeminorm G μ f * fullSeminorm G μ g :=
  (fullSeminorm_le_iff (mul_nonneg (apply_nonneg _ f) (apply_nonneg _ g))).2
    fun _ _ _ _ _ hU hcont => by
      rw [map_mul]
      exact (norm_mul_le _ _).trans <|
        mul_le_mul (norm_integratedStarAlgHom_le_fullSeminorm hU hcont f)
          (norm_integratedStarAlgHom_le_fullSeminorm hU hcont g) (norm_nonneg _) (apply_nonneg _ f)

/-- The full group C⋆-seminorm is invariant under the modular-weighted involution. -/
@[simp] theorem fullSeminorm_star (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (star f) = fullSeminorm G μ f := by
  have key (g : GroupConvolutionAlgebra G μ) : fullSeminorm G μ (star g) ≤ fullSeminorm G μ g :=
    (fullSeminorm_le_iff (apply_nonneg _ g)).2 fun _ _ _ _ _ hU hcont => by
      rw [map_star, _root_.norm_star]; exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  exact le_antisymm (key f) (by simpa using key (star f))

/-- The full group C⋆-seminorm satisfies the C⋆-identity `‖f⋆ * f‖ᵤ = ‖f‖ᵤ²`. -/
theorem fullSeminorm_star_mul_self (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (star f * f) = fullSeminorm G μ f * fullSeminorm G μ f := by
  refine le_antisymm ((fullSeminorm_mul_le _ _).trans_eq (by rw [fullSeminorm_star])) ?_
  have hsqrt : fullSeminorm G μ f ≤ √(fullSeminorm G μ (star f * f)) :=
    (fullSeminorm_le_iff (Real.sqrt_nonneg _)).2 fun _ _ _ _ _ hU hcont =>
      Real.le_sqrt_of_sq_le <| by
        rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
        exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont _
  exact (mul_le_mul hsqrt hsqrt (apply_nonneg _ f) (Real.sqrt_nonneg _)).trans_eq
    (Real.mul_self_sqrt (apply_nonneg _ _))

/-- The full group C⋆-seminorm is definite for every left Haar measure `μ` (without regularity
assumptions on `μ`, via comparison with `Measure.haar` and the left regular representation). -/
@[simp] theorem fullSeminorm_eq_zero_iff {f : GroupConvolutionAlgebra G μ} :
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
@[simp] theorem fullSeminorm_translateLIE (r : G) (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (translateLIE r f) = fullSeminorm G μ f := by
  have h (t : G) (g : GroupConvolutionAlgebra G μ) :
      fullSeminorm G μ (translateLIE t g) ≤ fullSeminorm G μ g :=
    (fullSeminorm_le_iff (apply_nonneg _ _)).2 fun _ _ _ _ _ hU hcont => by
      rw [hU.integratedStarAlgHom_translateLIE, CStarRing.norm_mem_unitary_mul _ (hU.mem_unitary t)]
      exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  have hinv : translateLIE r⁻¹ (translateLIE r f) = f := by apply ext; ext s; simp
  refine le_antisymm (h r f) ?_
  conv_lhs => rw [← hinv]
  exact h r⁻¹ (translateLIE r f)

end TauCeti.GroupConvolutionAlgebra

end
