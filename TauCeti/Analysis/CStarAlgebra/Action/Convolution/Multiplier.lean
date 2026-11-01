/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Translate

/-!
# Bounds for the canonical convolution multipliers

The coefficient algebra and the group act on compactly supported convolution coefficients by
`(i_A(a) f)(s) = a * f(s)` and `(i_G(r) f)(s) = α r (f (r⁻¹ * s))`.
Here these operators are bundled for the L¹ norm. The coefficient operator has bound `‖a‖`,
and the group operator is an isometry with L¹-continuous orbits. The multiplication and covariance
formulas are included on the dense convolution algebra. These are the bounded left actions used
in constructing the canonical multipliers on crossed-product completions.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for the canonical coefficient
and group multipliers.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped CompactlySupported

namespace TauCeti.CStarAction.ConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} {μ : Measure G}

section FiniteMeasure

variable [IsFiniteMeasureOnCompacts μ]

/-- Left multiplication by a coefficient `a` multiplies the L¹ norm by at most `‖a‖`. -/
private theorem norm_toConv_smul_le (a : A) (f : ConvolutionAlgebra α μ) :
    ‖(toConv (a • f.ofConv) : ConvolutionAlgebra α μ)‖ ≤ ‖a‖ * ‖f‖ := by
  simp only [norm_eq_integral_norm, ← integral_const_mul]
  exact integral_mono (a • f.ofConv).integrable.norm (f.ofConv.integrable.norm.const_mul _)
    fun s => norm_mul_le a (f.ofConv s)

/-- The canonical left coefficient multiplier, as a bounded operator for the L¹ norm. -/
def coefficientMul (a : A) : ConvolutionAlgebra α μ →L[ℂ] ConvolutionAlgebra α μ :=
  LinearMap.mkContinuous
    { toFun := fun f => toConv (a • f.ofConv)
      map_add' := fun f g => by ext s; simp [mul_add]
      map_smul' := fun c f => by ext s; simp [mul_smul_comm] }
    ‖a‖ (norm_toConv_smul_le a)

@[simp]
theorem ofConv_coefficientMul (a : A) (f : ConvolutionAlgebra α μ) :
    (coefficientMul a f).ofConv = a • f.ofConv :=
  (rfl)

/-- The L¹ operator norm of a coefficient multiplier is at most the coefficient norm. -/
theorem norm_coefficientMul_le (a : A) : ‖coefficientMul (α := α) (μ := μ) a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _

@[simp]
theorem coefficientMul_zero : coefficientMul (α := α) (μ := μ) 0 = 0 := by
  ext f s
  simp

@[simp]
theorem coefficientMul_add (a b : A) : coefficientMul (α := α) (μ := μ) (a + b) =
    coefficientMul a + coefficientMul b := by
  ext f s
  simp [add_mul]

@[simp]
theorem coefficientMul_smul (c : ℂ) (a : A) : coefficientMul (α := α) (μ := μ) (c • a) =
    c • coefficientMul a := by
  ext f s
  simp [smul_mul_assoc]

/-- The canonical coefficient multipliers respect multiplication in the coefficient algebra. -/
@[simp]
theorem coefficientMul_mul (a b : A) : coefficientMul (α := α) (μ := μ) (a * b) =
    coefficientMul a * coefficientMul b := by
  ext f s
  simp [mul_assoc]

variable [IsTopologicalGroup G]

/-- A coefficient multiplier is a left multiplier of the convolution algebra. -/
theorem coefficientMul_apply_mul (a : A) (f g : ConvolutionAlgebra α μ) :
    coefficientMul a (f * g) = coefficientMul a f * g := by
  apply ext
  simp [α.smul_convolution]

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The twisted left translation, as a linear isometric equivalence for the L¹ norm. -/
def translateLIE (r : G) : ConvolutionAlgebra α μ ≃ₗᵢ[ℂ] ConvolutionAlgebra α μ where
  toFun f := toConv (α.translate r f.ofConv)
  invFun f := toConv (α.translate r⁻¹ f.ofConv)
  left_inv f := by simp [← α.translate_mul]
  right_inv f := by simp [← α.translate_mul]
  map_add' f g := by simp
  map_smul' c f := by simp
  norm_map' f := (norm_toConv (α.translate r f.ofConv)).trans <| by
    simp only [translate_apply, StarAlgEquiv.norm_map, norm_eq_integral_norm]
    exact integral_mul_left_eq_self (μ := μ) (fun s => ‖f.ofConv s‖) r⁻¹

@[simp]
theorem ofConv_translateLIE (r : G) (f : ConvolutionAlgebra α μ) :
    (translateLIE r f).ofConv = α.translate r f.ofConv :=
  (rfl)

@[simp]
theorem ofConv_translateLIE_symm (r : G) (f : ConvolutionAlgebra α μ) :
    ((translateLIE r).symm f).ofConv = α.translate r⁻¹ f.ofConv :=
  (rfl)

@[simp]
theorem translateLIE_one : translateLIE (α := α) (μ := μ) 1 = 1 := by
  ext f s
  simp

theorem translateLIE_symm (r : G) :
    (translateLIE (α := α) (μ := μ) r).symm = translateLIE r⁻¹ := by
  -- Both equivalences have the inverse translation as their forward map.
  ext f s
  rfl

@[simp]
theorem translateLIE_inv_translateLIE (r : G) (f : ConvolutionAlgebra α μ) :
    translateLIE r⁻¹ (translateLIE r f) = f := by
  rw [← translateLIE_symm]
  exact LinearIsometryEquiv.symm_apply_apply _ _

@[simp]
theorem translateLIE_translateLIE_inv (r : G) (f : ConvolutionAlgebra α μ) :
    translateLIE r (translateLIE r⁻¹ f) = f := by
  rw [← translateLIE_symm]
  exact LinearIsometryEquiv.apply_symm_apply _ _

/-- The canonical group multipliers form a left action. -/
theorem translateLIE_mul (r t : G) : translateLIE (α := α) (μ := μ) (r * t) =
    translateLIE r * translateLIE t := by
  ext f s
  simp [α.translate_mul]

/-- A group multiplier is a left multiplier of the convolution algebra. -/
theorem translateLIE_apply_mul (r : G) (f g : ConvolutionAlgebra α μ) :
    translateLIE r (f * g) = translateLIE r f * g := by
  apply ext
  simp [α.translate_convolution]

/-- The coefficient and group multipliers satisfy covariance. -/
theorem translateLIE_coefficientMul (r : G) (a : A) (f : ConvolutionAlgebra α μ) :
    translateLIE r (coefficientMul a f) = coefficientMul (α r a) (translateLIE r f) := by
  ext s
  simp [map_mul]

variable [LocallyCompactSpace G]

/-- Group orbits of compact-support coefficients are continuous in L¹, with no separability
or global σ-finiteness hypothesis. -/
theorem continuous_translateLIE (f : ConvolutionAlgebra α μ) :
    Continuous fun r : G => translateLIE r f := by
  rw [continuous_iff_continuousAt]
  intro r
  obtain ⟨K, hK, hrK⟩ := exists_compact_mem_nhds r
  have hcont : ContinuousOn (fun t : G => ‖translateLIE t f - translateLIE r f‖) K := by
    simp only [norm_eq_integral_norm, ofConv_sub, ofConv_translateLIE,
      CompactlySupportedContinuousMap.sub_apply, translate_apply]
    refine continuousOn_integral_of_compact_support (hK.mul f.ofConv.hasCompactSupport)
      ?_ ?_
    · exact ((α.continuous_apply continuous_fst
        (f.ofConv.continuous.comp (continuous_fst.inv.mul continuous_snd))).sub
          (α.continuous_apply (continuous_const (y := r)) (f.ofConv.continuous.comp
            ((continuous_const (y := r⁻¹)).mul continuous_snd)))).norm.continuousOn
    · intro t s ht hs
      have hzero (u : G) (hu : u ∈ K) : f.ofConv (u⁻¹ * s) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hs ⟨u, hu, u⁻¹ * s, hmem, by simp⟩
      simp [hzero t ht, hzero r (mem_of_mem_nhds hrK)]
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (by simpa using (hcont.continuousAt hrK).tendsto)

end FiniteMeasure

end TauCeti.CStarAction.ConvolutionAlgebra
