/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.FullSeminorm

/-!
# Bounds for the canonical convolution multipliers

The coefficient algebra and the group act on compactly supported convolution coefficients by
`(i_A(a) f)(s) = a * f(s)` and `(i_G(r) f)(s) = α r (f (r⁻¹ * s))`.
Here these operators are bundled for the L¹ norm, and their bounds for the universal C⋆-seminorm
are proved. The coefficient operator has bound `‖a‖`, and the group operator is an isometry for
both norms. The group orbits are L¹-continuous, hence also continuous for the universal seminorm.
These estimates allow the canonical left multipliers to extend to the crossed-product
completion; no faithful coefficient representation is needed for the estimates.

The multiplication and covariance formulas are included on the dense convolution algebra.
The universal bounds use the existing vector-integrated formulas
`CovariantRepresentation.integratedOperator_smul` and
`CovariantRepresentation.integratedOperator_translate`, not operator-valued Bochner integration.

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

/-- Left multiplication by a coefficient decreases the L¹ norm by at most its norm. -/
theorem norm_toConv_smul_le (a : A) (f : ConvolutionAlgebra α μ) :
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
theorem norm_coefficientMul_le (a : A) : ‖coefficientMul (α := α) (μ := μ) a‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun f => ?_
  simpa only [← ofConv_coefficientMul, toConv_ofConv] using norm_toConv_smul_le a f

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
theorem coefficientMul_mul_apply (a : A) (f g : ConvolutionAlgebra α μ) :
    coefficientMul a (f * g) = coefficientMul a f * g := by
  apply ext
  simp [α.smul_convolution]

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The twisted left translation, as a linear isometric equivalence for the L¹ norm. -/
def translateLI (r : G) : ConvolutionAlgebra α μ ≃ₗᵢ[ℂ] ConvolutionAlgebra α μ where
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
theorem ofConv_translateLI (r : G) (f : ConvolutionAlgebra α μ) :
    (translateLI r f).ofConv = α.translate r f.ofConv :=
  (rfl)

@[simp]
theorem translateLI_one (f : ConvolutionAlgebra α μ) : translateLI 1 f = f := by
  apply ext
  simp

theorem translateLI_symm (r : G) : (translateLI (α := α) (μ := μ) r).symm = translateLI r⁻¹ := by
  -- Both equivalences have the inverse translation as their forward map.
  ext f s
  rfl

/-- The canonical group multipliers form a left action. -/
theorem translateLI_mul (r t : G) (f : ConvolutionAlgebra α μ) :
    translateLI (r * t) f = translateLI r (translateLI t f) := by
  apply ext
  simp [α.translate_mul]

/-- A group multiplier is a left multiplier of the convolution algebra. -/
theorem translateLI_mul_apply (r : G) (f g : ConvolutionAlgebra α μ) :
    translateLI r (f * g) = translateLI r f * g := by
  apply ext
  simp [α.translate_convolution]

/-- The coefficient and group multipliers satisfy covariance. -/
theorem translateLI_coefficientMul (r : G) (a : A) (f : ConvolutionAlgebra α μ) :
    translateLI r (coefficientMul a f) = coefficientMul (α r a) (translateLI r f) := by
  ext s
  simp [map_mul]

variable [LocallyCompactSpace G]

/-- Group orbits of compact-support coefficients are continuous in L¹, with no separability
or global σ-finiteness hypothesis. -/
theorem continuous_translateLI (f : ConvolutionAlgebra α μ) :
    Continuous fun r : G => translateLI r f := by
  rw [continuous_iff_continuousAt]
  intro r
  obtain ⟨K, hK, hrK⟩ := exists_compact_mem_nhds r
  have hcont : ContinuousOn (fun t : G => ‖translateLI t f - translateLI r f‖) K := by
    simp only [norm_eq_integral_norm, ofConv_sub, ofConv_translateLI,
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

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

/-- The canonical coefficient multiplier has bound `‖a‖` for the full C⋆-seminorm. -/
theorem fullSeminorm_coefficientMul_le (a : A) (f : ConvolutionAlgebra α μ) :
    fullSeminorm α μ (coefficientMul a f) ≤ ‖a‖ * fullSeminorm α μ f := by
  refine (fullSeminorm_le_iff (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2
    fun H _ _ _ P => ?_
  rw [CovariantRepresentation.integratedStarAlgHom_apply, ofConv_coefficientMul,
    P.integratedOperator_smul, ← P.integratedStarAlgHom_apply]
  exact (norm_mul_le _ _).trans (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le _ _)
    (norm_integratedStarAlgHom_le_fullSeminorm P f) (norm_nonneg _) (norm_nonneg _))

/-- Twisted left translation preserves the full C⋆-seminorm. -/
@[simp]
theorem fullSeminorm_translateLI (r : G) (f : ConvolutionAlgebra α μ) :
    fullSeminorm α μ (translateLI r f) = fullSeminorm α μ f := by
  have h (t : G) (g : ConvolutionAlgebra α μ) :
      fullSeminorm α μ (translateLI t g) ≤ fullSeminorm α μ g := by
    refine (fullSeminorm_le_iff (apply_nonneg _ _)).2 fun H _ _ _ P => ?_
    rw [CovariantRepresentation.integratedStarAlgHom_apply, ofConv_translateLI,
      P.integratedOperator_translate]
    calc ‖P.group t * P.integratedOperator μ g.ofConv‖
        ≤ 1 * ‖P.integratedOperator μ g.ofConv‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (P.isUnitary.norm_le_one t) (norm_nonneg _))
      _ ≤ fullSeminorm α μ g := by
        simpa using norm_integratedStarAlgHom_le_fullSeminorm P g
  exact le_antisymm (h r f) (by simpa [← translateLI_mul] using h r⁻¹ (translateLI r f))

/-- The group orbits are also continuous for the full C⋆-seminorm. This is the dense-algebra
continuity estimate needed for strict continuity of the canonical group multipliers. -/
theorem tendsto_fullSeminorm_translateLI_sub (f : ConvolutionAlgebra α μ) (r : G) :
    Tendsto (fun t => fullSeminorm α μ (translateLI t f - translateLI r f)) (𝓝 r) (𝓝 0) := by
  exact squeeze_zero (fun _ => apply_nonneg _ _) (fun _ => fullSeminorm_le_norm _)
    (by simpa using ((continuous_translateLI f).sub
      (continuous_const (y := translateLI r f))).norm.tendsto r)

end TauCeti.CStarAction.ConvolutionAlgebra
