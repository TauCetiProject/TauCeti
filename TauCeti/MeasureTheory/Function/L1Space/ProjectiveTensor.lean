/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.Integral.SetToL1.L1
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Bochner `L¹` as a completed projective tensor product

For an arbitrary measure `μ` and a Banach space `X` over `𝕜 = ℝ` or `ℂ`, the bounded bilinear map
`(φ, x) ↦ [s ↦ φ s • x]` from `L¹(μ) × X` to the Bochner space `L¹(μ; X)` extends to a linear
isometric equivalence

`L¹(μ) ⊗̂π X ≃ₗᵢ L¹(μ; X)`

between the completed projective tensor product and Bochner `L¹`. Thus every Bochner-integrable
function is represented by a projective tensor, with the Bochner `L¹` norm equal to the projective
norm, and bounded bilinear maps on `L¹(μ) × X` act on `L¹(μ; X)`.

## Main declarations

* `TauCeti.lpOneTensorEquiv`: the linear isometric equivalence
  `CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X ≃ₗᵢ[𝕜] Lp X 1 μ`.
* `TauCeti.lpOneTensorEquiv_coe_tmul` and `TauCeti.coeFn_lpOneTensorEquiv_coe_tmul`: it sends
  `φ ⊗ x` to the class of `s ↦ φ s • x`.
* `TauCeti.lpOneTensorEquiv_symm_indicatorConstLp`: its inverse sends `𝟙_A x` to `𝟙_A ⊗ x`.
* `TauCeti.lpOneTensorEquiv_mapL_id` and `TauCeti.lpOneTensorEquiv_mapL_compMeasurePreserving`:
  naturality under bounded operators of the target and measure-preserving pullbacks.

## Implementation notes

The map is a contraction by the universal property of the completed projective tensor product,
`TauCeti.CompletedProjectiveTensor.liftIsometry`. For the reverse inequality, a bounded functional
`ℓ` on `L¹(μ) ⊗̂π X` gives the set function `A ↦ (x ↦ ℓ (𝟙_A ⊗ x))`, dominated by `‖ℓ‖ μ A`;
Mathlib's extension of dominated set functions, `MeasureTheory.L1.setToL1'`, turns it into a
functional on `L¹(μ; X)` of norm at most `‖ℓ‖` that recovers `ℓ`, and the Hahn–Banach theorem
bounds the projective norm by the Bochner norm. Surjectivity follows from density of the simple
functions in `L¹(μ; X)`.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Example 2.19.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal TensorProduct

namespace TauCeti

variable {𝕜 S S' X Y : Type*} [RCLike 𝕜] [MeasurableSpace S] [MeasurableSpace S']
  {μ : Measure S} {μ' : Measure S'}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A pure tensor whose `L¹` factor is an indicator `𝟙_A c` equals `𝟙_A ⊗ (c • x)`. -/
private theorem tmul_indicatorConstLp {A : Set S} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (c : 𝕜) (x : X) :
    CompletedProjectiveTensor.tmulL (𝕜 := 𝕜) (indicatorConstLp 1 hA hμA c) x =
      CompletedProjectiveTensor.tmulL (𝕜 := 𝕜) (indicatorConstLp 1 hA hμA (1 : 𝕜)) (c • x) := by
  have : indicatorConstLp 1 hA hμA c = c • indicatorConstLp 1 hA hμA (1 : 𝕜) := by
    rw [← indicatorConstLp_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_apply, map_smul]

section SetFunction

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

open Classical in
/-- The set function `A ↦ (x ↦ ℓ (𝟙_A ⊗ x))` attached to a functional `ℓ` on `L¹(μ) ⊗̂π X`, set
to zero on sets that are not measurable of finite measure. -/
private def tensorSetFunction (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X))
    (A : Set S) : X →L[ℝ] 𝕜 :=
  if h : MeasurableSet A ∧ μ A ≠ ∞ then
    (ℓ ∘L CompletedProjectiveTensor.tmulL (indicatorConstLp 1 h.1 h.2 (1 : 𝕜))).restrictScalars ℝ
  else 0

private theorem tensorSetFunction_apply
    (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X)) {A : Set S}
    (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (x : X) :
    tensorSetFunction ℓ A x =
      ℓ (CompletedProjectiveTensor.tmulL (indicatorConstLp 1 hA hμA (1 : 𝕜)) x) := by
  simp [tensorSetFunction, hA, hμA]

private theorem tensorSetFunction_smul
    (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X)) (c : 𝕜) (A : Set S) (x : X) :
    tensorSetFunction ℓ A (c • x) = c • tensorSetFunction ℓ A x := by
  by_cases h : MeasurableSet A ∧ μ A ≠ ∞
  · simp [tensorSetFunction_apply ℓ h.1 h.2]
  · simp [tensorSetFunction, h]

private theorem dominatedFinMeasAdditive_tensorSetFunction
    (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X)) :
    DominatedFinMeasAdditive μ (tensorSetFunction ℓ) ‖ℓ‖ := by
  refine ⟨fun A B hA hB hμA hμB hAB ↦ ?_, fun A hA hμA ↦ ?_⟩
  · ext x
    have hμAB : μ (A ∪ B) ≠ ∞ := (measure_union_lt_top hμA.lt_top hμB.lt_top).ne
    simp only [add_apply, tensorSetFunction_apply ℓ (hA.union hB) hμAB,
      tensorSetFunction_apply ℓ hA hμA, tensorSetFunction_apply ℓ hB hμB,
      indicatorConstLp_disjoint_union hA hB hμA hμB hAB, map_add]
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
    rw [tensorSetFunction_apply ℓ hA hμA.ne]
    calc ‖ℓ (CompletedProjectiveTensor.tmulL (indicatorConstLp 1 hA hμA.ne (1 : 𝕜)) x)‖
        ≤ ‖ℓ‖ * (‖indicatorConstLp 1 hA hμA.ne (1 : 𝕜)‖ * ‖x‖) := by
          rw [CompletedProjectiveTensor.tmulL_apply]
          exact ℓ.le_opNorm_of_le (CompletedProjectiveTensor.norm_coe_tmul_le _ _)
      _ = ‖ℓ‖ * μ.real A * ‖x‖ := by
          rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
          simp [mul_assoc]

/-- The functional on `L¹(μ; X)` induced by a functional `ℓ` on `L¹(μ) ⊗̂π X`: the extension of
the set function `A ↦ (x ↦ ℓ (𝟙_A ⊗ x))`. -/
private def tensorFunctional (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X)) :
    StrongDual 𝕜 (Lp X 1 μ) :=
  L1.setToL1' 𝕜 (dominatedFinMeasAdditive_tensorSetFunction ℓ) (tensorSetFunction_smul ℓ)

private theorem norm_tensorFunctional_apply_le
    (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X)) (f : Lp X 1 μ) :
    ‖tensorFunctional ℓ f‖ ≤ ‖ℓ‖ * ‖f‖ := by
  rw [tensorFunctional, ← L1.setToL1_eq_setToL1']
  exact L1.norm_setToL1_le_mul_norm _ (norm_nonneg ℓ) f

private theorem tensorFunctional_indicatorConstLp
    (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X)) {A : Set S}
    (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (x : X) :
    tensorFunctional ℓ (indicatorConstLp 1 hA hμA x) =
      ℓ (CompletedProjectiveTensor.tmulL (indicatorConstLp 1 hA hμA (1 : 𝕜)) x) := by
  rw [tensorFunctional, ← L1.setToL1_eq_setToL1', L1.setToL1_indicatorConstLp,
    tensorSetFunction_apply]

end SetFunction

variable [CompleteSpace X] [CompleteSpace Y]

variable (𝕜 X μ) in
/-- The contraction `L¹(μ) ⊗̂π X → L¹(μ; X)` sending `φ ⊗ x` to the class of `s ↦ φ s • x`. -/
private def lpOneTensorL : CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X →L[𝕜] Lp X 1 μ :=
  CompletedProjectiveTensor.liftIsometry 𝕜 _ _ _
    (ContinuousLinearMap.compLpL₂ 1 μ (ContinuousLinearMap.lsmul 𝕜 𝕜).flip).flip

private theorem lpOneTensorL_coe_tmul (φ : Lp 𝕜 1 μ) (x : X) :
    lpOneTensorL 𝕜 X μ (⟨φ ⊗ₜ x⟩ : ProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) =
      (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp φ := by
  simp only [lpOneTensorL, CompletedProjectiveTensor.liftIsometry_coe,
    ProjectiveTensor.liftIsometry_apply_tmul, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compLpL₂_apply_apply, ContinuousLinearMap.lsmul_flip_apply]

private theorem lpOneTensorL_tmulL_indicatorConstLp {A : Set S} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (x : X) :
    lpOneTensorL 𝕜 X μ (CompletedProjectiveTensor.tmulL (indicatorConstLp 1 hA hμA (1 : 𝕜)) x) =
      indicatorConstLp 1 hA hμA x := by
  rw [CompletedProjectiveTensor.tmulL_apply, lpOneTensorL_coe_tmul,
    ContinuousLinearMap.compLp_indicatorConstLp, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul]

private theorem norm_lpOneTensorL_le (u : CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) :
    ‖lpOneTensorL 𝕜 X μ u‖ ≤ ‖u‖ := by
  refine ((lpOneTensorL 𝕜 X μ).le_of_opNorm_le ?_ u).trans_eq (one_mul _)
  rw [lpOneTensorL, LinearIsometryEquiv.norm_map, ContinuousLinearMap.opNorm_flip]
  exact (ContinuousLinearMap.norm_compLpL₂_le _).trans <|
    (ContinuousLinearMap.opNorm_flip _).trans_le ContinuousLinearMap.opNorm_lsmul_le

private theorem surjective_lpOneTensorL (h : Isometry (lpOneTensorL 𝕜 X μ)) :
    Function.Surjective (lpOneTensorL 𝕜 X μ) := by
  intro f
  induction f using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c hA hμA =>
    exact ⟨_, (lpOneTensorL_tmulL_indicatorConstLp hA hμA.ne c).trans
      (Lp.simpleFunc.coe_indicatorConst hA hμA.ne c).symm⟩
  | add _ _ _ hf hg =>
    obtain ⟨u, hu⟩ := hf
    obtain ⟨v, hv⟩ := hg
    exact ⟨u + v, by rw [map_add, hu, hv]⟩
  | isClosed => exact h.isClosedEmbedding.isClosed_range

section Isometry

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

private theorem tensorFunctional_lpOneTensorL
    (ℓ : StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X))
    (u : CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) :
    tensorFunctional ℓ (lpOneTensorL 𝕜 X μ u) = ℓ u := by
  suffices tensorFunctional ℓ ∘L lpOneTensorL 𝕜 X μ = ℓ from congr($this u)
  refine CompletedProjectiveTensor.continuousLinearMap_ext fun φ x ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ← CompletedProjectiveTensor.tmulL_apply]
  induction φ using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c hA hμA =>
    rw [Lp.simpleFunc.coe_indicatorConst, tmul_indicatorConstLp,
      lpOneTensorL_tmulL_indicatorConstLp, tensorFunctional_indicatorConstLp]
  | add _ _ _ hf hg => simp only [map_add, add_apply, hf, hg]
  | isClosed => exact isClosed_eq (by fun_prop) (by fun_prop)

private theorem norm_lpOneTensorL (u : CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) :
    ‖lpOneTensorL 𝕜 X μ u‖ = ‖u‖ := by
  refine le_antisymm (norm_lpOneTensorL_le u) <|
    NormedSpace.norm_le_dual_bound 𝕜 u (norm_nonneg _) fun ℓ ↦ ?_
  rw [← tensorFunctional_lpOneTensorL ℓ u, mul_comm]
  exact norm_tensorFunctional_apply_le ℓ _

variable (𝕜 X μ) in
/-- **Bochner `L¹` is a completed projective tensor product.** For an arbitrary measure `μ` and a
Banach space `X`, the map `φ ⊗ x ↦ [s ↦ φ s • x]` extends to a linear isometric equivalence
`L¹(μ) ⊗̂π X ≃ₗᵢ L¹(μ; X)`. -/
def lpOneTensorEquiv : CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X ≃ₗᵢ[𝕜] Lp X 1 μ :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (lpOneTensorL 𝕜 X μ).toLinearMap
      norm_map' := norm_lpOneTensorL }
    (surjective_lpOneTensorL <| AddMonoidHomClass.isometry_of_norm _ norm_lpOneTensorL)

/-- The isometry `L¹(μ) ⊗̂π X ≃ L¹(μ; X)` sends `φ ⊗ x` to the class of `s ↦ φ s • x`, written as
the composition of `φ` with `c ↦ c • x`. -/
@[simp]
theorem lpOneTensorEquiv_coe_tmul (φ : Lp 𝕜 1 μ) (x : X) :
    lpOneTensorEquiv 𝕜 X μ (⟨φ ⊗ₜ x⟩ : ProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) =
      (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp φ :=
  lpOneTensorL_coe_tmul φ x

/-- The isometry `L¹(μ) ⊗̂π X ≃ L¹(μ; X)` sends `φ ⊗ x` to the class of `s ↦ φ s • x`. -/
theorem coeFn_lpOneTensorEquiv_coe_tmul (φ : Lp 𝕜 1 μ) (x : X) :
    lpOneTensorEquiv 𝕜 X μ (⟨φ ⊗ₜ x⟩ : ProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) =ᵐ[μ]
      fun s ↦ φ s • x := by
  rw [lpOneTensorEquiv_coe_tmul]
  filter_upwards [ContinuousLinearMap.coeFn_compLp (ContinuousLinearMap.toSpanSingleton 𝕜 x) φ]
    with s hs
  rw [hs, ContinuousLinearMap.toSpanSingleton_apply]

/-- The isometry `L¹(μ) ⊗̂π X ≃ L¹(μ; X)` sends `𝟙_A c ⊗ x` to `𝟙_A (c • x)`. -/
theorem lpOneTensorEquiv_coe_tmul_indicatorConstLp {A : Set S} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : 𝕜) (x : X) :
    lpOneTensorEquiv 𝕜 X μ
        (⟨indicatorConstLp 1 hA hμA c ⊗ₜ x⟩ : ProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) =
      indicatorConstLp 1 hA hμA (c • x) := by
  rw [lpOneTensorEquiv_coe_tmul, ContinuousLinearMap.compLp_indicatorConstLp,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- The inverse of the isometry `L¹(μ) ⊗̂π X ≃ L¹(μ; X)` sends the indicator `𝟙_A x` of a set of
finite measure to the pure tensor `𝟙_A ⊗ x`. -/
@[simp]
theorem lpOneTensorEquiv_symm_indicatorConstLp {A : Set S} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (x : X) :
    (lpOneTensorEquiv 𝕜 X μ).symm (indicatorConstLp 1 hA hμA x) =
      (⟨indicatorConstLp 1 hA hμA (1 : 𝕜) ⊗ₜ x⟩ : ProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) := by
  rw [LinearIsometryEquiv.symm_apply_eq, lpOneTensorEquiv_coe_tmul_indicatorConstLp, one_smul]

/-- Naturality of `L¹(μ) ⊗̂π X ≃ L¹(μ; X)` in the target: a bounded operator `T : X → Y` acting on
the second tensor factor corresponds to pointwise composition with `T` on Bochner `L¹`. -/
theorem lpOneTensorEquiv_mapL_id [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜 Y] (T : X →L[𝕜] Y)
    (u : CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) :
    lpOneTensorEquiv 𝕜 Y μ (CompletedProjectiveTensor.mapL (.id 𝕜 _) T u) =
      T.compLp (lpOneTensorEquiv 𝕜 X μ u) := by
  suffices ((lpOneTensorEquiv 𝕜 Y μ).toContinuousLinearEquiv : _ →L[𝕜] Lp Y 1 μ) ∘L
      CompletedProjectiveTensor.mapL (.id 𝕜 _) T =
        T.compLpL 1 μ ∘L ((lpOneTensorEquiv 𝕜 X μ).toContinuousLinearEquiv : _ →L[𝕜] Lp X 1 μ)
    from congr($this u)
  refine CompletedProjectiveTensor.continuousLinearMap_ext fun φ x ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, CompletedProjectiveTensor.mapL_coe,
    ProjectiveTensor.mapL_tmul, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, lpOneTensorEquiv_coe_tmul,
    ContinuousLinearMap.compLpL_apply, ContinuousLinearMap.compLp_compLp,
    ContinuousLinearMap.comp_toSpanSingleton]

/-- Naturality of `L¹(μ) ⊗̂π X ≃ L¹(μ; X)` under measure-preserving maps: pulling back the scalar
factor along a measure-preserving `g` corresponds to pulling back Bochner `L¹` along `g`. -/
theorem lpOneTensorEquiv_mapL_compMeasurePreserving {g : S' → S} (hg : MeasurePreserving g μ' μ)
    (u : CompletedProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X) :
    lpOneTensorEquiv 𝕜 X μ' (CompletedProjectiveTensor.mapL
        (Lp.compMeasurePreservingₗᵢ 𝕜 g hg).toContinuousLinearMap (.id 𝕜 X) u) =
      Lp.compMeasurePreserving g hg (lpOneTensorEquiv 𝕜 X μ u) := by
  suffices ((lpOneTensorEquiv 𝕜 X μ').toContinuousLinearEquiv : _ →L[𝕜] Lp X 1 μ') ∘L
      CompletedProjectiveTensor.mapL (Lp.compMeasurePreservingₗᵢ 𝕜 g hg).toContinuousLinearMap
        (.id 𝕜 X) = (Lp.compMeasurePreservingₗᵢ 𝕜 g hg).toContinuousLinearMap ∘L
          ((lpOneTensorEquiv 𝕜 X μ).toContinuousLinearEquiv : _ →L[𝕜] Lp X 1 μ)
    from congr($this u)
  refine CompletedProjectiveTensor.continuousLinearMap_ext fun φ x ↦ Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply, CompletedProjectiveTensor.mapL_coe,
    ProjectiveTensor.mapL_tmul, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometry.coe_toContinuousLinearMap,
    Lp.compMeasurePreservingₗᵢ_apply]
  filter_upwards [coeFn_lpOneTensorEquiv_coe_tmul (Lp.compMeasurePreserving g hg φ) x,
    Lp.coeFn_compMeasurePreserving φ hg, Lp.coeFn_compMeasurePreserving
      (lpOneTensorEquiv 𝕜 X μ (⟨φ ⊗ₜ x⟩ : ProjectiveTensor 𝕜 (Lp 𝕜 1 μ) X)) hg,
    hg.quasiMeasurePreserving.ae (coeFn_lpOneTensorEquiv_coe_tmul φ x)] with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Function.comp_apply, Function.comp_apply, h₄]

end Isometry

end TauCeti
