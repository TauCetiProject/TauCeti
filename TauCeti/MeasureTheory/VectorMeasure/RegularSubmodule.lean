/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.MeasureTheory.Integral.ContinuousMap
public import TauCeti.MeasureTheory.Measure.Regular
public import TauCeti.MeasureTheory.VectorMeasure.Uniqueness
public import TauCeti.MeasureTheory.VectorMeasure.Variation.Regular

/-!
# The normed space of scalar measures of regular variation

Let `X` be a topological space with its Borel σ-algebra and let `𝕜` be `ℝ` or `ℂ` (any `RCLike`
field). The `𝕜`-valued measures `μ` on `X` whose variation `|μ|` is regular form a submodule
`MeasureTheory.VectorMeasure.regularSubmodule X 𝕜` of `VectorMeasure X 𝕜`, written `M(X)` below,
as soon as `X` is an `R₁` space. The variation of a scalar measure is always finite, so this is
the space of scalar measures of finite regular variation. It is a normed space for the
total-variation norm `‖μ‖ = |μ|(X)`, and it contains the Dirac measures `δₓ`, of norm one.

When `X` is compact, integration of continuous functions against a scalar measure `μ` is a
continuous linear functional `f ↦ ∫ f dμ` on `C(X, 𝕜)` of norm at most `|μ|(X)`. On a compact
Hausdorff space this gives a contractive injective linear map
`M(X) →L[𝕜] StrongDual 𝕜 C(X, 𝕜)` sending `δₓ` to evaluation at `x`. Injectivity is the
uniqueness theorem for scalar measures of regular variation,
`MeasureTheory.VectorMeasure.ext_of_integral_eq_on_continuousMap`. This is the map of the Riesz
representation theorem, not proved here, which states that it is an isometric isomorphism onto
the dual.

## Main declarations

* `MeasureTheory.VectorMeasure.integralContinuousMap`: the functional `f ↦ ∫ f dμ` on `C(X, 𝕜)`
  of a scalar measure `μ` on a compact space, with `‖∫ f dμ‖ ≤ ‖f‖ |μ|(X)`.
* `MeasureTheory.VectorMeasure.regularSubmodule`: the submodule `M(X)` of scalar measures of
  regular variation.
* `MeasureTheory.VectorMeasure.regularSubmodule.norm_def`: `M(X)` is normed by the total
  variation `|μ|(X)`.
* `MeasureTheory.VectorMeasure.regularSubmodule.dirac`: the Dirac measure `δₓ ∈ M(X)`, of norm
  one (`MeasureTheory.VectorMeasure.regularSubmodule.norm_dirac`).
* `MeasureTheory.VectorMeasure.regularSubmodule.toDual`: the integration map
  `M(X) →L[𝕜] StrongDual 𝕜 C(X, 𝕜)`, which is contractive (`norm_toDual_le`) and injective
  (`toDual_injective`), and sends `δₓ` to evaluation at `x` (`toDual_dirac`).

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), §6.1 and Theorem 6.19.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap Set

namespace MeasureTheory.VectorMeasure

variable {X 𝕜 : Type*} [MeasurableSpace X] [TopologicalSpace X] [RCLike 𝕜]

/-! ### Integration of continuous functions -/

section Integral

variable [CompactSpace X] [OpensMeasurableSpace X]

/-- Integration of continuous functions against a scalar measure `μ` on a compact space, as a
continuous linear functional `f ↦ ∫ f dμ` on `C(X, 𝕜)`. -/
def integralContinuousMap (μ : VectorMeasure X 𝕜) : StrongDual 𝕜 C(X, 𝕜) :=
  LinearMap.mkContinuous
    { toFun f := ∫ᵛ x, f x ∂[mul ℝ 𝕜; μ]
      map_add' f g := by
        simpa using integral_add (f.integrable μ.variation) (g.integrable μ.variation)
      map_smul' c f := by simpa using integral_const_mul μ c f }
    (μ.variation.real univ) fun f ↦ by
      -- `‖∫ f dμ‖ ≤ ‖f‖ ‖mul ℝ 𝕜‖ |μ|(X)`, and multiplication has operator norm at most one.
      refine (norm_integral_le_of_norm_le_const (.of_forall f.norm_coe_le_norm)).trans ?_
      rw [mul_comm _ ‖f‖]
      gcongr
      exact mul_le_of_le_one_right (norm_nonneg f) (opNorm_mul_le ℝ 𝕜)

@[simp]
theorem integralContinuousMap_apply (μ : VectorMeasure X 𝕜) (f : C(X, 𝕜)) :
    μ.integralContinuousMap f = ∫ᵛ x, f x ∂[mul ℝ 𝕜; μ] :=
  (rfl)

/-- The functional of a scalar measure `μ` on `C(X, 𝕜)` has norm at most `|μ|(X)`. -/
theorem norm_integralContinuousMap_le (μ : VectorMeasure X 𝕜) :
    ‖μ.integralContinuousMap‖ ≤ μ.variation.real univ :=
  LinearMap.mkContinuous_norm_le _ measureReal_nonneg _

@[simp]
theorem integralContinuousMap_zero : (0 : VectorMeasure X 𝕜).integralContinuousMap = 0 := by
  ext f
  simp

@[simp]
theorem integralContinuousMap_add (μ ν : VectorMeasure X 𝕜) :
    (μ + ν).integralContinuousMap = μ.integralContinuousMap + ν.integralContinuousMap := by
  ext f
  simpa using integral_add_vectorMeasure (f.integrable μ.variation) (f.integrable ν.variation)

@[simp]
theorem integralContinuousMap_smul (c : 𝕜) (μ : VectorMeasure X 𝕜) :
    (c • μ).integralContinuousMap = c • μ.integralContinuousMap := by
  ext f
  simp

/-- The functional of the Dirac measure `δₓ` with weight `c` is `f ↦ f x * c`. -/
theorem integralContinuousMap_dirac_apply (x : X) (c : 𝕜) (f : C(X, 𝕜)) :
    (dirac x c).integralContinuousMap f = f x * c := by
  rw [integralContinuousMap_apply, integral_dirac' f.continuous.stronglyMeasurable, mul_apply']

/-- The functional of the Dirac measure `δₓ` with weight `c` is `c` times evaluation at `x`. -/
@[simp]
theorem integralContinuousMap_dirac (x : X) (c : 𝕜) :
    (dirac x c).integralContinuousMap = c • ContinuousMap.evalCLM 𝕜 x := by
  ext f
  rw [integralContinuousMap_dirac_apply, smul_apply, ContinuousMap.evalCLM_apply, smul_eq_mul,
    mul_comm]

end Integral

/-! ### The submodule of scalar measures of regular variation -/

section Submodule

variable (X 𝕜) [BorelSpace X] [R1Space X]

/-- The scalar measures `μ` whose variation `|μ|` is regular, as a submodule of
`VectorMeasure X 𝕜`. The variation of a scalar measure is always finite
(`MeasureTheory.VectorMeasure.isFiniteMeasure_variation`), so these are the scalar measures of
finite regular variation. On an `R₁` space they are closed under sums since `|μ + ν|` is dominated
by `|μ| + |ν|`. -/
def regularSubmodule : Submodule 𝕜 (VectorMeasure X 𝕜) where
  carrier := {μ | μ.variation.Regular}
  add_mem' {μ ν} (_ : μ.variation.Regular) (_ : ν.variation.Regular) :=
    regular_variation_add (μ := μ) (ν := ν)
  zero_mem' := by
    rw [Set.mem_ofPred_eq, variation_zero]
    infer_instance
  smul_mem' c μ (_ : μ.variation.Regular) := regular_variation_smul (μ := μ) (c := c)

variable {X 𝕜}

@[simp]
theorem mem_regularSubmodule {μ : VectorMeasure X 𝕜} :
    μ ∈ regularSubmodule X 𝕜 ↔ μ.variation.Regular :=
  Iff.rfl

namespace regularSubmodule

instance (μ : regularSubmodule X 𝕜) : (μ : VectorMeasure X 𝕜).variation.Regular :=
  μ.2

/-- The total-variation norm `‖μ‖ = |μ|(X)`. -/
instance : Norm (regularSubmodule X 𝕜) where
  norm μ := (μ : VectorMeasure X 𝕜).variation.real univ

theorem norm_def (μ : regularSubmodule X 𝕜) :
    ‖μ‖ = (μ : VectorMeasure X 𝕜).variation.real univ :=
  rfl

/-- The total variation is a norm on the scalar measures of regular variation. -/
theorem normedSpaceCore : NormedSpace.Core 𝕜 (regularSubmodule X 𝕜) where
  norm_nonneg _ := measureReal_nonneg
  norm_smul c μ := by
    simp [norm_def, variation_smul, measureReal_def, ENNReal.toReal_mul]
  norm_triangle μ ν := by
    simp only [norm_def, Submodule.coe_add, measureReal_def]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← add_apply]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (variation_add_le univ)
  norm_eq_zero_iff μ := by
    rw [norm_def, measureReal_eq_zero_iff, Measure.measure_univ_eq_zero, variation_eq_zero,
      ZeroMemClass.coe_eq_zero]

instance : NormedAddCommGroup (regularSubmodule X 𝕜) :=
  .ofCore normedSpaceCore

instance : NormedSpace 𝕜 (regularSubmodule X 𝕜) :=
  .ofCore normedSpaceCore

theorem enorm_eq (μ : regularSubmodule X 𝕜) :
    ‖μ‖ₑ = (μ : VectorMeasure X 𝕜).variation univ := by
  rw [← ofReal_norm, norm_def, ofReal_measureReal]

/-- The value of a scalar measure of regular variation on any set is bounded by its norm. -/
theorem norm_apply_le (μ : regularSubmodule X 𝕜) (s : Set X) :
    ‖(μ : VectorMeasure X 𝕜) s‖ ≤ ‖μ‖ :=
  (norm_measure_le_variation).trans (measureReal_mono (subset_univ s))

/-- The Dirac measure `δₓ` with unit weight, as a scalar measure of regular variation. -/
def dirac (x : X) : regularSubmodule X 𝕜 :=
  ⟨VectorMeasure.dirac x 1, by
    rw [mem_regularSubmodule, variation_dirac, enorm_one, one_smul]
    infer_instance⟩

@[simp]
theorem coe_dirac (x : X) :
    ((dirac x : regularSubmodule X 𝕜) : VectorMeasure X 𝕜) = VectorMeasure.dirac x 1 :=
  (rfl)

@[simp]
theorem norm_dirac (x : X) : ‖(dirac x : regularSubmodule X 𝕜)‖ = 1 := by
  simp [norm_def, coe_dirac]

/-! ### The integration map into the dual of `C(X, 𝕜)` -/

variable [CompactSpace X]

variable (X 𝕜) in
/-- Integration of continuous functions, as a contractive linear map from the scalar measures of
regular variation to the dual of `C(X, 𝕜)`: `toDual μ f = ∫ f dμ`. -/
def toDual : regularSubmodule X 𝕜 →L[𝕜] StrongDual 𝕜 C(X, 𝕜) :=
  LinearMap.mkContinuous
    { toFun μ := (μ : VectorMeasure X 𝕜).integralContinuousMap
      map_add' μ ν := by simp
      map_smul' c μ := by simp }
    1 fun μ ↦ by simpa [norm_def] using norm_integralContinuousMap_le (μ : VectorMeasure X 𝕜)

@[simp]
theorem toDual_apply (μ : regularSubmodule X 𝕜) (f : C(X, 𝕜)) :
    toDual X 𝕜 μ f = ∫ᵛ x, f x ∂[mul ℝ 𝕜; (μ : VectorMeasure X 𝕜)] :=
  (rfl)

/-- The functional of a scalar measure of regular variation has norm at most its total
variation. -/
theorem norm_toDual_le (μ : regularSubmodule X 𝕜) : ‖toDual X 𝕜 μ‖ ≤ ‖μ‖ :=
  norm_integralContinuousMap_le (μ : VectorMeasure X 𝕜)

/-- The integration map is contractive. -/
theorem norm_toDual_le_one : ‖toDual X 𝕜‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The functional of the Dirac measure `δₓ` is evaluation at `x`. -/
@[simp]
theorem toDual_dirac (x : X) : toDual X 𝕜 (dirac x) = ContinuousMap.evalCLM 𝕜 x := by
  ext f
  rw [toDual_apply, coe_dirac, ← integralContinuousMap_apply, integralContinuousMap_dirac_apply,
    mul_one, ContinuousMap.evalCLM_apply]

/-- The Dirac measure `δₓ` integrates a continuous function to its value at `x`. -/
theorem toDual_dirac_apply (x : X) (f : C(X, 𝕜)) : toDual X 𝕜 (dirac x) f = f x := by
  simp

/-- The functional of a Dirac measure has norm one. -/
theorem norm_toDual_dirac (x : X) : ‖toDual X 𝕜 (dirac x)‖ = 1 := by
  refine le_antisymm ((norm_toDual_le _).trans_eq (norm_dirac x)) ?_
  have : Nonempty X := ⟨x⟩
  simpa only [toDual_dirac_apply, ContinuousMap.one_apply, norm_one, mul_one] using
    (toDual X 𝕜 (dirac x)).le_opNorm 1

/-- On a compact Hausdorff space, a scalar measure of regular variation is determined by its
integrals of continuous functions. -/
theorem toDual_injective [T2Space X] : Function.Injective (toDual X 𝕜) := fun μ ν h ↦
  Subtype.ext <| ext_of_integral_eq_on_continuousMap fun f ↦ by
    simpa using DFunLike.congr_fun h f

end regularSubmodule

end Submodule

end MeasureTheory.VectorMeasure
