/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Geometry.Lie.TestFunction.ApproximateIdentity
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.RepresentationTheory.Continuous.StronglyContinuous

/-!
# Test functions acting on a representation of a Lie group

Let `π` be a strongly continuous representation of a Lie group `G` on a complex Banach space `V`
(every orbit `g ↦ π g v` is continuous) and `μ` a measure on `G` that is finite on compact sets.
A test function `a ∈ C_c^∞(G)` acts on `V` by the **integrated operator**

`π(a) v = ∫ y, a y • π y v ∂μ`,

a bounded operator, linear in `a`. By `ContRepresentation.exists_norm_le_of_isCompact` (the
Banach–Steinhaus theorem) the operators `π y` are uniformly bounded on the compact support of `a`,
which bounds `π(a)`. For a left-invariant measure `π g ∘ π(a) = π(L_g a)`, where
`L_g a = a (g⁻¹ * ·)` is left translation, and along the smooth approximate identities `u_U` of
`TauCeti/Geometry/Lie/TestFunction/ApproximateIdentity.lean`, `π(u_U) v → v` for every `v`.

This is the operator of Gårding's smoothing argument, which shows that each `π(a) v` is a smooth
vector and hence that the smooth vectors are dense.

## Main definitions

* `ContRepresentation.lieIntegratedOperator π hπ μ`: the integrated operator `a ↦ π(a)`, a linear
  map from the test functions to the bounded operators on `V`.

## Main results

* `ContRepresentation.lieIntegratedOperator_apply`: `π(a) v = ∫ y, a y • π y v ∂μ`.
* `ContRepresentation.norm_lieIntegratedOperator_le`: `‖π(a)‖ ≤ C * ∫ ‖a‖ dμ` when `‖π y‖ ≤ C`
  on the support of `a`.
* `ContRepresentation.apply_lieIntegratedOperator`: `π g (π(a) v) = π(L_g a) v` for a
  left-invariant measure.
* `ContRepresentation.tendsto_lieIntegratedOperator_smoothApproximateIdentity`:
  `π(u_U) v → v` as `U` shrinks to the identity.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology TopologicalSpace TauCeti
open scoped ContDiff Manifold

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [MeasurableSpace G]
  [OpensMeasurableSpace G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (π : ContRepresentation ℂ G V) (hπ : ∀ v, Continuous fun g ↦ π g v) (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

include hπ in
/-- The integrand `y ↦ a y • π y v` of the integrated operator is integrable. -/
theorem integrable_lieTestFunction_smul (a : LieTestFunction I G) (v : V) :
    Integrable (fun y ↦ a y • π y v) μ :=
  (a.continuous.smul (hπ v)).integrable_of_hasCompactSupport a.hasCompactSupport.smul_right

/-- The integral `∫ y, a y • π y v ∂μ` as a linear map in `v`. -/
private def lieIntegratedOperatorₗ (a : LieTestFunction I G) : V →ₗ[ℂ] V where
  toFun v := ∫ y, a y • π y v ∂μ
  map_add' v w := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_lieTestFunction_smul π hπ μ a v)
      (integrable_lieTestFunction_smul π hπ μ a w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply, smul_comm (a _) c]
    exact integral_smul c _

/-- Evaluation of `lieIntegratedOperatorₗ`. -/
private theorem lieIntegratedOperatorₗ_apply (a : LieTestFunction I G) (v : V) :
    lieIntegratedOperatorₗ π hπ μ a v = ∫ y, a y • π y v ∂μ :=
  (rfl)

/-- The bound `‖∫ y, a y • π y v ∂μ‖ ≤ C * (∫ ‖a‖ dμ) * ‖v‖` when `‖π y‖ ≤ C` on a set containing
the support of `a`. -/
private theorem norm_integral_lieTestFunction_smul_le (a : LieTestFunction I G) {K : Set G}
    (hK : tsupport a ⊆ K) {C : ℝ} (hC : ∀ y ∈ K, ‖(π y : V →L[ℂ] V)‖ ≤ C) (v : V) :
    ‖∫ y, a y • π y v ∂μ‖ ≤ C * (∫ y, ‖a y‖ ∂μ) * ‖v‖ := by
  have hC0 : ∀ y, ‖a y • π y v‖ ≤ ‖a y‖ * (C * ‖v‖) := fun y ↦ by
    rw [norm_smul]
    by_cases hy : y ∈ tsupport a
    · exact mul_le_mul_of_nonneg_left (((π y : V →L[ℂ] V).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hC y (hK hy)) (norm_nonneg v))) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  calc ‖∫ y, a y • π y v ∂μ‖ ≤ ∫ y, ‖a y‖ * (C * ‖v‖) ∂μ :=
        norm_integral_le_of_norm_le ((a.continuous.norm.integrable_of_hasCompactSupport
          a.hasCompactSupport.norm).mul_const _) (ae_of_all _ hC0)
    _ = C * (∫ y, ‖a y‖ ∂μ) * ‖v‖ := by rw [integral_mul_const]; ring

variable [CompleteSpace V]

/-- The **integrated operator** of a strongly continuous representation of a Lie group on a
complex Banach space: a test function `a` acts by `π(a) v = ∫ y, a y • π y v ∂μ`. -/
def lieIntegratedOperator : LieTestFunction I G →ₗ[ℂ] V →L[ℂ] V where
  toFun a := (lieIntegratedOperatorₗ π hπ μ a).mkContinuousOfExistsBound <| by
    obtain ⟨C, hC⟩ := exists_norm_le_of_isCompact hπ a.hasCompactSupport.isCompact
    exact ⟨C * ∫ y, ‖a y‖ ∂μ,
      norm_integral_lieTestFunction_smul_le π μ a subset_rfl hC⟩
  map_add' a b := by
    ext v
    simp only [LinearMap.mkContinuousOfExistsBound_apply, lieIntegratedOperatorₗ_apply,
      IsAddApply.add_apply, add_smul]
    exact integral_add (integrable_lieTestFunction_smul π hπ μ a v)
      (integrable_lieTestFunction_smul π hπ μ b v)
  map_smul' c a := by
    ext v
    simp only [LinearMap.mkContinuousOfExistsBound_apply, lieIntegratedOperatorₗ_apply,
      IsSMulApply.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact integral_smul c _

/-- The integrated operator is integration of the orbit against the test function. -/
theorem lieIntegratedOperator_apply (a : LieTestFunction I G) (v : V) :
    lieIntegratedOperator π hπ μ a v = ∫ y, a y • π y v ∂μ :=
  (rfl)

/-- `‖π(a) v‖ ≤ C * (∫ ‖a‖ dμ) * ‖v‖` when `‖π y‖ ≤ C` on a set containing the support of `a`. -/
theorem norm_lieIntegratedOperator_apply_le (a : LieTestFunction I G) {K : Set G}
    (hK : tsupport a ⊆ K) {C : ℝ} (hC : ∀ y ∈ K, ‖(π y : V →L[ℂ] V)‖ ≤ C) (v : V) :
    ‖lieIntegratedOperator π hπ μ a v‖ ≤ C * (∫ y, ‖a y‖ ∂μ) * ‖v‖ :=
  norm_integral_lieTestFunction_smul_le π μ a hK hC v

/-- `‖π(a)‖ ≤ C * ∫ ‖a‖ dμ` when `‖π y‖ ≤ C` on a set containing the support of `a`. -/
theorem norm_lieIntegratedOperator_le (a : LieTestFunction I G) {K : Set G}
    (hK : tsupport a ⊆ K) {C : ℝ} (hC : ∀ y ∈ K, ‖(π y : V →L[ℂ] V)‖ ≤ C) :
    ‖lieIntegratedOperator π hπ μ a‖ ≤ C * ∫ y, ‖a y‖ ∂μ := by
  rcases K.eq_empty_or_nonempty with hKe | ⟨y₀, hy₀⟩
  · have ha : (a : G → ℂ) = 0 := by
      funext y
      exact image_eq_zero_of_notMem_tsupport fun hy ↦ by simpa [hKe] using hK hy
    have : lieIntegratedOperator π hπ μ a = 0 := by
      ext v
      simp [lieIntegratedOperator_apply, ha]
    simp [this, ha]
  · refine ContinuousLinearMap.opNorm_le_bound _ ?_
      (norm_lieIntegratedOperator_apply_le π hπ μ a hK hC)
    exact mul_nonneg ((norm_nonneg _).trans (hC y₀ hy₀)) (integral_nonneg fun _ ↦ norm_nonneg _)

variable [LieGroup I ∞ G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- **Translation.** For a left-invariant measure, `π g (π(a) v) = π(L_g a) v`, where
`L_g a = a (g⁻¹ * ·)` is the left translate of `a`. -/
theorem apply_lieIntegratedOperator (g : G) (a : LieTestFunction I G) (v : V) :
    π g (lieIntegratedOperator π hπ μ a v) =
      lieIntegratedOperator π hπ μ (LieTestFunction.leftTranslate g a) v := by
  rw [lieIntegratedOperator_apply, lieIntegratedOperator_apply,
    ← (π g : V →L[ℂ] V).integral_comp_comm (integrable_lieTestFunction_smul π hπ μ a v),
    ← integral_mul_left_eq_self _ g⁻¹]
  congr 1 with y
  simp [LieTestFunction.leftTranslate_apply]

end ContRepresentation

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [MeasurableSpace G] [OpensMeasurableSpace G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  {π : ContRepresentation ℂ G V} (hπ : ∀ v, Continuous fun g ↦ π g v) (μ : Measure G)
  [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

/-- **Approximate identity.** Along the smooth approximate identities `u_U`, the integrated
operators tend strongly to the identity: `π(u_U) v → v` as `U` shrinks to the identity. -/
theorem tendsto_lieIntegratedOperator_smoothApproximateIdentity (v : V) :
    Tendsto (fun U ↦ lieIntegratedOperator π hπ μ
      (LieTestFunction.smoothApproximateIdentity I μ U) v) atBot (𝓝 v) := by
  simpa [lieIntegratedOperator_apply] using
    LieTestFunction.tendsto_integral_smoothApproximateIdentity_smul I μ (hπ v)

end ContRepresentation
