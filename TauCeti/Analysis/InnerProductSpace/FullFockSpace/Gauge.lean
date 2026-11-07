/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Gauge (conservation) operators on full Fock space

Given an inner product space `H` over `𝕜` (`ℝ` or `ℂ`) and a bounded operator `T : H →L[𝕜] H`, the
*gauge* (or *conservation* / *differential second quantization*) operator `FullFockSpace.gauge T`
(`Λ(T)`) on `FullFockSpace 𝕜 H` kills the vacuum vector (`gauge T vacuum = 0`) and acts as
`T ⊗ id` on the leftmost tensor factor of each positive completed tensor grade:
`gauge T (creation 𝕜 h x) = creation 𝕜 (T h) x`.

In quantum stochastic calculus and free probability, the gauge operators implement multiplicative
bookkeeping on the first tensor factor while annihilating the vacuum line; in particular
`annihilation 𝕜 h ∘L (gauge T ∘L creation 𝕜 k) = ⟪h, T k⟫_𝕜 • id`.

## Main definitions

* `TauCeti.FullFockSpace.gauge`: the bounded operator `Λ(T)` on `FullFockSpace 𝕜 H`.
* `TauCeti.FullFockSpace.gaugeₗᵢ`: the bundled linear isometric embedding `T ↦ Λ(T)`.

## Main results

* `TauCeti.FullFockSpace.gauge_vacuum`: `Λ(T) Ω = 0`.
* `TauCeti.FullFockSpace.gauge_comp_creation`: `Λ(T) ∘L ℓ(h) = ℓ(T h)`.
* `TauCeti.FullFockSpace.norm_gauge`: `‖Λ(T)‖ = ‖T‖`.
* `TauCeti.FullFockSpace.gauge_id`: `Λ(id) = 1 - P_Ω`.
* `TauCeti.FullFockSpace.gauge_comp`: `Λ(S ∘L T) = Λ(S) ∘L Λ(T)`.
* `TauCeti.FullFockSpace.adjoint_gauge`: when `H` is complete, `Λ(T)* = Λ(T*)`.

## References

* K. R. Parthasarathy, *An Introduction to Quantum Stochastic Calculus*, Birkhäuser, 1992, §II.19.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
-/

public section

noncomputable section

open UniformSpace
open scoped InnerProductSpace TensorProduct

namespace TauCeti

universe u v

namespace FullFockSpace

section Gauge

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Acting by `T : H →L[𝕜] H` on the leftmost factor of completed tensor grade `n + 1`. -/
private def stepGauge (T : H →L[𝕜] H) (n : ℕ) :
    CompletedTensorPower 𝕜 H (n + 1) →L[𝕜] CompletedTensorPower 𝕜 H (n + 1) :=
  (CompletedTensorPower.succEquiv 𝕜 H n).symm.toLinearIsometry.toContinuousLinearMap ∘L
    (T.rTensor (CompletedTensorPower 𝕜 H n)).completion ∘L
      (CompletedTensorPower.succEquiv 𝕜 H n).toLinearIsometry.toContinuousLinearMap

private theorem norm_stepGauge_apply_le (T : H →L[𝕜] H) (n : ℕ)
    (x : CompletedTensorPower 𝕜 H (n + 1)) :
    ‖stepGauge T n x‖ ≤ ‖T‖ * ‖x‖ := by
  simp only [stepGauge, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
  rw [← (CompletedTensorPower.succEquiv 𝕜 H n).norm_map x]
  refine Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
      (isClosed_le (by fun_prop) (continuous_const.mul continuous_norm)) fun z => ?_
  rw [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe, Completion.norm_coe]
  exact ((T.rTensor _).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (T.norm_rTensor_le _) (norm_nonneg z))

private theorem stepGauge_add (S T : H →L[𝕜] H) (n : ℕ) :
    stepGauge (S + T) n = stepGauge S n + stepGauge T n := by
  ext x : 1
  simp only [stepGauge, ContinuousLinearMap.comp_apply, add_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, ← map_add]
  congr 1
  refine Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
      (isClosed_eq (by fun_prop) (by fun_prop)) fun z => ?_
  simp [Completion.coe_add]

private theorem stepGauge_smul (c : 𝕜) (T : H →L[𝕜] H) (n : ℕ) :
    stepGauge (c • T) n = c • stepGauge T n := by
  ext x : 1
  simp only [stepGauge, ContinuousLinearMap.comp_apply, smul_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    ← (CompletedTensorPower.succEquiv 𝕜 H n).symm.map_smul]
  congr 1
  refine Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
      (isClosed_eq (ContinuousLinearMap.continuous _)
        ((ContinuousLinearMap.continuous _).const_smul c)) fun z => ?_
  simp [Completion.coe_smul]

private theorem stepGauge_id (n : ℕ) :
    stepGauge (ContinuousLinearMap.id 𝕜 H) n = .id 𝕜 _ := by
  ext x : 1
  simp only [stepGauge, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.symm_apply_eq]
  refine Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
      (isClosed_eq (by fun_prop) continuous_id) fun z => ?_
  simp

private theorem stepGauge_comp (S T : H →L[𝕜] H) (n : ℕ) :
    stepGauge (S ∘L T) n = stepGauge S n ∘L stepGauge T n := by
  ext x : 1
  simp only [stepGauge, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
  congr 1
  refine Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
      (isClosed_eq (by fun_prop) (by fun_prop)) fun z => ?_
  simp [ContinuousLinearMap.rTensor_comp]

private def gaugeRaw (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) : ∀ n, CompletedTensorPower 𝕜 H n
  | 0 => 0
  | n + 1 => stepGauge T n (x (n + 1))

private theorem memℓp_gaugeRaw (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    Memℓp (gaugeRaw T x) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat]
  rw [← _root_.summable_nat_add_iff 1]
  have hx0 : Summable fun m => ‖x m‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (by simp)
  have hx : Summable fun n => ‖x (n + 1)‖ ^ (2 : ℝ) :=
    (_root_.summable_nat_add_iff 1 (f := fun m => ‖x m‖ ^ (2 : ℝ))).mpr hx0
  refine (hx.mul_left (‖T‖ ^ (2 : ℝ))).of_nonneg_of_le (fun _ => by positivity) fun n => ?_
  rw [← Real.mul_rpow (norm_nonneg T) (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_stepGauge_apply_le T n (x (n + 1))) (by positivity)

/-- The *gauge* (or *conservation*) operator `Λ(T)` on `FullFockSpace 𝕜 H` associated with a
bounded operator `T : H →L[𝕜] H`. It kills the vacuum (`gauge T vacuum = 0`) and acts as `T ⊗ id`
on the leftmost factor of each positive tensor grade. -/
def gauge (T : H →L[𝕜] H) : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  LinearMap.mkContinuous
    { toFun x := ⟨gaugeRaw T x, memℓp_gaugeRaw T x⟩
      map_add' x y := by
        apply lp.ext
        rw [lp.coeFn_add]
        ext (_ | n) <;> simp [gaugeRaw]
      map_smul' c x := by
        ext (_ | n) <;> simp [gaugeRaw] }
    ‖T‖ fun x => by
      refine lp.norm_le_of_forall_sum_le (by simp) (mul_nonneg (norm_nonneg T) (norm_nonneg x))
        fun s => ?_
      simp only [ENNReal.toReal_ofNat]
      calc
        ∑ i ∈ s, ‖gaugeRaw T x i‖ ^ (2 : ℝ)
          ≤ ∑ i ∈ s, (‖T‖ * ‖x i‖) ^ (2 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            cases i with
            | zero =>
              simp only [gaugeRaw, norm_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
              exact Real.rpow_nonneg (mul_nonneg (norm_nonneg T) (norm_nonneg (x 0))) 2
            | succ n =>
              exact Real.rpow_le_rpow (norm_nonneg _)
                (norm_stepGauge_apply_le T n (x (n + 1))) (by positivity)
        _ = ‖T‖ ^ (2 : ℝ) * ∑ i ∈ s, ‖x i‖ ^ (2 : ℝ) := by
          simp_rw [Real.mul_rpow (norm_nonneg T) (norm_nonneg _), ← Finset.mul_sum]
        _ ≤ ‖T‖ ^ (2 : ℝ) * ‖x‖ ^ (2 : ℝ) := by
          gcongr
          simpa using lp.sum_rpow_le_norm_rpow (p := 2) (by simp) x s
        _ = (‖T‖ * ‖x‖) ^ (2 : ℝ) :=
          (Real.mul_rpow (norm_nonneg T) (norm_nonneg x)).symm

@[simp]
theorem gauge_apply_zero (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    (gauge T x) 0 = 0 :=
  (rfl)

theorem gauge_apply_succ (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) (n : ℕ) :
    (gauge T x) (n + 1) =
      (CompletedTensorPower.succEquiv 𝕜 H n).symm
        ((T.rTensor (CompletedTensorPower 𝕜 H n)).completion
          (CompletedTensorPower.succEquiv 𝕜 H n (x (n + 1)))) :=
  (rfl)

/-- The gauge operator `Λ(T)` kills the vacuum vector. -/
@[simp]
theorem gauge_vacuum (T : H →L[𝕜] H) : gauge T (vacuum : FullFockSpace 𝕜 H) = 0 := by
  ext (_ | n) <;> simp [gauge_apply_succ]

@[simp]
theorem gauge_comp_vacuumProj (T : H →L[𝕜] H) :
    gauge T ∘L vacuumProj = 0 := by
  ext x : 1
  simp [vacuumProj_apply]

@[simp]
theorem inner_vacuum_gauge (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    ⟪vacuum, gauge T x⟫_𝕜 = 0 := by
  simp [inner_vacuum_left]

@[simp]
theorem inner_gauge_vacuum (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    ⟪gauge T x, vacuum⟫_𝕜 = 0 := by
  rw [← inner_conj_symm, inner_vacuum_gauge, map_zero]

@[simp]
theorem vacuumProj_gauge (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    vacuumProj (gauge T x) = 0 := by
  simp [vacuumProj_apply]

@[simp]
theorem vacuumProj_comp_gauge (T : H →L[𝕜] H) :
    vacuumProj ∘L gauge T = 0 :=
  ContinuousLinearMap.ext (vacuumProj_gauge T)

@[simp]
theorem gauge_creation (T : H →L[𝕜] H) (h : H) (x : FullFockSpace 𝕜 H) :
    gauge T (creation 𝕜 h x) = creation 𝕜 (T h) x := by
  ext (_ | n)
  · simp
  · simp [gauge_apply_succ]

/-- Left-composing `creation 𝕜 h` with `gauge T` applies `T` to the created vector `h`. -/
@[simp]
theorem gauge_comp_creation (T : H →L[𝕜] H) (h : H) :
    gauge T ∘L creation 𝕜 h = creation 𝕜 (T h) :=
  ContinuousLinearMap.ext (gauge_creation T h)

/-- The gauge operator `Λ(T)` has exact operator norm `‖T‖`. -/
@[simp]
theorem norm_gauge (T : H →L[𝕜] H) : ‖gauge T‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (gauge T)) fun h => ?_
  calc
    ‖T h‖ = ‖creation 𝕜 (T h) (vacuum : FullFockSpace 𝕜 H)‖ := by simp
    _ = ‖gauge T (creation 𝕜 h (vacuum : FullFockSpace 𝕜 H))‖ := by rw [gauge_creation]
    _ ≤ ‖gauge T‖ * ‖creation 𝕜 h (vacuum : FullFockSpace 𝕜 H)‖ := (gauge T).le_opNorm _
    _ = ‖gauge T‖ * ‖h‖ := by simp

@[simp]
theorem gauge_add (S T : H →L[𝕜] H) : gauge (S + T) = gauge S + gauge T := by
  ext x (_ | n)
  · simp
  · exact congrArg (fun R => R (x (n + 1))) (stepGauge_add S T n)

@[simp]
theorem gauge_smul (c : 𝕜) (T : H →L[𝕜] H) : gauge (c • T) = c • gauge T := by
  ext x (_ | n)
  · simp
  · exact congrArg (fun R => R (x (n + 1))) (stepGauge_smul c T n)

end Gauge

/-- The gauge representation `T ↦ Λ(T)` as a linear isometric embedding. -/
def gaugeₗᵢ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    (H →L[𝕜] H) →ₗᵢ[𝕜] FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H where
  toFun := gauge
  map_add' := gauge_add
  map_smul' := gauge_smul
  norm_map' := norm_gauge

section GaugeAlgebra

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem gaugeₗᵢ_apply (T : H →L[𝕜] H) : gaugeₗᵢ 𝕜 H T = gauge T :=
  (rfl)

@[simp]
theorem gauge_zero : gauge (0 : H →L[𝕜] H) = 0 :=
  (gaugeₗᵢ 𝕜 H).map_zero

@[simp]
theorem gauge_neg (T : H →L[𝕜] H) : gauge (-T) = -gauge T :=
  (gaugeₗᵢ 𝕜 H).map_neg T

@[simp]
theorem gauge_sub (S T : H →L[𝕜] H) : gauge (S - T) = gauge S - gauge T :=
  (gaugeₗᵢ 𝕜 H).map_sub S T

/-- `Λ(id)` is the orthogonal projection `1 - vacuumProj` onto the positive-grade Fock subspace. -/
theorem gauge_id :
    gauge (ContinuousLinearMap.id 𝕜 H) = 1 - vacuumProj := by
  ext x (_ | n)
  · simp
  · rw [sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply,
      vacuumProj_apply_succ, sub_zero]
    exact DFunLike.congr_fun (stepGauge_id (𝕜 := 𝕜) (H := H) n) (x (n + 1))

theorem gauge_one :
    gauge (1 : H →L[𝕜] H) = 1 - vacuumProj :=
  gauge_id

@[simp]
theorem norm_one_sub_vacuumProj [Nontrivial H] :
    ‖(1 : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) - vacuumProj‖ = 1 := by
  rw [← gauge_one, norm_gauge, norm_one]

/-- The gauge map is multiplicative: `Λ(S ∘L T) = Λ(S) ∘L Λ(T)`. -/
theorem gauge_comp (S T : H →L[𝕜] H) : gauge (S ∘L T) = gauge S ∘L gauge T := by
  ext x (_ | n)
  · simp
  · exact congrArg (fun R => R (x (n + 1))) (stepGauge_comp S T n)

theorem gauge_mul (S T : H →L[𝕜] H) : gauge (S * T) = gauge S * gauge T :=
  gauge_comp S T

section CompleteSpace

variable [CompleteSpace H]

private theorem inner_stepGauge (T : H →L[𝕜] H) (n : ℕ)
    (x y : CompletedTensorPower 𝕜 H (n + 1)) :
    ⟪stepGauge T n x, y⟫_𝕜 = ⟪x, stepGauge T.adjoint n y⟫_𝕜 := by
  set x' := CompletedTensorPower.succEquiv 𝕜 H n x
  set y' := CompletedTensorPower.succEquiv 𝕜 H n y
  have hx : x = (CompletedTensorPower.succEquiv 𝕜 H n).symm x' := by simp [x']
  have hy : y = (CompletedTensorPower.succEquiv 𝕜 H n).symm y' := by simp [y']
  rw [hx, hy]
  simp only [stepGauge, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.inner_map_map]
  refine Completion.induction_on₂ x' y' (isClosed_eq (by fun_prop) (by fun_prop)) fun u v => ?_
  rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
    Completion.inner_coe, Completion.inner_coe]
  refine TensorProduct.inductionOn u (fun a w => ?_) (fun u₁ u₂ hu₁ hu₂ => ?_)
  · refine TensorProduct.inductionOn v (fun b z => ?_) (fun v₁ v₂ hv₁ hv₂ => ?_)
    · rw [ContinuousLinearMap.rTensor_tmul, ContinuousLinearMap.rTensor_tmul,
        TensorProduct.inner_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_right]
    · rw [map_add, inner_add_right, inner_add_right, hv₁, hv₂]
  · rw [map_add, inner_add_left, inner_add_left, hu₁, hu₂]

/-- When `H` is complete, the gauge representation commutes with taking Hilbert-space adjoints. -/
@[simp]
theorem adjoint_gauge (T : H →L[𝕜] H) : (gauge T).adjoint = gauge T.adjoint := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left 𝕜 fun x => ?_
  have hs₁ : Summable fun i => ⟪(gauge T x) i, y i⟫_𝕜 :=
    lp.summable_inner (𝕜 := 𝕜) (gauge T x) y
  have hs₂ : Summable fun i => ⟪x i, (gauge T.adjoint y) i⟫_𝕜 :=
    lp.summable_inner (𝕜 := 𝕜) x (gauge T.adjoint y)
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum, lp.inner_eq_tsum,
    hs₁.tsum_eq_zero_add, hs₂.tsum_eq_zero_add]
  simp only [gauge_apply_zero, inner_zero_left, inner_zero_right, zero_add]
  congr 1
  ext n
  exact inner_stepGauge T n (x (n + 1)) (y (n + 1))

@[simp]
theorem star_gauge (T : H →L[𝕜] H) : star (gauge T) = gauge (star T) :=
  adjoint_gauge T

@[simp]
theorem annihilation_comp_gauge (h : H) (T : H →L[𝕜] H) :
    annihilation 𝕜 h ∘L gauge T = annihilation 𝕜 (T.adjoint h) := by
  rw [← ContinuousLinearMap.adjoint_adjoint (annihilation 𝕜 h ∘L gauge T),
    ContinuousLinearMap.adjoint_comp, adjoint_gauge, adjoint_annihilation,
    gauge_comp_creation, adjoint_creation]

@[simp]
theorem annihilation_gauge (h : H) (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    annihilation 𝕜 h (gauge T x) = annihilation 𝕜 (T.adjoint h) x :=
  DFunLike.congr_fun (annihilation_comp_gauge h T) x

end CompleteSpace

end GaugeAlgebra

end FullFockSpace

end TauCeti
