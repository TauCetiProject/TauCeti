/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Free gauge (conservation) operators on full Fock space

Given an inner product space `H` over `𝕜` (`ℝ` or `ℂ`) and a bounded operator `T : H →L[𝕜] H`, the
*free* (or *left*) *gauge* (*conservation*) operator `T.gauge` (`Λ(T)`) on `FullFockSpace 𝕜 H`
kills the vacuum vector (`T.gauge vacuum = 0`) and acts as `T ⊗ id` on the first (leftmost) tensor
factor of each positive completed tensor grade: `T.gauge (creation 𝕜 h x) = creation 𝕜 (T h) x`.

In free probability (for example in the Fock-space realization of free Poisson variables), the free
gauge operators implement multiplicative bookkeeping on the leftmost tensor factor while
annihilating the vacuum line; in particular `Λ(id) = 1 - P_Ω` and
`annihilation 𝕜 h ∘L (T.gauge ∘L creation 𝕜 k) = ⟪h, T k⟫_𝕜 • id`.

## Main definitions

* `ContinuousLinearMap.gauge`: the bounded free gauge operator `Λ(T)` on `FullFockSpace 𝕜 H`.
* `TauCeti.FullFockSpace.gaugeₗᵢ`: the bundled linear isometric embedding `T ↦ Λ(T)`.

## Main results

* `ContinuousLinearMap.gauge_vacuum`: `Λ(T) Ω = 0`.
* `ContinuousLinearMap.gauge_comp_creation`: `Λ(T) ∘L ℓ(h) = ℓ(T h)`.
* `ContinuousLinearMap.norm_gauge`: `‖Λ(T)‖ = ‖T‖`.
* `ContinuousLinearMap.gauge_id`: `Λ(id) = 1 - P_Ω`.
* `ContinuousLinearMap.gauge_comp`: `Λ(S ∘L T) = Λ(S) ∘L Λ(T)`.
* `ContinuousLinearMap.adjoint_gauge`: when `H` is complete, `Λ(T)* = Λ(T*)`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lecture 7.
-/

public section

noncomputable section

open UniformSpace TauCeti TauCeti.FullFockSpace
open scoped InnerProductSpace TensorProduct

universe u v

namespace ContinuousLinearMap

section Gauge

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Acting by `T : H →L[𝕜] H` on the leftmost factor of completed tensor grade `n + 1`. -/
private def stepGauge (T : H →L[𝕜] H) (n : ℕ) :
    CompletedTensorPower 𝕜 H (n + 1) →L[𝕜] CompletedTensorPower 𝕜 H (n + 1) :=
  (CompletedTensorPower.succEquiv 𝕜 H n).symm.toLinearIsometry.toContinuousLinearMap ∘L
    (T.rTensor (CompletedTensorPower 𝕜 H n)).completion ∘L
      (CompletedTensorPower.succEquiv 𝕜 H n).toLinearIsometry.toContinuousLinearMap

private theorem succEquiv_stepGauge (T : H →L[𝕜] H) (n : ℕ)
    (x : CompletedTensorPower 𝕜 H (n + 1)) :
    CompletedTensorPower.succEquiv 𝕜 H n (stepGauge T n x) =
      (T.rTensor (CompletedTensorPower 𝕜 H n)).completion
        (CompletedTensorPower.succEquiv 𝕜 H n x) := by
  simp [stepGauge]

private theorem stepGauge_symm_coe (T : H →L[𝕜] H) (n : ℕ)
    (z : H ⊗[𝕜] CompletedTensorPower 𝕜 H n) :
    stepGauge T n ((CompletedTensorPower.succEquiv 𝕜 H n).symm z) =
      (CompletedTensorPower.succEquiv 𝕜 H n).symm (T.rTensor (CompletedTensorPower 𝕜 H n) z) := by
  simp [stepGauge]

private theorem stepGauge_ext {n : ℕ}
    {A B : CompletedTensorPower 𝕜 H (n + 1) →L[𝕜] CompletedTensorPower 𝕜 H (n + 1)}
    (h : ∀ z : H ⊗[𝕜] CompletedTensorPower 𝕜 H n,
      A ((CompletedTensorPower.succEquiv 𝕜 H n).symm z) =
        B ((CompletedTensorPower.succEquiv 𝕜 H n).symm z)) :
    A = B := by
  ext x : 1
  rw [← (CompletedTensorPower.succEquiv 𝕜 H n).symm_apply_apply x]
  exact Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
    (isClosed_eq (by fun_prop) (by fun_prop)) h

private theorem norm_stepGauge_apply_le (T : H →L[𝕜] H) (n : ℕ)
    (x : CompletedTensorPower 𝕜 H (n + 1)) :
    ‖stepGauge T n x‖ ≤ ‖T‖ * ‖x‖ := by
  rw [← (CompletedTensorPower.succEquiv 𝕜 H n).norm_map (stepGauge T n x),
    succEquiv_stepGauge, ← (CompletedTensorPower.succEquiv 𝕜 H n).norm_map x]
  refine Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
      (isClosed_le (by fun_prop) (continuous_const.mul continuous_norm)) fun z => ?_
  rw [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe, Completion.norm_coe]
  exact ((T.rTensor _).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (T.norm_rTensor_le _) (norm_nonneg z))

private theorem stepGauge_add (S T : H →L[𝕜] H) (n : ℕ) :
    stepGauge (S + T) n = stepGauge S n + stepGauge T n :=
  stepGauge_ext fun z => by simp [stepGauge_symm_coe, Completion.coe_add]

private theorem stepGauge_smul (c : 𝕜) (T : H →L[𝕜] H) (n : ℕ) :
    stepGauge (c • T) n = c • stepGauge T n :=
  stepGauge_ext fun z => by simp [stepGauge_symm_coe, Completion.coe_smul]

private theorem stepGauge_id (n : ℕ) :
    stepGauge (ContinuousLinearMap.id 𝕜 H) n = .id 𝕜 _ :=
  stepGauge_ext fun z => by simp [stepGauge_symm_coe]

private theorem stepGauge_comp (S T : H →L[𝕜] H) (n : ℕ) :
    stepGauge (S ∘L T) n = stepGauge S n ∘L stepGauge T n :=
  stepGauge_ext fun z => by simp [stepGauge_symm_coe, ContinuousLinearMap.rTensor_comp]

private def gaugeCoord (T : H →L[𝕜] H) :
    ∀ n, CompletedTensorPower 𝕜 H n →L[𝕜] CompletedTensorPower 𝕜 H n
  | 0 => 0
  | n + 1 => stepGauge T n

private theorem norm_gaugeCoord_le (T : H →L[𝕜] H) : ∀ n, ‖gaugeCoord T n‖ ≤ ‖T‖
  | 0 => by simp [gaugeCoord]
  | n + 1 => opNorm_le_bound _ (norm_nonneg T) (norm_stepGauge_apply_le T n)

/-- The *free* (or *left*) *gauge* (*conservation*) operator `Λ(T)` on `FullFockSpace 𝕜 H`
associated with a bounded operator `T : H →L[𝕜] H`. It kills the vacuum (`T.gauge vacuum = 0`) and
acts as `T ⊗ id` on the first tensor factor of each positive tensor grade. -/
def gauge (T : H →L[𝕜] H) : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  lp.mapCLM 2 (gaugeCoord T) (norm_nonneg T) (norm_gaugeCoord_le T)

@[simp]
theorem gauge_apply_zero (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    (T.gauge x) 0 = 0 := by
  simp [gauge, gaugeCoord]

private theorem gauge_apply_succ_eq_stepGauge (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) (n : ℕ) :
    (T.gauge x) (n + 1) = stepGauge T n (x (n + 1)) := by
  simp [gauge, gaugeCoord]

theorem gauge_apply_succ (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) (n : ℕ) :
    (T.gauge x) (n + 1) =
      (CompletedTensorPower.succEquiv 𝕜 H n).symm
        ((T.rTensor (CompletedTensorPower 𝕜 H n)).completion
          (CompletedTensorPower.succEquiv 𝕜 H n (x (n + 1)))) := by
  simp [gauge_apply_succ_eq_stepGauge, stepGauge]

/-- The free gauge operator `Λ(T)` kills the vacuum vector. -/
@[simp]
theorem gauge_vacuum (T : H →L[𝕜] H) : T.gauge (vacuum : FullFockSpace 𝕜 H) = 0 := by
  ext (_ | n) <;> simp [gauge_apply_succ_eq_stepGauge]

@[simp]
theorem gauge_comp_vacuumProj (T : H →L[𝕜] H) :
    T.gauge ∘L vacuumProj = 0 := by
  ext x : 1
  simp [vacuumProj_apply]

@[simp]
theorem inner_vacuum_gauge (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    ⟪vacuum, T.gauge x⟫_𝕜 = 0 := by
  simp [inner_vacuum_left]

@[simp]
theorem inner_gauge_vacuum (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    ⟪T.gauge x, vacuum⟫_𝕜 = 0 := by
  rw [← inner_conj_symm, inner_vacuum_gauge, map_zero]

@[simp]
theorem vacuumProj_gauge (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    vacuumProj (T.gauge x) = 0 := by
  simp [vacuumProj_apply]

@[simp]
theorem vacuumProj_comp_gauge (T : H →L[𝕜] H) :
    vacuumProj ∘L T.gauge = 0 :=
  ContinuousLinearMap.ext (vacuumProj_gauge T)

@[simp]
theorem gauge_creation (T : H →L[𝕜] H) (h : H) (x : FullFockSpace 𝕜 H) :
    T.gauge (creation 𝕜 h x) = creation 𝕜 (T h) x := by
  ext (_ | n)
  · simp
  · simp [gauge_apply_succ]

/-- Left-composing `creation 𝕜 h` with `T.gauge` applies `T` to the created vector `h`. -/
@[simp]
theorem gauge_comp_creation (T : H →L[𝕜] H) (h : H) :
    T.gauge ∘L creation 𝕜 h = creation 𝕜 (T h) :=
  ContinuousLinearMap.ext (gauge_creation T h)

/-- The free gauge operator `Λ(T)` has exact operator norm `‖T‖`. -/
@[simp]
theorem norm_gauge (T : H →L[𝕜] H) : ‖T.gauge‖ = ‖T‖ := by
  refine le_antisymm (lp.norm_mapCLM_le 2 _ (norm_nonneg T) _) ?_
  refine opNorm_le_bound _ (norm_nonneg T.gauge) fun h => ?_
  calc
    ‖T h‖ = ‖creation 𝕜 (T h) (vacuum : FullFockSpace 𝕜 H)‖ := by simp
    _ = ‖T.gauge (creation 𝕜 h (vacuum : FullFockSpace 𝕜 H))‖ := by rw [gauge_creation]
    _ ≤ ‖T.gauge‖ * ‖creation 𝕜 h (vacuum : FullFockSpace 𝕜 H)‖ := T.gauge.le_opNorm _
    _ = ‖T.gauge‖ * ‖h‖ := by simp

@[simp]
theorem gauge_add (S T : H →L[𝕜] H) : (S + T).gauge = S.gauge + T.gauge := by
  ext x (_ | n)
  · simp
  · simpa [gauge_apply_succ_eq_stepGauge] using
      congrArg (fun R => R (x (n + 1))) (stepGauge_add S T n)

@[simp]
theorem gauge_smul (c : 𝕜) (T : H →L[𝕜] H) : (c • T).gauge = c • T.gauge := by
  ext x (_ | n)
  · simp
  · simpa [gauge_apply_succ_eq_stepGauge] using
      congrArg (fun R => R (x (n + 1))) (stepGauge_smul c T n)

end Gauge

end ContinuousLinearMap

namespace TauCeti.FullFockSpace

/-- The free gauge representation `T ↦ Λ(T)` as a linear isometric embedding. -/
def gaugeₗᵢ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    (H →L[𝕜] H) →ₗᵢ[𝕜] FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H where
  toFun := ContinuousLinearMap.gauge
  map_add' := ContinuousLinearMap.gauge_add
  map_smul' := ContinuousLinearMap.gauge_smul
  norm_map' := ContinuousLinearMap.norm_gauge

@[simp]
theorem gaugeₗᵢ_apply {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (T : H →L[𝕜] H) :
    gaugeₗᵢ 𝕜 H T = T.gauge :=
  (rfl)

end TauCeti.FullFockSpace

namespace ContinuousLinearMap

section GaugeAlgebra

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem gauge_zero : (0 : H →L[𝕜] H).gauge = 0 :=
  (gaugeₗᵢ 𝕜 H).map_zero

@[simp]
theorem gauge_neg (T : H →L[𝕜] H) : (-T).gauge = -T.gauge :=
  (gaugeₗᵢ 𝕜 H).map_neg T

@[simp]
theorem gauge_sub (S T : H →L[𝕜] H) : (S - T).gauge = S.gauge - T.gauge :=
  (gaugeₗᵢ 𝕜 H).map_sub S T

/-- `Λ(id)` is the orthogonal projection `1 - vacuumProj` onto the positive-grade Fock subspace. -/
@[simp]
theorem gauge_id :
    (ContinuousLinearMap.id 𝕜 H).gauge = 1 - vacuumProj := by
  ext x (_ | n)
  · simp
  · rw [gauge_apply_succ_eq_stepGauge, sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply,
      vacuumProj_apply_succ, sub_zero]
    exact DFunLike.congr_fun (stepGauge_id (𝕜 := 𝕜) (H := H) n) (x (n + 1))

@[simp]
theorem gauge_one :
    (1 : H →L[𝕜] H).gauge = 1 - vacuumProj :=
  gauge_id

/-- The free gauge map is multiplicative: `Λ(S ∘L T) = Λ(S) ∘L Λ(T)`. -/
@[simp]
theorem gauge_comp (S T : H →L[𝕜] H) : (S ∘L T).gauge = S.gauge ∘L T.gauge := by
  ext x (_ | n)
  · simp
  · simpa [gauge_apply_succ_eq_stepGauge] using
      congrArg (fun R => R (x (n + 1))) (stepGauge_comp S T n)

@[simp]
theorem gauge_mul (S T : H →L[𝕜] H) : (S * T).gauge = S.gauge * T.gauge :=
  gauge_comp S T

section CompleteSpace

variable [CompleteSpace H]

private theorem inner_stepGauge (T : H →L[𝕜] H) (n : ℕ)
    (x y : CompletedTensorPower 𝕜 H (n + 1)) :
    ⟪stepGauge T n x, y⟫_𝕜 = ⟪x, stepGauge T.adjoint n y⟫_𝕜 := by
  rw [← (CompletedTensorPower.succEquiv 𝕜 H n).inner_map_map (stepGauge T n x) y,
    ← (CompletedTensorPower.succEquiv 𝕜 H n).inner_map_map x (stepGauge T.adjoint n y),
    succEquiv_stepGauge, succEquiv_stepGauge]
  refine Completion.induction_on₂ (CompletedTensorPower.succEquiv 𝕜 H n x)
      (CompletedTensorPower.succEquiv 𝕜 H n y)
      (isClosed_eq (by fun_prop) (by fun_prop)) fun u v => ?_
  rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
    Completion.inner_coe, Completion.inner_coe]
  refine TensorProduct.inductionOn u (fun a w => ?_) (fun u₁ u₂ hu₁ hu₂ => ?_)
  · refine TensorProduct.inductionOn v (fun b z => ?_) (fun v₁ v₂ hv₁ hv₂ => ?_)
    · rw [ContinuousLinearMap.rTensor_tmul, ContinuousLinearMap.rTensor_tmul,
        TensorProduct.inner_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_right]
    · rw [map_add, inner_add_right, inner_add_right, hv₁, hv₂]
  · rw [map_add, inner_add_left, inner_add_left, hu₁, hu₂]

/-- When `H` is complete, the free gauge representation commutes with taking Hilbert-space
adjoints. -/
@[simp]
theorem adjoint_gauge (T : H →L[𝕜] H) : T.gauge.adjoint = T.adjoint.gauge := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left 𝕜 fun x => ?_
  have hs₁ : Summable fun i => ⟪(T.gauge x) i, y i⟫_𝕜 :=
    lp.summable_inner (𝕜 := 𝕜) (T.gauge x) y
  have hs₂ : Summable fun i => ⟪x i, (T.adjoint.gauge y) i⟫_𝕜 :=
    lp.summable_inner (𝕜 := 𝕜) x (T.adjoint.gauge y)
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum, lp.inner_eq_tsum,
    hs₁.tsum_eq_zero_add, hs₂.tsum_eq_zero_add]
  simp only [gauge_apply_zero, inner_zero_left, inner_zero_right, zero_add]
  congr 1
  ext n
  rw [gauge_apply_succ_eq_stepGauge, gauge_apply_succ_eq_stepGauge]
  exact inner_stepGauge T n (x (n + 1)) (y (n + 1))

@[simp]
theorem star_gauge (T : H →L[𝕜] H) : star T.gauge = (star T).gauge :=
  adjoint_gauge T

end CompleteSpace

end GaugeAlgebra

end ContinuousLinearMap

namespace TauCeti.FullFockSpace

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem norm_one_sub_vacuumProj [Nontrivial H] :
    ‖(1 : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) - vacuumProj‖ = 1 := by
  rw [← ContinuousLinearMap.gauge_one, ContinuousLinearMap.norm_gauge, norm_one]

section CompleteSpace

variable [CompleteSpace H]

@[simp]
theorem annihilation_comp_gauge (h : H) (T : H →L[𝕜] H) :
    annihilation 𝕜 h ∘L T.gauge = annihilation 𝕜 (T.adjoint h) := by
  rw [← ContinuousLinearMap.adjoint_adjoint (annihilation 𝕜 h ∘L T.gauge),
    ContinuousLinearMap.adjoint_comp, T.adjoint_gauge, adjoint_annihilation,
    T.adjoint.gauge_comp_creation, adjoint_creation]

@[simp]
theorem annihilation_gauge (h : H) (T : H →L[𝕜] H) (x : FullFockSpace 𝕜 H) :
    annihilation 𝕜 h (T.gauge x) = annihilation 𝕜 (T.adjoint h) x :=
  DFunLike.congr_fun (annihilation_comp_gauge h T) x

end CompleteSpace

end TauCeti.FullFockSpace
