/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Coordinates on `lp`

The characteristic equation for Mathlib's bundled coordinate evaluation lets users compute
with `lp.evalCLM` without unfolding its construction as a bounded linear map, and the ℓ¹ norm is
the sum of the norms of the coordinates (`lp.hasSum_norm_one`). The scalar
coordinate vectors are linearly independent, and vectors in their span vanish outside the
corresponding indices. These algebraic facts hold over normed rings at every exponent. In `ℓ²`,
the squared norm of a finite sum of single-coordinate vectors is the sum of the squared norms of
its coordinates (`lp.norm_sum_single_sq`, and `lp.enorm_sum_single` for the extended norm). It
follows that the operators `v ↦ (aᵢ v)ᵢ` from `F` to `ℓ²(F)` and `(wᵢ) ↦ ∑ᵢ aᵢ wᵢ` from `ℓ²(F)` to
`F`, for finitely many scalars `aᵢ`, have norm at most `‖(aᵢ)‖_{ℓ²}`
(`lp.norm_sum_single_comp_lsmul_le`, `lp.norm_sum_lsmul_comp_evalCLM_le`).
-/

public section

open scoped ENNReal

namespace lp

variable {ι 𝕜 : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
  {p : ℝ≥0∞}

/-- The bundled coordinate evaluation returns the corresponding coordinate. -/
@[simp]
theorem evalCLM_apply [Fact (1 ≤ p)] (i : ι) (x : lp E p) : evalCLM 𝕜 E p i x = x i := (rfl)

/-- The ℓ¹ norm is the sum of the norms of the coordinates. -/
theorem hasSum_norm_one (y : lp E 1) : HasSum (fun i ↦ ‖y i‖) ‖y‖ := by
  simpa using lp.hasSum_norm (p := 1) (by simp) y

section Single

variable [DecidableEq ι]

/-- The scalar coordinate vectors in `lp` are linearly independent. -/
theorem linearIndependent_single_one :
    LinearIndependent 𝕜 (fun i : ι ↦ lp.single p i (1 : 𝕜)) := by
  apply LinearIndependent.of_comp (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype
  have hcoe : (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype ∘
      (fun i : ι ↦ lp.single p i (1 : 𝕜)) = fun i ↦ Pi.single i (1 : 𝕜) := by
    funext i
    exact lp.coeFn_single p i 1
  rw [hcoe]
  exact Pi.linearIndependent_single_one ι 𝕜

/-- A vector in the span of a family of coordinate vectors vanishes outside their indices. -/
theorem apply_eq_zero_of_mem_span_single {κ : Type*} (f : κ → ι) {x : ℓ^p(ι, 𝕜)}
    (hx : x ∈ Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (1 : 𝕜)))
    {i : ι} (hi : i ∉ Set.range f) : x i = 0 := by
  have hle : Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (1 : 𝕜)) ≤
      LinearMap.ker (evalₗ (𝕜 := 𝕜) (fun _ : ι ↦ 𝕜) p i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [evalₗ_apply]
    exact lp.single_apply_ne (E := fun _ : ι ↦ 𝕜) p (f j) 1
      (fun hij ↦ hi ⟨j, hij.symm⟩)
  simpa only [evalₗ_apply] using LinearMap.mem_ker.mp (hle hx)

end Single

/-- The square of the `ℓ²` norm of a finite sum of single-coordinate vectors is the sum of the
squared norms of the coordinates. -/
theorem norm_sum_single_sq {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq ι]
    (f : ∀ i, E i) (s : Finset ι) :
    ‖∑ i ∈ s, lp.single 2 i (f i)‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  simpa [Real.rpow_two] using lp.norm_sum_single (E := E) (p := 2) (by norm_num) f s

/-- The extended `ℓ²` norm of a finite sum of single-coordinate vectors is the square root of the
sum of the squared extended norms of the coordinates. -/
theorem enorm_sum_single {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq ι]
    (f : ∀ i, E i) (s : Finset ι) :
    ‖∑ i ∈ s, lp.single 2 i (f i)‖ₑ = (∑ i ∈ s, ‖f i‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
  have h := congrArg (· ^ (2⁻¹ : ℝ)) (lp.norm_sum_single (E := E) (p := 2) (by norm_num) f s)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_ofNat,
    mul_inv_cancel₀ two_ne_zero, Real.rpow_one] at h
  rw [← ofReal_norm, h, ← ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun _ _ ↦ by positivity) (by norm_num),
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

section Operator

open ContinuousLinearMap

variable {𝕜 R F : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Module R F] [IsBoundedSMul R F]
  [IsScalarTower 𝕜 R F] [DecidableEq ι]

/-- The operator `v ↦ (aᵢ v)ᵢ` from `F` to `ℓ²(F)` has norm at most `‖(aᵢ)‖_{ℓ²}`. -/
theorem norm_sum_single_comp_lsmul_le (s : Finset ι) (a : ι → R) :
    ‖∑ i ∈ s, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ F) 2 i).comp (lsmul 𝕜 R (a i))‖ ≤
      ‖∑ i ∈ s, lp.single 2 i (a i)‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  simp only [sum_apply, coe_comp, Function.comp_apply, lsmul_apply,
    lp.singleContinuousLinearMap_apply]
  rw [lp.norm_sum_single_sq, mul_pow, lp.norm_sum_single_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_smul_le _ _) 2

/-- The operator `(wᵢ) ↦ ∑ᵢ aᵢ wᵢ` from `ℓ²(F)` to `F` has norm at most `‖(aᵢ)‖_{ℓ²}`. -/
theorem norm_sum_lsmul_comp_evalCLM_le (s : Finset ι) (a : ι → R) :
    ‖∑ i ∈ s, (lsmul 𝕜 R (a i)).comp (lp.evalCLM 𝕜 (fun _ : ι ↦ F) 2 i)‖ ≤
      ‖∑ i ∈ s, lp.single 2 i (a i)‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun w ↦ ?_
  have ha : √(∑ i ∈ s, ‖a i‖ ^ 2) = ‖∑ i ∈ s, lp.single 2 i (a i)‖ := by
    rw [← lp.norm_sum_single_sq, Real.sqrt_sq (norm_nonneg _)]
  have hw : √(∑ i ∈ s, ‖w i‖ ^ 2) ≤ ‖w‖ := by
    refine Real.sqrt_le_iff.2 ⟨norm_nonneg _, ?_⟩
    simpa [Real.rpow_two] using lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) w s
  simp only [sum_apply, coe_comp, Function.comp_apply, lsmul_apply, evalCLM_apply]
  calc ‖∑ i ∈ s, a i • w i‖
      ≤ ∑ i ∈ s, ‖a i‖ * ‖w i‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦
        norm_smul_le _ _)
    _ ≤ √(∑ i ∈ s, ‖a i‖ ^ 2) * √(∑ i ∈ s, ‖w i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ ‖∑ i ∈ s, lp.single 2 i (a i)‖ * ‖w‖ := by rw [ha]; gcongr

end Operator

end lp
