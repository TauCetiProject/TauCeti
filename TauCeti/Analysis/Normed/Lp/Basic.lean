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
the sum of the norms of the coordinates (`lp.hasSum_norm_one`, and `lp.hasSum_enorm_one` for
extended norms); for `1 ≤ p` it bounds the `ℓ^p` norm (`lp.norm_le_tsum_norm`). The scalar
coordinate vectors are linearly independent, and vectors in their span vanish outside the
corresponding indices. These algebraic facts hold over normed rings at every exponent. In `ℓ²`,
the squared norm of a finite sum of single-coordinate vectors is the sum of the squared norms of
its coordinates (`lp.norm_sum_single_sq`, and `lp.enorm_sum_single` for the extended norm). It
follows that the operators `v ↦ (aᵢ v)ᵢ` from `F` to `ℓ²(F)` and `(wᵢ) ↦ ∑ᵢ aᵢ wᵢ` from `ℓ²(F)` to
`F`, for finitely many scalars `aᵢ`, have norm at most `‖(aᵢ)‖_{ℓ²}`
(`lp.norm_sum_single_comp_lsmul_le`, `lp.norm_sum_lsmul_comp_evalCLM_le`).

For a finite exponent `p` and a countable index type, `lp E p` is separable as soon as every
`E i` is (`lp.separableSpace`): the finite sums of coordinate vectors with entries in countable
dense subsets are dense.
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

/-- For `1 ≤ p`, the `ℓ^p` norm of a sequence is at most its `ℓ¹` norm. -/
theorem norm_le_tsum_norm [Fact (1 ≤ p)] (f : lp E p)
    (hf : Summable fun i ↦ ‖f i‖) : ‖f‖ ≤ ∑' i, ‖f i‖ := by
  have hC : 0 ≤ ∑' i, ‖f i‖ := tsum_nonneg fun i ↦ norm_nonneg _
  have hle (i : ι) : ‖f i‖ ≤ ∑' i, ‖f i‖ := hf.le_tsum i fun j _ ↦ norm_nonneg _
  rcases eq_or_ne p ∞ with rfl | hp_top
  · exact lp.norm_le_of_forall_le hC hle
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top (Fact.out : 1 ≤ p)
  refine lp.norm_le_of_forall_sum_le (by linarith) hC fun s ↦ ?_
  -- `x ^ p ≤ x * C ^ (p - 1)` for `0 ≤ x ≤ C`, and the `x` sum to at most `C`
  calc ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ∑ i ∈ s, ‖f i‖ * (∑' i, ‖f i‖) ^ (p.toReal - 1) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        calc ‖f i‖ ^ p.toReal = ‖f i‖ * ‖f i‖ ^ (p.toReal - 1) := by
              rw [← Real.rpow_one_add' (norm_nonneg _) (by linarith), add_sub_cancel]
          _ ≤ ‖f i‖ * (∑' i, ‖f i‖) ^ (p.toReal - 1) := by
              gcongr
              exact hle i
    _ = (∑ i ∈ s, ‖f i‖) * (∑' i, ‖f i‖) ^ (p.toReal - 1) := (Finset.sum_mul ..).symm
    _ ≤ (∑' i, ‖f i‖) * (∑' i, ‖f i‖) ^ (p.toReal - 1) := by
        gcongr
        exact hf.sum_le_tsum s fun i _ ↦ norm_nonneg _
    _ = (∑' i, ‖f i‖) ^ p.toReal := by
        rw [← Real.rpow_one_add' hC (by linarith), add_sub_cancel]

/-- The extended ℓ¹ norm is the sum of the extended norms of the coordinates. -/
theorem hasSum_enorm_one (y : lp E 1) : HasSum (fun i ↦ ‖y i‖ₑ) ‖y‖ₑ := by
  simp only [enorm_eq_nnnorm]
  exact ENNReal.hasSum_coe.2 (NNReal.hasSum_coe.1 (hasSum_norm_one y))

/-- For a finite exponent and a countable index type, `lp E p` is separable when every `E i` is.
-/
theorem separableSpace [Countable ι] [∀ i, TopologicalSpace.SeparableSpace (E i)]
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) : TopologicalSpace.SeparableSpace (lp E p) := by
  classical
  set S : Set (lp E p) := ⋃ i, Set.range (lp.single p i)
  have hS : TopologicalSpace.IsSeparable S :=
    .iUnion fun i ↦ TopologicalSpace.isSeparable_range (lp.isometry_single i).continuous
  rw [← TopologicalSpace.isSeparable_univ_iff]
  -- Every element is the limit of the finite sums of its coordinate vectors, which lie in the
  -- additive span of `S`.
  refine (hS.span (R := ℕ)).closure.mono fun f _ ↦
    mem_closure_of_tendsto (lp.hasSum_single hp f) (Filter.Eventually.of_forall fun s ↦ ?_)
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span (Set.mem_iUnion.2 ⟨i, f i, rfl⟩)

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
