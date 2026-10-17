/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Hilbert–Schmidt energy and approximation numbers

For a bounded operator `T : E →L[𝕜] F` from a Hilbert space to an inner product space and a
Hilbert basis `(bᵢ)` of the source, the Hilbert–Schmidt energy `E_b(T) = ∑' i, ‖T bᵢ‖ₑ²` is
defined by an orthonormal expansion, without any spectral theory. This file proves that it is the
sum of the squares of the approximation numbers:

`∑' n, aₙ(T)² = E_b(T)` in `ℝ≥0∞`.

So the Hilbert–Schmidt class, defined through columns, is the class of operators whose
approximation-number sequence is square-summable, and the Hilbert–Schmidt norm is the `ℓ²` norm of
that sequence. This is the `p = 2` case of the identification of Schatten classes defined by
approximation numbers with their concrete models.

Both inequalities go through finite-dimensional compressions. For a finite-dimensional subspace
`V ≤ E`, the compression `C : V → T(V)`, `C x = P_{T(V)} (T x)`, has approximation numbers at most
those of `T` and energy at most that of `T`. Between finite-dimensional spaces, Eckart–Young
identifies the approximation numbers of `C` with its singular values, and the energy of `C` is the
square of its Frobenius seminorm, the sum of the squared singular values.

* `E_b(T) ≤ ∑' n, aₙ(T)²`: each finite partial sum `∑_{i ∈ s} ‖T bᵢ‖²` is the energy of the
  compression of `T` to the span of the `bᵢ` with `i ∈ s`. This direction needs no completeness.
* `∑' n, aₙ(T)² ≤ E_b(T)`: on a complete source, the converse min–max localization supplies, for
  every `k` and `δ > 0`, a compression `C` with `aₙ(T) ≤ aₙ(C) + δ` for all `n < k`. Letting
  `δ → 0` bounds every partial sum `∑_{n < k} aₙ(T)²` by `E_b(T)`.

## Main results

* `ContinuousLinearMap.hilbertSchmidtEnergy_le_tsum_singularValue_sq`: `E_b(T) ≤ ∑' n, aₙ(T)²`.
* `ContinuousLinearMap.tsum_singularValue_sq_le_hilbertSchmidtEnergy`: `∑' n, aₙ(T)² ≤ E_b(T)`.
* `ContinuousLinearMap.tsum_singularValue_sq_eq_hilbertSchmidtEnergy`: `∑' n, aₙ(T)² = E_b(T)`.
* `ContinuousLinearMap.hilbertSchmidtEnergy_ne_top_iff_summable_singularValue_sq`: `T` has finite
  energy exactly when `n ↦ aₙ(T)²` is summable.
* `ContinuousLinearMap.sq_hilbertSchmidtNorm_eq_tsum_singularValue_sq`:
  `‖T‖_HS² = ∑' n, aₙ(T)²`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* B. Simon, *Trace Ideals and Their Applications*, second edition, Mathematical Surveys and
  Monographs 120, American Mathematical Society, 2005, Section 2.
-/

public section

open Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace ContinuousLinearMap

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Between finite-dimensional spaces, the energy is the sum of the squared approximation numbers:
both are the sum of the squared singular values, by Eckart–Young and the singular-value form of
the Frobenius seminorm. -/
private theorem tsum_singularValue_sq_eq_hilbertSchmidtEnergy_of_finiteDimensional
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    ∑' n, (T.singularValue n : ℝ≥0∞) ^ 2 = T.hilbertSchmidtEnergy b := by
  have := FiniteDimensional.complete 𝕜 F
  set σ := (T : E →ₗ[𝕜] F).singularValues
  have hσ (n : ℕ) : (T.singularValue n : ℝ≥0∞) ^ 2 = ENNReal.ofReal (σ n ^ 2) := by
    rw [← T.singularValue_eq_linearMap_singularValues, ENNReal.ofReal_pow NNReal.zero_le_coe,
      ENNReal.ofReal_coe_nnreal]
  have hs : 0 ≤ σ.sum fun _ s ↦ s ^ 2 := Finsupp.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [hilbertSchmidtEnergy_eq_ofReal_sq_frobenius,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    Real.sq_sqrt hs, tsum_congr hσ,
    tsum_eq_sum (s := σ.support) fun n hn ↦ by simp [Finsupp.notMem_support_iff.mp hn],
    Finsupp.sum, ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ sq_nonneg _]

/-- Compressing `T` to a finite-dimensional subspace `V` of the source, with values in `T(V)`,
does not increase approximation numbers. -/
private theorem singularValue_compression_le (T : E →L[𝕜] F) (V : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 V] (n : ℕ) :
    ((V.map (T : E →ₗ[𝕜] F)).orthogonalProjectionOnto.comp (T.comp V.subtypeL)).singularValue n ≤
      T.singularValue n := by
  have hP : ‖(V.map (T : E →ₗ[𝕜] F)).orthogonalProjectionOnto‖₊ ≤ 1 := by
    exact_mod_cast Submodule.orthogonalProjectionOnto_norm_le _
  have hι : ‖V.subtypeL‖₊ ≤ 1 := by exact_mod_cast Submodule.norm_subtypeL_le V
  calc _ ≤ _ := singularValue_comp_comp_le _ T _ n
    _ ≤ 1 * T.singularValue n * 1 := by gcongr
    _ = T.singularValue n := by rw [one_mul, mul_one]

/-- **Lower half of the Hilbert–Schmidt reconciliation.** The Hilbert–Schmidt energy is at most the
sum of the squared approximation numbers: `E_b(T) ≤ ∑' n, aₙ(T)²`. No completeness is needed. -/
theorem hilbertSchmidtEnergy_le_tsum_singularValue_sq (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b ≤ ∑' n, (T.singularValue n : ℝ≥0∞) ^ 2 := by
  classical
  rw [hilbertSchmidtEnergy_def, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  -- The partial sum over `s` is the energy of the compression of `T` to the span of the `bᵢ`,
  -- `i ∈ s`, computed in the orthonormal basis formed by these `bᵢ`.
  set V : Submodule 𝕜 E := Submodule.span 𝕜 (s.image b : Set E)
  set W : Submodule 𝕜 F := V.map (T : E →ₗ[𝕜] F)
  set c := OrthonormalBasis.span b.orthonormal s
  set C : V →L[𝕜] W := W.orthogonalProjectionOnto.comp (T.comp V.subtypeL)
  have hC (i : s) : ‖C (c i)‖ₑ = ‖T (b i)‖ₑ := by
    have hW : T (c i : E) ∈ W := Submodule.mem_map_of_mem (c i).2
    rw [← ofReal_norm, ← ofReal_norm, comp_apply, comp_apply, Submodule.subtypeL_apply,
      W.norm_orthogonalProjectionOnto_apply hW, OrthonormalBasis.span_apply]
  calc ∑ i ∈ s, ‖T (b i)‖ₑ ^ 2 = C.hilbertSchmidtEnergy c.toHilbertBasis := by
        rw [hilbertSchmidtEnergy_def, tsum_fintype, ← Finset.sum_coe_sort s]
        simp_rw [c.coe_toHilbertBasis, hC]
    _ = ∑' n, (C.singularValue n : ℝ≥0∞) ^ 2 :=
        (tsum_singularValue_sq_eq_hilbertSchmidtEnergy_of_finiteDimensional C _).symm
    _ ≤ ∑' n, (T.singularValue n : ℝ≥0∞) ^ 2 := by
        gcongr with n
        exact T.singularValue_compression_le V n

variable [CompleteSpace E]

/-- Compressing `T` to a finite-dimensional subspace `V` of the source, with values in `T(V)`,
does not increase the Hilbert–Schmidt energy. -/
private theorem hilbertSchmidtEnergy_compression_le (T : E →L[𝕜] F) (V : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 V] {κ : Type*} (c : HilbertBasis κ 𝕜 V) (b : HilbertBasis ι 𝕜 E) :
    ((V.map (T : E →ₗ[𝕜] F)).orthogonalProjectionOnto.comp
      (T.comp V.subtypeL)).hilbertSchmidtEnergy c ≤ T.hilbertSchmidtEnergy b := by
  set W := V.map (T : E →ₗ[𝕜] F)
  have := FiniteDimensional.complete 𝕜 W
  have hP : ‖W.orthogonalProjectionOnto‖ₑ ≤ 1 := by
    rw [enorm_eq_nnnorm, ENNReal.coe_le_one_iff]
    exact_mod_cast Submodule.orthogonalProjectionOnto_norm_le _
  have hι : ‖V.subtypeL‖ₑ ≤ 1 := by
    rw [enorm_eq_nnnorm, ENNReal.coe_le_one_iff]
    exact_mod_cast Submodule.norm_subtypeL_le V
  -- The middle space of `(P_W ∘ T) ∘ ι_V` is the complete source `E`, so `F` need not be complete.
  rw [← comp_assoc]
  calc _ ≤ _ := hilbertSchmidtEnergy_comp_le_right _ V.subtypeL c b
    _ ≤ ‖W.orthogonalProjectionOnto‖ₑ ^ 2 * T.hilbertSchmidtEnergy b * ‖V.subtypeL‖ₑ ^ 2 := by
        gcongr; exact hilbertSchmidtEnergy_comp_le_left _ T b
    _ ≤ 1 ^ 2 * T.hilbertSchmidtEnergy b * 1 ^ 2 := by gcongr
    _ = T.hilbertSchmidtEnergy b := by rw [one_pow, one_mul, mul_one]

/-- The partial sums of `n ↦ aₙ(T)²` exceed the energy by at most a multiple of any `δ ∈ (0, 1]`:
`∑_{n < k} aₙ(T)² ≤ E_b(T) + δ ∑_{n < k} (2 aₙ(T) + 1)`. -/
private theorem sum_range_singularValue_sq_le (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) (k : ℕ)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∑ n ∈ Finset.range k, (T.singularValue n : ℝ≥0∞) ^ 2 ≤ T.hilbertSchmidtEnergy b +
      ((δ * ∑ n ∈ Finset.range k, (2 * T.singularValue n + 1) : ℝ≥0) : ℝ≥0∞) := by
  -- A compression `C` with `aₙ(T) ≤ aₙ(C) + δ` for `n < k` gives
  -- `aₙ(T)² ≤ aₙ(C)² + δ (2 aₙ(T) + 1)`, while `∑ₙ aₙ(C)² = E(C) ≤ E_b(T)`.
  obtain ⟨V, _, hV⟩ := (TauCeti.HasMinMaxLowerBound.of_completeSpace (𝕜 := 𝕜) (E := E)
    (F := F)).exists_singularValue_le_compression T k (δ := δ) (by exact_mod_cast hδ)
  set C := (V.map (T : E →ₗ[𝕜] F)).orthogonalProjectionOnto.comp (T.comp V.subtypeL)
  have hCE : ∑ n ∈ Finset.range k, (C.singularValue n : ℝ≥0∞) ^ 2 ≤
      T.hilbertSchmidtEnergy b := by
    set c := (stdOrthonormalBasis 𝕜 V).toHilbertBasis
    calc _ ≤ ∑' n, (C.singularValue n : ℝ≥0∞) ^ 2 := ENNReal.sum_le_tsum _
      _ = C.hilbertSchmidtEnergy c :=
          tsum_singularValue_sq_eq_hilbertSchmidtEnergy_of_finiteDimensional C c
      _ ≤ _ := T.hilbertSchmidtEnergy_compression_le V c b
  have hpt (n : ℕ) (hn : n ∈ Finset.range k) : (T.singularValue n : ℝ≥0∞) ^ 2 ≤
      (C.singularValue n : ℝ≥0∞) ^ 2 + ((δ * (2 * T.singularValue n + 1) : ℝ≥0) : ℝ≥0∞) := by
    have h₁ := hV n (Finset.mem_range.mp hn)
    have h₂ : (C.singularValue n : ℝ) ≤ T.singularValue n := T.singularValue_compression_le V n
    have hδ1' : (δ : ℝ) ≤ 1 := hδ1
    rw [← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_add, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe]
    push_cast
    nlinarith [(T.singularValue n).coe_nonneg, (C.singularValue n).coe_nonneg, δ.coe_nonneg]
  calc _ ≤ ∑ n ∈ Finset.range k, ((C.singularValue n : ℝ≥0∞) ^ 2 +
        ((δ * (2 * T.singularValue n + 1) : ℝ≥0) : ℝ≥0∞)) := Finset.sum_le_sum hpt
    _ = ∑ n ∈ Finset.range k, (C.singularValue n : ℝ≥0∞) ^ 2 +
        ((δ * ∑ n ∈ Finset.range k, (2 * T.singularValue n + 1) : ℝ≥0) : ℝ≥0∞) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, ENNReal.ofNNReal_finsetSum]
    _ ≤ _ := by gcongr

/-- **Upper half of the Hilbert–Schmidt reconciliation.** For a bounded operator from a Hilbert
space to an inner product space, the sum of the squared approximation numbers is at most the
Hilbert–Schmidt energy: `∑' n, aₙ(T)² ≤ E_b(T)`. -/
theorem tsum_singularValue_sq_le_hilbertSchmidtEnergy (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    ∑' n, (T.singularValue n : ℝ≥0∞) ^ 2 ≤ T.hilbertSchmidtEnergy b := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun k ↦ ?_
  set K : ℝ≥0 := ∑ n ∈ Finset.range k, (2 * T.singularValue n + 1)
  -- Let `δ → 0` in `sum_range_singularValue_sq_le`.
  have hcont : Continuous fun δ : ℝ≥0 ↦ T.hilbertSchmidtEnergy b + ((δ * K : ℝ≥0) : ℝ≥0∞) :=
    continuous_const.add (ENNReal.continuous_coe.comp (continuous_id.mul continuous_const))
  have hlim : Tendsto (fun δ : ℝ≥0 ↦ T.hilbertSchmidtEnergy b + ((δ * K : ℝ≥0) : ℝ≥0∞))
      (𝓝[>] 0) (𝓝 (T.hilbertSchmidtEnergy b)) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with δ hδ
  using T.sum_range_singularValue_sq_le b k hδ.1 hδ.2

/-- **Hilbert–Schmidt reconciliation.** For a bounded operator from a Hilbert space to an inner
product space and any Hilbert basis `(bᵢ)` of the source, the sum of the squared approximation
numbers is the Hilbert–Schmidt energy: `∑' n, aₙ(T)² = ∑' i, ‖T bᵢ‖²` in `ℝ≥0∞`. -/
theorem tsum_singularValue_sq_eq_hilbertSchmidtEnergy (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    ∑' n, (T.singularValue n : ℝ≥0∞) ^ 2 = T.hilbertSchmidtEnergy b :=
  (T.tsum_singularValue_sq_le_hilbertSchmidtEnergy b).antisymm
    (T.hilbertSchmidtEnergy_le_tsum_singularValue_sq b)

/-- An operator from a Hilbert space to an inner product space has finite Hilbert–Schmidt energy
exactly when its approximation numbers are square-summable. -/
theorem hilbertSchmidtEnergy_ne_top_iff_summable_singularValue_sq (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b ≠ ∞ ↔ Summable fun n ↦ (T.singularValue n : ℝ) ^ 2 := by
  rw [← T.tsum_singularValue_sq_eq_hilbertSchmidtEnergy b]
  simp_rw [← ENNReal.coe_pow, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe,
    NNReal.coe_pow]

/-- The square of the Hilbert–Schmidt norm is the sum of the squared approximation numbers,
`‖T‖_HS² = ∑' n, aₙ(T)²`. When `T` has infinite energy both sides are `0`. -/
theorem sq_hilbertSchmidtNorm_eq_tsum_singularValue_sq [CompleteSpace F] (T : E →L[𝕜] F) :
    T.hilbertSchmidtNorm ^ 2 = ∑' n, (T.singularValue n : ℝ) ^ 2 := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [T.sq_hilbertSchmidtNorm b, ← T.tsum_singularValue_sq_eq_hilbertSchmidtEnergy b,
    ENNReal.tsum_toReal_eq fun _ ↦ ENNReal.pow_ne_top ENNReal.coe_ne_top]
  simp

end ContinuousLinearMap
