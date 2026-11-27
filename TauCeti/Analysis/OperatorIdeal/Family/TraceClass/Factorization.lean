/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Columns
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Schmidt
public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass

/-!
# Trace-class operators are products of two Hilbert–Schmidt operators

Let `T : E →L[𝕜] F` be a compact operator between Hilbert spaces and let `(bᵢ)` be a Hilbert
basis of `E` whose images `T bᵢ` are pairwise orthogonal, as supplied by
`IsCompactOperator.exists_hilbertBasis_pairwise_inner_eq_zero`. The norms `σᵢ = ‖T bᵢ‖` are the
singular values of `T` with multiplicity, so the nuclear gauge of `T` is their sum,

`ν(T) = ∑ᵢ ‖T bᵢ‖`.

The upper bound comes from the Schmidt series `T = ∑ᵢ ⟪bᵢ, ·⟫ T bᵢ` and the Fatou inequality for
the nuclear gauge; the lower bound compares every finite sum of the `σᵢ` with an initial sum of
their decreasing rearrangement, which is the sequence of approximation numbers of `T`.

If `T` is trace class, the `σᵢ` are summable, and `T` factors through its square-root modulus:
`T = B C` with

`C bᵢ = √σᵢ bᵢ` and `B bᵢ = σᵢ^(-1/2) T bᵢ` (and `B bᵢ = 0` when `σᵢ = 0`).

Both families of columns have norms `√σᵢ`, so `B` and `C` are the operators represented by `ℓ²`
column families (`HilbertBasis.columnOperator`), and both have Hilbert–Schmidt energy
`∑ᵢ σᵢ = ν(T)`. In particular the factorization is sharp: `‖T‖₁ = ‖B‖₂ ‖C‖₂`.

## Main results

* `HilbertBasis.nuclearENorm_eq_tsum_enorm_apply`: for a compact operator sending a Hilbert basis
  to pairwise orthogonal vectors, `ν(T) = ∑ᵢ ‖T bᵢ‖ₑ`.
* `ContinuousLinearMap.exists_comp_eq_gauge_hilbertSchmidt_eq`: every trace-class operator is a
  composition `B ∘L C` whose factors both have Hilbert–Schmidt gauge `ν(T)^(1/2)`.
* `ContinuousLinearMap.exists_comp_eq_of_mem_traceClass`: every trace-class operator is a
  composition of two Hilbert–Schmidt operators.
* `ContinuousLinearMap.exists_comp_eq_toReal_nuclearENorm_eq_mul`: the factors can be chosen with
  `‖T‖₁ = ‖B‖₂ ‖C‖₂`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

open InnerProductSpace TauCeti TauCeti.OperatorIdealFamily
open scoped InnerProductSpace ENNReal NNReal lp

universe u v w

namespace HilbertBasis

variable {𝕜 ι E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] F}

/-- **The nuclear gauge in a Schmidt basis.** If `T` is compact and sends the Hilbert basis
`(bᵢ)` to pairwise orthogonal vectors, then its nuclear gauge is the sum of the norms of these
images: `ν(T) = ∑ᵢ ‖T bᵢ‖ₑ`. -/
theorem nuclearENorm_eq_tsum_enorm_apply (hTc : IsCompactOperator T)
    (hT : Pairwise fun i j ↦ ⟪T (b i), T (b j)⟫_𝕜 = 0) :
    T.nuclearENorm = ∑' i, ‖T (b i)‖ₑ := by
  refine le_antisymm ?_ ?_
  · -- The Schmidt series `T = ∑ᵢ ⟪bᵢ, ·⟫ T bᵢ` has rank-one terms of gauge `‖T bᵢ‖`.
    refine (ContinuousLinearMap.nuclearENorm_le_tsum_of_hasSum (b.hasSum_rankOne hTc hT)).trans_eq
      (tsum_congr fun i ↦ ?_)
    rw [ContinuousLinearMap.nuclearENorm_rankOne, ← ofReal_norm (b i), b.orthonormal.1 i,
      ENNReal.ofReal_one, mul_one]
  · -- Every finite sum of the `‖T bᵢ‖` is bounded by an initial sum of approximation numbers.
    have hbdd : BddAbove (Set.range fun i ↦ ‖T (b i)‖) := ⟨‖T‖, by
      rintro _ ⟨i, rfl⟩
      simpa [b.orthonormal.1 i] using T.le_opNorm (b i)⟩
    rw [tsum_eq_iSup_sum]
    refine iSup_le fun s ↦ ?_
    calc ∑ i ∈ s, ‖T (b i)‖ₑ = ENNReal.ofReal (∑ i ∈ s, ‖T (b i)‖) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _]
          simp only [ofReal_norm]
      _ ≤ ENNReal.ofReal (∑ n ∈ Finset.range s.card, (T.singularValue n : ℝ)) := by
          gcongr
          simpa only [b.singularValue_eq_decreasingRearrangement hT] using
            sum_le_sum_decreasingRearrangement hbdd s
      _ = ∑ n ∈ Finset.range s.card, (T.singularValue n : ℝ≥0∞) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ NNReal.coe_nonneg _]
          simp only [ENNReal.ofReal_coe_nnreal]
      _ ≤ T.nuclearENorm := by rw [T.nuclearENorm_def]; exact sum_le_tsum _

end HilbertBasis

namespace ContinuousLinearMap

variable {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A family of vectors with norms `√σᵢ` for summable `σᵢ ≥ 0` is square-summable. -/
private theorem memℓp_two_of_norm_eq_sqrt {ι G : Type*} [NormedAddCommGroup G] {f : ι → G}
    {σ : ι → ℝ} (hσ : Summable σ) (hσ0 : ∀ i, 0 ≤ σ i) (hf : ∀ i, ‖f i‖ = √(σ i)) :
    Memℓp f 2 := by
  refine memℓp_gen ?_
  simpa only [hf, ENNReal.toReal_ofNat, Real.rpow_two, Real.sq_sqrt (hσ0 _)] using hσ

/-- A vector of norm `√‖y‖` has extended squared norm `‖y‖ₑ`. -/
private theorem enorm_sq_of_norm_eq_sqrt {G H : Type*} [NormedAddCommGroup G]
    [NormedAddCommGroup H] {x : G} {y : H} (hx : ‖x‖ = √‖y‖) : ‖x‖ₑ ^ 2 = ‖y‖ₑ := by
  rw [← ofReal_norm, hx, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _),
    ofReal_norm]

/-- **The square-root factorization of a trace-class operator.** A trace-class operator
`T : E →L[𝕜] F` is a composition `T = B ∘L C` of operators `B : E →L[𝕜] F` and `C : E →L[𝕜] E`
whose Hilbert–Schmidt gauges are both `ν(T)^(1/2)`. -/
theorem exists_comp_eq_gauge_hilbertSchmidt_eq {T : E →L[𝕜] F}
    (hT : T ∈ ((traceClass.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    ∃ (B : E →L[𝕜] F) (C : E →L[𝕜] E), B ∘L C = T ∧
      (hilbertSchmidt.{u, v, w} 𝕜).gauge B = T.nuclearENorm ^ (1 / 2 : ℝ) ∧
      (hilbertSchmidt.{u, v, v} 𝕜).gauge C = T.nuclearENorm ^ (1 / 2 : ℝ) := by
  have hν := (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top T).1 hT
  have hTc := isCompactOperator_of_nuclearENorm_ne_top hν
  obtain ⟨s, b, -, hb⟩ := hTc.exists_hilbertBasis_pairwise_inner_eq_zero
  have hνb := b.nuclearENorm_eq_tsum_enorm_apply hTc hb
  set σ : s → ℝ := fun i ↦ ‖T (b i)‖ with hσdef
  have hσ : Summable σ := by
    rw [hνb] at hν
    simpa only [eNorm_eq_nnNorm, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe,
      coe_nnNorm] using hν
  -- The columns of `C` and of `B`, both of norm `√σᵢ`.
  set c : s → E := fun i ↦ ((√(σ i) : ℝ) : 𝕜) • b i
  set g : s → F := fun i ↦ (((√(σ i))⁻¹ : ℝ) : 𝕜) • T (b i)
  have hc (i : s) : ‖c i‖ = √(σ i) := by
    simp [c, norm_smul, b.orthonormal.1 i]
  have hg (i : s) : ‖g i‖ = √(σ i) := by
    simp only [g, norm_smul, RCLike.norm_ofReal, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [inv_mul_eq_div, Real.div_sqrt]
  set C := b.columnOperator ⟨c, memℓp_two_of_norm_eq_sqrt hσ (fun _ ↦ norm_nonneg _) hc⟩
  set B := b.columnOperator ⟨g, memℓp_two_of_norm_eq_sqrt hσ (fun _ ↦ norm_nonneg _) hg⟩
  have hB : (hilbertSchmidt.{u, v, w} 𝕜).gauge B = T.nuclearENorm ^ (1 / 2 : ℝ) := by
    rw [gauge_hilbertSchmidt B b, hilbertSchmidtEnergy_def, hνb]
    simp only [B, b.columnOperator_apply_self]
    exact congrArg (· ^ (1 / 2 : ℝ)) (tsum_congr fun i ↦ enorm_sq_of_norm_eq_sqrt (hg i))
  have hC : (hilbertSchmidt.{u, v, v} 𝕜).gauge C = T.nuclearENorm ^ (1 / 2 : ℝ) := by
    rw [gauge_hilbertSchmidt C b, hilbertSchmidtEnergy_def, hνb]
    simp only [C, b.columnOperator_apply_self]
    exact congrArg (· ^ (1 / 2 : ℝ)) (tsum_congr fun i ↦ enorm_sq_of_norm_eq_sqrt (hc i))
  refine ⟨B, C, b.ext_continuousLinearMap fun i ↦ ?_, hB, hC⟩
  rw [comp_apply]
  simp only [C, B, c, map_smul, b.columnOperator_apply_self, g,
    smul_smul]
  rcases eq_or_ne (σ i) 0 with h0 | h0
  · rw [norm_eq_zero.1 h0, smul_zero]
  · have hs : √(σ i) ≠ 0 := Real.sqrt_ne_zero'.2 ((norm_nonneg _).lt_of_ne' h0)
    rw [← RCLike.ofReal_mul, mul_inv_cancel₀ hs, RCLike.ofReal_one, one_smul]

/-- **Trace-class operators are products of Hilbert–Schmidt operators.** Every trace-class
operator `T : E →L[𝕜] F` is a composition `T = B ∘L C` of Hilbert–Schmidt operators
`B : E →L[𝕜] F` and `C : E →L[𝕜] E`. -/
theorem exists_comp_eq_of_mem_traceClass {T : E →L[𝕜] F}
    (hT : T ∈ ((traceClass.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    ∃ (B : E →L[𝕜] F) (C : E →L[𝕜] E),
      B ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule ∧
      C ∈ ((hilbertSchmidt.{u, v, v} 𝕜).operatorGauge E E).finiteSubmodule ∧ B ∘L C = T := by
  obtain ⟨B, C, hBC, hB, hC⟩ := exists_comp_eq_gauge_hilbertSchmidt_eq hT
  have hν := (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top T).1 hT
  have hlt : T.nuclearENorm ^ (1 / 2 : ℝ) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hν
  refine ⟨B, C, ?_, ?_, hBC⟩
  · rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply, hB]
    exact hlt
  · rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply, hC]
    exact hlt

/-- **The square-root factorization is sharp.** Every trace-class operator `T` factors as
`T = B ∘L C` with `‖T‖₁ = ‖B‖₂ ‖C‖₂`, where `‖T‖₁` is the real value of the nuclear gauge and
`‖·‖₂` is the Hilbert–Schmidt norm. -/
theorem exists_comp_eq_toReal_nuclearENorm_eq_mul {T : E →L[𝕜] F}
    (hT : T ∈ ((traceClass.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    ∃ (B : E →L[𝕜] F) (C : E →L[𝕜] E), B ∘L C = T ∧
      T.nuclearENorm.toReal = B.hilbertSchmidtNorm * C.hilbertSchmidtNorm := by
  obtain ⟨B, C, hBC, hB, hC⟩ := exists_comp_eq_gauge_hilbertSchmidt_eq hT
  refine ⟨B, C, hBC, ?_⟩
  rw [← toReal_gauge_hilbertSchmidt.{u, v, w}, ← toReal_gauge_hilbertSchmidt.{u, v, v}, hB, hC,
    ← ENNReal.toReal_mul, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

end ContinuousLinearMap
