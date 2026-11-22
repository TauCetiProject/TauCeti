/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Schmidt
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# The trace of a trace-class operator

Let `E` be a Hilbert space over `𝕜 = ℝ` or `ℂ`. An operator `T : E →L[𝕜] E` is trace class when
its approximation numbers `aₙ(T)` are summable. Its **trace** is the sum of its diagonal entries
along a Hilbert basis `(bᵢ)` of `E`,

`Tr T = ∑ᵢ ⟪bᵢ, T bᵢ⟫`,

and this file proves that the sum converges and does not depend on the basis. The trace is the
functional from which the conditional trace and the Chern characters of finitely summable
Fredholm modules are built, and it pairs the trace class with the bounded operators.

The trace is linear on the trace class and bounded by the trace norm, `|Tr T| ≤ ∑ₙ aₙ(T)`, so it
is a continuous linear functional of norm at most one on the normed trace-class carrier. It is
tracial against bounded operators, `Tr (A T) = Tr (T A)`, it conjugates under the adjoint,
`Tr T† = conj (Tr T)`, and on a finite-dimensional space it is the trace of the underlying linear
map.

## Main definitions

* `ContinuousLinearMap.trace`: the trace of a trace-class operator, with the junk value `0`
  outside the trace class.
* `TauCeti.traceClassTraceCLM`: the trace as a continuous linear functional on the normed
  trace-class carrier.

## Main results

* `HilbertBasis.hasSum_inner_apply_of_hasSum_rankOne`: if `T = ∑ₖ ⟪uₖ, ·⟫ vₖ` with
  `∑ₖ ‖uₖ‖ ‖vₖ‖ < ∞`, the diagonal entries of `T` along any Hilbert basis sum to `∑ₖ ⟪uₖ, vₖ⟫`.
* `ContinuousLinearMap.exists_hasSum_rankOne_of_mem_traceClass`: every trace-class operator is
  such a series, with `∑ₖ ‖uₖ‖ ‖vₖ‖ ≤ ∑ₙ aₙ(T)`.
* `ContinuousLinearMap.hasSum_inner_apply_trace`: `Tr T = ∑ᵢ ⟪bᵢ, T bᵢ⟫` along every Hilbert
  basis.
* `ContinuousLinearMap.trace_eq_tsum_of_hasSum_rankOne`: `Tr T = ∑ₖ ⟪uₖ, vₖ⟫` for every such
  series, and `ContinuousLinearMap.trace_rankOne`: `Tr (⟪y, ·⟫ x) = ⟪y, x⟫`.
* `ContinuousLinearMap.enorm_trace_le`: `|Tr T| ≤ ∑ₙ aₙ(T)`.
* `ContinuousLinearMap.trace_comp_comm`: `Tr (A T) = Tr (T A)` for bounded `A`.
* `ContinuousLinearMap.trace_adjoint`: `Tr T† = conj (Tr T)`.
* `ContinuousLinearMap.trace_eq_linearMap_trace`: in finite dimension, the trace is
  `LinearMap.trace`.

## Implementation notes

The singular value decomposition `T = ∑ₖ σₖ ⟪eₖ, ·⟫ fₖ` of a compact operator
(`IsCompactOperator.exists_orthonormal_hasSum_rankOne`) writes a trace-class operator as a series
of rank-one operators whose norms sum to at most `∑ₙ aₙ(T)`. Along any Hilbert basis the double
series `∑ₖ ∑ᵢ ⟪uₖ, bᵢ⟫ ⟪bᵢ, vₖ⟫` then converges absolutely, so its two iterated sums agree: summing
over `i` first gives `∑ₖ ⟪uₖ, vₖ⟫` by Parseval's identity, and summing over `k` first gives the
diagonal sum. Both the independence of the basis and the trace property come from this, since
`A T` and `T A` are the series `∑ₖ ⟪uₖ, ·⟫ A vₖ` and `∑ₖ ⟪A† uₖ, ·⟫ vₖ`.

The definition sums along a Hilbert basis chosen once and for all, and is `0` outside the trace
class so that it does not depend on that choice.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, §VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 3.
-/

public section

open InnerProductSpace TauCeti TauCeti.OperatorIdealFamily
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

universe u

variable {𝕜 : Type*} {E : Type u} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! ### Diagonal sums of nuclear series -/

namespace HilbertBasis

variable {ι κ : Type*} (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] E} {u v : κ → E}

/-- **Diagonal sums of a nuclear series.** If `T = ∑ₖ ⟪uₖ, ·⟫ vₖ` in operator norm with
`∑ₖ ‖uₖ‖ ‖vₖ‖ < ∞`, then the diagonal entries `⟪bᵢ, T bᵢ⟫` of `T` along any Hilbert basis sum to
`∑ₖ ⟪uₖ, vₖ⟫`. -/
theorem hasSum_inner_apply_of_hasSum_rankOne (huv : Summable fun k ↦ ‖u k‖ * ‖v k‖)
    (hT : HasSum (fun k ↦ rankOne 𝕜 (v k) (u k)) T) :
    HasSum (fun i ↦ ⟪b i, T (b i)⟫_𝕜) (∑' k, ⟪u k, v k⟫_𝕜) := by
  -- The double series `∑ₖ ∑ᵢ ⟪uₖ, bᵢ⟫ ⟪bᵢ, vₖ⟫` converges absolutely, by Cauchy–Schwarz.
  set g : κ × ι → 𝕜 := fun p ↦ ⟪u p.1, b p.2⟫_𝕜 * ⟪b p.2, v p.1⟫_𝕜
  have hg : Summable fun p ↦ ‖g p‖ :=
    (summable_prod_of_nonneg fun _ ↦ norm_nonneg _).2
      ⟨fun k ↦ b.summable_norm_inner_mul_inner (u k) (v k),
        huv.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _)
          fun k ↦ b.tsum_norm_inner_mul_inner_le (u k) (v k)⟩
  have hsum := hg.of_norm.hasSum
  -- Summing over the basis first gives `⟪uₖ, vₖ⟫`, by Parseval's identity.
  have h₁ := hsum.prod_fiberwise fun k ↦ b.hasSum_inner_mul_inner (u k) (v k)
  -- Summing over the series first gives the diagonal entry `⟪bᵢ, T bᵢ⟫`.
  have h₂ := ((Equiv.prodComm ι κ).hasSum_iff.2 hsum).prod_fiberwise fun i ↦ by
    simpa [g, inner_smul_right] using
      hT.mapL ((innerSL 𝕜 (b i)).comp (ContinuousLinearMap.apply 𝕜 E (b i)))
  rwa [h₁.tsum_eq]

end HilbertBasis

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F] {T : E →L[𝕜] E}

/-! ### Trace-class operators as nuclear series -/

/-- **Trace-class operators are nuclear series.** A trace-class operator is an operator-norm sum
`T = ∑ₖ ⟪uₖ, ·⟫ vₖ` of rank-one operators with `∑ₖ ‖uₖ‖ ‖vₖ‖ ≤ ∑ₙ aₙ(T)`. -/
theorem exists_hasSum_rankOne_of_mem_traceClass {T : E →L[𝕜] F}
    (hT : T ∈ ((traceClass 𝕜).operatorGauge E F).finiteSubmodule) :
    ∃ (κ : Type u) (u : κ → E) (v : κ → F), Summable (fun k ↦ ‖u k‖ * ‖v k‖) ∧
      ∑' k, ‖u k‖ * ‖v k‖ ≤ ∑' n, (T.singularValue n : ℝ) ∧
        HasSum (fun k ↦ rankOne 𝕜 (v k) (u k)) T := by
  have hsv := (mem_finiteSubmodule_traceClass_iff T).1 hT
  have hc := isCompactOperator_of_nuclearENorm_ne_top
    ((mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top T).1 hT)
  obtain ⟨κ, e, f, σ, -, he, hf, hσ0, hσ, hTσ, hdec⟩ := hc.exists_orthonormal_hasSum_rankOne
  -- Every finite sum of the `σₖ` is bounded by a sum of approximation numbers.
  have hle (s : Finset κ) : ∑ k ∈ s, σ k ≤ ∑' n, (T.singularValue n : ℝ) :=
    calc ∑ k ∈ s, σ k ≤ ∑ n ∈ Finset.range s.card, decreasingRearrangement σ n :=
          sum_le_sum_decreasingRearrangement hσ.bddAbove_range_of_cofinite s
      _ = ∑ n ∈ Finset.range s.card, (T.singularValue n : ℝ) := by simp [hdec]
      _ ≤ _ := (NNReal.summable_coe.2 hsv).sum_le_tsum _ fun n _ ↦ NNReal.coe_nonneg _
  have hnorm (k : κ) : ‖e k‖ * ‖(σ k : 𝕜) • f k‖ = σ k := by
    rw [he.1 k, norm_smul, hf.1 k, RCLike.norm_ofReal, abs_of_pos (hσ0 k), one_mul, mul_one]
  refine ⟨κ, e, fun k ↦ (σ k : 𝕜) • f k, ?_, ?_, ?_⟩
  · simpa only [hnorm] using summable_of_sum_le (fun k ↦ (hσ0 k).le) hle
  · simpa only [hnorm] using Real.tsum_le_of_sum_le (fun k ↦ (hσ0 k).le) hle
  · simpa using hTσ

/-- **Nuclear series are trace class.** An operator-norm sum `T = ∑ₖ ⟪uₖ, ·⟫ vₖ` of rank-one
operators with `∑ₖ ‖uₖ‖ ‖vₖ‖ < ∞` is a trace-class operator. -/
theorem mem_traceClass_of_hasSum_rankOne {κ : Type*} {u : κ → E} {v : κ → F} {T : E →L[𝕜] F}
    (huv : Summable fun k ↦ ‖u k‖ * ‖v k‖) (hT : HasSum (fun k ↦ rankOne 𝕜 (v k) (u k)) T) :
    T ∈ ((traceClass 𝕜).operatorGauge E F).finiteSubmodule := by
  rw [mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top]
  refine ne_top_of_le_ne_top ?_ (nuclearENorm_le_tsum_of_hasSum hT)
  simp_rw [nuclearENorm_rankOne, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) huv]
  exact ENNReal.ofReal_ne_top

/-! ### The trace -/

open scoped Classical in
/-- The **trace** `Tr T = ∑ᵢ ⟪bᵢ, T bᵢ⟫` of a trace-class operator `T` on a Hilbert space, summed
along a Hilbert basis `(bᵢ)`. The sum converges and does not depend on the basis
(`ContinuousLinearMap.hasSum_inner_apply_trace`). Outside the trace class the trace takes the junk
value `0`. -/
noncomputable def trace (T : E →L[𝕜] E) : 𝕜 :=
  if T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule then
    ∑' x : (exists_hilbertBasis 𝕜 E).choose, ⟪(x : E), T x⟫_𝕜
  else 0

/-- The trace vanishes outside the trace class. -/
@[simp]
theorem trace_of_notMem (hT : T ∉ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule) :
    T.trace = 0 :=
  ite_eq_right hT

/-- **The trace as a diagonal sum.** For a trace-class operator `T` and any Hilbert basis `(bᵢ)`,
the diagonal entries `⟪bᵢ, T bᵢ⟫` sum to `Tr T`. -/
theorem hasSum_inner_apply_trace {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule) :
    HasSum (fun i ↦ ⟪b i, T (b i)⟫_𝕜) T.trace := by
  obtain ⟨κ, u, v, huv, -, hTuv⟩ := exists_hasSum_rankOne_of_mem_traceClass hT
  obtain ⟨b₀, hb₀⟩ := (exists_hilbertBasis 𝕜 E).choose_spec
  have h₀ := b₀.hasSum_inner_apply_of_hasSum_rankOne huv hTuv
  rw [hb₀] at h₀
  rw [trace, ite_eq_left hT, h₀.tsum_eq]
  exact b.hasSum_inner_apply_of_hasSum_rankOne huv hTuv

/-- **The trace as a diagonal sum.** `Tr T = ∑ᵢ ⟪bᵢ, T bᵢ⟫` along any Hilbert basis. -/
theorem trace_eq_tsum_inner_apply {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule) :
    T.trace = ∑' i, ⟪b i, T (b i)⟫_𝕜 :=
  (hasSum_inner_apply_trace b hT).tsum_eq.symm

/-- **The trace of a nuclear series.** If `T = ∑ₖ ⟪uₖ, ·⟫ vₖ` in operator norm with
`∑ₖ ‖uₖ‖ ‖vₖ‖ < ∞`, then `Tr T = ∑ₖ ⟪uₖ, vₖ⟫`. -/
theorem trace_eq_tsum_of_hasSum_rankOne {κ : Type*} {u v : κ → E}
    (huv : Summable fun k ↦ ‖u k‖ * ‖v k‖) (hT : HasSum (fun k ↦ rankOne 𝕜 (v k) (u k)) T) :
    T.trace = ∑' k, ⟪u k, v k⟫_𝕜 := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  exact (hasSum_inner_apply_trace b (mem_traceClass_of_hasSum_rankOne huv hT)).unique
    (b.hasSum_inner_apply_of_hasSum_rankOne huv hT)

/-- The trace of the rank-one operator `z ↦ ⟪y, z⟫ x` is `⟪y, x⟫`. -/
@[simp]
theorem trace_rankOne (x y : E) : (rankOne 𝕜 x y).trace = ⟪y, x⟫_𝕜 := by
  simpa using trace_eq_tsum_of_hasSum_rankOne (T := rankOne 𝕜 x y) (u := fun _ : Unit ↦ y)
    (v := fun _ ↦ x) .of_finite (by simp)

/-! ### Linearity and the trace-norm bound -/

/-- The trace is additive on the trace class. -/
theorem trace_add {S : E →L[𝕜] E} (hS : S ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule)
    (hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule) :
    (S + T).trace = S.trace + T.trace := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  refine (hasSum_inner_apply_trace b (Submodule.add_mem _ hS hT)).unique ?_
  simpa [inner_add_right] using (hasSum_inner_apply_trace b hS).add (hasSum_inner_apply_trace b hT)

/-- The trace of the zero operator is zero. -/
@[simp]
theorem trace_zero : (0 : E →L[𝕜] E).trace = 0 := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  exact (hasSum_inner_apply_trace b (Submodule.zero_mem _)).unique (by simp)

/-- The trace is homogeneous. Outside the trace class both sides vanish. -/
@[simp]
theorem trace_smul (c : 𝕜) (T : E →L[𝕜] E) : (c • T).trace = c * T.trace := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  by_cases hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule
  · refine (hasSum_inner_apply_trace b (Submodule.smul_mem _ c hT)).unique ?_
    simpa [inner_smul_right] using (hasSum_inner_apply_trace b hT).mul_left c
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [trace_of_notMem hT, trace_of_notMem fun h ↦ hT (by
        simpa [hc] using Submodule.smul_mem _ c⁻¹ h), mul_zero]

/-- The trace commutes with negation. -/
@[simp]
theorem trace_neg (T : E →L[𝕜] E) : (-T).trace = -T.trace := by
  simpa using trace_smul (-1 : 𝕜) T

/-- The trace of a difference of trace-class operators is the difference of their traces. -/
theorem trace_sub {S : E →L[𝕜] E} (hS : S ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule)
    (hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule) :
    (S - T).trace = S.trace - T.trace := by
  rw [sub_eq_add_neg, trace_add hS (Submodule.neg_mem _ hT), trace_neg, sub_eq_add_neg]

/-- **The trace is bounded by the trace norm**: `|Tr T| ≤ ∑ₙ aₙ(T)`. Outside the trace class the
right-hand side is infinite. -/
theorem enorm_trace_le (T : E →L[𝕜] E) : ‖T.trace‖ₑ ≤ T.nuclearENorm := by
  by_cases hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule
  · obtain ⟨κ, u, v, huv, hle, hTuv⟩ := exists_hasSum_rankOne_of_mem_traceClass hT
    have hsv := NNReal.summable_coe.2 ((mem_finiteSubmodule_traceClass_iff T).1 hT)
    have hs : Summable fun k ↦ ‖⟪u k, v k⟫_𝕜‖ :=
      huv.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ norm_inner_le_norm _ _
    have hnorm : ‖T.trace‖ ≤ ∑' n, (T.singularValue n : ℝ) := by
      rw [trace_eq_tsum_of_hasSum_rankOne huv hTuv]
      calc _ ≤ ∑' k, ‖⟪u k, v k⟫_𝕜‖ := norm_tsum_le_tsum_norm hs
        _ ≤ ∑' k, ‖u k‖ * ‖v k‖ := hs.tsum_le_tsum (fun k ↦ norm_inner_le_norm _ _) huv
        _ ≤ _ := hle
    rw [← ofReal_norm, nuclearENorm_def]
    refine (ENNReal.ofReal_le_ofReal hnorm).trans_eq ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ NNReal.coe_nonneg _) hsv]
    simp
  · have hT' : T.nuclearENorm = ∞ :=
      not_ne_iff.1 ((mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top T).not.1 hT)
    simp [hT']

/-- **The trace is bounded by the trace norm**: `|Tr T| ≤ ∑ₙ aₙ(T)`. -/
theorem norm_trace_le (hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule) :
    ‖T.trace‖ ≤ T.nuclearENorm.toReal := by
  have hne := (mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top T).1 hT
  have h := enorm_trace_le T
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h

/-! ### The trace property and the adjoint -/

/-- **The trace property.** For a trace-class operator `T : F →L[𝕜] E` and a bounded operator
`A : E →L[𝕜] F`, `Tr (A T) = Tr (T A)`. -/
theorem trace_comp_comm {T : F →L[𝕜] E} (A : E →L[𝕜] F)
    (hT : T ∈ ((traceClass 𝕜).operatorGauge F E).finiteSubmodule) :
    (A ∘L T).trace = (T ∘L A).trace := by
  obtain ⟨κ, u, v, huv, -, hTuv⟩ := exists_hasSum_rankOne_of_mem_traceClass hT
  -- `A T = ∑ₖ ⟪uₖ, ·⟫ A vₖ` and `T A = ∑ₖ ⟪A† uₖ, ·⟫ vₖ`.
  have hAT : HasSum (fun k ↦ rankOne 𝕜 (A (v k)) (u k)) (A ∘L T) := by
    simpa [comp_rankOne] using hTuv.mapL (compL 𝕜 F E F A)
  have hTA : HasSum (fun k ↦ rankOne 𝕜 (v k) (adjoint A (u k))) (T ∘L A) := by
    simpa [rankOne_comp] using hTuv.mapL ((compL 𝕜 E F E).flip A)
  rw [trace_eq_tsum_of_hasSum_rankOne ?_ hAT, trace_eq_tsum_of_hasSum_rankOne ?_ hTA]
  · simp [adjoint_inner_left]
  · refine (huv.mul_left ‖A‖).of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
    calc ‖adjoint A (u k)‖ * ‖v k‖ ≤ ‖adjoint A‖ * ‖u k‖ * ‖v k‖ := by
          gcongr; exact le_opNorm _ _
      _ = ‖A‖ * (‖u k‖ * ‖v k‖) := by rw [adjoint.norm_map, mul_assoc]
  · refine (huv.mul_left ‖A‖).of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
    calc ‖u k‖ * ‖A (v k)‖ ≤ ‖u k‖ * (‖A‖ * ‖v k‖) := by gcongr; exact le_opNorm _ _
      _ = ‖A‖ * (‖u k‖ * ‖v k‖) := by ring

/-- **The trace of the adjoint** is the complex conjugate of the trace. Outside the trace class
both sides vanish. -/
@[simp]
theorem trace_adjoint (T : E →L[𝕜] E) : (adjoint T).trace = conj T.trace := by
  by_cases hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule
  · obtain ⟨κ, u, v, huv, -, hTuv⟩ := exists_hasSum_rankOne_of_mem_traceClass hT
    have hT' : HasSum (fun k ↦ rankOne 𝕜 (u k) (v k)) (adjoint T) := by
      simpa [Function.comp_def] using
        hTuv.map (adjoint : (E →L[𝕜] E) ≃ₗᵢ⋆[𝕜] (E →L[𝕜] E)) adjoint.continuous
    rw [trace_eq_tsum_of_hasSum_rankOne (by simpa only [mul_comm] using huv) hT',
      trace_eq_tsum_of_hasSum_rankOne huv hTuv, RCLike.conj_tsum]
    simp
  · have hT' : adjoint T ∉ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
      simpa [mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top] using hT
    simp [hT, hT']

/-! ### Finite dimension -/

/-- **The trace in finite dimension.** On a finite-dimensional space every operator is trace
class, and its trace is the trace of the underlying linear map. -/
theorem trace_eq_linearMap_trace [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
    T.trace = LinearMap.trace 𝕜 E T := by
  have hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
    rw [mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top]
    exact T.nuclearENorm_ne_top_of_rank_le (k := Module.finrank 𝕜 E)
      ((Submodule.rank_le _).trans (Module.finrank_eq_rank 𝕜 E).symm.le)
  set b := stdOrthonormalBasis 𝕜 E
  rw [trace_eq_tsum_inner_apply b.toHilbertBasis hT, LinearMap.trace_eq_sum_inner _ b, tsum_fintype]
  simp

end ContinuousLinearMap

/-! ### The trace as a continuous linear functional -/

namespace TauCeti

variable (𝕜 E) [CompleteSpace E]

/-- **The trace on the normed trace class**, a continuous linear functional of norm at most `1`:
`|Tr T| ≤ ∑ₙ aₙ(T)`. -/
noncomputable def traceClassTraceCLM : ((traceClass 𝕜).operatorGauge E E).Carrier →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun T := T.toContinuousLinearMap.trace
      map_add' S T := by
        simpa using ContinuousLinearMap.trace_add S.mem_finiteSubmodule T.mem_finiteSubmodule
      map_smul' c T := by simp }
    1 fun T ↦ by
      rw [one_mul, OperatorGauge.Carrier.norm_def, operatorGauge_apply, gauge_traceClass]
      exact ContinuousLinearMap.norm_trace_le T.mem_finiteSubmodule

variable {𝕜 E}

/-- Applying `TauCeti.traceClassTraceCLM` takes the trace of the underlying operator. -/
@[simp]
theorem traceClassTraceCLM_apply (T : ((traceClass 𝕜).operatorGauge E E).Carrier) :
    traceClassTraceCLM 𝕜 E T = T.toContinuousLinearMap.trace :=
  (rfl)

/-- The trace has norm at most `1` on the normed trace class. -/
theorem norm_traceClassTraceCLM_le : ‖traceClassTraceCLM 𝕜 E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end TauCeti
