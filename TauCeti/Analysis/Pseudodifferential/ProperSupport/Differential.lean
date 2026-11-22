/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Distribution
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Distribution.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Differential operators as properly supported operators on distributions

The classical symbol `TauCeti.ClassicalSymbol.ofDifferentialSymbol` of a differential operator
`P u = ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` on `ℝⁿ` with smooth coefficients quantizes to `P` itself on
Schwartz functions (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialSymbol`). This
file shows that its kernel is supported on the diagonal: `Op(a) u (x)` only depends on `u` near
`x`, so the operator has propagation at most `ε` and kernel supported within distance `R` of the
diagonal for all `ε, R > 0`
(`TauCeti.ClassicalSymbol.hasPropagationLE_toSymbol_ofDifferentialSymbol`,
`TauCeti.ClassicalSymbol.hasNearDiagonalKernel_toSymbol_ofDifferentialSymbol`). No bound on the
coefficients uniform in the position is needed. On test functions the properly supported operator
is again `P` (`TauCeti.ClassicalSymbol.quantizeTestFunctionCLM_ofDifferentialSymbol_apply`).

Differential operators are therefore properly supported, and act on all distributions on `ℝⁿ` by
transposition (`TauCeti.Symbol.quantizeDistribution`). For an operator
`P = ∑ i ∈ t, c i g i ∂^(m i)` with complex constants `c i`, smooth real coefficient functions
`g i` and orders `k i`, the form in which differential operators act on distributions in
`TauCeti.Analysis.Pseudodifferential.DistributionalRegularity`, this action is the
distributional differential operator:

* `TauCeti.ClassicalSymbol.adjointTestFunctionCLM_ofDifferentialSymbol`: the formal adjoint of
  `P` on test functions is `P* φ = ∑ i ∈ t, conj (c i) (-1) ^ k i ∂^(m i ∘ rev) (g i φ)`, by
  `k i` integrations by parts
  (`TestFunction.integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right`);
* `TauCeti.ClassicalSymbol.quantizeDistribution_ofDifferentialSymbol`: for every distribution
  `T`, `Op(a) T = ∑ i ∈ t, c i g i ∂^(m i) T`, with the distributional derivatives of `T`.

So the pseudodifferential action of a differential operator on distributions is exactly the
differential operator, with no smoothing remainder.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions LineDeriv SchwartzMap Topology

namespace TauCeti

namespace ClassicalSymbol

variable {n : ℕ} {ι : Type*} {k : ι → ℕ}

/-! ### The kernel is supported on the diagonal -/

section Propagation

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] (M : ℕ) (s : Finset ι)
  (v : ∀ i, Fin (k i) → CoordinateSpace n) (b : ι → CoordinateSpace n → V →L[ℂ] W)
  (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (hk : ∀ i ∈ s, k i ≤ M)

/-- **Differential operators have arbitrarily small propagation.** The quantization of the
classical symbol of a differential operator has propagation at most `ε` for every `ε > 0`: the
value of `Op(a) u` at `x` only depends on the derivatives of `u` at `x`. -/
theorem hasPropagationLE_toSymbol_ofDifferentialSymbol {ε : ℝ} (hε : 0 < ε) :
    (ofDifferentialSymbol M s v b hb hk).toSymbol.HasPropagationLE ε := by
  refine Symbol.hasPropagationLE_iff.2 fun u x hu ↦ ?_
  have h0 : (u : CoordinateSpace n → V) =ᶠ[𝓝 x] 0 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x hε) hu
  rw [coefficient_toSymbol_ofDifferentialSymbol,
    quantizeSchwartzValue_differentialSymbol_eq_sum_iteratedFDeriv]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [(h0.iteratedFDeriv ℝ (k i)).eq_of_nhds]
  simp

/-- **The kernel of a differential operator is supported on the diagonal.** The quantization of
the classical symbol of a differential operator has kernel supported within distance `R` of the
diagonal for every `R > 0`, so it acts on all distributions
(`TauCeti.Symbol.quantizeDistribution`). -/
theorem hasNearDiagonalKernel_toSymbol_ofDifferentialSymbol {R : ℝ} (hR : 0 < R) :
    (ofDifferentialSymbol M s v b hb hk).toSymbol.HasNearDiagonalKernel R :=
  Symbol.hasNearDiagonalKernel_iff.2 (Symbol.hasPropagationLE_iff.1
    (hasPropagationLE_toSymbol_ofDifferentialSymbol M s v b hb hk hR))

/-- **Differential operators on test functions.** On a test function `u`, the quantization of the
classical symbol of a differential operator is the differential operator,
`Op(a) u = ∑ i ∈ s, bᵢ ∂^{vᵢ} u`, with the directional derivatives of the test function `u`. -/
theorem quantizeTestFunctionCLM_ofDifferentialSymbol_apply {R : ℝ}
    (ha : (ofDifferentialSymbol M s v b hb hk).toSymbol.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) (x : CoordinateSpace n) :
    Symbol.quantizeTestFunctionCLM ha u x = ∑ i ∈ s, b i x ((∂^{v i} u) x) := by
  rw [Symbol.quantizeTestFunctionCLM_apply, quantizeSchwartzValue_ofDifferentialSymbol]
  -- The Schwartz function of `u` is `TestFunction.toSchwartzMapCLM ℝ u`.
  have hu : u.hasCompactSupport.toSchwartzMap u.contDiff = TestFunction.toSchwartzMapCLM ℝ u :=
    SchwartzMap.ext fun y ↦ by simp
  simp only [hu, ← TestFunction.toSchwartzMapCLM_iteratedLineDerivOp,
    TestFunction.toSchwartzMapCLM_apply]

end Propagation

/-! ### Scalar differential operators on test functions and distributions -/

section Scalar

variable {M : ℕ} {t : Finset ι} {m : ∀ i, Fin (k i) → CoordinateSpace n} {c : ι → ℂ}
  {g : ι → CoordinateSpace n → ℝ} {hk : ∀ i ∈ t, k i ≤ M}
  {hb : ∀ i ∈ t, ContDiff ℝ ∞ fun x ↦ (c i * g i x) • ContinuousLinearMap.id ℂ ℂ} {R : ℝ}

/-- The real bilinear pairing `(z, w) ↦ conj z * w`, the inner product of `ℂ`. -/
private def innerPairing : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp conjCLE.toContinuousLinearMap

private theorem innerPairing_apply (z w : ℂ) : innerPairing z w = starRingEnd ℂ z * w := by
  simp [innerPairing, mul_comm]

/-- A pairing `x ↦ z ⟪f x, h x⟫` of two test functions is integrable. -/
private theorem integrable_mul_innerPairing (f h : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ))
    (z : ℂ) : Integrable fun x ↦ z * innerPairing (f x) (h x) :=
  (continuous_const.mul (innerPairing.continuous₂.comp₂ f.continuous
    h.continuous)).integrable_of_hasCompactSupport
      (h.hasCompactSupport.mono' fun x hx ↦ subset_tsupport _ fun h0 ↦ hx (by simp [h0]))

/-- The integration by parts behind the formal adjoint of a differential operator:
`∫ ⟪P u, φ⟫ = ∫ ⟪u, ∑ i ∈ t, conj (c i) (-1) ^ k i ∂^(m i ∘ rev) (g i φ)⟫`. -/
private theorem integral_inner_quantizeTestFunctionCLM_ofDifferentialSymbol
    (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (ha : (ofDifferentialSymbol M t m (fun i x ↦ (c i * g i x) • ContinuousLinearMap.id ℂ ℂ) hb
      hk).toSymbol.HasNearDiagonalKernel R) (u φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    ∫ x, inner ℂ (Symbol.quantizeTestFunctionCLM ha u x) (φ x) =
      ∫ x, inner ℂ (u x) ((∑ i ∈ t, (starRingEnd ℂ (c i) * (-1) ^ k i) •
        ∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i) φ)) x) := by
  have hOp (x : CoordinateSpace n) : inner ℂ (Symbol.quantizeTestFunctionCLM ha u x) (φ x) =
      ∑ i ∈ t, starRingEnd ℂ (c i) *
        innerPairing ((∂^{m i} u) x) (TestFunction.smulLeftCLM (hg i) φ x) := by
    rw [quantizeTestFunctionCLM_ofDifferentialSymbol_apply, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [smul_apply, ContinuousLinearMap.id_apply, innerPairing_apply,
      TestFunction.smulLeftCLM_apply, RCLike.inner_apply', Complex.real_smul, smul_eq_mul]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hψ (x : CoordinateSpace n) : inner ℂ (u x) ((∑ i ∈ t, (starRingEnd ℂ (c i) * (-1) ^ k i) •
      ∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i) φ)) x) =
        ∑ i ∈ t, (starRingEnd ℂ (c i) * (-1) ^ k i) *
          innerPairing (u x) ((∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i) φ)) x) := by
    simp only [sum_apply, smul_apply, smul_eq_mul, innerPairing_apply, RCLike.inner_apply',
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [hOp, hψ]
  rw [integral_finsetSum _ fun i _ ↦ integrable_mul_innerPairing _ _ _,
    integral_finsetSum _ fun i _ ↦ integrable_mul_innerPairing _ _ _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Move the `k i` derivatives from `u` to `g i φ`.
  rw [integral_const_mul, integral_const_mul,
    TestFunction.integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right,
    Complex.real_smul]
  push_cast
  ring

/-- **The formal adjoint of a differential operator.** For `P = ∑ i ∈ t, c i g i ∂^(m i)` with
smooth real coefficients `g i`, the formal adjoint `Op(a)*` of the quantization of its classical
symbol is `P* φ = ∑ i ∈ t, conj (c i) (-1) ^ k i ∂^(m i ∘ rev) (g i φ)` on test functions. -/
theorem adjointTestFunctionCLM_ofDifferentialSymbol (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (ha : (ofDifferentialSymbol M t m (fun i x ↦ (c i * g i x) • ContinuousLinearMap.id ℂ ℂ) hb
      hk).toSymbol.HasNearDiagonalKernel R) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    Symbol.adjointTestFunctionCLM ha φ =
      ∑ i ∈ t, (starRingEnd ℂ (c i) * (-1) ^ k i) •
        ∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i) φ) := by
  set A := Symbol.adjointTestFunctionCLM ha φ
  set ψ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) := ∑ i ∈ t, (starRingEnd ℂ (c i) * (-1) ^ k i) •
    ∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i) φ)
  -- Both `A` and `ψ` are formal adjoints of `Op(a)` on `φ`, so they have the same integrals against
  -- every real test function `χ`.
  have hae : ∀ᵐ x, A x = ψ x := ae_eq_of_integral_contDiff_smul_eq
    A.continuous.locallyIntegrable ψ.continuous.locallyIntegrable fun χ hχ hχc ↦ by
      let u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) := ⟨fun x ↦ (χ x : ℂ),
        ofRealCLM.contDiff.comp hχ, hχc.comp_left ofReal_zero, subset_univ _⟩
      have hu (x : CoordinateSpace n) : u x = χ x := rfl
      have h := (Symbol.integral_inner_quantizeTestFunctionCLM ha u φ).symm.trans
        (integral_inner_quantizeTestFunctionCLM_ofDifferentialSymbol hg ha u φ)
      simp only [RCLike.inner_apply', hu, Complex.conj_ofReal] at h
      simpa only [Complex.real_smul] using h
  exact TestFunction.ext (congrFun ((A.continuous.ae_eq_iff_eq volume ψ.continuous).1 hae))

/-- **Differential operators on distributions.** For `P = ∑ i ∈ t, c i g i ∂^(m i)` with smooth
real coefficients `g i`, the action of the quantization of its classical symbol on a distribution
`T` by transposition is the differential operator `P T = ∑ i ∈ t, c i g i ∂^(m i) T`, with the
distributional derivatives of `T`. -/
theorem quantizeDistribution_ofDifferentialSymbol (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (ha : (ofDifferentialSymbol M t m (fun i x ↦ (c i * g i x) • ContinuousLinearMap.id ℂ ℂ) hb
      hk).toSymbol.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    Symbol.quantizeDistribution ha T =
      ∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T) := by
  ext φ
  rw [Symbol.quantizeDistribution_apply, adjointTestFunctionCLM_ofDifferentialSymbol hg]
  -- The transpose `conj (Op(a)* φ)` of a real test function `φ` is real.
  have hφ (i : ι) : ∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i)
      (TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM φ)) = TestFunction.postcompCLM (𝕜 := ℝ)
        ofRealCLM (∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i) φ)) := by
    rw [← TestFunction.iteratedLineDerivOp_postcompCLM]
    congr 1
    ext x
    simp
  have htest : TestFunction.postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap
      (∑ i ∈ t, (starRingEnd ℂ (c i) * (-1) ^ k i) • ∂^{m i ∘ Fin.rev}
        (TestFunction.smulLeftCLM (hg i) (TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM φ))) =
      ∑ i ∈ t, (c i * (-1) ^ k i) • TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM
        (∂^{m i ∘ Fin.rev} (TestFunction.smulLeftCLM (hg i) φ)) := by
    ext x
    simp [hφ, sum_apply]
  rw [htest]
  simp [mul_assoc]

end Scalar

end ClassicalSymbol

end TauCeti
