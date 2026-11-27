/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass.HilbertSchmidt
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.HilbertSchmidt
import TauCeti.Analysis.InnerProductSpace.L2.Star
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# The trace of a product of integral operators

Let `μ` and `ν` be σ-finite measures on `α` and `β`, with scalars `𝕜 = ℝ` or `ℂ`, and write
`T_K = TauCeti.integralOperatorL2 μ ν K : L²(ν) → L²(μ)` for the Hilbert–Schmidt operator of a
kernel `K ∈ L²(μ ⊗ ν)`. For kernels `K₁ ∈ L²(μ ⊗ ν)` and `K₂ ∈ L²(ν ⊗ μ)` the composite
`T_{K₁} T_{K₂}` is trace class, as a product of two Hilbert–Schmidt operators, and

`Tr (T_{K₁} T_{K₂}) = ∫∫ K₁ (x, y) K₂ (y, x) dν(y) dμ(x)`.

The proof goes through three identities, each of independent use.

* The adjoint of `T_K` is the integral operator of the conjugate transpose kernel
  `K⋆ (x, y) = conj (K (y, x))` (`TauCeti.adjointKernel`).
* The Hilbert–Schmidt pairing of two integral operators is the `L²` pairing of their kernels:
  `∑ⱼ ⟪T_K bⱼ, T_L bⱼ⟫ = ⟪K, L⟫` along any Hilbert basis `(bⱼ)` of `L²(ν)`. This is Parseval's
  identity in the product basis `aᵢ ⊗ star bⱼ` of `L²(μ ⊗ ν)`, polarizing
  `TauCeti.hilbertSchmidtEnergy_integralOperatorL2`.
* Writing `T_{K₁} = (T_{K₁⋆})†`, the trace `Tr (T_{K₁} T_{K₂})` is the Hilbert–Schmidt pairing
  `⟪K₁⋆, K₂⟫`, which is the displayed double integral after the measure-preserving swap
  `μ ⊗ ν ≃ ν ⊗ μ`. Fubini applies because `K₁ (x, y) K₂ (y, x)` is absolutely integrable, with
  `L¹` norm at most `‖K₁‖₂ ‖K₂‖₂`.

A class in `L²(μ ⊗ μ)` has no well-defined values on the diagonal, which is a null set in
general. The diagonal form of the trace formula therefore takes a function `K` on `α × α`,
supplied by the user, whose diagonal values are almost everywhere the integrals
`∫ K₁ (x, y) K₂ (y, x) dμ(y)`, for instance a continuous kernel of the composite. Then
`Tr (T_{K₁} T_{K₂}) = ∫ K (x, x) dμ(x)` (`TauCeti.trace_integralOperatorL2_comp_eq_integral_diag`).

## Main declarations

* `TauCeti.adjointKernel`, `TauCeti.adjoint_integralOperatorL2`: the conjugate transpose kernel
  and `T_K† = T_{K⋆}`.
* `TauCeti.hasSum_inner_integralOperatorL2_apply`: `∑ⱼ ⟪T_K bⱼ, T_L bⱼ⟫ = ⟪K, L⟫`.
* `TauCeti.trace_adjoint_integralOperatorL2_comp`: `Tr (T_K† T_L) = ⟪K, L⟫`.
* `TauCeti.trace_integralOperatorL2_comp`:
  `Tr (T_{K₁} T_{K₂}) = ∫ K₁ (x, y) K₂ (y, x) d(μ ⊗ ν)`.
* `TauCeti.trace_integralOperatorL2_comp_eq_integral_integral`: the same as an iterated integral.
* `TauCeti.trace_integralOperatorL2_comp_eq_integral_diag`: the diagonal trace formula
  `Tr (T_{K₁} T_{K₂}) = ∫ K (x, x) dμ(x)`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS, 2014, §6.3,
  (6.10)–(6.12) and Lemma 6.15.
* The diagonal trace formula is the one used by the Riemann-Masullo formalization
  (https://github.com/mccorvie/riemann-masullo, `hilbertTrace_integralKernelOperator_comp` in
  `RiemannMasullo/AppC_LCTVS/Sec3b.lean`). No code is copied; here the proof is the
  Hilbert–Schmidt pairing of `TauCeti.MeasureTheory.Function.Lp.Operator.Integral.HilbertSchmidt`
  and `TauCeti.Analysis.OperatorIdeal.Family.TraceClass.HilbertSchmidt`.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Lp
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {α β 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

namespace TauCeti

/-! ### The conjugate transpose kernel -/

section Adjoint

variable [SFinite μ] [SFinite ν]

/-- The conjugate transpose `K⋆ (x, y) = conj (K (y, x))` of a kernel `K ∈ L²(ν ⊗ μ)`, an element
of `L²(μ ⊗ ν)`. Its integral operator is the adjoint of that of `K`
(`TauCeti.adjoint_integralOperatorL2`). -/
def adjointKernel (K : Lp 𝕜 2 (ν.prod μ)) : Lp 𝕜 2 (μ.prod ν) :=
  star (Lp.compMeasurePreserving Prod.swap Measure.measurePreserving_swap K)

theorem coeFn_adjointKernel (K : Lp 𝕜 2 (ν.prod μ)) :
    adjointKernel K =ᵐ[μ.prod ν] fun p ↦ conj (K p.swap) := by
  filter_upwards [coeFn_star (Lp.compMeasurePreserving Prod.swap
      Measure.measurePreserving_swap K),
    coeFn_compMeasurePreserving K (Measure.measurePreserving_swap (μ := μ) (ν := ν))]
    with p hs hc
  rw [adjointKernel, hs, Pi.star_apply, hc, Function.comp_apply, RCLike.star_def]

@[simp]
theorem norm_adjointKernel (K : Lp 𝕜 2 (ν.prod μ)) : ‖adjointKernel K‖ = ‖K‖ := by
  rw [adjointKernel, norm_star, norm_compMeasurePreserving]

@[simp]
theorem adjointKernel_adjointKernel (K : Lp 𝕜 2 (ν.prod μ)) :
    adjointKernel (adjointKernel K) = K := by
  refine Lp.ext ?_
  filter_upwards [coeFn_adjointKernel (adjointKernel K),
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      (coeFn_adjointKernel (μ := μ) K)] with q hq hK
  simp only [Function.comp_apply] at hK
  rw [hq, hK, Prod.swap_swap, RCLike.conj_conj]

/-- **The kernel of the adjoint.** The adjoint of the integral operator of `K ∈ L²(ν ⊗ μ)` is the
integral operator of the conjugate transpose kernel `(x, y) ↦ conj (K (y, x))`. -/
theorem adjoint_integralOperatorL2 (K : Lp 𝕜 2 (ν.prod μ)) :
    ContinuousLinearMap.adjoint (integralOperatorL2 ν μ K) =
      integralOperatorL2 μ ν (adjointKernel K) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [← inner_conj_symm, inner_integralOperatorL2, inner_integralOperatorL2, L2.inner_def,
    L2.inner_def, ← integral_conj,
    ← (Measure.measurePreserving_swap (μ := μ) (ν := ν)).integral_comp
      MeasurableEquiv.prodComm.measurableEmbedding]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_prodMul g (star f), coeFn_adjointKernel K,
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp (coeFn_prodMul f (star g)),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (coeFn_star g),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (coeFn_star f)] with p h₁ h₂ h₃ hg hf
  simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, Prod.fst_swap,
    Prod.snd_swap] at h₃ hg hf
  simp only [h₁, h₂, h₃, hg, hf, RCLike.inner_apply, map_mul, RCLike.conj_conj]
  ring

end Adjoint

/-! ### The Hilbert–Schmidt pairing of integral operators -/

section Pairing

variable [SigmaFinite μ] [SigmaFinite ν]

/-- **The Hilbert–Schmidt pairing of integral operators is the pairing of their kernels.** For
`K, L ∈ L²(μ ⊗ ν)` and any Hilbert basis `(bⱼ)` of `L²(ν)`, `∑ⱼ ⟪T_K bⱼ, T_L bⱼ⟫ = ⟪K, L⟫`. -/
theorem hasSum_inner_integralOperatorL2_apply {ι : Type*} (K L : Lp 𝕜 2 (μ.prod ν))
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) :
    HasSum (fun j ↦ ⟪integralOperatorL2 μ ν K (b j), integralOperatorL2 μ ν L (b j)⟫_𝕜)
      ⟪K, L⟫_𝕜 := by
  obtain ⟨κ, a, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 μ)
  let e := HilbertBasis.prod a b.star
  have hsum : HasSum (fun p : ι × κ ↦ ⟪K, e p.swap⟫_𝕜 * ⟪e p.swap, L⟫_𝕜) ⟪K, L⟫_𝕜 :=
    (Equiv.prodComm ι κ).hasSum_iff.2 (e.hasSum_inner_mul_inner K L)
  refine hsum.prod_fiberwise fun j ↦ ?_
  convert a.hasSum_inner_mul_inner (integralOperatorL2 μ ν K (b j))
    (integralOperatorL2 μ ν L (b j)) using 2 with i
  simp only [e, Prod.swap_prod_mk, HilbertBasis.prod_apply, HilbertBasis.star_apply]
  rw [← inner_integralOperatorL2, ← inner_conj_symm K, ← inner_integralOperatorL2,
    inner_conj_symm]

/-- **The Hilbert–Schmidt pairing of integral operators as a trace.** For kernels
`K, L ∈ L²(μ ⊗ ν)`, `Tr (T_K† T_L) = ⟪K, L⟫`. -/
theorem trace_adjoint_integralOperatorL2_comp (K L : Lp 𝕜 2 (μ.prod ν)) :
    (ContinuousLinearMap.adjoint (integralOperatorL2 μ ν K) ∘L integralOperatorL2 μ ν L).trace =
      ⟪K, L⟫_𝕜 := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 ν)
  exact (ContinuousLinearMap.hasSum_inner_apply_apply_trace_adjoint_comp
    (integralOperatorL2_mem_finiteSubmodule_hilbertSchmidt K)
    (integralOperatorL2_mem_finiteSubmodule_hilbertSchmidt L) b).unique
    (hasSum_inner_integralOperatorL2_apply K L b)

end Pairing

/-! ### The trace of a product of integral operators -/

section Trace

variable [SigmaFinite μ] [SigmaFinite ν]

/-- For `K₁ ∈ L²(μ ⊗ ν)` and `K₂ ∈ L²(ν ⊗ μ)`, the function `(x, y) ↦ K₁ (x, y) * K₂ (y, x)` is
integrable on `μ ⊗ ν`, with `L¹` norm at most `‖K₁‖₂ ‖K₂‖₂` by Hölder's inequality. -/
theorem integrable_mul_comp_swap (K₁ : Lp 𝕜 2 (μ.prod ν)) (K₂ : Lp 𝕜 2 (ν.prod μ)) :
    Integrable (fun p ↦ K₁ p * K₂ p.swap) (μ.prod ν) :=
  (Lp.memLp K₁).integrable_mul
    ((Lp.memLp K₂).comp_measurePreserving Measure.measurePreserving_swap)

/-- **The trace of a product of integral operators.** For kernels `K₁ ∈ L²(μ ⊗ ν)` and
`K₂ ∈ L²(ν ⊗ μ)`, the trace-class operator `T_{K₁} T_{K₂}` on `L²(μ)` has trace
`∫ K₁ (x, y) K₂ (y, x) d(μ ⊗ ν)`. -/
theorem trace_integralOperatorL2_comp (K₁ : Lp 𝕜 2 (μ.prod ν)) (K₂ : Lp 𝕜 2 (ν.prod μ)) :
    (integralOperatorL2 μ ν K₁ ∘L integralOperatorL2 ν μ K₂).trace =
      ∫ p, K₁ p * K₂ p.swap ∂(μ.prod ν) := by
  have h : integralOperatorL2 μ ν K₁ =
      ContinuousLinearMap.adjoint (integralOperatorL2 ν μ (adjointKernel K₁)) := by
    rw [adjoint_integralOperatorL2, adjointKernel_adjointKernel]
  rw [h, trace_adjoint_integralOperatorL2_comp, L2.inner_def,
    ← (Measure.measurePreserving_swap (μ := ν) (ν := μ)).integral_comp
      MeasurableEquiv.prodComm.measurableEmbedding]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_adjointKernel K₁] with q hq
  rw [RCLike.inner_apply, hq, RCLike.conj_conj, Prod.swap_swap, mul_comm]

/-- **The trace of a product of integral operators as an iterated integral.** For kernels
`K₁ ∈ L²(μ ⊗ ν)` and `K₂ ∈ L²(ν ⊗ μ)`,
`Tr (T_{K₁} T_{K₂}) = ∫ (∫ K₁ (x, y) K₂ (y, x) dν(y)) dμ(x)`. -/
theorem trace_integralOperatorL2_comp_eq_integral_integral (K₁ : Lp 𝕜 2 (μ.prod ν))
    (K₂ : Lp 𝕜 2 (ν.prod μ)) :
    (integralOperatorL2 μ ν K₁ ∘L integralOperatorL2 ν μ K₂).trace =
      ∫ x, ∫ y, K₁ (x, y) * K₂ (y, x) ∂ν ∂μ := by
  rw [trace_integralOperatorL2_comp, integral_prod _ (integrable_mul_comp_swap K₁ K₂)]
  rfl

/-- **The diagonal trace formula.** Let `K₁, K₂ ∈ L²(μ ⊗ μ)`. If a function `K` on `α × α` has
diagonal values `K (x, x) = ∫ K₁ (x, y) K₂ (y, x) dμ(y)` for almost every `x`, then
`Tr (T_{K₁} T_{K₂}) = ∫ K (x, x) dμ(x)`.

The hypothesis fixes the values of `K` on the diagonal, which a class in `L²(μ ⊗ μ)` does not
determine. It holds, for instance, when `K (x, z) = ∫ K₁ (x, y) K₂ (y, z) dμ(y)` at every
diagonal point outside a `μ`-null set. Its right-hand side does not depend on the
representatives of `K₁` and `K₂`, and it is automatically almost everywhere strongly measurable
in `x`. -/
theorem trace_integralOperatorL2_comp_eq_integral_diag (K₁ K₂ : Lp 𝕜 2 (μ.prod μ))
    {K : α × α → 𝕜} (hK : ∀ᵐ x ∂μ, K (x, x) = ∫ y, K₁ (x, y) * K₂ (y, x) ∂μ) :
    (integralOperatorL2 μ μ K₁ ∘L integralOperatorL2 μ μ K₂).trace = ∫ x, K (x, x) ∂μ := by
  rw [trace_integralOperatorL2_comp_eq_integral_integral]
  exact integral_congr_ae (hK.mono fun _ hx ↦ hx.symm)

end Trace

end TauCeti
