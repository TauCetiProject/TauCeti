/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.L2
import TauCeti.Analysis.InnerProductSpace.L2.Star

/-!
# Hilbert–Schmidt integral operators of square-integrable kernels

Let `μ` and `ν` be σ-finite measures on `α` and `β`, with scalars `𝕜 = ℝ` or `ℂ`. The integral
operator `T_K = TauCeti.integralOperatorL2 μ ν K : L²(ν) →L[𝕜] L²(μ)` of a kernel
`K ∈ L²(μ ⊗ ν)` (defined in `TauCeti.MeasureTheory.Function.Lp.Operator.Integral.L2`) is
Hilbert–Schmidt with Hilbert–Schmidt norm exactly `‖K‖₂`.

Fubini's theorem gives `⟪h, T_K f⟫ = ⟪h ⊗ star f, K⟫` for `h ∈ L²(μ)` and `f ∈ L²(ν)`
(`TauCeti.inner_integralOperatorL2`). For Hilbert bases `(aⱼ)` of `L²(μ)` and `(bᵢ)` of `L²(ν)`,
the tensors `aⱼ ⊗ star bᵢ` form a Hilbert basis of `L²(μ ⊗ ν)` (`HilbertBasis.prod` applied to
`(aⱼ)` and the conjugate basis `HilbertBasis.star`), so Parseval's identity turns the
Hilbert–Schmidt energy `∑ᵢ ∑ⱼ |⟪aⱼ, T_K bᵢ⟫|²` into `‖K‖₂²`. No countability of the bases is
needed. In particular the kernel-to-operator map is an isometric linear embedding of `L²(μ ⊗ ν)`
into the Hilbert–Schmidt operators. For the rank-one kernel `w ⊗ star u`
(`TauCeti.integralOperatorL2_prodMul_star`) the norm `‖w‖₂ ‖u‖₂` is
`ContinuousLinearMap.hilbertSchmidtNorm_rankOne`.

## Main declarations

* `TauCeti.hilbertSchmidtEnergy_integralOperatorL2`,
  `TauCeti.hilbertSchmidtNorm_integralOperatorL2`: the Hilbert–Schmidt energy and norm of `T_K`
  are `‖K‖₂²` and `‖K‖₂`.
* `TauCeti.integralOperatorL2_mem_finiteSubmodule_hilbertSchmidt`: `T_K` lies in the
  Hilbert–Schmidt ideal.
* `TauCeti.integralOperatorL2HS`: the kernel-to-operator map as a linear isometry into the
  normed Hilbert–Schmidt ideal.
* `TauCeti.integralOperatorL2_injective`: equal operators have equal kernel classes.
* `TauCeti.hasSum_inner_integralOperatorL2_apply`: the Hilbert–Schmidt pairing
  `∑ⱼ ⟪T_K bⱼ, T_L bⱼ⟫` of two integral operators is the pairing `⟪K, L⟫` of their kernels.

## Implementation notes

Only σ-finiteness of the factors is assumed, which is what `HilbertBasis.prod` needs. No standard
Borel structure, separability of the `L²` spaces or countability of the bases is required.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS, 2014, §6.3,
  (6.8)–(6.13) and Lemma 6.10.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Theorem VI.23.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Lp
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {α β 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

namespace TauCeti

/-! ### The Hilbert–Schmidt norm -/

section HilbertSchmidt

variable [SigmaFinite μ] [SigmaFinite ν]

/-- **The Hilbert–Schmidt energy of an integral operator** is the squared `L²` norm of its kernel,
in every Hilbert basis of the source. -/
@[simp]
theorem hilbertSchmidtEnergy_integralOperatorL2 {ι : Type*} (K : Lp 𝕜 2 (μ.prod ν))
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) :
    (integralOperatorL2 μ ν K).hilbertSchmidtEnergy b = ‖K‖ₑ ^ 2 := by
  obtain ⟨_, a, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 μ)
  let e := HilbertBasis.prod a b.star
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_eq_tsum_tsum _ b a, ← e.tsum_eNorm_inner_sq K,
    tsum_comm, ← tsum_prod]
  refine tsum_congr fun p ↦ ?_
  rw [inner_integralOperatorL2, HilbertBasis.prod_apply, HilbertBasis.star_apply]

/-- **The Hilbert–Schmidt norm of an integral operator** is the `L²` norm of its kernel. -/
@[simp]
theorem hilbertSchmidtNorm_integralOperatorL2 (K : Lp 𝕜 2 (μ.prod ν)) :
    (integralOperatorL2 μ ν K).hilbertSchmidtNorm = ‖K‖ := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 ν)
  rw [ContinuousLinearMap.hilbertSchmidtNorm_eq_toReal_rpow _ b,
    hilbertSchmidtEnergy_integralOperatorL2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The integral operator of a square-integrable kernel lies in the Hilbert–Schmidt ideal. -/
theorem integralOperatorL2_mem_finiteSubmodule_hilbertSchmidt (K : Lp 𝕜 2 (μ.prod ν)) :
    integralOperatorL2 μ ν K ∈ ((OperatorIdealFamily.hilbertSchmidt 𝕜).operatorGauge
      (Lp 𝕜 2 ν) (Lp 𝕜 2 μ)).finiteSubmodule := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 ν)
  rw [OperatorIdealFamily.mem_finiteSubmodule_hilbertSchmidt_iff _ b,
    hilbertSchmidtEnergy_integralOperatorL2]
  exact ENNReal.pow_ne_top eNorm_ne_top

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

variable (μ ν) in
/-- **The kernel-to-operator map as a linear isometry** from `L²(μ ⊗ ν)` into the Hilbert–Schmidt
ideal `𝓛₂(L²(ν), L²(μ))`, normed by the Hilbert–Schmidt norm. -/
def integralOperatorL2HS : Lp 𝕜 2 (μ.prod ν) →ₗᵢ[𝕜]
    ((OperatorIdealFamily.hilbertSchmidt 𝕜).operatorGauge (Lp 𝕜 2 ν) (Lp 𝕜 2 μ)).Carrier where
  toFun K := ⟨integralOperatorL2 μ ν K, integralOperatorL2_mem_finiteSubmodule_hilbertSchmidt K⟩
  map_add' K L := by ext1; simp
  map_smul' c K := by ext1; simp
  norm_map' K := by
    rw [OperatorGauge.Carrier.norm_def, OperatorIdealFamily.operatorGauge_apply,
      OperatorIdealFamily.toReal_gauge_hilbertSchmidt]
    exact hilbertSchmidtNorm_integralOperatorL2 K

@[simp]
theorem toContinuousLinearMap_integralOperatorL2HS (K : Lp 𝕜 2 (μ.prod ν)) :
    (integralOperatorL2HS μ ν K).toContinuousLinearMap = integralOperatorL2 μ ν K :=
  (rfl)

/-- **Uniqueness of the kernel.** Kernels with the same integral operator are equal in
`L²(μ ⊗ ν)`. -/
theorem integralOperatorL2_injective :
    Function.Injective (integralOperatorL2 μ ν : Lp 𝕜 2 (μ.prod ν) → _) := by
  intro K L h
  refine (integralOperatorL2HS μ ν).injective
    (OperatorGauge.Carrier.toContinuousLinearMap_injective ?_)
  rwa [toContinuousLinearMap_integralOperatorL2HS, toContinuousLinearMap_integralOperatorL2HS]

end HilbertSchmidt

end TauCeti
