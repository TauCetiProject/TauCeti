/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.L2.Product
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Integral operators with square-integrable kernels

Let `μ` and `ν` be measures on `α` and `β`, with `ν` s-finite, and scalars `𝕜 = ℝ` or `ℂ`. A
kernel `K ∈ L²(μ ⊗ ν)` defines the integral operator

`T_K f = (x ↦ ∫ y, K (x, y) * f y ∂ν) : L²(ν) → L²(μ)`.

For almost every `x` the section `K (x, ·)` is square integrable, so by the Cauchy–Schwarz
inequality the integral converges and `|T_K f (x)| ≤ ‖K (x, ·)‖₂ ‖f‖₂`. Integrating in `x` gives
`‖T_K f‖₂ ≤ ‖K‖₂ ‖f‖₂`, so `K ↦ T_K` is a bounded bilinear map
`TauCeti.integralOperatorL2 : L²(μ ⊗ ν) →L[𝕜] L²(ν) →L[𝕜] L²(μ)`. For a fixed kernel the
operator is `TauCeti.integralOperatorLpOfBound`, the constructor shared with Schur's test.

The Hilbert–Schmidt norm of `T_K` is computed in
`TauCeti.MeasureTheory.Function.Lp.Operator.Integral.HilbertSchmidt`.

## Main declarations

* `TauCeti.eLpNorm_integral_mul_le`, `TauCeti.memLp_integral_mul`,
  `TauCeti.ae_integrable_kernel_mul`: for square-integrable functions `K` on `α × β` and `f` on
  `β`, the integral `x ↦ ∫ y, K (x, y) * f y ∂ν` converges almost everywhere and is square
  integrable with `L²` norm at most `‖K‖₂ ‖f‖₂`.
* `TauCeti.integralOperatorL2`: the integral operator of a kernel in `L²(μ ⊗ ν)`, as a bounded
  bilinear map.
* `TauCeti.coeFn_integralOperatorL2`: the operator computes `x ↦ ∫ y, K (x, y) * f y ∂ν` almost
  everywhere.
* `TauCeti.integralOperatorL2_eq_iff`: `T_K f` is the unique `L²` class agreeing almost everywhere
  with `x ↦ ∫ y, K (x, y) * f y ∂ν`.
* `TauCeti.inner_integralOperatorL2`: `⟪h, T_K f⟫ = ⟪h ⊗ star f, K⟫`.
* `TauCeti.integralOperatorL2_prodMul_star`: the kernel `w ⊗ star u` gives the rank-one operator
  `InnerProductSpace.rankOne 𝕜 w u = ⟪u, ·⟫ • w`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS, 2014, §6.3, (6.8)–(6.9).
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Lp
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

variable {α β 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

namespace TauCeti

variable [SFinite ν]

/-! ### Square-integrable kernels on functions -/

/-- **Cauchy–Schwarz for kernels.** The integral `x ↦ ∫ y, K (x, y) * f y ∂ν` has `L²` norm at
most `‖K‖₂ ‖f‖₂`. -/
theorem eLpNorm_integral_mul_le {K : α × β → 𝕜} {f : β → 𝕜}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : AEStronglyMeasurable f ν) :
    eLpNorm (fun x ↦ ∫ y, K (x, y) * f y ∂ν) 2 μ ≤ eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν := by
  calc eLpNorm (fun x ↦ ∫ y, K (x, y) * f y ∂ν) 2 μ
      ≤ eLpNorm (fun x ↦ eLpNorm f 2 ν * eLpNorm (fun y ↦ K (x, y)) 2 ν) 2 μ := by
        refine eLpNorm_mono_eNorm (hK.mul hf.comp_snd).integral_prod_right' fun x ↦ ?_
        rw [eNorm_eq_self, mul_comm]
        exact enorm_integral_mul_le (p := 2) (q := 2)
    _ = eLpNorm f 2 ν * eLpNorm K 2 (μ.prod ν) := by
        rw [eLpNorm_const_mul_ennreal hK.eLpNorm_prod_right,
          ← eLpNorm_prod_eq_eLpNorm_eLpNorm hK]
    _ = _ := mul_comm _ _

/-- For square-integrable `K` and `f`, the integral `x ↦ ∫ y, K (x, y) * f y ∂ν` is square
integrable. -/
theorem memLp_integral_mul {K : α × β → 𝕜} {f : β → 𝕜} (hK : MemLp K 2 (μ.prod ν))
    (hf : MemLp f 2 ν) : MemLp (fun x ↦ ∫ y, K (x, y) * f y ∂ν) 2 μ :=
  (eLpNorm_integral_mul_le hK.aestronglyMeasurable hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top hK.eLpNorm_lt_top hf.eLpNorm_lt_top)

/-- For square-integrable `K` and `f`, the integrand `y ↦ K (x, y) * f y` is integrable for
almost every `x`. -/
theorem ae_integrable_kernel_mul {K : α × β → 𝕜} {f : β → 𝕜} (hK : MemLp K 2 (μ.prod ν))
    (hf : MemLp f 2 ν) : ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) * f y) ν := by
  filter_upwards [hK.ae_memLp_prod_right] with x hx
  exact hx.integrable_mul hf

/-! ### The integral operator -/

/-- The integral operator of a fixed kernel `K ∈ L²(μ ⊗ ν)`; see `integralOperatorL2`. -/
private def kernelOperator (K : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  integralOperatorLpOfBound (fun x y ↦ ContinuousLinearMap.mul 𝕜 𝕜 (K (x, y))) 2 2
    (fun f ↦ by
      simpa only [ContinuousLinearMap.mul_apply'] using
        ae_integrable_kernel_mul (Lp.memLp K) (Lp.memLp f))
    (fun f ↦ by
      simpa only [ContinuousLinearMap.mul_apply'] using
        memLp_integral_mul (Lp.memLp K) (Lp.memLp f))
    ‖K‖₊ fun f ↦ by
      simpa only [ContinuousLinearMap.mul_apply', ← Lp.eNorm_def, eNorm_eq_nnNorm] using
        eLpNorm_integral_mul_le (Lp.aestronglyMeasurable K) (Lp.aestronglyMeasurable f)

private theorem coeFn_kernelOperator (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelOperator K f =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν :=
  coeFn_integralOperatorLpOfBound f

private theorem kernelOperator_eq {K : Lp 𝕜 2 (μ.prod ν)} {f : Lp 𝕜 2 ν} {g : Lp 𝕜 2 μ}
    (h : g =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν) : kernelOperator K f = g :=
  Lp.ext ((coeFn_kernelOperator K f).trans h.symm)

private theorem norm_kernelOperator_le (K : Lp 𝕜 2 (μ.prod ν)) : ‖kernelOperator K‖ ≤ ‖K‖ :=
  norm_integralOperatorLpOfBound_le

private theorem kernelOperator_add (K L : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelOperator (K + L) f = kernelOperator K f + kernelOperator L f := by
  apply kernelOperator_eq
  filter_upwards [Lp.coeFn_add (kernelOperator K f) (kernelOperator L f),
    coeFn_kernelOperator K f, coeFn_kernelOperator L f,
    ae_integrable_kernel_mul (Lp.memLp K) (Lp.memLp f),
    ae_integrable_kernel_mul (Lp.memLp L) (Lp.memLp f),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add K L)] with x hx hK hL hiK hiL hKL
  rw [hx, Pi.add_apply, hK, hL, ← integral_add hiK hiL]
  refine integral_congr_ae ?_
  filter_upwards [hKL] with y hy
  rw [hy, Pi.add_apply, add_mul]

private theorem kernelOperator_smul (c : 𝕜) (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelOperator (c • K) f = c • kernelOperator K f := by
  apply kernelOperator_eq
  filter_upwards [Lp.coeFn_smul c (kernelOperator K f), coeFn_kernelOperator K f,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c K)] with x hx hK hcK
  rw [hx, Pi.smul_apply, hK, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hcK] with y hy
  rw [hy, Pi.smul_apply, smul_eq_mul, mul_assoc]

variable (μ ν) in
/-- **The integral operator of a square-integrable kernel.** A kernel `K ∈ L²(μ ⊗ ν)` acts by
`f ↦ (x ↦ ∫ y, K (x, y) * f y ∂ν)` from `L²(ν)` to `L²(μ)`; see `coeFn_integralOperatorL2`. The
assignment is bilinear, and `‖integralOperatorL2 μ ν K f‖ ≤ ‖K‖ * ‖f‖`. -/
def integralOperatorL2 : Lp 𝕜 2 (μ.prod ν) →L[𝕜] Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous
    { toFun := kernelOperator
      map_add' K L := ContinuousLinearMap.ext (kernelOperator_add K L)
      map_smul' c K := ContinuousLinearMap.ext (kernelOperator_smul c K) }
    1 fun K ↦ by simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using
      norm_kernelOperator_le K

/-- **The integral formula.** `integralOperatorL2 μ ν K f` is almost everywhere
`x ↦ ∫ y, K (x, y) * f y ∂ν`; the integrand is integrable for almost every `x` by
`ae_integrable_kernel_mul`. -/
theorem coeFn_integralOperatorL2 (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    integralOperatorL2 μ ν K f =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν :=
  coeFn_kernelOperator K f

/-- The integral operator applied to `f` is the unique `L²` class that agrees almost everywhere
with `x ↦ ∫ y, K (x, y) * f y ∂ν`. -/
theorem integralOperatorL2_eq_iff {K : Lp 𝕜 2 (μ.prod ν)} {f : Lp 𝕜 2 ν} {g : Lp 𝕜 2 μ} :
    integralOperatorL2 μ ν K f = g ↔ g =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν :=
  ⟨fun h ↦ h ▸ coeFn_integralOperatorL2 K f, kernelOperator_eq⟩

/-- The operator norm of the integral operator is at most the `L²` norm of its kernel. -/
theorem norm_integralOperatorL2_apply_le (K : Lp 𝕜 2 (μ.prod ν)) :
    ‖integralOperatorL2 μ ν K‖ ≤ ‖K‖ :=
  norm_kernelOperator_le K

/-- **The kernel pairing.** For `h ∈ L²(μ)` and `f ∈ L²(ν)`,
`⟪h, T_K f⟫ = ⟪h ⊗ star f, K⟫ = ∫∫ conj (h x) * K (x, y) * f y`. -/
theorem inner_integralOperatorL2 [SFinite μ] (K : Lp 𝕜 2 (μ.prod ν)) (h : Lp 𝕜 2 μ)
    (f : Lp 𝕜 2 ν) :
    ⟪h, integralOperatorL2 μ ν K f⟫_𝕜 = ⟪prodMul h (star f), K⟫_𝕜 := by
  have hint : Integrable (fun p : α × β ↦ conj (h p.1) * (K p * f p.2)) (μ.prod ν) := by
    have := ((Lp.memLp (star h)).mul_prod (Lp.memLp f)).integrable_mul (Lp.memLp K)
    refine this.congr ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp (coeFn_star h)] with p hp
    simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def] at hp
    simp only [Pi.mul_apply, hp]
    ring
  rw [L2.inner_def, L2.inner_def]
  calc ∫ x, ⟪h x, integralOperatorL2 μ ν K f x⟫_𝕜 ∂μ
      = ∫ x, ∫ y, conj (h x) * (K (x, y) * f y) ∂ν ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_integralOperatorL2 K f] with x hx
        rw [hx, RCLike.inner_apply, integral_const_mul, mul_comm]
    _ = ∫ p, conj (h p.1) * (K p * f p.2) ∂(μ.prod ν) := (integral_prod _ hint).symm
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_prodMul h (star f),
          Measure.quasiMeasurePreserving_snd.ae_eq_comp (coeFn_star f)] with p hp hs
        simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def] at hs
        simp only [hp, hs, RCLike.inner_apply, map_mul, RCLike.conj_conj]
        ring

/-- **Rank-one kernels.** The kernel `(x, y) ↦ w x * conj (u y)` gives the rank-one operator
`rankOne 𝕜 w u = ⟪u, ·⟫ • w`. -/
@[simp]
theorem integralOperatorL2_prodMul_star (w : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν) :
    integralOperatorL2 μ ν (prodMul w (star u)) = InnerProductSpace.rankOne 𝕜 w u := by
  ext1 f
  refine integralOperatorL2_eq_iff.2 ?_
  rw [InnerProductSpace.rankOne_apply]
  filter_upwards [Lp.coeFn_smul ⟪u, f⟫_𝕜 w,
    Measure.ae_ae_of_ae_prod (coeFn_prodMul w (star u))] with x hx hK
  rw [hx, Pi.smul_apply, smul_eq_mul, L2.inner_def, mul_comm, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hK, coeFn_star u] with y hy hs
  simp only [hy, hs, Pi.star_apply, RCLike.star_def, RCLike.inner_apply]
  ring

end TauCeti
