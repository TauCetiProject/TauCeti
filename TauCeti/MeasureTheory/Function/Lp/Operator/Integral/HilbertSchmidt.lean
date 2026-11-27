/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.L2.Product
public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Iterated

/-!
# Integral operators with square-integrable kernels

Let `μ` and `ν` be σ-finite measures on `α` and `β`, with scalars `𝕜 = ℝ` or `ℂ`. A kernel
`K ∈ L²(μ ⊗ ν)` defines the integral operator

`T_K f = (x ↦ ∫ y, K (x, y) * f y ∂ν) : L²(ν) → L²(μ)`.

For almost every `x` the section `K (x, ·)` is square integrable, so by the Cauchy–Schwarz
inequality the integral converges and `|T_K f (x)| ≤ ‖K (x, ·)‖₂ ‖f‖₂`. Integrating in `x` gives
`‖T_K f‖₂ ≤ ‖K‖₂ ‖f‖₂`, so `K ↦ T_K` is a bounded bilinear map
`TauCeti.integralOperatorL2 : L²(μ ⊗ ν) →L[𝕜] L²(ν) →L[𝕜] L²(μ)`.

The operator `T_K` is Hilbert–Schmidt with Hilbert–Schmidt norm exactly `‖K‖₂`. Fubini's theorem
gives `⟪h, T_K f⟫ = ⟪h ⊗ star f, K⟫` for `h ∈ L²(μ)` and `f ∈ L²(ν)`. For Hilbert bases `(aⱼ)` of
`L²(μ)` and `(bᵢ)` of `L²(ν)`, the tensors `aⱼ ⊗ star bᵢ` form a Hilbert basis of `L²(μ ⊗ ν)`
(`HilbertBasis.prod` applied to `(aⱼ)` and the conjugate basis `HilbertBasis.star`), so Parseval's
identity turns the Hilbert–Schmidt energy `∑ᵢ ∑ⱼ |⟪aⱼ, T_K bᵢ⟫|²` into `‖K‖₂²`. No
countability of the bases is needed. In particular the kernel-to-operator map is an isometric
linear embedding of `L²(μ ⊗ ν)` into the Hilbert–Schmidt operators.

## Main declarations

* `HilbertBasis.star`: the complex conjugate of a Hilbert basis of `L²`.
* `TauCeti.integralOperatorL2`: the integral operator of a kernel in `L²(μ ⊗ ν)`, as a bounded
  bilinear map.
* `TauCeti.ae_integrable_kernel_mul`, `TauCeti.coeFn_integralOperatorL2`: the defining integral
  converges and computes `T_K f` almost everywhere.
* `TauCeti.integralOperatorL2_eq_iff`: `T_K f` is the unique `L²` class agreeing almost everywhere
  with `x ↦ ∫ y, K (x, y) * f y ∂ν`.
* `TauCeti.inner_integralOperatorL2`: `⟪h, T_K f⟫ = ⟪h ⊗ star f, K⟫`.
* `TauCeti.hilbertSchmidtEnergy_integralOperatorL2`,
  `TauCeti.hilbertSchmidtNorm_integralOperatorL2`: the Hilbert–Schmidt energy and norm of `T_K`
  are `‖K‖₂²` and `‖K‖₂`.
* `TauCeti.integralOperatorL2_mem_hilbertSchmidt`: `T_K` lies in the Hilbert–Schmidt ideal.
* `TauCeti.integralOperatorL2_injective`: equal operators have equal kernel classes.
* `TauCeti.integralOperatorL2HS`: the kernel-to-operator map as a linear isometry into the
  normed Hilbert–Schmidt ideal.
* `TauCeti.integralOperatorL2_prodMul_star`: the kernel `w ⊗ star u` gives the rank-one operator
  `f ↦ ⟪u, f⟫ w`, whose Hilbert–Schmidt norm is therefore `‖u‖₂ ‖w‖₂`.

## Implementation notes

The roadmap target asks for σ-finite standard Borel spaces with separable `L²` spaces and
countable bases. Neither standard Borel structure nor separability is used: σ-finiteness of the
factors is what `HilbertBasis.prod` needs, and the bilinear map itself only needs `ν` to be
s-finite.

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

/-! ### Complex conjugation on `L²` -/

namespace MeasureTheory.Lp

/-- Conjugating both arguments of the `L²` inner product swaps them. -/
theorem inner_star_star (f g : Lp 𝕜 2 ν) : ⟪star f, star g⟫_𝕜 = ⟪g, f⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_star f, coeFn_star g] with y hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

/-- Conjugating the first argument of the `L²` inner product gives the bilinear pairing
`∫ f g`, which is symmetric. -/
theorem inner_star_left_comm (f g : Lp 𝕜 2 ν) : ⟪star f, g⟫_𝕜 = ⟪star g, f⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_star f, coeFn_star g] with y hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

@[simp]
theorem star_eq_zero_iff {f : Lp 𝕜 2 ν} : star f = 0 ↔ f = 0 := by
  constructor <;> intro h
  · rw [← norm_eq_zero, ← sq_eq_zero_iff, ← inner_self_eq_norm_sq (𝕜 := 𝕜), ← inner_star_star,
      h, inner_zero_left, map_zero]
  · rw [h, ← norm_eq_zero, ← sq_eq_zero_iff, ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_star_star,
      inner_zero_left, map_zero]

end MeasureTheory.Lp

namespace HilbertBasis

variable {ι : Type*}

/-- The pointwise complex conjugate of a Hilbert basis of `L²(ν)` is again a Hilbert basis. -/
protected def star (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν) :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun i ↦ star (b i))
    (by
      classical
      have hb := orthonormal_iff_ite.1 b.orthonormal
      refine orthonormal_iff_ite.2 fun i j ↦ ?_
      rw [inner_star_star, hb j i]
      simp only [eq_comm])
    (by
      refine (Submodule.eq_bot_iff _).2 fun h hh ↦ ?_
      rw [Submodule.mem_orthogonal] at hh
      rw [← star_star h, star_eq_zero_iff]
      refine b.eq_zero_of_forall_inner_eq_zero fun i ↦ ?_
      rw [inner_star_left_comm]
      exact hh _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp]
theorem star_apply (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 ν)) (i : ι) : b.star i = star (b i) := by
  rw [HilbertBasis.star, HilbertBasis.coe_mkOfOrthogonalEqBot]

end HilbertBasis

/-! ### The integral operator -/

namespace TauCeti

variable [SFinite ν]

/-- For almost every `x`, the integrand `y ↦ K (x, y) * f y` of the integral operator is
integrable. -/
theorem ae_integrable_kernel_mul (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) * f y) ν := by
  filter_upwards [(Lp.memLp K).ae_memLp_prod_right] with x hx
  exact hx.integrable_mul (Lp.memLp f)

/-- The defining integral of the integral operator is an `L²` function, with norm at most
`‖K‖₂ ‖f‖₂`. -/
private theorem memLp_and_eLpNorm_le (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    MemLp (fun x ↦ ∫ y, K (x, y) * f y ∂ν) 2 μ ∧
      eLpNorm (fun x ↦ ∫ y, K (x, y) * f y ∂ν) 2 μ ≤
        eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν := by
  have hK := Lp.aestronglyMeasurable K
  have hf := Lp.aestronglyMeasurable f
  have hmeas : AEStronglyMeasurable (fun x ↦ ∫ y, K (x, y) * f y ∂ν) μ :=
    (hK.mul hf.comp_snd).integral_prod_right'
  have hle : eLpNorm (fun x ↦ ∫ y, K (x, y) * f y ∂ν) 2 μ ≤
      eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν := by
    calc eLpNorm (fun x ↦ ∫ y, K (x, y) * f y ∂ν) 2 μ
        ≤ eLpNorm (fun x ↦ eLpNorm f 2 ν * eLpNorm (fun y ↦ K (x, y)) 2 ν) 2 μ := by
          refine eLpNorm_mono_eNorm_ae hmeas (ae_of_all _ fun x ↦ ?_)
          rw [eNorm_eq_self, mul_comm]
          exact enorm_integral_mul_le (p := 2) (q := 2)
      _ = eLpNorm f 2 ν * eLpNorm K 2 (μ.prod ν) := by
          rw [eLpNorm_const_mul_ennreal hK.eLpNorm_prod_right,
            ← eLpNorm_prod_eq_eLpNorm_eLpNorm hK]
      _ = _ := mul_comm _ _
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top K) (Lp.eLpNorm_lt_top f)), hle⟩

/-- The `L²` class of `x ↦ ∫ y, K (x, y) * f y ∂ν`; see `integralOperatorL2`. -/
private def kernelApply (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) : Lp 𝕜 2 μ :=
  (memLp_and_eLpNorm_le K f).1.toLp _

private theorem coeFn_kernelApply (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelApply K f =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν :=
  MemLp.coeFn_toLp _

private theorem kernelApply_eq {K : Lp 𝕜 2 (μ.prod ν)} {f : Lp 𝕜 2 ν} {g : Lp 𝕜 2 μ}
    (h : g =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν) : kernelApply K f = g :=
  Lp.ext ((coeFn_kernelApply K f).trans h.symm)

private theorem norm_kernelApply_le (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    ‖kernelApply K f‖ ≤ ‖K‖ * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul,
    eLpNorm_congr_ae (coeFn_kernelApply K f)]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top K) (Lp.eLpNorm_ne_top f))
    (memLp_and_eLpNorm_le K f).2

private theorem kernelApply_add_right (K : Lp 𝕜 2 (μ.prod ν)) (f g : Lp 𝕜 2 ν) :
    kernelApply K (f + g) = kernelApply K f + kernelApply K g := by
  apply kernelApply_eq
  filter_upwards [Lp.coeFn_add (kernelApply K f) (kernelApply K g), coeFn_kernelApply K f,
    coeFn_kernelApply K g, ae_integrable_kernel_mul K f, ae_integrable_kernel_mul K g]
    with x hx hf hg hif hig
  rw [hx, Pi.add_apply, hf, hg, ← integral_add hif hig]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f g] with y hy
  rw [hy, Pi.add_apply, mul_add]

private theorem kernelApply_smul_right (K : Lp 𝕜 2 (μ.prod ν)) (c : 𝕜) (f : Lp 𝕜 2 ν) :
    kernelApply K (c • f) = c • kernelApply K f := by
  apply kernelApply_eq
  filter_upwards [Lp.coeFn_smul c (kernelApply K f), coeFn_kernelApply K f] with x hx hf
  rw [hx, Pi.smul_apply, hf, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with y hy
  rw [hy, Pi.smul_apply, smul_eq_mul]
  ring

private theorem kernelApply_add_left (K L : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelApply (K + L) f = kernelApply K f + kernelApply L f := by
  apply kernelApply_eq
  filter_upwards [Lp.coeFn_add (kernelApply K f) (kernelApply L f), coeFn_kernelApply K f,
    coeFn_kernelApply L f, ae_integrable_kernel_mul K f, ae_integrable_kernel_mul L f,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add K L)] with x hx hK hL hiK hiL hKL
  rw [hx, Pi.add_apply, hK, hL, ← integral_add hiK hiL]
  refine integral_congr_ae ?_
  filter_upwards [hKL] with y hy
  rw [hy, Pi.add_apply, add_mul]

private theorem kernelApply_smul_left (c : 𝕜) (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelApply (c • K) f = c • kernelApply K f := by
  apply kernelApply_eq
  filter_upwards [Lp.coeFn_smul c (kernelApply K f), coeFn_kernelApply K f,
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
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 kernelApply kernelApply_add_left kernelApply_smul_left
      kernelApply_add_right fun c K f ↦ kernelApply_smul_right K c f)
    1 fun K f ↦ by simpa only [LinearMap.mk₂_apply, one_mul] using norm_kernelApply_le K f

/-- **The integral formula.** `integralOperatorL2 μ ν K f` is almost everywhere
`x ↦ ∫ y, K (x, y) * f y ∂ν`; the integrand is integrable for almost every `x` by
`ae_integrable_kernel_mul`. -/
theorem coeFn_integralOperatorL2 (K : Lp 𝕜 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    integralOperatorL2 μ ν K f =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν :=
  coeFn_kernelApply K f

/-- The integral operator applied to `f` is the unique `L²` class that agrees almost everywhere
with `x ↦ ∫ y, K (x, y) * f y ∂ν`. -/
theorem integralOperatorL2_eq_iff {K : Lp 𝕜 2 (μ.prod ν)} {f : Lp 𝕜 2 ν} {g : Lp 𝕜 2 μ} :
    integralOperatorL2 μ ν K f = g ↔ g =ᵐ[μ] fun x ↦ ∫ y, K (x, y) * f y ∂ν :=
  ⟨fun h ↦ h ▸ coeFn_integralOperatorL2 K f, kernelApply_eq⟩

/-- The operator norm of the integral operator is at most the `L²` norm of its kernel. -/
theorem norm_integralOperatorL2_apply_le (K : Lp 𝕜 2 (μ.prod ν)) :
    ‖integralOperatorL2 μ ν K‖ ≤ ‖K‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K) (norm_kernelApply_le K)

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

/-! ### The Hilbert–Schmidt norm -/

section HilbertSchmidt

variable [SigmaFinite μ] [SigmaFinite ν]

/-- **The Hilbert–Schmidt energy of an integral operator** is the squared `L²` norm of its kernel,
in every Hilbert basis of the source. -/
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
theorem integralOperatorL2_mem_hilbertSchmidt (K : Lp 𝕜 2 (μ.prod ν)) :
    integralOperatorL2 μ ν K ∈ ((OperatorIdealFamily.hilbertSchmidt 𝕜).operatorGauge
      (Lp 𝕜 2 ν) (Lp 𝕜 2 μ)).finiteSubmodule := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 ν)
  rw [OperatorIdealFamily.mem_finiteSubmodule_hilbertSchmidt_iff _ b,
    hilbertSchmidtEnergy_integralOperatorL2]
  exact ENNReal.pow_ne_top eNorm_ne_top

/-- **Uniqueness of the kernel.** Kernels with the same integral operator are equal in
`L²(μ ⊗ ν)`. -/
theorem integralOperatorL2_injective :
    Function.Injective (integralOperatorL2 μ ν : Lp 𝕜 2 (μ.prod ν) → _) := by
  intro K L h
  rw [← sub_eq_zero, ← norm_eq_zero, ← hilbertSchmidtNorm_integralOperatorL2, map_sub, h,
    sub_self, ContinuousLinearMap.hilbertSchmidtNorm_zero]

variable (μ ν) in
/-- **The kernel-to-operator map as a linear isometry** from `L²(μ ⊗ ν)` into the Hilbert–Schmidt
ideal `𝓛₂(L²(ν), L²(μ))`, normed by the Hilbert–Schmidt norm. -/
@[expose] def integralOperatorL2HS : Lp 𝕜 2 (μ.prod ν) →ₗᵢ[𝕜]
    ((OperatorIdealFamily.hilbertSchmidt 𝕜).operatorGauge (Lp 𝕜 2 ν) (Lp 𝕜 2 μ)).Carrier where
  toFun K := ⟨integralOperatorL2 μ ν K, integralOperatorL2_mem_hilbertSchmidt K⟩
  map_add' K L := by ext1; simp
  map_smul' c K := by ext1; simp
  norm_map' K := by
    rw [OperatorGauge.Carrier.norm_def, OperatorIdealFamily.operatorGauge_apply,
      OperatorIdealFamily.toReal_gauge_hilbertSchmidt]
    exact hilbertSchmidtNorm_integralOperatorL2 K

@[simp]
theorem integralOperatorL2HS_apply (K : Lp 𝕜 2 (μ.prod ν)) :
    (integralOperatorL2HS μ ν K).toContinuousLinearMap = integralOperatorL2 μ ν K :=
  rfl

omit [SigmaFinite ν] in
/-- **Rank-one kernels.** The kernel `(x, y) ↦ w x * conj (u y)` gives the rank-one operator
`f ↦ ⟪u, f⟫ w`. -/
theorem integralOperatorL2_prodMul_star (w : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν) :
    integralOperatorL2 μ ν (prodMul w (star u)) = (innerSL 𝕜 u).smulRight w := by
  ext1 f
  refine ext_inner_left 𝕜 fun h ↦ ?_
  rw [inner_integralOperatorL2, inner_prodMul, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, inner_smul_right, inner_star_star, mul_comm]

/-- The rank-one operator `f ↦ ⟪u, f⟫ w` between `L²` spaces has Hilbert–Schmidt norm
`‖u‖ * ‖w‖`. -/
theorem hilbertSchmidtNorm_smulRight_innerSL (u : Lp 𝕜 2 ν) (w : Lp 𝕜 2 μ) :
    ((innerSL 𝕜 u).smulRight w).hilbertSchmidtNorm = ‖u‖ * ‖w‖ := by
  rw [← integralOperatorL2_prodMul_star, hilbertSchmidtNorm_integralOperatorL2, norm_prodMul,
    mul_comm]
  congr 1
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← RCLike.ofReal_inj (K := 𝕜),
    RCLike.ofReal_pow, RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K,
    ← inner_self_eq_norm_sq_to_K, inner_star_star]

end HilbertSchmidt

end TauCeti
