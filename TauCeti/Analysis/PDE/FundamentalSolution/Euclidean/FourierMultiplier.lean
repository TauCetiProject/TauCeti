/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential
public import TauCeti.Analysis.PDE.FundamentalSolution.FourierMultiplier
import TauCeti.Analysis.Normed.Group.Bounded
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Hessian
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.MeasureTheory.Function.Lp.Integral.BoundedSmul

/-!
# The kernel of the Hessian Fourier multiplier and the Riesz transforms of the Newtonian potential

For `v, w ∈ ℝⁿ`, the Fourier multiplier `T_{m_{v,w}}` on `L²(ℝⁿ, F)` with symbol
`m_{v,w}(ξ) = ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` (`TauCeti.hessianSymbolLp`) is the operator `∂_v ∂_w Δ⁻¹`
(`SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM`). This file shows that for
`n ≥ 3` it is a singular integral operator whose kernel is the Hessian of the Newtonian kernel
`Gₙ = TauCeti.newtonianKernel n`: if `f ∈ L²` vanishes off a compact set `s`, then for almost
every `x ∉ s`

`T_{m_{v,w}} f (x) = -∫ D²Gₙ(x - y)(v, w) f(y) dy`

(`TauCeti.ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral`). Together with the size and
smoothness estimates of `D²Gₙ` (`TauCeti.norm_iteratedFDeriv_two_newtonianKernel_le`,
`TauCeti.norm_iteratedFDeriv_two_newtonianKernel_sub_le`), this is the kernel representation that
the Calderón–Zygmund theory asks of an `L²`-bounded operator before it bounds the operator on
`Lᵖ`, `1 < p < ∞`; for `T_{m_{v,w}}` that bound is the estimate `‖∂_v ∂_w u‖_p ≤ C ‖Δu‖_p`.

## The argument

For `φ` smooth with compact support, the Newtonian potential `u = Gₙ ⋆ φ` solves `-Δu = φ`, so
`T_{m_{v,w}} φ` should be `-∂_v ∂_w u`. The identity `∂_v ∂_w = T_{m_{v,w}} ∘ Δ` holds on Schwartz
functions, and `u` is not one, but the identity extends to smooth solutions of Poisson's equation
that grow slowly enough at infinity
(`TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg`).
For `n ≥ 3` the potential decays: `u = O(‖x‖ ^ (2 - n))` and `Du = O(‖x‖ ^ (1 - n))`
(`TauCeti.norm_newtonianKernel_convolution_le`,
`TauCeti.norm_fderiv_newtonianKernel_convolution_le`). In dimension one `u` grows linearly
(`TauCeti.norm_newtonianKernel_one_convolution_le`) and `Du` is bounded, which is still slow
enough. Hence `T_{m_{v,w}} φ = -∂_v ∂_w u` almost everywhere for `n = 1` and `n ≥ 3`
(`TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp`). Since `T_{m_{v,w}} = -R_v R_w` for
the Riesz transforms, this gives `D²u(v, w) = R_v R_w φ`
(`TauCeti.coeFn_rieszTransform_rieszTransform_toLp_newtonianKernel`).

Off the support of `φ`, integrating by parts twice moves the derivatives from `φ` onto the
kernel: `D²u(x)(v, w) = ∫ D²Gₙ(x - y)(v, w) φ(y) dy`
(`TauCeti.iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport`). A general
`f ∈ L²` vanishing off `s` is the `L²` limit of smooth functions supported in shrinking
thickenings of `s`
(`MeasureTheory.MemLp.exist_contDiff_tsupport_subset_eLpNorm_sub_le`).
For `x ∉ s` the kernel is bounded on a fixed thickening of `s`, so the kernel integrals converge
(`TauCeti.tendsto_integral_smul_of_tendsto_eLpNorm_sub`), while `T_{m_{v,w}}` of the approximations
converges almost everywhere along a subsequence.

## Main declarations

* `TauCeti.iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport`: the second
  derivatives of the Newtonian potential off the support of the density.
* `TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp`: `T_{m_{v,w}} φ = -D²(Gₙ ⋆ φ)(v, w)`
  for `φ` smooth with compact support, `n = 1` or `n ≥ 3`.
* `TauCeti.coeFn_rieszTransform_rieszTransform_toLp_newtonianKernel`:
  `D²(Gₙ ⋆ φ)(v, w) = R_v R_w φ` for `n = 1` and `n ≥ 3`.
* `TauCeti.ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral`: the kernel representation of
  `T_{m_{v,w}}` off the support of its argument.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.4 and Section 9.4.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set Topology
open scoped Convolution ContDiff

variable {n : ℕ}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : EuclideanSpace ℝ (Fin n) → F}

/-- For `n = 1` and for `n ≥ 3`, the Newtonian potential `u = Gₙ ⋆ φ` of a continuous `φ` with
compact support satisfies the growth conditions of
`TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg`:
`‖x‖ ^ (n/2 - 2) ‖u x‖ → 0` and `‖x‖ ^ (n/2 - 1) ‖Du x‖ → 0` at infinity. For `n ≥ 3` this is the
decay `u = O(‖x‖ ^ (2 - n))`, `Du = O(‖x‖ ^ (1 - n))`; for `n = 1` the potential grows linearly
and its derivative is bounded. -/
private theorem tendsto_newtonianKernel_convolution_growth (hn : n = 1 ∨ 3 ≤ n)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun x => ‖x‖ ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) / 2 - 2) *
        ‖(newtonianKernel n ⋆ φ) x‖) (cocompact _) (𝓝 0) ∧
      Tendsto (fun x => ‖x‖ ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) / 2 - 1) *
        ‖fderiv ℝ (newtonianKernel n ⋆ φ) x‖) (cocompact _) (𝓝 0) := by
  have hn1 : (1 : ℝ) ≤ n := by rcases hn with rfl | hn <;> [norm_num; exact_mod_cast (by omega)]
  rw [finrank_euclideanSpace_fin, ← Metric.cobounded_eq_cocompact]
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hRs : Function.support φ ⊆ closedBall 0 R :=
    (subset_tsupport φ).trans (hR₀.trans (closedBall_subset_closedBall (le_max_left _ _)))
  have hV := volume_real_unitBall_pos n
  set I := ∫ y, ‖φ y‖
  -- Beyond `2R`, `‖x‖ - R` is comparable to `‖x‖`.
  have hsub : ∀ {b : ℝ} {x : EuclideanSpace ℝ (Fin n)}, 2 * R ≤ ‖x‖ →
      (‖x‖ - R) ^ b ≤ 2 ^ |b| * ‖x‖ ^ b := fun hx =>
    rpow_le_two_rpow_abs_mul (by linarith) (by linarith)
  refine ⟨?_, tendsto_norm_rpow_mul_cobounded_of_le (R := 2 * R)
    (K := 2 ^ |1 - (n : ℝ)| *
      (((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * I))
    (b := 1 - n) (by linarith) (fun x => norm_nonneg _) fun x hx => ?_⟩
  · rcases hn with rfl | hn
    · -- In dimension one, `‖u x‖ ≤ ‖x‖ ∫ ‖φ‖`.
      exact tendsto_norm_rpow_mul_cobounded_of_le (R := R) (K := I) (b := 1) (by norm_num)
        (fun x => norm_nonneg _) fun x hx => by
          rw [Real.rpow_one, mul_comm]
          exact norm_newtonianKernel_one_convolution_le (hφ.integrable_of_hasCompactSupport hc)
            hRs hx
    · -- For `n ≥ 3`, `‖u x‖ ≤ Cₙ (‖x‖ - R) ^ (2 - n) ∫ ‖φ‖`.
      have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
      refine tendsto_norm_rpow_mul_cobounded_of_le (R := 2 * R)
        (K := 2 ^ |2 - (n : ℝ)| *
          (((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * I))
        (b := 2 - n) (by linarith) (fun x => norm_nonneg _) fun x hx => ?_
      have hCn : 0 ≤ ((n : ℝ) * ((n : ℝ) - 2) *
          volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ :=
        inv_nonneg.2 (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hV.le)
      refine (norm_newtonianKernel_convolution_le hn hRs (by linarith)).trans ?_
      have h := hsub (b := 2 - n) hx
      calc _ = _ * (‖x‖ - R) ^ (2 - (n : ℝ)) * I := rfl
        _ ≤ ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
            (2 ^ |2 - (n : ℝ)| * ‖x‖ ^ (2 - (n : ℝ))) * I := by gcongr
        _ = _ := by ring
  · -- In every dimension, `‖Du x‖ ≤ Cₙ' (‖x‖ - R) ^ (1 - n) ∫ ‖φ‖`.
    refine (norm_fderiv_newtonianKernel_convolution_le hRs (by linarith)).trans ?_
    have h := hsub (b := 1 - n) hx
    calc _ ≤ ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
            (2 ^ |1 - (n : ℝ)| * ‖x‖ ^ (1 - (n : ℝ))) * I := by
          gcongr
      _ = _ := by ring

/-- Away from a closed set `s`, the kernel `y ↦ D²Gₙ(x - y)(v, w)` is continuous and bounded on a
closed thickening of `s`. -/
private theorem exists_continuousOn_norm_le_cthickening {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsClosed s) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ s) (v w : EuclideanSpace ℝ (Fin n)) :
    ∃ η > 0, x ∉ cthickening η s ∧ ∃ B, 0 ≤ B ∧
      ContinuousOn (fun y => iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w])
        (cthickening η s) ∧
      ∀ y ∈ cthickening η s, ‖iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w]‖ ≤ B := by
  -- Choose `η > 0` with `x ∉ cthickening (2η) s`; then `η ≤ ‖x - y‖` on `cthickening η s`.
  obtain ⟨η, hη, hxη⟩ : ∃ η > 0, x ∉ cthickening (η + η) s := by
    have : x ∉ closure s := hs.closure_eq.symm ▸ hx
    rw [closure_eq_iInter_cthickening] at this
    simp only [mem_iInter, not_forall] at this
    obtain ⟨δ, hδ, hxδ⟩ := this
    exact ⟨δ / 2, half_pos hδ, by rwa [add_halves]⟩
  have hdist : ∀ y ∈ cthickening η s, η ≤ ‖x - y‖ := fun y hy => by
    rw [← dist_eq_norm]
    by_contra h
    exact hxη (cthickening_cthickening_subset hη.le hη.le s
      (mem_cthickening_of_dist_le x y η _ hy (not_le.1 h).le))
  have hne : ∀ y ∈ cthickening η s, x - y ≠ 0 := fun y hy h => by
    have := hdist y hy
    rw [h, norm_zero] at this
    exact hη.not_ge this
  have := volume_real_unitBall_pos n
  refine ⟨η, hη, fun h => hxη (cthickening_mono (by linarith) s h),
    ((n : ℝ) + 1) * ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      η ^ (-(n : ℝ)) * (‖v‖ * ‖w‖), by positivity, fun y hy => ?_, fun y hy => ?_⟩
  · exact (((contDiffAt_newtonianKernel n (hne y hy)).continuousAt_iteratedFDeriv le_rfl).comp
      (continuous_const.sub continuous_id).continuousAt).eval_const _ |>.continuousWithinAt
  refine ((iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y)).le_opNorm _).trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine mul_le_mul_of_nonneg_right ((norm_iteratedFDeriv_two_newtonianKernel_le (x - y)).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))) (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hη (hdist y hy) (neg_nonpos.2 (Nat.cast_nonneg n))

section Multiplier

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {φ : EuclideanSpace ℝ (Fin n) → F}

open scoped Laplacian LineDeriv SchwartzMap

/-- **The Hessian multiplier on smooth functions with compact support.** For `n = 1` or `n ≥ 3`
and `φ` smooth with compact support on `ℝⁿ`, the Fourier multiplier `T_{m_{v,w}}` with symbol
`⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` sends `φ` to `-D²(Gₙ ⋆ φ)(v, w)`. Since `-Δ (Gₙ ⋆ φ) = φ`, this says that
`T_{m_{v,w}} = ∂_v ∂_w Δ⁻¹` on such functions, with `Δ⁻¹` given by the Newtonian potential.

The Newtonian potential `u = Gₙ ⋆ φ` is not a Schwartz function, but it grows slowly enough for
`TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg`. -/
theorem coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp (hn : n = 1 ∨ 3 ≤ n)
    (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v w : EuclideanSpace ℝ (Fin n)) :
    Lp.fourierMultiplierCLM F (hessianSymbolLp v w)
        ((hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).toLp φ) =ᵐ[volume]
      fun x => -iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ φ) x ![v, w] :=
  coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg
    (contDiff_newtonianKernel_convolution hφ hc)
    (laplacian_newtonianKernel_convolution (by omega) (by omega) (hφ.of_le (by simp)) hc) _ hc
    (tendsto_newtonianKernel_convolution_growth hn hφ.continuous hc).1
    (tendsto_newtonianKernel_convolution_growth hn hφ.continuous hc).2 v w

/-- **Second derivatives of the Newtonian potential are Riesz transforms.** For `n = 1` or
`n ≥ 3` and `φ` smooth with compact support on `ℝⁿ`, the Newtonian potential `u = Gₙ ⋆ φ`, the
solution of `-Δu = φ`, has second derivatives

`D²u(v, w) = R_v R_w φ`

almost everywhere, where `R_v` is the Riesz transform with symbol `-i ⟪ξ, v⟫ / ‖ξ‖`. On the
Fourier side both sides have symbol `-⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` times that of `φ`. In dimension one
`R_v R_w = -⟪v, w⟫` and the identity is `u'' = -φ`; in the plane the logarithmic kernel takes the
place of `Gₙ` (`TauCeti.coeFn_rieszTransform_rieszTransform_toLp_planarNewtonianKernel`). -/
theorem coeFn_rieszTransform_rieszTransform_toLp_newtonianKernel (hn : n = 1 ∨ 3 ≤ n)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v w : EuclideanSpace ℝ (Fin n)) :
    rieszTransform F v (rieszTransform F w
        ((hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).toLp φ)) =ᵐ[volume]
      fun x => iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ φ) x ![v, w] :=
  coeFn_rieszTransform_rieszTransform_toLp_of_laplacian_eq_neg
    (contDiff_newtonianKernel_convolution hφ hc)
    (laplacian_newtonianKernel_convolution (by omega) (by omega) (hφ.of_le (by simp)) hc) _ hc
    (tendsto_newtonianKernel_convolution_growth hn hφ.continuous hc).1
    (tendsto_newtonianKernel_convolution_growth hn hφ.continuous hc).2 v w

/-- **The kernel of the Hessian multiplier.** Let `n ≥ 3` and `v, w ∈ ℝⁿ`, and let `T_{m_{v,w}}`
be the Fourier multiplier with symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²`, that is `∂_v ∂_w Δ⁻¹`. If `f ∈ L²`
vanishes almost everywhere off a compact set `s`, then for almost every `x ∉ s`

`T_{m_{v,w}} f (x) = -∫ D²Gₙ(x - y)(v, w) f(y) dy`.

So off the support of its argument, `T_{m_{v,w}}` is the singular integral operator with kernel
`-D²Gₙ(x - y)(v, w)`, the Hessian of the Newtonian kernel; the integral converges because the
kernel is bounded for `y ∈ s` and `x` away from `s`. -/
theorem ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral (hn : 3 ≤ n)
    (v w : EuclideanSpace ℝ (Fin n)) (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsCompact s) (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → Lp.fourierMultiplierCLM F (hessianSymbolLp v w) f x =
      -∫ y, iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] • f y := by
  set T := Lp.fourierMultiplierCLM F (hessianSymbolLp v w)
  -- A representative `f'` of `f` vanishing everywhere off `s`, and smooth approximations `φ k`
  -- of it supported in shrinking thickenings of `s`.
  obtain ⟨f', hff', hf'0⟩ : ∃ f' : EuclideanSpace ℝ (Fin n) → F,
      (f : EuclideanSpace ℝ (Fin n) → F) =ᵐ[volume] f' ∧ ∀ y, y ∉ s → f' y = 0 := by
    refine ⟨s.indicator f, ?_, fun y hy => indicator_of_notMem hy _⟩
    filter_upwards [hf] with x hx
    by_cases h : x ∈ s
    · simp [h]
    · simp [h, hx h]
  have hf'L : MemLp f' 2 := (Lp.memLp f).ae_eq hff'
  choose φ hφc hφ hφs hφf using fun k : ℕ =>
    hf'L.exist_contDiff_tsupport_subset_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two
      hs.isClosed (cthickening_mem_nhdsSet s (Nat.one_div_pos_of_nat (n := k)))
      (ae_of_all _ hf'0) (Nat.one_div_pos_of_nat (n := k))
  have hφL : ∀ k, MemLp (φ k) 2 := fun k =>
    (hφ k).continuous.memLp_of_hasCompactSupport (μ := volume) (hφc k)
  have hφlim : Tendsto (fun k => eLpNorm (φ k - f') 2 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (fun _ => bot_le) fun k => (eLpNorm_sub_comm _ _ _ _).trans_le (hφf k)
  have hΦ : Tendsto (fun k => (hφL k).toLp (φ k)) atTop (𝓝 f) := by
    rw [← Lp.toLp_coeFn f (Lp.memLp f), ← hf'L.toLp_congr (Lp.memLp f) hff'.symm]
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' φ hφL f' hf'L).2 hφlim
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((T.continuous.tendsto f).comp hΦ)).exists_seq_tendsto_ae
  have hsmooth : ∀ᵐ x, ∀ k, T ((hφL k).toLp (φ k)) x =
      -iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ φ k) x ![v, w] :=
    ae_all_iff.2 fun k =>
      coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp (Or.inr hn) (hφ k) (hφc k) v w
  filter_upwards [hae, hsmooth] with x hx hxk hxs
  rw [integral_congr_ae (hff'.mono fun y hy => by rw [hy])]
  obtain ⟨η, hη, hxη, B, hB, hkc, hkB⟩ :=
    exists_continuousOn_norm_le_cthickening (n := n) hs.isClosed hxs v w
  -- Eventually `tsupport (φ k) ⊆ cthickening η s`, so `x ∉ tsupport (φ k)` and `T (φ k) x` is
  -- given by the kernel.
  have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ η :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hη)).mono fun _ h => h.le
  have hφW : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ η → tsupport (φ k) ⊆ cthickening η s := fun k hk =>
    (hφs k).trans (cthickening_mono hk s)
  have hev : ∀ᶠ k in atTop, T ((hφL k).toLp (φ k)) x =
      -∫ y, iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] • φ k y := by
    filter_upwards [hsmall] with k hk
    rw [hxk k, iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport
      ((hφ k).of_le (by simp)) (hφc k) (fun h => hxη (hφW k hk h)) v w]
  -- The kernel integrals of `φ k` converge to that of `f'`, by the Cauchy–Schwarz bound.
  have hW := hs.cthickening (r := η)
  have hconv := tendsto_integral_smul_of_tendsto_eLpNorm_sub (μ := volume)
    hW.measure_lt_top.ne hB (hkc.aestronglyMeasurable hW.measurableSet)
    (ae_restrict_of_forall_mem hW.measurableSet hkB) one_le_two (Eventually.of_forall hφL) hf'L
    (hsmall.mono fun k hk => ae_of_all _ fun y hy =>
      image_eq_zero_of_notMem_tsupport fun h => hy (hφW k hk h))
    (ae_of_all _ fun y hy => hf'0 y fun h => hy (self_subset_cthickening s h)) hφlim
  exact tendsto_nhds_unique hx ((hconv.comp hns.tendsto_atTop).neg.congr'
    ((hns.tendsto_atTop.eventually hev).mono fun _ h => h.symm))

end Multiplier

end TauCeti
