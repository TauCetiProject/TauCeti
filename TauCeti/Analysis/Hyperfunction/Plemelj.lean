/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
public import TauCeti.Analysis.Hyperfunction.CauchyTransform
public import TauCeti.Probability.Distributions.Cauchy.Basic
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.Support
import TauCeti.Basic.Complex.OfRealSub
import TauCeti.Probability.Distributions.Cauchy.ApproximateIdentity

/-!
# The Sokhotski–Plemelj jump of the Cauchy transform

Let `u` be a complex-valued distribution on the real line with compact support and let `χ` be a
real test function equal to one near the support of `u`. The Cauchy transform
`C(z) = (2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩` (`Distribution.cauchyTransform`) is holomorphic on
`ℂ ∖ ℝ`. This file proves that `u` is the jump of `C` across the real line, in the sense of
distributions:

`∫ φ(x) (C(x + iε) - C(x - iε)) dx → ⟨u, φ⟩` as `ε → 0⁺`,

for every real test function `φ`. This is the relation `bv₊ C - bv₋ C = u` with boundary values
taken in the sense of distributions, the identity behind representing `u` as a one-dimensional
hyperfunction by the class of `C`.

The proof has three steps.

* **The jump is a Poisson regularization.** Since
  `1 / (t - x - iγ) - 1 / (t - x + iγ) = 2iγ / ((t - x) ^ 2 + γ ^ 2)`, the jump
  `C(x + iγ) - C(x - iγ)` is `u` paired with `χ` times the Cauchy density of location `x` and
  scale `γ`, the Poisson kernel of the upper half-plane at height `γ`
  (`Distribution.cauchyTransform_add_mul_I_sub_cauchyTransform_sub_mul_I`). This holds on every
  open `Ω ⊆ ℝ`.
* **Exchange of `u` and the integral.** Near the support of `u` the kernel `χ(t) P_γ(t - x)`
  agrees with the translate by `x` of a fixed compactly supported truncation `ρ_γ = b P_γ` of the
  Poisson kernel, where `b` is a bump function equal to one on a large ball. Hence the integral of
  the jump against `φ` is `u` applied to the convolution `φ ⋆ ρ_γ`
  (`Distribution.apply_eq_integral_smul_translatePairing`).
* **Approximate identity.** The derivatives of `φ ⋆ ρ_γ` are `ρ_γ ⋆ φ⁽ⁱ⁾`, which converge to
  `φ⁽ⁱ⁾` uniformly because the truncated Poisson kernels form an approximate identity
  (`TauCeti.Probability.tendstoUniformly_integral_mul_cauchyPDFReal_smul`). All of these test
  functions are supported in one compact set, on which `u` has finite order, so
  `u (φ ⋆ ρ_γ) → u φ`.

The limit theorem is stated for distributions on all of `ℝ`, where every translate of `ρ_γ` is a
test function; the jump identity itself holds on every open subset of `ℝ`.

## Main declarations

* `Distribution.cauchyTransform_add_mul_I_sub_cauchyTransform_sub_mul_I`: the jump of the Cauchy
  transform at height `γ` is `u` paired with `χ` times the Poisson kernel.
* `Distribution.tendsto_integral_smul_cauchyTransform_sub`: the Sokhotski–Plemelj formula
  `bv₊ C - bv₋ C = u` for a compactly supported distribution on `ℝ`.

## References

* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1.
* L. Hörmander, *The analysis of linear partial differential operators I*, §3.1.
* A. Kaneko, *Introduction to hyperfunctions*, Chapter 1.
-/

public section

noncomputable section

open Complex Filter Metric Set TopologicalSpace TestFunction MeasureTheory ProbabilityTheory
open ContinuousLinearMap (lsmul)
open scoped ContDiff Distributions NNReal Pointwise Real Topology Convolution

namespace Distribution

variable {Ω : Opens ℝ}

/-- **The jump of the Cauchy transform is a Poisson regularization.** For a real `x` and a scale
`γ ≥ 0`, the difference `C(x + iγ) - C(x - iγ)` of the Cauchy transform of `u` with cutoff `χ` is
`u` paired with `χ` times the Cauchy density `t ↦ γ / (π ((t - x) ^ 2 + γ ^ 2))` of location `x`
and scale `γ`, the Poisson kernel of the upper half-plane at the point `x + iγ`. -/
theorem cauchyTransform_add_mul_I_sub_cauchyTransform_sub_mul_I (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ))
    (x : ℝ) (γ : ℝ≥0) :
    cauchyTransform u χ (x + (γ : ℝ) * I) - cauchyTransform u χ (x - (γ : ℝ) * I) =
      u (smulLeftCLM (TauCeti.Probability.contDiff_cauchyPDFReal x γ) χ) := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · have h0 : smulLeftCLM (TauCeti.Probability.contDiff_cauchyPDFReal x 0) χ = 0 := by
      ext t
      simp
    rw [h0, map_zero]
    simp
  have hγ' : (0 : ℝ) < γ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hγ)
  have hp : ((x : ℂ) + (γ : ℝ) * I).im ≠ 0 := by simpa using hγ'.ne'
  have hm : ((x : ℂ) - (γ : ℝ) * I).im ≠ 0 := by simpa using hγ'.ne'
  have hk : cauchyKernel χ 1 hp - cauchyKernel χ 1 hm = (2 * π * I) •
      postcompCLM ofRealCLM (smulLeftCLM (TauCeti.Probability.contDiff_cauchyPDFReal x γ) χ) := by
    ext t
    have h1 := ofReal_sub_ne_zero_of_im_ne_zero hp t
    have h2 := ofReal_sub_ne_zero_of_im_ne_zero hm t
    have h3 : ((t : ℂ) - x) ^ 2 + ((γ : ℝ) : ℂ) ^ 2 ≠ 0 := by
      exact_mod_cast (by positivity : ((t - x) ^ 2 + (γ : ℝ) ^ 2 : ℝ) ≠ 0)
    simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, cauchyKernel_apply,
      pow_one, postcompCLM_apply, Function.comp_apply, ofRealCLM_apply, smulLeftCLM_apply,
      cauchyPDFReal_def, smul_eq_mul, ofReal_mul, ofReal_inv, ofReal_add, ofReal_pow, ofReal_sub]
    field_simp
    linear_combination (2 * (χ t : ℂ) * ((γ : ℝ) : ℂ) ^ 3 * I) * I_sq
  rw [cauchyTransform_of_im_ne_zero u χ hp, cauchyTransform_of_im_ne_zero u χ hm, ← mul_sub,
    ← map_sub, hk, map_smul, complexPairing_postcompCLM_ofRealCLM, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]

/-! ### The Sokhotski–Plemelj formula -/

/-- The Poisson kernel `cauchyPDFReal 0 γ` of the half-plane, truncated by a bump function `b`,
as a test function on `ℝ`. -/
private def truncatedPoissonKernel (b : ContDiffBump (0 : ℝ)) (γ : ℝ≥0) :
    𝓓((⊤ : Opens ℝ), ℝ) where
  toFun s := b s * cauchyPDFReal 0 γ s
  contDiff' := b.contDiff.mul (TauCeti.Probability.contDiff_cauchyPDFReal 0 γ)
  hasCompactSupport' := b.hasCompactSupport.mul_right
  tsupport_subset' := by simp

private theorem truncatedPoissonKernel_apply (b : ContDiffBump (0 : ℝ)) (γ : ℝ≥0) (s : ℝ) :
    truncatedPoissonKernel b γ s = b s * cauchyPDFReal 0 γ s := (rfl)

/-- The regularization `φ ⋆ ρ_γ` of a test function `φ` by the truncated Poisson kernel
`ρ_γ = b P_γ`, as a test function on `ℝ`. -/
private def poissonRegularization (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (b : ContDiffBump (0 : ℝ))
    (γ : ℝ≥0) : 𝓓((⊤ : Opens ℝ), ℝ) where
  toFun := (φ : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] truncatedPoissonKernel b γ
  contDiff' := (truncatedPoissonKernel b γ).hasCompactSupport.contDiff_convolution_right _
    (φ.continuous.locallyIntegrable) (truncatedPoissonKernel b γ).contDiff
  hasCompactSupport' := φ.hasCompactSupport.convolution _
    (truncatedPoissonKernel b γ).hasCompactSupport
  tsupport_subset' := by simp

private theorem coe_poissonRegularization (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (b : ContDiffBump (0 : ℝ))
    (γ : ℝ≥0) :
    ⇑(poissonRegularization φ b γ) = (φ : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] truncatedPoissonKernel b γ :=
  (rfl)

/-- The derivatives of `φ ⋆ ρ_γ` are the weighted Poisson integrals `ρ_γ ⋆ φ⁽ⁱ⁾`. -/
private theorem iteratedFDeriv_poissonRegularization (φ : 𝓓((⊤ : Opens ℝ), ℝ))
    (b : ContDiffBump (0 : ℝ)) (γ : ℝ≥0) (i : ℕ) (t : ℝ) :
    iteratedFDeriv ℝ i (poissonRegularization φ b γ) t =
      ∫ s, (b s * cauchyPDFReal 0 γ s) • iteratedFDeriv ℝ i φ (t - s) := by
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    ext
    simp
  have hcoe : ⇑(poissonRegularization φ b γ) =
      (truncatedPoissonKernel b γ : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] φ := by
    rw [← convolution_flip, hflip, coe_poissonRegularization]
  rw [hcoe, φ.hasCompactSupport.iteratedFDeriv_convolution_right _
    (truncatedPoissonKernel b γ).continuous.locallyIntegrable φ.contDiff
    (by exact_mod_cast le_top), convolution_def]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  ext
  simp [truncatedPoissonKernel_apply]

private theorem tsupport_poissonRegularization_subset (φ : 𝓓((⊤ : Opens ℝ), ℝ))
    (b : ContDiffBump (0 : ℝ)) (γ : ℝ≥0) :
    tsupport (poissonRegularization φ b γ) ⊆ tsupport φ + closedBall 0 b.rOut := by
  refine closure_minimal ((support_convolution_subset _).trans (add_subset_add
    (subset_tsupport _) fun s hs ↦ ?_)) (φ.hasCompactSupport.isCompact.add
      (isCompact_closedBall _ _)).isClosed
  have hs' : b s ≠ 0 := fun h0 ↦ hs (by rw [truncatedPoissonKernel_apply, h0, zero_mul])
  exact ball_subset_closedBall (b.support_eq ▸ Function.mem_support.2 hs')

/-- **The truncated Poisson regularizations converge in the space of test functions.** Every
distribution `T` on `ℝ` satisfies `T (φ ⋆ ρ_γ) → T φ` as `γ → 0⁺`: all of these test functions
are supported in one compact set, on which `T` has finite order, and their derivatives converge
uniformly. -/
private theorem tendsto_apply_poissonRegularization {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : 𝓓'((⊤ : Opens ℝ), F)) (φ : 𝓓((⊤ : Opens ℝ), ℝ))
    (b : ContDiffBump (0 : ℝ)) :
    Tendsto (fun γ ↦ T (poissonRegularization φ b γ)) (𝓝[≠] 0) (𝓝 (T φ)) := by
  let L : Compacts ℝ := ⟨tsupport φ + closedBall 0 b.rOut,
    φ.hasCompactSupport.isCompact.add (isCompact_closedBall _ _)⟩
  have hLφ : tsupport φ ⊆ L := fun t ht ↦ ⟨t, ht, 0, by simpa using b.rOut_pos.le, add_zero t⟩
  obtain ⟨N, C, hC0, hC⟩ := exists_norm_apply_le T (K := L) (subset_univ _)
  -- The derivatives of order at most `N` converge uniformly.
  have hderiv (i : Fin (N + 1)) : TendstoUniformly
      (fun (γ : ℝ≥0) (t : ℝ) ↦ ∫ s, (b s * cauchyPDFReal 0 γ s) • iteratedFDeriv ℝ i φ (t - s))
      (iteratedFDeriv ℝ i φ) (𝓝[≠] 0) := by
    have hcs := φ.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) i
    have hcont := φ.contDiff.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
    exact TauCeti.Probability.tendstoUniformly_integral_mul_cauchyPDFReal_smul
      (hcs.uniformContinuous_of_continuous hcont) hM b.continuous (H := 1)
      (fun s ↦ by rw [abs_of_nonneg b.nonneg]; exact b.le_one)
      (b.one_of_mem_closedBall (by simpa using b.rIn_pos.le))
  rw [Metric.tendsto_nhds]
  intro e he
  have hη : 0 < e / (C + 1) := by positivity
  filter_upwards [Filter.eventually_all.2 fun i ↦ Metric.tendstoUniformly_iff.1 (hderiv i) _ hη]
    with γ hγ
  rw [dist_eq_norm, ← map_sub]
  have hsupp : tsupport (poissonRegularization φ b γ - φ : 𝓓((⊤ : Opens ℝ), ℝ)) ⊆ L := by
    rw [FunLike.coe_sub]
    exact (tsupport_sub _ _).trans
      (union_subset (tsupport_poissonRegularization_subset φ b γ) hLφ)
  refine (hC _ hsupp (e / (C + 1)) hη.le fun i hi t ↦ ?_).trans_lt ?_
  · rw [FunLike.coe_sub, iteratedFDeriv_sub
      ((poissonRegularization φ b γ).contDiff.of_le (by exact_mod_cast le_top))
      (φ.contDiff.of_le (by exact_mod_cast le_top)), Pi.sub_apply, ← dist_eq_norm, dist_comm,
      iteratedFDeriv_poissonRegularization]
    exact (hγ ⟨i, Nat.lt_succ_of_le hi⟩ t).le
  · rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith

/-- **Exchange of `u` and the integral.** If `χ` equals one near the support of `u`, the bump `b`
equals one on a ball containing `tsupport χ - tsupport φ`, then the integral of the jump of the
Cauchy transform against `φ` is `u (φ ⋆ ρ_γ)`. -/
private theorem integral_smul_cauchyTransform_sub_eq (u : 𝓓'((⊤ : Opens ℝ), ℂ))
    {χ : 𝓓((⊤ : Opens ℝ), ℝ)} (hχ : ∀ᶠ t in 𝓝ˢ (dsupport u), χ t = 1)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) {A B : ℝ} (hA : tsupport χ ⊆ closedBall 0 A)
    (hB : tsupport φ ⊆ closedBall 0 B) {b : ContDiffBump (0 : ℝ)} (hb : A + B + 1 ≤ b.rIn)
    (γ : ℝ≥0) :
    (∫ x : ℝ, φ x •
      (cauchyTransform u χ (x + (γ : ℝ) * I) - cauchyTransform u χ (x - (γ : ℝ) * I))) =
      u (poissonRegularization φ b γ) := by
  have hdsupp : dsupport u ⊆ ball 0 (A + 1) := fun t ht ↦ by
    have h1 : χ t = 1 := hχ.self_of_nhdsSet t ht
    have ht' : ‖t‖ ≤ A := mem_closedBall_zero_iff.1
      (hA (subset_tsupport _ (by simp [Function.mem_support, h1])))
    exact mem_ball_zero_iff.2 (by linarith)
  -- Near the support of `u`, `χ` times the Poisson kernel at `x ∈ tsupport φ` is the translate of
  -- the truncated kernel by `x`.
  have htrans (x : ℝ) (hx : x ∈ tsupport φ) :
      u (smulLeftCLM (TauCeti.Probability.contDiff_cauchyPDFReal x γ) χ) =
        translatePairing u (truncatedPoissonKernel b γ) x := by
    have hmaps : MapsTo (· + x) ((⊤ : Opens ℝ) : Set ℝ) ((⊤ : Opens ℝ) : Set ℝ) := by simp
    rw [translatePairing_eq u
      (φ := TauCeti.translateTestFunction hmaps (truncatedPoissonKernel b γ))
      (TauCeti.translateTestFunction_apply hmaps _)]
    apply map_eq_map_of_eventuallyEq
    filter_upwards [hχ, isOpen_ball.mem_nhdsSet.2 hdsupp] with t ht1 htb
    have hx' : ‖x‖ ≤ B := mem_closedBall_zero_iff.1 (hB hx)
    have htb' : ‖t‖ < A + 1 := mem_ball_zero_iff.1 htb
    have hb1 : b (t - x) = 1 := b.one_of_mem_closedBall (mem_closedBall_zero_iff.2
      ((norm_sub_le t x).trans (by linarith)))
    rw [TauCeti.translateTestFunction_apply, truncatedPoissonKernel_apply, hb1, smulLeftCLM_apply,
      ht1]
    simp [cauchyPDFReal_def]
  rw [apply_eq_integral_smul_translatePairing u (truncatedPoissonKernel b γ)
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport) φ.hasCompactSupport
    (fun _ _ ↦ by simp) (coe_poissonRegularization φ b γ)]
  congr 1
  ext x
  by_cases hx : x ∈ tsupport φ
  · rw [cauchyTransform_add_mul_I_sub_cauchyTransform_sub_mul_I, htrans x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **The Sokhotski–Plemelj formula.** Let `u` be a complex-valued distribution on `ℝ` and `χ` a
real test function equal to one near the support of `u` (so that `u` has compact support). Then
`u` is the difference of the boundary values of its Cauchy transform `C` from the upper and the
lower half-plane: for every real test function `φ`,

`∫ φ(x) (C(x + iε) - C(x - iε)) dx → u φ` as `ε → 0⁺`. -/
theorem tendsto_integral_smul_cauchyTransform_sub (u : 𝓓'((⊤ : Opens ℝ), ℂ))
    {χ : 𝓓((⊤ : Opens ℝ), ℝ)} (hχ : ∀ᶠ t in 𝓝ˢ (dsupport u), χ t = 1)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    Tendsto (fun ε : ℝ ↦ ∫ x : ℝ,
        φ x • (cauchyTransform u χ (x + ε * I) - cauchyTransform u χ (x - ε * I)))
      (𝓝[>] 0) (𝓝 (u φ)) := by
  obtain ⟨A, hA0, hA⟩ := χ.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  obtain ⟨B, hB0, hB⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  let b : ContDiffBump (0 : ℝ) := ⟨A + B + 1, A + B + 2, by positivity, by linarith⟩
  have hlim : Tendsto Real.toNNReal (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_real_toNNReal.tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦
        (Real.toNNReal_pos.2 hε).ne'⟩
  refine ((tendsto_apply_poissonRegularization u φ b).comp hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [Function.comp_apply, ← integral_smul_cauchyTransform_sub_eq u hχ φ hA hB le_rfl,
    Real.coe_toNNReal ε hε.le]

end Distribution
