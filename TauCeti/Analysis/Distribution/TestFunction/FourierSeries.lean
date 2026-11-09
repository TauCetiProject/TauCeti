/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv

/-!
# Fourier series of test functions supported in a small compact set

Let `L` be a full lattice in a finite-dimensional real inner product space `E`, with dual lattice
`L^∨`, and let `K` be a compact set that meets none of its translates `K + ℓ` by nonzero lattice
vectors; for the lattice `pℤⁿ` in `ℝⁿ`, any closed coordinate box of side smaller than `p` will
do. A smooth function `φ` supported in `K` agrees on `K` with its `L`-periodization, whose Fourier
series is given by Poisson summation: the coefficient of the character `x ↦ exp (2πi ⟪x, m⟫)`,
`m ∈ L^∨`, is `(covolume L)⁻¹ 𝓕 φ (m)`. Multiplying by a cutoff `χ`, also supported in `K` and
equal to one on the support of `φ`, turns this periodic expansion into an expansion of `φ` itself
in the *modulated cutoffs* `χ.modulate m : x ↦ exp (2πi ⟪x, m⟫) χ x`, which are again smooth
functions supported in `K`:

`φ = ∑ m : L^∨, ((covolume L)⁻¹ 𝓕 φ (m)) • χ.modulate m`.

The series converges in the topology of `𝓓_{K}(E, ℂ)`, that is, uniformly together with every
derivative (`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`). The two estimates behind
this are of independent use:

* each derivative of a modulated cutoff grows at most polynomially in the frequency,
  `N_k (χ.modulate w) ≤ (sup_{i ≤ k} N_i χ) (1 + 2π ‖w‖) ^ k`
  (`ContDiffMapSupportedIn.seminorm_modulate_le`), so every continuous seminorm, for instance
  `ψ ↦ ‖T ψ‖` for a continuous linear map `T` to a normed space, grows polynomially along the
  modulated cutoffs (`ContDiffMapSupportedIn.exists_seminorm_modulate_le`);
* the coefficients `𝓕 φ (m)` decay faster than every power of `‖m‖`, since `𝓕 φ` is a Schwartz
  function (`ZLattice.summable_one_add_norm_pow_mul_norm`).

Expansions of this kind are the first step of the Fourier-series proof of the Schwartz kernel
theorem: a continuous linear map on test functions is determined by its values on the
modulated cutoffs, which grow at most polynomially, and the rapidly decreasing coefficients make
the resulting double series converge.

## Main definitions

* `ContDiffMapSupportedIn.modulate`: the modulation `x ↦ exp (2πi ⟪x, w⟫) • χ x` of a function
  `χ` supported in `K` by the character of frequency `w`.
* `ContDiffMapSupportedIn.modulateCLM`: modulation by a fixed frequency, as a continuous linear
  map.

## Main results

* `ContDiffMapSupportedIn.seminorm_modulate_le`: the polynomial bound on the derivatives of a
  modulated cutoff.
* `ContDiffMapSupportedIn.exists_seminorm_modulate_le`: a continuous seminorm grows at most
  polynomially along modulated cutoffs.
* `ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`: the Fourier expansion of a smooth
  function supported in `K`, converging in `𝓓_{K}(E, ℂ)`.
* `TauCeti.exists_tendstoUniformlyOn_iteratedFDeriv_sum_cexp`: on a small ball in `ℝⁿ`, every
  smooth function supported in it is the limit in every `C^k` norm of trigonometric polynomials.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Theorem 5.2.1.
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967,
  Chapter 51.
-/

public section

noncomputable section

open Complex Function Set TopologicalSpace
open scoped Real RealInnerProductSpace FourierTransform Distributions ContDiff SchwartzMap

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ∞} {K : Compacts E}

/-! ### The phase of a character -/

/-- The phase `x ↦ 2πi ⟪x, w⟫` of the character of frequency `w`, as a real-linear map. -/
private def phase (w : E) : E →L[ℝ] ℂ :=
  (2 * π * I) • (ofRealCLM.comp (innerSL ℝ w))

private theorem phase_apply (w x : E) : phase w x = 2 * π * I * ⟪x, w⟫ := by
  simp [phase, real_inner_comm]

private theorem norm_phase_le (w : E) : ‖phase w‖ ≤ 2 * π * ‖w‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ by
    have h : ‖phase w x‖ = 2 * π * |⟪x, w⟫| := by
      rw [phase_apply]
      simp [abs_of_pos Real.pi_pos]
    rw [h]
    calc 2 * π * |⟪x, w⟫| ≤ 2 * π * (‖w‖ * ‖x‖) := by
          gcongr
          exact abs_real_inner_le_norm x w |>.trans_eq (mul_comm _ _)
      _ = 2 * π * ‖w‖ * ‖x‖ := by ring

private theorem norm_exp_phase (w x : E) : ‖cexp (phase w x)‖ = 1 := by
  rw [phase_apply, norm_exp]
  simp

private theorem contDiff_exp_phase (w : E) : ContDiff ℝ ∞ fun x ↦ cexp (phase w x) :=
  (phase w).contDiff.cexp

/-- Every derivative of the character `x ↦ exp (2πi ⟪x, w⟫)` of frequency `w` has norm at most
`(2π ‖w‖) ^ k`. -/
private theorem norm_iteratedFDeriv_exp_phase_le (w x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ cexp (phase w y)) x‖ ≤ (2 * π * ‖w‖) ^ k := by
  refine ((phase w).norm_iteratedFDeriv_cexp_comp_le k x).trans ?_
  rw [norm_exp_phase, one_mul]
  gcongr
  exact norm_phase_le w

/-- `(1 + 2π a) ^ k ≤ (2π) ^ k (1 + a) ^ k` for `a ≥ 0`, since `2π ≥ 1`. -/
private theorem one_add_two_pi_mul_pow_le {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (1 + 2 * π * a) ^ k ≤ (2 * π) ^ k * (1 + a) ^ k := by
  rw [← mul_pow]
  gcongr
  nlinarith [Real.two_le_pi]

/-! ### Modulated cutoffs -/

/-- Modulation `χ ↦ (x ↦ exp (2πi ⟪x, w⟫) • χ x)` by the character of frequency `w`, as a
continuous `ℂ`-linear map on `𝓓^{n}_{K}(E, F)`. -/
def modulateCLM (w : E) : 𝓓^{n}_{K}(E, F) →L[ℂ] 𝓓^{n}_{K}(E, F) :=
  bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip
    ((contDiff_exp_phase w).of_le (mod_cast le_top))

/-- The modulation `x ↦ exp (2πi ⟪x, w⟫) • χ x` of `χ` by the character of frequency `w`. It is
supported in the same compact set as `χ` and has the same regularity. -/
def modulate (χ : 𝓓^{n}_{K}(E, F)) (w : E) : 𝓓^{n}_{K}(E, F) :=
  modulateCLM w χ

@[simp]
theorem modulateCLM_apply (χ : 𝓓^{n}_{K}(E, F)) (w : E) : modulateCLM w χ = χ.modulate w := by
  rw [modulate]

@[simp]
theorem modulate_apply (χ : 𝓓^{n}_{K}(E, F)) (w x : E) :
    χ.modulate w x = cexp (2 * π * I * ⟪x, w⟫) • χ x := by
  simp [modulate, modulateCLM, bilinLeftCLM_apply, phase_apply]

@[simp]
theorem zero_modulate (w : E) : (0 : 𝓓^{n}_{K}(E, F)).modulate w = 0 :=
  map_zero (modulateCLM w)

@[simp]
theorem add_modulate (χ ψ : 𝓓^{n}_{K}(E, F)) (w : E) :
    (χ + ψ).modulate w = χ.modulate w + ψ.modulate w :=
  map_add (modulateCLM w) χ ψ

@[simp]
theorem smul_modulate (c : ℂ) (χ : 𝓓^{n}_{K}(E, F)) (w : E) :
    (c • χ).modulate w = c • χ.modulate w :=
  map_smul (modulateCLM w) c χ

@[simp]
theorem sum_modulate {ι : Type*} (s : Finset ι) (χ : ι → 𝓓^{n}_{K}(E, F)) (w : E) :
    (∑ i ∈ s, χ i).modulate w = ∑ i ∈ s, (χ i).modulate w :=
  map_sum (modulateCLM w) χ s

@[simp]
theorem modulate_zero (χ : 𝓓^{n}_{K}(E, F)) : χ.modulate 0 = χ := by
  ext x
  simp

/-- Modulating by `w` and then by `w'` is modulating by `w + w'`. -/
@[simp]
theorem modulate_modulate (χ : 𝓓^{n}_{K}(E, F)) (w w' : E) :
    (χ.modulate w).modulate w' = χ.modulate (w + w') := by
  ext x
  simp only [modulate_apply, smul_smul, inner_add_right, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The `k`-th derivatives of a modulated cutoff grow at most polynomially in the frequency:
`N_k (χ.modulate w) ≤ (sup_{i ≤ k} N_i χ) (1 + 2π ‖w‖) ^ k`. -/
theorem seminorm_modulate_le (χ : 𝓓_{K}(E, F)) (w : E) (k : ℕ) :
    N[ℂ]_{K, k} (χ.modulate w) ≤
      ContDiffMapSupportedIn.supSeminorm ℂ E F ⊤ K k χ * (1 + 2 * π * ‖w‖) ^ k := by
  set S := ContDiffMapSupportedIn.supSeminorm ℂ E F ⊤ K k χ
  rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (by positivity)]
  intro x _
  -- Leibniz's rule, with `N_i χ ≤ S` for `i ≤ k`, and the binomial theorem.
  have hχ (i : ℕ) (hi : i ≤ k) : ‖iteratedFDeriv ℝ i χ x‖ ≤ S :=
    norm_iteratedFDeriv_apply_le_seminorm_top ℂ |>.trans <|
      Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℂ E F ⊤ K) (Finset.mem_Iic.2 hi) χ
  have hcoe : ⇑(χ.modulate w) = fun y ↦ cexp (phase w y) • χ y := by
    ext y
    simp [phase_apply]
  rw [hcoe]
  refine (norm_iteratedFDeriv_smul_le (contDiff_exp_phase w) χ.contDiff x
    (mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y ↦ cexp (phase w y)) x‖ * ‖iteratedFDeriv ℝ (k - i) χ x‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * π * ‖w‖) ^ i * S := by
        gcongr with i hi
        · exact norm_iteratedFDeriv_exp_phase_le w x i
        · exact hχ _ (Nat.sub_le k i)
    _ = S * (1 + 2 * π * ‖w‖) ^ k := by
        rw [add_comm 1, add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring

/-- Every continuous seminorm `q` on `𝓓_{K}(E, F)` grows at most polynomially along the
modulated cutoffs `χ.modulate w`: there are `C` and `k` with
`q (χ.modulate w) ≤ C (1 + ‖w‖) ^ k` for every frequency `w`. Applied to `ψ ↦ ‖T ψ‖`, this bounds
the images of modulated cutoffs under a continuous linear map `T` to a normed space. -/
theorem exists_seminorm_modulate_le (χ : 𝓓_{K}(E, F)) (q : Seminorm ℂ 𝓓_{K}(E, F))
    (hq : Continuous q) : ∃ C k, ∀ w : E, q (χ.modulate w) ≤ C * (1 + ‖w‖) ^ k := by
  obtain ⟨s, C, -, hC⟩ :=
    Seminorm.bound_of_continuous (ContDiffMapSupportedIn.withSeminorms ℂ E F ⊤ K) q hq
  set k := s.sup id
  set S := ContDiffMapSupportedIn.supSeminorm ℂ E F ⊤ K k χ
  refine ⟨C * (S * (2 * π) ^ k), k, fun w ↦ ?_⟩
  have h1 : 1 ≤ 1 + 2 * π * ‖w‖ := by
    have := Real.pi_pos
    nlinarith [norm_nonneg w]
  -- Each seminorm `N_i` with `i ∈ s` is bounded by the polynomial of the largest degree `k`.
  have hs : s.sup (ContDiffMapSupportedIn.seminorm ℂ E F ⊤ K) (χ.modulate w) ≤
      S * (1 + 2 * π * ‖w‖) ^ k := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦ ?_
    have hik : i ≤ k := Finset.le_sup (f := id) hi
    refine (seminorm_modulate_le χ w i).trans ?_
    gcongr ?_ * ?_
    · exact Finset.sup_mono (f := ContDiffMapSupportedIn.seminorm ℂ E F ⊤ K)
        (Finset.Iic_subset_Iic.2 hik) χ
    · exact pow_le_pow_right₀ h1 hik
  calc q (χ.modulate w) ≤ C * s.sup (ContDiffMapSupportedIn.seminorm ℂ E F ⊤ K) (χ.modulate w) :=
        hC _
    _ ≤ C * (S * ((2 * π) ^ k * (1 + ‖w‖) ^ k)) := by
        gcongr
        exact hs.trans (by gcongr; exact one_add_two_pi_mul_pow_le (norm_nonneg w) k)
    _ = C * (S * (2 * π) ^ k) * (1 + ‖w‖) ^ k := by ring

/-! ### The Fourier expansion -/

variable (L : Submodule ℤ E)

/-- A smooth function `φ` supported in a compact set `K` that meets none of its nonzero lattice
translates is recovered from its `L`-periodization by multiplying with a cutoff `χ` equal to one
on the support of `φ`. -/
private theorem mul_tsum_add_eq (φ χ : 𝓓_{K}(E, ℂ))
    (hK : ∀ x ∈ K, ∀ ℓ : L, x + ℓ ∈ K → ℓ = 0) (hχ : EqOn χ 1 (support φ)) (x : E) :
    χ x * ∑' ℓ : L, φ (x + ℓ) = φ x := by
  by_cases hx : x ∈ K
  · rw [tsum_eq_single 0 fun ℓ hℓ ↦ φ.zero_on_compl fun h ↦ hℓ (hK x hx ℓ h)]
    by_cases hφ : φ x = 0
    · simp [hφ]
    · simp [hχ hφ]
  · simp [χ.zero_on_compl hx, φ.zero_on_compl hx]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L]

/-- The Fourier expansion of `φ` in the modulated cutoffs holds pointwise. -/
private theorem hasSum_fourier_smul_modulate_apply (φ χ : 𝓓_{K}(E, ℂ))
    (hK : ∀ x ∈ K, ∀ ℓ : L, x + ℓ ∈ K → ℓ = 0) (hχ : EqOn χ 1 (support φ)) (x : E) :
    HasSum (fun m : ZLattice.dual L ↦
      (((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m) • χ.modulate m) x) (φ x) := by
  let g : 𝓢(E, ℂ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  -- `g` is `φ`, read as a Schwartz function.
  have hg : (g : E → ℂ) = φ := rfl
  have h := (ZLattice.summable_poisson_right L g x).hasSum.mul_left
    (χ x * (ZLattice.covolume L : ℂ)⁻¹)
  -- Poisson summation identifies the sum with `χ` times the periodization of `φ`.
  have hval : χ x * (ZLattice.covolume L : ℂ)⁻¹ *
      ∑' m : ZLattice.dual L, 𝓕 (g : E → ℂ) m * cexp (2 * π * I * ⟪x, (m : E)⟫) = φ x := by
    rw [mul_assoc (χ x), ← SchwartzMap.tsum_eq_tsum_dual_fourier, hg, mul_tsum_add_eq L φ χ hK hχ]
  rw [hval, hg] at h
  convert h using 1
  ext m
  simp only [FunLike.coe_smul, Pi.smul_apply, modulate_apply, smul_eq_mul]
  ring

/-- The `k`-th seminorm bound for the terms of the Fourier expansion is summable. -/
private theorem summable_norm_fourier_mul (φ χ : 𝓓_{K}(E, ℂ)) (k : ℕ) :
    Summable fun m : ZLattice.dual L ↦ ‖(ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m‖ *
      (ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * (1 + 2 * π * ‖(m : E)‖) ^ k) := by
  let g : 𝓢(E, ℂ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  -- `g` is `φ`, read as a Schwartz function.
  have hg : (g : E → ℂ) = φ := rfl
  have hdecay := ZLattice.summable_one_add_norm_pow_mul_norm (ZLattice.dual L) (𝓕 g) k
  rw [SchwartzMap.fourier_coe, hg] at hdecay
  refine (hdecay.mul_left (‖(ZLattice.covolume L : ℂ)⁻¹‖ *
    ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * (2 * π) ^ k)).of_nonneg_of_le
      (fun m ↦ by positivity) fun m ↦ ?_
  rw [norm_mul]
  calc ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ‖𝓕 (φ : E → ℂ) m‖ *
        (ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * (1 + 2 * π * ‖(m : E)‖) ^ k)
      ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ‖𝓕 (φ : E → ℂ) m‖ *
        (ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ *
          ((2 * π) ^ k * (1 + ‖(m : E)‖) ^ k)) := by
        gcongr
        exact one_add_two_pi_mul_pow_le (norm_nonneg _) k
    _ = ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ *
          (2 * π) ^ k * ((1 + ‖(m : E)‖) ^ k * ‖𝓕 (φ : E → ℂ) m‖) := by
        ring

/-- **Fourier expansion of a test function on a small compact set.** Let `L` be a full lattice
and `K` a compact set meeting none of its translates by nonzero vectors of `L`. A smooth function
`φ` supported in `K` is the sum, in the topology of `𝓓_{K}(E, ℂ)`, of its Fourier series in the
modulated cutoffs `χ.modulate m`, `m ∈ L^∨`, for any `χ` supported in `K` and equal to one on the
support of `φ`:

`φ = ∑ m : L^∨, ((covolume L)⁻¹ 𝓕 φ (m)) • χ.modulate m`.

Convergence in `𝓓_{K}(E, ℂ)` means uniform convergence together with all derivatives. -/
theorem hasSum_fourier_smul_modulate (φ χ : 𝓓_{K}(E, ℂ))
    (hK : ∀ x ∈ K, ∀ ℓ : L, x + ℓ ∈ K → ℓ = 0) (hχ : EqOn χ 1 (support φ)) :
    HasSum (fun m : ZLattice.dual L ↦
      ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m) • χ.modulate m) φ := by
  -- The `k`-th seminorms of the terms have the summable bounds `summable_norm_fourier_mul`.
  have hfu (k : ℕ) (m : ZLattice.dual L) :
      N[ℂ]_{K, k} (((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m) • χ.modulate m) ≤
        ‖(ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m‖ *
          (ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ *
            (1 + 2 * π * ‖(m : E)‖) ^ k) := by
    rw [map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (seminorm_modulate_le χ m k) (norm_nonneg _)
  have hu := summable_norm_fourier_mul L φ χ
  -- The terms sum to `φ` pointwise, so their derivatives sum to the derivatives of `φ`.
  have hφ : (fun y ↦ ∑' m : ZLattice.dual L,
      (((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m) • χ.modulate m) y) = φ :=
    funext fun y ↦ (hasSum_fourier_smul_modulate_apply L φ χ hK hχ y).tsum_eq
  -- Convergence in `𝓓_{K}(E, ℂ)` is convergence of every derivative in sup norm.
  rw [← (isUniformEmbedding_pi_structureMapCLM ℂ).isInducing.hasSum_iff, Pi.hasSum]
  intro k
  simp only [comp_apply, ContinuousLinearMap.pi_apply]
  have hsum := (hu k).of_norm_bounded (f := fun m : ZLattice.dual L ↦
    structureMapCLM ℂ ⊤ k (((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m) • χ.modulate m))
    fun m ↦ by
      rw [← ContDiffMapSupportedIn.seminorm_apply]
      exact hfu k m
  convert hsum.hasSum using 1
  ext x : 1
  have h := (BoundedContinuousFunction.evalCLM ℂ x).map_tsum hsum
  simp only [BoundedContinuousFunction.evalCLM_apply] at h
  rw [h]
  simp only [structureMapCLM_top_apply]
  rw [← iteratedFDeriv_tsum_apply (fun m ↦ (_ : 𝓓_{K}(E, ℂ)).contDiff) (fun k _ ↦ hu k)
    (fun k m x _ ↦ (norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans (hfu k m))
    (mod_cast le_top), hφ]

end ContDiffMapSupportedIn

namespace TauCeti

/-- **Trigonometric approximation on a small ball.** There is a ball `‖y‖ < r` in `ℝⁿ` on which
every smooth function `g` supported in it is the limit in every `C^k` norm of trigonometric
polynomials `∑ m ∈ s, c m exp (2πi ⟪w m, y⟫)`, as the finite set `s` of frequencies grows. These
are the partial sums of the Fourier expansion of `g` in modulated cutoffs
(`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`), read where the cutoff equals one. -/
theorem exists_tendstoUniformlyOn_iteratedFDeriv_sum_cexp (N : ℕ) :
    ∃ r > 0, ∀ g : EuclideanSpace ℝ (Fin N) → ℂ, ContDiff ℝ ∞ g →
      support g ⊆ Metric.ball 0 r → ∃ (κ : Type) (w : κ → EuclideanSpace ℝ (Fin N)) (c : κ → ℂ),
        ∀ k : ℕ, TendstoUniformlyOn (fun s : Finset κ ↦ iteratedFDeriv ℝ k
          fun y ↦ ∑ m ∈ s, c m * cexp (2 * π * I * (innerSL ℝ (w m) y : ℂ)))
          (iteratedFDeriv ℝ k g) Filter.atTop (Metric.ball 0 r) := by
  let Y := EuclideanSpace ℝ (Fin N)
  -- The lattice `Λ` of integer vectors, whose nonzero vectors have norm at least `ε`.
  let Λ : Submodule ℤ Y := Submodule.span ℤ (range (EuclideanSpace.basisFun _ ℝ).toBasis)
  obtain ⟨ε, hε, hΛ⟩ := Metric.isOpen_singleton_iff.1 (isOpen_discrete {(0 : Λ)})
  -- The ball `K` of radius `ε / 3` meets none of its nonzero `Λ`-translates.
  let K : Compacts Y := ⟨Metric.closedBall 0 (ε / 3), isCompact_closedBall _ _⟩
  have hK : ∀ y ∈ K, ∀ ℓ : Λ, y + ℓ ∈ K → ℓ = 0 := fun y hy ℓ hyℓ ↦ hΛ ℓ <| by
    have hy' : ‖y‖ ≤ ε / 3 := mem_closedBall_zero_iff.1 hy
    have hyℓ' : ‖y + ℓ‖ ≤ ε / 3 := mem_closedBall_zero_iff.1 hyℓ
    rw [dist_zero_right]
    calc ‖(ℓ : Y)‖ = ‖(y + ℓ) - y‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖y + ℓ‖ + ‖y‖ := norm_sub_le _ _
      _ < ε := by linarith
  -- A cutoff `χ` supported in `K`, equal to one on the ball of radius `ε / 6`.
  let b : ContDiffBump (0 : Y) := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  have hof : ContDiff ℝ ∞ fun r : ℝ ↦ (r : ℂ) := ofRealCLM.contDiff
  let χ : 𝓓_{K}(Y, ℂ) := .of_support_subset (hof.comp b.contDiff) fun y hy ↦
    Metric.ball_subset_closedBall (b.support_eq ▸ support_comp_subset ofReal_zero _ hy)
  have hχ1 (y : Y) (hy : y ∈ Metric.ball (0 : Y) (ε / 6)) : χ y = 1 := by
    change ((b y : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), ofReal_one]
  refine ⟨ε / 6, by positivity, fun g hg hgsupp ↦ ?_⟩
  -- The Fourier expansion of `g` in the modulated cutoffs converges in `𝓓_{K}(Y, ℂ)`.
  let φ : 𝓓_{K}(Y, ℂ) := .of_support_subset hg fun y hy ↦
    Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall (hgsupp hy))
  obtain ⟨c, hc⟩ : ∃ c : ZLattice.dual Λ → ℂ, HasSum (fun m ↦ c m • χ.modulate m) φ :=
    ⟨_, ContDiffMapSupportedIn.hasSum_fourier_smul_modulate Λ φ χ hK fun y hy ↦
      hχ1 y (hgsupp hy)⟩
  refine ⟨ZLattice.dual Λ, (↑), c, fun k ↦ ?_⟩
  have h1 := ((ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ k).continuous.tendsto φ).comp hc
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly] at h1
  -- Near the ball `χ = 1`, so there the partial sums are the trigonometric polynomials.
  refine h1.tendstoUniformlyOn.congr (Filter.Eventually.of_forall fun s y hy ↦ ?_)
  simp only [comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
  refine (Filter.EventuallyEq.iteratedFDeriv ℝ (Filter.eventually_of_mem
    (Metric.isOpen_ball.mem_nhds hy) fun y' hy' ↦ ?_) k).eq_of_nhds
  simp [hχ1 y' hy', real_inner_comm]

end TauCeti
