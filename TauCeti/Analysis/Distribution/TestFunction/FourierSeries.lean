/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.PositiveDefinite.FourierAtom

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
  modulated cutoffs, uniformly over the cutoffs with bounded derivatives
  (`ContDiffMapSupportedIn.exists_seminorm_modulate_le`);
* the coefficients `𝓕 φ (m)` decay faster than every power of `‖m‖`, since `𝓕 φ` is a Schwartz
  function (`ContDiffMapSupportedIn.summable_one_add_norm_pow_mul_norm_fourier`).

Expansions of this kind are the first step of the Fourier-series proof of the Schwartz kernel
theorem: a continuous linear map on test functions is determined by its values on the
modulated cutoffs, which grow at most polynomially, and the rapidly decreasing coefficients make
the resulting double series converge.

## Main definitions

* `ContDiffMapSupportedIn.modulate`: the modulation `x ↦ exp (2πi ⟪x, w⟫) • χ x` of a function
  `χ` supported in `K` by the character of frequency `w`.
* `ContDiffMapSupportedIn.modulateCLM`: modulation by a fixed frequency, as a continuous linear
  map.
* `TestFunction.toSupportedInTSupport`: a test function `χ` on an open set, as a function
  supported in the compact set `tsupport χ`, whose modulations are the modulated cutoffs of
  Fourier series with cutoff `χ`.

## Main results

* `ContDiffMapSupportedIn.seminorm_modulate_le`: the polynomial bound on the derivatives of a
  modulated cutoff.
* `ContDiffMapSupportedIn.exists_seminorm_modulate_le`: a continuous seminorm grows at most
  polynomially along modulated cutoffs, with a degree independent of the cutoff and a constant
  proportional to a sup norm of finitely many of its derivatives.
* `ContDiffMapSupportedIn.summable_one_add_norm_pow_mul_norm_fourier`: the Fourier transform of a
  smooth function supported in `K` decays rapidly along a lattice;
  `ContDiffMapSupportedIn.exists_tsum_one_add_norm_pow_mul_norm_fourier_le` bounds the weighted
  sums by a sup norm of finitely many derivatives.
* `ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`: the Fourier expansion of a smooth
  function supported in `K`, converging in `𝓓_{K}(E, ℂ)`.
* `ContDiffMapSupportedIn.exists_compacts_cutoff_lattice`: around every point there are a compact
  set `K` inside a given neighbourhood, a smooth function supported in `K` equal to one near the
  point, and a full lattice none of whose nonzero translates of `K` meet `K`: the data of the
  Fourier expansions above.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Theorem 5.2.1.
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967,
  Chapter 51.
-/

public section

noncomputable section

open Complex Function Set TopologicalSpace
open scoped Real RealInnerProductSpace FourierTransform Distributions ContDiff SchwartzMap Topology

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ∞} {K : Compacts E}

/-! ### The phase of a character -/

/-- The phase `x ↦ 2πi ⟪x, w⟫` of the character of frequency `w`, as a real-linear map. -/
private def phase (w : E) : E →L[ℝ] ℂ :=
  (2 * π * I) • (ofRealCLM.comp (innerSL ℝ w))

private theorem phase_apply (w x : E) : phase w x = 2 * π * I * ⟪x, w⟫ := by
  simp [phase, real_inner_comm]

private theorem contDiff_exp_phase (w : E) : ContDiff ℝ ∞ fun x ↦ cexp (phase w x) :=
  (phase w).contDiff.cexp

/-- Every derivative of the character `x ↦ exp (2πi ⟪x, w⟫)` of frequency `w` has norm at most
`(2π ‖w‖) ^ k`. -/
private theorem norm_iteratedFDeriv_exp_phase_le (w x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ cexp (phase w y)) x‖ ≤ (2 * π * ‖w‖) ^ k := by
  have h : (fun y ↦ cexp (phase w y)) = TauCeti.fourierAtom (-w) := by
    ext y
    rw [TauCeti.fourierAtom_apply, phase_apply, inner_neg_right]
    push_cast
    ring_nf
  rw [h, ← norm_neg w]
  exact TauCeti.norm_iteratedFDeriv_fourierAtom_le (-w) x k

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
        gcongr with i _
        · exact norm_iteratedFDeriv_exp_phase_le w x i
        · exact hχ _ (Nat.sub_le k i)
    _ = S * (1 + 2 * π * ‖w‖) ^ k := by
        rw [add_comm 1, add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring

/-- Every continuous seminorm `q` on `𝓓_{K}(E, F)` grows at most polynomially along the
modulated cutoffs `χ.modulate w`, with a degree and a constant independent of the cutoff: there are
`k` and `C` such that `q (χ.modulate w) ≤ C (sup_{i ≤ k} N_i χ) (1 + ‖w‖) ^ k` for every `χ` and
every frequency `w`. Applied to `ψ ↦ ‖T ψ‖`, this bounds the images of modulated cutoffs under a
continuous linear map `T` to a normed space, uniformly over the cutoffs with bounded derivatives
of order at most `k`. -/
theorem exists_seminorm_modulate_le (q : Seminorm ℂ 𝓓_{K}(E, F)) (hq : Continuous q) :
    ∃ (k : ℕ) (C : ℝ), ∀ (χ : 𝓓_{K}(E, F)) (w : E),
      q (χ.modulate w) ≤ C * ContDiffMapSupportedIn.supSeminorm ℂ E F ⊤ K k χ * (1 + ‖w‖) ^ k := by
  obtain ⟨s, C, -, hC⟩ :=
    Seminorm.bound_of_continuous (ContDiffMapSupportedIn.withSeminorms ℂ E F ⊤ K) q hq
  set k := s.sup id
  refine ⟨k, C * (2 * π) ^ k, fun χ w ↦ ?_⟩
  set S := ContDiffMapSupportedIn.supSeminorm ℂ E F ⊤ K k χ
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
    _ = C * (2 * π) ^ k * S * (1 + ‖w‖) ^ k := by ring

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

/-- Around every point `x` there are a compact set `K` inside a given neighbourhood `U` of `x`, a
smaller neighbourhood `K₁` of `x`, a smooth function supported in `K` equal to one on `K₁`, and a
full lattice none of whose nonzero translates of `K` meet `K`: the data of a Fourier expansion
(`hasSum_fourier_smul_modulate`) of the functions supported in `K₁`. -/
theorem exists_compacts_cutoff_lattice [FiniteDimensional ℝ E] {x : E} {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ (K : Compacts E) (K₁ : Set E), (K : Set E) ⊆ U ∧ K₁ ∈ 𝓝 x ∧ K₁ ⊆ K ∧
      (∃ χ : 𝓓_{K}(E, ℂ), ∀ y ∈ K₁, χ y = 1) ∧ ∃ (L : Submodule ℤ E) (_ : DiscreteTopology L)
        (_ : IsZLattice ℝ L), ∀ y ∈ K, ∀ ℓ : L, y + ℓ ∈ K → ℓ = 0 := by
  obtain ⟨K₂, hK₂x, hK₂U, hK₂⟩ := local_compact_nhds hU
  obtain ⟨K₁, hK₁x, hK₁K₂, hK₁⟩ := local_compact_nhds (interior_mem_nhds.2 hK₂x)
  obtain ⟨χ₀, hχ₀, -, hχ₀1, -, hχ₀s⟩ := hK₁.exists_contDiff_cutoff isOpen_interior hK₁K₂
  obtain ⟨L, hLd, hLz, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
  refine ⟨⟨K₂, hK₂⟩, K₁, hK₂U, hK₁x, hK₁K₂.trans interior_subset,
    ⟨ContDiffMapSupportedIn.of_support_subset (ofRealCLM.contDiff.comp hχ₀)
      fun y hy ↦ interior_subset (hχ₀s (subset_tsupport _ (by simpa using hy))), fun y hy ↦ ?_⟩,
    L, hLd, hLz, fun y hy ℓ h ↦ Subtype.ext (hL y hy ℓ ℓ.property h)⟩
  have h1 : χ₀ y = 1 := interior_subset (hχ₀1 hy)
  exact (ContDiffMapSupportedIn.coe_of_support_subset _ _ y).trans (by simp [h1])

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

/-- **Rapid decay of the Fourier transform along a lattice.** The Fourier transform of a smooth
function `φ` supported in `K` decays faster than every power along a discrete subgroup `Λ`: the
family `ℓ ↦ (1 + ‖ℓ‖) ^ k ‖𝓕 φ ℓ‖` is summable for every `k`. -/
theorem summable_one_add_norm_pow_mul_norm_fourier (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (φ : 𝓓_{K}(E, ℂ)) (k : ℕ) :
    Summable fun ℓ : Λ ↦ (1 + ‖(ℓ : E)‖) ^ k * ‖𝓕 (φ : E → ℂ) ℓ‖ := by
  let g : 𝓢(E, ℂ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  -- `g` is `φ`, read as a Schwartz function.
  have hg : (g : E → ℂ) = φ := rfl
  have hdecay := ZLattice.summable_one_add_norm_pow_mul_norm Λ (𝓕 g) k
  rwa [SchwartzMap.fourier_coe, hg] at hdecay

/-- **Uniform rapid decay of the Fourier transform along a lattice.** For a discrete subgroup `Λ`
and a degree `j`, the sums `∑ ℓ : Λ, (1 + ‖ℓ‖) ^ j ‖𝓕 φ ℓ‖` of the smooth functions `φ`
supported in `K` are bounded by a constant times a sup norm of finitely many derivatives of `φ`.
In particular they are bounded uniformly over the functions supported in `K` whose derivatives of
order at most `r` are bounded. -/
theorem exists_tsum_one_add_norm_pow_mul_norm_fourier_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (j : ℕ) : ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : 𝓓_{K}(E, ℂ),
      ∑' ℓ : Λ, (1 + ‖(ℓ : E)‖) ^ j * ‖𝓕 (φ : E → ℂ) ℓ‖ ≤
        C * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K r φ := by
  set d := Module.finrank ℤ Λ + 1
  set N := j + d
  -- The Schwartz seminorms of `𝓕 g` controlling `(1 + ‖ξ‖) ^ N ‖𝓕 g ξ‖` are bounded by finitely
  -- many Schwartz seminorms of `g`.
  let q : Seminorm ℂ 𝓢(E, ℂ) :=
    ((Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ E ℂ)).comp
      (SchwartzMap.fourierTransformCLM ℂ).toLinearMap
  have hq : Continuous q := ((schwartz_withSeminorms ℂ E ℂ).continuous_finsetSup_seminorm _).comp
    (SchwartzMap.fourierTransformCLM ℂ).continuous
  obtain ⟨s, C₁, -, hC₁⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
  set R₁ := max R 1
  set A := s.sup Prod.fst; set r := s.sup Prod.snd
  have hsum := ZLattice.summable_one_add_norm_pow_inv Λ (r := d) (by omega)
  refine ⟨r, 2 ^ N * (C₁ * R₁ ^ A) * ∑' ℓ : Λ, ((1 + ‖(ℓ : E)‖) ^ d)⁻¹,
    mul_nonneg (by positivity) (tsum_nonneg fun _ ↦ by positivity), fun φ ↦ ?_⟩
  let g : 𝓢(E, ℂ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  have hg : (g : E → ℂ) = φ := rfl
  set S := ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K r φ
  -- The Schwartz seminorms of `g` occurring in `s` are at most `R₁ ^ A S`.
  have hgs : s.sup (schwartzSeminormFamily ℂ E ℂ) g ≤ R₁ ^ A * S := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun m hm ↦ ?_
    refine SchwartzMap.seminorm_le_bound ℂ m.1 m.2 g (by positivity) fun x ↦ ?_
    by_cases hx : x ∈ K
    · have hxR : ‖x‖ ≤ R₁ := (hR x hx).trans (le_max_left _ _)
      gcongr ?_ * ?_
      · exact (pow_le_pow_left₀ (norm_nonneg x) hxR m.1).trans
          (pow_le_pow_right₀ (le_max_right _ _) (Finset.le_sup (f := Prod.fst) hm))
      · rw [hg]
        exact (norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans <|
          Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K)
            (Finset.mem_Iic.2 (Finset.le_sup (f := Prod.snd) hm)) φ
    · rw [hg, φ.iteratedFDeriv_zero_on_compl hx]
      simp only [Pi.zero_apply, norm_zero, mul_zero]
      positivity
  -- Pointwise, `(1 + ‖ξ‖) ^ N ‖𝓕 φ ξ‖ ≤ 2 ^ N q g`.
  have hpt (ξ : E) : (1 + ‖ξ‖) ^ N * ‖𝓕 (φ : E → ℂ) ξ‖ ≤ 2 ^ N * (C₁ * (R₁ ^ A * S)) := by
    have h := (𝓕 g).one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) le_rfl le_rfl ξ
    rw [norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe, hg] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ E ℂ) (𝓕 g) = q g := rfl
      _ ≤ C₁ * s.sup (schwartzSeminormFamily ℂ E ℂ) g := hC₁ g
      _ ≤ C₁ * (R₁ ^ A * S) := by gcongr
  rw [mul_assoc (2 ^ N * (C₁ * R₁ ^ A)), ← tsum_mul_right, ← tsum_mul_left]
  refine (summable_one_add_norm_pow_mul_norm_fourier Λ φ j).tsum_le_tsum (fun ℓ ↦ ?_)
    ((hsum.mul_right S).mul_left _)
  have hpos : 0 < (1 + ‖(ℓ : E)‖) ^ d := by positivity
  rw [inv_mul_eq_div, mul_div_assoc', le_div_iff₀ hpos, mul_right_comm, ← pow_add]
  calc (1 + ‖(ℓ : E)‖) ^ (j + d) * ‖𝓕 (φ : E → ℂ) ℓ‖ ≤ 2 ^ N * (C₁ * (R₁ ^ A * S)) := hpt ℓ
    _ = 2 ^ N * (C₁ * R₁ ^ A) * S := by ring

/-- The `k`-th seminorm bound for the terms of the Fourier expansion is summable. -/
private theorem summable_norm_fourier_mul (φ χ : 𝓓_{K}(E, ℂ)) (k : ℕ) :
    Summable fun m : ZLattice.dual L ↦ ‖(ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m‖ *
      (ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * (1 + 2 * π * ‖(m : E)‖) ^ k) := by
  have hdecay := summable_one_add_norm_pow_mul_norm_fourier (ZLattice.dual L) φ k
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

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

/-- A test function `χ` on `Ω`, as a `C^n` function supported in the compact set `tsupport χ`.
Its modulations `χ.toSupportedInTSupport.modulate w` are the modulated cutoffs of the Fourier
series with cutoff `χ`. -/
def toSupportedInTSupport (χ : 𝓓^{n}(Ω, F)) :
    𝓓^{n}_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩}(E, F) :=
  .of_support_subset χ.contDiff (subset_tsupport _)

@[simp]
theorem coe_toSupportedInTSupport (χ : 𝓓^{n}(Ω, F)) : ⇑χ.toSupportedInTSupport = χ := by
  rw [toSupportedInTSupport]
  rfl

end TestFunction
