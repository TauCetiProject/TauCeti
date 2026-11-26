/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.Analysis.Fourier.Torus.SchwartzMultiplier
import TauCeti.Analysis.PDE.HeatKernel.Basic
import TauCeti.Analysis.PDE.HeatKernel.FrequencyLocalized

/-!
# The heat semigroup on periodic Besov spaces

On the torus `𝕋ᵈ = UnitAddTorus d` the Laplacian acts on the Fourier mode `eₙ(x) = e^{2πi n·x}` by
`Δ eₙ = -4π² ‖n‖² eₙ`, so the heat semigroup `e^{tΔ}` multiplies the `n`-th Fourier coefficient by
`exp(-4π² t ‖n‖²)`. Periodic distributions, and the periodic Besov spaces `B^s_{p,q}(𝕋ᵈ)`
(`TauCeti.UnitAddTorus.BesovSpace`), are described by their Fourier coefficients `c : ℤᵈ → ℂ`, and
this file defines `e^{tΔ}` on all formal Fourier series (`TauCeti.UnitAddTorus.heatSemigroup`).

The heat semigroup acts on every periodic Besov space `B^s_{p,q}(𝕋ᵈ)`, `1 ≤ p, q ≤ ∞`, by
contractions (`TauCeti.UnitAddTorus.BesovSpace.heatSemigroup`), and for `t > 0` it gains any amount
of smoothness: it is a continuous linear map `B^s_{p,q}(𝕋ᵈ) → B^{s'}_{p,q}(𝕋ᵈ)` for every `s'`
(`TauCeti.UnitAddTorus.BesovSpace.heatSemigroupOfNeZero`), and for `σ ≥ 0` there is a constant
`C`, depending only on the bump function `φ` of the Littlewood–Paley partition and on `σ`, such that

`‖e^{tΔ} u‖_{B^{s + 2σ}_{p,q}} ≤ C t^{-σ} ‖u‖_{B^s_{p,q}}` for `0 < t ≤ 1`

(`TauCeti.UnitAddTorus.BesovSpace.exists_norm_heatSemigroupOfNeZero_le_rpow_neg`). At
`p = q = ∞` this is the smoothing estimate `‖e^{tΔ} u‖_{𝒞^{s + 2σ}} ≤ C t^{-σ} ‖u‖_{𝒞^s}` on the
periodic Hölder–Zygmund scale. For `σ > 0` the restriction `t ≤ 1` cannot be dropped: the constant
function `1`, whose only nonzero Fourier coefficient is at `n = 0`, lies in every `B^s_{p,q}(𝕋ᵈ)`
and is fixed by `e^{tΔ}`, so its norm does not tend to `0` as `t → ∞`, while `t^{-σ}` does. For all
`t > 0` the bound holds with `max 1 (t^{-σ})` in place of `t^{-σ}`
(`TauCeti.UnitAddTorus.BesovSpace.exists_norm_heatSemigroupOfNeZero_le`). This is the periodic
counterpart of `TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le_rpow_neg` on `ℝᵈ`.

## The argument

Everything reduces to the blocks `Δⱼ c = ∑ₙ ψⱼ(n) c(n) eₙ`, which are trigonometric polynomials. If
a Schwartz function `σ` on `ℝᵈ` agrees with the heat symbol `exp(-4π² t ‖ξ‖²)` wherever `ψⱼ` does
not vanish, then `Δⱼ e^{tΔ} c` is the Fourier multiplier with symbol `σ` applied to `Δⱼ c`, which by
transference from `ℝᵈ` (`TauCeti.UnitAddTorus.eLpNorm_fourierMultiplier_le`) has `Lᵖ(𝕋ᵈ)` norm at
most `‖𝓕⁻ σ‖_{L¹(ℝᵈ)} ‖Δⱼ c‖_p`.

* With `σ` the Gaussian itself, `𝓕⁻ σ` is the heat kernel of `ℝᵈ`, a probability density, so
  `‖Δⱼ e^{tΔ} c‖_p ≤ ‖Δⱼ c‖_p` for every `j`
  (`TauCeti.UnitAddTorus.norm_littlewoodPaleyBlockLp_heatSemigroup_le`).
* For `j ≥ 1` the symbol `ψⱼ` lives in an annulus of size `2^j`, and `σ` can be the Gaussian cut
  off to that annulus (`TauCeti.cutoffHeatSymbol`), whose kernel has `L¹` norm
  `O(exp(-c 4^j t))` (`TauCeti.exists_integral_norm_fourierInv_mul_exp_le`). This gives
  `‖Δⱼ e^{tΔ} c‖_p ≤ C exp(-c (4^j - 1) t) ‖Δⱼ c‖_p` for every `j`
  (`TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_heatSemigroup_le`).

Finally `2^{js'} exp(-c (4^j - 1) t) ≤ A max 1 (t^{-σ}) 2^{js}` for `s' ≤ s + 2σ`
(`TauCeti.exists_two_rpow_mul_exp_neg_le`), which converts the decay of the `j`-th block into
the gain `2^{2σj}` of the weights of `B^{s+2σ}_{p,q}`.

## Main declarations

* `TauCeti.UnitAddTorus.heatSemigroup`: `e^{tΔ}` on formal Fourier series, with
  `TauCeti.UnitAddTorus.heatSemigroup_zero` and the semigroup law
  `TauCeti.UnitAddTorus.heatSemigroup_heatSemigroup_apply`.
* `TauCeti.UnitAddTorus.norm_littlewoodPaleyBlockLp_heatSemigroup_le` and
  `TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_heatSemigroup_le`: the heat flow of a
  periodic Littlewood–Paley block, a contraction in every `Lᵖ(𝕋ᵈ)`, decaying like
  `exp(-c (4^j - 1) t)`.
* `TauCeti.UnitAddTorus.MemBesov.heatSemigroup` and
  `TauCeti.UnitAddTorus.MemBesov.heatSemigroup_of_ne_zero`: `e^{tΔ}` preserves `B^s_{p,q}(𝕋ᵈ)` and,
  for `t > 0`, maps it into every `B^{s'}_{p,q}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.BesovSpace.heatSemigroup`: `e^{tΔ}` as a contraction of `B^s_{p,q}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.BesovSpace.heatSemigroupOfNeZero`: for `t > 0`, `e^{tΔ}` as a continuous
  linear map `B^s_{p,q}(𝕋ᵈ) → B^{s'}_{p,q}(𝕋ᵈ)`, with the bounds
  `TauCeti.UnitAddTorus.BesovSpace.exists_norm_heatSemigroupOfNeZero_le` and
  `TauCeti.UnitAddTorus.BesovSpace.exists_norm_heatSemigroupOfNeZero_le_rpow_neg`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.4 (the
  heat flow on frequency-localized functions).
* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (periodic Besov spaces).
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter VII,
  Section 3 (the transference of multipliers to the torus).
-/

public section

noncomputable section

open MeasureTheory Real
open scoped ENNReal NNReal FourierTransform SchwartzMap lp

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Littlewood–Paley blocks and the periodic Besov spaces live on `Lᵖ` for the product
-- of the Haar probability measures on the circle factors, given by this instance; use it here so
-- that the bounds below are about those same spaces.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

/-! ### The heat semigroup on formal Fourier series -/

variable (d) in
/-- The **heat semigroup** `e^{tΔ}` on formal Fourier series on the torus `𝕋ᵈ`: it multiplies the
`n`-th Fourier coefficient by `exp(-4π² t ‖n‖²)`, the eigenvalue of `e^{tΔ}` on the Fourier mode
`eₙ(x) = e^{2πi n·x}`. -/
def heatSemigroup (t : ℝ≥0) : ((d → ℤ) → ℂ) →ₗ[ℂ] (d → ℤ) → ℂ where
  toFun c n := (rexp (-(4 * π ^ 2 * t * ‖latticePoint n‖ ^ 2)) : ℂ) * c n
  map_add' _ _ := funext fun _ ↦ mul_add _ _ _
  map_smul' _ _ := funext fun _ ↦ mul_left_comm _ _ _

@[simp]
theorem heatSemigroup_apply (t : ℝ≥0) (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    heatSemigroup d t c n = (rexp (-(4 * π ^ 2 * t * ‖latticePoint n‖ ^ 2)) : ℂ) * c n :=
  (rfl)

variable (d) in
/-- At time `0` the heat semigroup is the identity. -/
@[simp]
theorem heatSemigroup_zero : heatSemigroup d 0 = LinearMap.id :=
  LinearMap.ext fun c ↦ funext fun n ↦ by simp

/-- **The semigroup law** `e^{t₂Δ} e^{t₁Δ} = e^{(t₁+t₂)Δ}` on formal Fourier series. -/
@[simp]
theorem heatSemigroup_heatSemigroup_apply (t₁ t₂ : ℝ≥0) (c : (d → ℤ) → ℂ) :
    heatSemigroup d t₂ (heatSemigroup d t₁ c) = heatSemigroup d (t₁ + t₂) c := by
  funext n
  simp only [heatSemigroup_apply, NNReal.coe_add, ← mul_assoc, ← Complex.ofReal_mul, ← exp_add]
  congr 3
  ring

/-! ### The heat flow of the periodic Littlewood–Paley blocks -/

variable {φ : ContDiffBump (0 : EuclideanSpace ℝ d)}

/-- **Transference of the heat flow of a block.** If a Schwartz function `σ` on `ℝᵈ` agrees with
the heat symbol `exp(-4π² t ‖ξ‖²)` wherever `ψⱼ` does not vanish, then the heat flow of the block
`Δⱼ c` is bounded in every `Lᵖ(𝕋ᵈ)` by `‖𝓕⁻ σ‖_{L¹(ℝᵈ)}`. -/
private theorem norm_littlewoodPaleyBlockLp_heatSemigroup_le_of_eq
    (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) {j : ℕ} {t : ℝ≥0}
    (hσ : ∀ ξ, φ.inhomogeneousLittlewoodPaley j ξ ≠ 0 →
      σ ξ = (rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : (d → ℤ) → ℂ) :
    ‖littlewoodPaleyBlockLp φ p j (heatSemigroup d t c)‖ ≤
      (∫ x, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) x‖) * ‖littlewoodPaleyBlockLp φ p j c‖ := by
  -- The symbol `σ` sampled on the lattice, a bounded sequence.
  let m : ℓ^∞(d → ℤ, ℂ) := ⟨fun n ↦ σ (latticePoint n), memℓp_infty
    ⟨SchwartzMap.seminorm ℂ 0 0 σ, by rintro _ ⟨n, rfl⟩; exact σ.norm_le_seminorm ℂ _⟩⟩
  have hm : ∀ n, m n = σ (latticePoint n) := fun _ ↦ rfl
  -- On the block `Δⱼ c ∈ L²(𝕋ᵈ)` the multiplier with symbol `σ` is the heat flow.
  have hf : fourierMultiplier m (littlewoodPaleyBlockLp φ 2 j c) =
      littlewoodPaleyBlockLp φ 2 j (heatSemigroup d t c) := by
    refine mFourierBasis.repr.injective (lp.ext (funext fun n ↦ ?_))
    simp only [mFourierBasis_repr, mFourierCoeff_fourierMultiplier,
      mFourierCoeff_littlewoodPaleyBlockLp, hm, heatSemigroup_apply]
    by_cases hψ : φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0
    · simp [hψ]
    · rw [hσ _ hψ]
      ring
  have h := eLpNorm_fourierMultiplier_le σ hm (Fact.out : (1 : ℝ≥0∞) ≤ p)
    (littlewoodPaleyBlockLp φ 2 j c)
  rw [hf, eLpNorm_congr_ae (coeFn_littlewoodPaleyBlockLp_ae_eq 2 p j _),
    eLpNorm_congr_ae (coeFn_littlewoodPaleyBlockLp_ae_eq 2 p j c)] at h
  have hI : 0 ≤ ∫ x, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) x‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  simpa [Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hI] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)) h

/-- **The heat flow contracts every periodic block:** `‖Δⱼ e^{tΔ} c‖_p ≤ ‖Δⱼ c‖_p` for every
`1 ≤ p ≤ ∞`, every `j`, every `t ≥ 0` and every formal Fourier series `c`. The kernel of `e^{tΔ}`
is a probability density. -/
theorem norm_littlewoodPaleyBlockLp_heatSemigroup_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ)
    (t : ℝ≥0) (c : (d → ℤ) → ℂ) :
    ‖littlewoodPaleyBlockLp φ p j (heatSemigroup d t c)‖ ≤ ‖littlewoodPaleyBlockLp φ p j c‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have ht' : (0 : ℝ) < t := by positivity
  have hb : 0 < ((4 * π ^ 2 * t : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  set g : 𝓢(EuclideanSpace ℝ d, ℂ) := SchwartzMap.gaussian hb
  have hg : (g : EuclideanSpace ℝ d → ℂ) =
      fun ξ ↦ ((rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ) :=
    SchwartzMap.coe_gaussian_ofReal hb
  have h := norm_littlewoodPaleyBlockLp_heatSemigroup_le_of_eq (φ := φ) g (j := j) (t := t)
    (fun ξ _ ↦ by rw [hg]) p c
  -- The kernel of the Gaussian symbol is the heat kernel, of integral `1`.
  have hI : ∫ x, ‖𝓕⁻ (g : EuclideanSpace ℝ d → ℂ) x‖ = 1 := by
    rw [hg, fourierInv_exp_neg_mul_norm_sq ht',
      ← integral_heatKernel (E := EuclideanSpace ℝ d) ht']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [Complex.norm_real, Real.norm_of_nonneg (heatKernel_pos ht' x).le]
  rwa [hI, one_mul] at h

variable (φ) in
/-- **The heat flow of every periodic Littlewood–Paley block.** There are constants `C ≥ 1` and
`κ > 0`, depending only on `φ`, such that for every `1 ≤ p ≤ ∞`, every `j`, every `t ≥ 0` and every
formal Fourier series `c`,

`‖Δⱼ e^{tΔ} c‖_p ≤ C exp(-κ (4^j - 1) t) ‖Δⱼ c‖_p`.

The factor `exp(-κ (4^j - 1) t)` is `1` for the low-frequency block `j = 0`; for `j ≥ 1` the block
has frequencies of size `2^j`, on which the heat flow decays exponentially in `4^j t`. -/
theorem exists_norm_littlewoodPaleyBlockLp_heatSemigroup_le :
    ∃ C κ : ℝ, 1 ≤ C ∧ 0 < κ ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (t : ℝ≥0)
      (c : (d → ℤ) → ℂ),
      ‖littlewoodPaleyBlockLp φ p j (heatSemigroup d t c)‖ ≤
        C * rexp (-(κ * ((4 ^ j - 1) * t))) * ‖littlewoodPaleyBlockLp φ p j c‖ := by
  obtain ⟨χ, hχ, hχc, hχ0, -, hχ1⟩ :=
    exists_contDiff_cutoff_annulus (E := EuclideanSpace ℝ d) φ.rIn_pos (2 * φ.rOut)
  obtain ⟨C₀, hC₀⟩ := exists_integral_norm_fourierInv_mul_exp_le hχ hχc (half_pos φ.rIn_pos) hχ0
  have hκ : 0 < π ^ 2 * φ.rIn ^ 2 / 16 := by
    have := φ.rIn_pos
    positivity
  refine ⟨max C₀ 1, π ^ 2 * φ.rIn ^ 2 / 16, le_max_right _ _, hκ, fun p _ j t c ↦ ?_⟩
  cases j with
  | zero =>
    simp only [pow_zero, sub_self, zero_mul, mul_zero, neg_zero, exp_zero, mul_one]
    exact (norm_littlewoodPaleyBlockLp_heatSemigroup_le p 0 t c).trans
      (le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _))
  | succ j =>
    -- The block `Δ_{j+1}` lives in the annulus `2^j φ.rIn ≤ ‖ξ‖ ≤ 2^j (2 φ.rOut)`, where the
    -- heat symbol cut off at scale `ν = 2^j` is the heat symbol itself.
    have hν : (0 : ℝ) < 2 ^ j := by positivity
    have hσ : ∀ ξ, φ.inhomogeneousLittlewoodPaley (j + 1) ξ ≠ 0 →
        cutoffHeatSymbol hχ hχc hν.ne' t ξ = (rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) := by
      intro ξ hξ
      obtain ⟨h₁, h₂⟩ :=
        φ.tsupport_inhomogeneousLittlewoodPaley_succ_subset j (subset_tsupport _ hξ)
      have hn : ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by
        rw [norm_smul, norm_inv, norm_of_nonneg hν.le]
      rw [cutoffHeatSymbol_apply, hχ1 _ (by rw [hn]; exact (le_inv_mul_iff₀ hν).2 h₁)
        (by rw [hn]; exact (inv_mul_le_iff₀ hν).2 (h₂.trans_eq (by ring))), one_mul]
    have hI := hC₀ (2 ^ j) hν t t.coe_nonneg
    rw [← funext (cutoffHeatSymbol_apply hχ hχc hν.ne' t)] at hI
    -- `π² (φ.rIn / 2)² 4^j t` dominates `κ (4^{j+1} - 1) t`.
    have he : -(π ^ 2 * (φ.rIn / 2) ^ 2 * (((2 : ℝ) ^ j) ^ 2 * t)) ≤
        -(π ^ 2 * φ.rIn ^ 2 / 16 * ((4 ^ (j + 1) - 1) * t)) := by
      have h4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have hd : π ^ 2 * (φ.rIn / 2) ^ 2 * (4 ^ j * t) -
          π ^ 2 * φ.rIn ^ 2 / 16 * ((4 ^ (j + 1) - 1) * t) = π ^ 2 * φ.rIn ^ 2 / 16 * t := by
        ring
      have : 0 ≤ π ^ 2 * φ.rIn ^ 2 / 16 * (t : ℝ) := by positivity
      rw [h4]
      linarith
    refine (norm_littlewoodPaleyBlockLp_heatSemigroup_le_of_eq _ hσ p c).trans
      (mul_le_mul_of_nonneg_right (hI.trans ?_) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (exp_le_exp.2 he) (zero_le_one.trans (le_max_right _ _)))

/-- **The weighted heat flow on a block.** For `σ ≥ 0` there is `C ≥ 0`, depending only on `φ` and
`σ`, such that `2^{js'} ‖Δⱼ e^{tΔ} c‖_p ≤ C max 1 (t^{-σ}) 2^{js} ‖Δⱼ c‖_p` whenever
`s' ≤ s + 2σ` and `t > 0`. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlockLp_heatSemigroup_le {σ : ℝ}
    (hσ : 0 ≤ σ) (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    ∃ C, 0 ≤ C ∧ ∀ {s s' : ℝ} (p : ℝ≥0∞) [Fact (1 ≤ p)], s' ≤ s + 2 * σ → ∀ t : ℝ≥0, t ≠ 0 →
      ∀ (j : ℕ) (c : (d → ℤ) → ℂ),
        2 ^ (s' * j) * ‖littlewoodPaleyBlockLp φ p j (heatSemigroup d t c)‖ ≤
          C * max 1 ((t : ℝ) ^ (-σ)) * (2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖) := by
  obtain ⟨C, κ, hC1, hκ, hCκ⟩ := exists_norm_littlewoodPaleyBlockLp_heatSemigroup_le φ
  obtain ⟨A, hA0, hA⟩ := exists_two_rpow_mul_exp_neg_le hσ hκ
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  refine ⟨C * A, mul_nonneg hC0 hA0, fun {s s'} p _ hs' t ht j c ↦ ?_⟩
  calc 2 ^ (s' * j) * ‖littlewoodPaleyBlockLp φ p j (heatSemigroup d t c)‖
      ≤ 2 ^ (s' * j) *
          (C * rexp (-(κ * ((4 ^ j - 1) * t))) * ‖littlewoodPaleyBlockLp φ p j c‖) := by
        gcongr
        exact hCκ p j t c
    _ = C * (2 ^ (s' * j) * rexp (-(κ * ((4 ^ j - 1) * t)))) *
          ‖littlewoodPaleyBlockLp φ p j c‖ := by
        ring
    _ ≤ C * (A * max 1 ((t : ℝ) ^ (-σ)) * 2 ^ (s * j)) * ‖littlewoodPaleyBlockLp φ p j c‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hA hs' j (NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht))) hC0) (norm_nonneg _)
    _ = C * A * max 1 ((t : ℝ) ^ (-σ)) * (2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖) := by
        ring

/-! ### The heat semigroup on the periodic Besov spaces -/

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The heat flow preserves periodic Besov membership.** If `c ∈ B^s_{p,q}(𝕋ᵈ)`, then
`e^{tΔ} c ∈ B^s_{p,q}(𝕋ᵈ)` for every `t ≥ 0`: each block is contracted. -/
theorem MemBesov.heatSemigroup {c : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c) (t : ℝ≥0) :
    MemBesov φ s p q (UnitAddTorus.heatSemigroup d t c) :=
  memBesov_def.2 <| (memBesov_def.1 hc).mono fun j ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_littlewoodPaleyBlockLp_heatSemigroup_le p j t c)
      (by positivity)

/-- **The heat flow gains every amount of smoothness.** If `c ∈ B^s_{p,q}(𝕋ᵈ)` and `t > 0`, then
`e^{tΔ} c ∈ B^{s'}_{p,q}(𝕋ᵈ)` for every `s'`. -/
theorem MemBesov.heatSemigroup_of_ne_zero {c : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c)
    {t : ℝ≥0} (ht : t ≠ 0) (s' : ℝ) : MemBesov φ s' p q (UnitAddTorus.heatSemigroup d t c) := by
  obtain ⟨C, -, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_heatSemigroup_le
    (le_max_left 0 ((s' - s) / 2)) φ
  have hs' : s' ≤ s + 2 * max 0 ((s' - s) / 2) := by linarith [le_max_right 0 ((s' - s) / 2)]
  refine memBesov_def.2 <| ((memBesov_def.1 hc).const_mul
    (C * max 1 ((t : ℝ) ^ (-max 0 ((s' - s) / 2))))).mono fun j ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC p hs' t ht j c

namespace BesovSpace

variable [Fact (1 ≤ q)]

variable (φ s p q) in
/-- **The heat semigroup on a periodic Besov space.** For `t ≥ 0`, `e^{tΔ}` maps
`B^s_{p,q}(𝕋ᵈ)` to itself with norm at most `1`. -/
def heatSemigroup (t : ℝ≥0) : BesovSpace φ s p q →L[ℂ] BesovSpace φ s p q :=
  LinearMap.mkContinuous
    { toFun u := ⟨UnitAddTorus.heatSemigroup d t u.coeff, u.memBesov_coeff.heatSemigroup t⟩
      map_add' u v := ext (map_add _ _ _)
      map_smul' a u := ext (map_smul _ _ _) }
    1 fun u ↦ norm_le_mul_norm_of_forall_rpow_mul_norm_le zero_le_one fun j ↦ by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_littlewoodPaleyBlockLp_heatSemigroup_le p j t u.coeff) (by positivity)

@[simp]
theorem coeff_heatSemigroup (t : ℝ≥0) (u : BesovSpace φ s p q) :
    (heatSemigroup φ s p q t u).coeff = UnitAddTorus.heatSemigroup d t u.coeff :=
  (rfl)

/-- The heat semigroup is a contraction of `B^s_{p,q}(𝕋ᵈ)`. -/
theorem norm_heatSemigroup_le (t : ℝ≥0) (u : BesovSpace φ s p q) :
    ‖heatSemigroup φ s p q t u‖ ≤ ‖u‖ :=
  ((heatSemigroup φ s p q t).le_opNorm u).trans (mul_le_of_le_one_left (norm_nonneg _)
    (LinearMap.mkContinuous_norm_le _ zero_le_one _))

variable (φ s p q) in
/-- At time `0` the heat semigroup on `B^s_{p,q}(𝕋ᵈ)` is the identity. -/
@[simp]
theorem heatSemigroup_zero : heatSemigroup φ s p q 0 = ContinuousLinearMap.id ℂ _ := by
  ext1 u
  exact ext (by simp)

/-- **The semigroup law** `e^{t₂Δ} e^{t₁Δ} = e^{(t₁+t₂)Δ}` on `B^s_{p,q}(𝕋ᵈ)`. -/
@[simp]
theorem heatSemigroup_heatSemigroup_apply (t₁ t₂ : ℝ≥0) (u : BesovSpace φ s p q) :
    heatSemigroup φ s p q t₂ (heatSemigroup φ s p q t₁ u) = heatSemigroup φ s p q (t₁ + t₂) u :=
  ext (by simp)

/-- The semigroup law `e^{t₂Δ} ∘ e^{t₁Δ} = e^{(t₁+t₂)Δ}` on `B^s_{p,q}(𝕋ᵈ)` as an identity of
operators. -/
theorem heatSemigroup_compL_heatSemigroup (t₁ t₂ : ℝ≥0) :
    heatSemigroup φ s p q t₂ ∘L heatSemigroup φ s p q t₁ = heatSemigroup φ s p q (t₁ + t₂) := by
  ext1 u
  exact heatSemigroup_heatSemigroup_apply t₁ t₂ u

variable (φ s p q) in
/-- **The smoothing heat semigroup on the periodic Besov scale.** For `t > 0`, `e^{tΔ}` maps
`B^s_{p,q}(𝕋ᵈ)` continuously into `B^{s'}_{p,q}(𝕋ᵈ)` for every `s'`
(`TauCeti.UnitAddTorus.MemBesov.heatSemigroup_of_ne_zero`). For `σ ≥ 0` and `s' ≤ s + 2σ` its norm
is `O(max 1 (t^{-σ}))`, uniformly in `s`, `s'`, `p`, `q` and `t`
(`TauCeti.UnitAddTorus.BesovSpace.exists_norm_heatSemigroupOfNeZero_le`). -/
def heatSemigroupOfNeZero (s' : ℝ) {t : ℝ≥0} (ht : t ≠ 0) :
    BesovSpace φ s p q →L[ℂ] BesovSpace φ s' p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := ⟨UnitAddTorus.heatSemigroup d t u.coeff,
        u.memBesov_coeff.heatSemigroup_of_ne_zero ht s'⟩
      map_add' u v := ext (map_add _ _ _)
      map_smul' a u := ext (map_smul _ _ _) } <| by
    obtain ⟨C, hC0, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_heatSemigroup_le
      (le_max_left 0 ((s' - s) / 2)) φ
    have hs' : s' ≤ s + 2 * max 0 ((s' - s) / 2) := by linarith [le_max_right 0 ((s' - s) / 2)]
    exact ⟨C * max 1 ((t : ℝ) ^ (-max 0 ((s' - s) / 2))), fun u ↦
      norm_le_mul_norm_of_forall_rpow_mul_norm_le (by positivity) fun j ↦
        hC p hs' t ht j u.coeff⟩

@[simp]
theorem coeff_heatSemigroupOfNeZero (s' : ℝ) {t : ℝ≥0} (ht : t ≠ 0) (u : BesovSpace φ s p q) :
    (heatSemigroupOfNeZero φ s p q s' ht u).coeff = UnitAddTorus.heatSemigroup d t u.coeff :=
  (rfl)

/-- At the order `s' = s` the smoothing heat semigroup is the heat semigroup on
`B^s_{p,q}(𝕋ᵈ)`. -/
theorem heatSemigroupOfNeZero_self {t : ℝ≥0} (ht : t ≠ 0) :
    heatSemigroupOfNeZero φ s p q s ht = heatSemigroup φ s p q t := by
  ext1 u
  exact ext (by simp)

variable (φ) in
/-- **The heat semigroup on a periodic Besov space gains smoothness.** For `σ ≥ 0` there is a
constant `C`, depending only on `φ` and `σ`, such that for every `1 ≤ p, q ≤ ∞`, every `s`, every
`s' ≤ s + 2σ`, every `t > 0` and every `u ∈ B^s_{p,q}(𝕋ᵈ)`,

`‖e^{tΔ} u‖_{B^{s'}_{p,q}} ≤ C max 1 (t^{-σ}) ‖u‖_{B^s_{p,q}}`. -/
theorem exists_norm_heatSemigroupOfNeZero_le {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ {s s' : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], s' ≤ s + 2 * σ →
      ∀ {t : ℝ≥0} (ht : t ≠ 0) (u : BesovSpace φ s p q),
        ‖heatSemigroupOfNeZero φ s p q s' ht u‖ ≤ C * max 1 ((t : ℝ) ^ (-σ)) * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_heatSemigroup_le hσ φ
  exact ⟨C, hC0, fun {s s' p q} _ _ hs' t ht u ↦
    norm_le_mul_norm_of_forall_rpow_mul_norm_le (by positivity) fun j ↦ hC p hs' t ht j u.coeff⟩

variable (φ) in
/-- **The smoothing estimate of the heat semigroup on periodic Besov spaces.** For `σ ≥ 0` there
is a constant `C`, depending only on `φ` and `σ`, such that for every `1 ≤ p, q ≤ ∞`, every `s`,
every `s' ≤ s + 2σ`, every `0 < t ≤ 1` and every `u ∈ B^s_{p,q}(𝕋ᵈ)`,

`‖e^{tΔ} u‖_{B^{s'}_{p,q}} ≤ C t^{-σ} ‖u‖_{B^s_{p,q}}`.

For `p = q = ∞` and `s' = s + 2σ` this is the smoothing estimate of the heat semigroup on the
periodic Hölder–Zygmund scale `𝒞^s(𝕋ᵈ) = B^s_{∞,∞}(𝕋ᵈ)`. -/
theorem exists_norm_heatSemigroupOfNeZero_le_rpow_neg {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ {s s' : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], s' ≤ s + 2 * σ →
      ∀ {t : ℝ≥0} (ht : t ≠ 0), t ≤ 1 → ∀ u : BesovSpace φ s p q,
        ‖heatSemigroupOfNeZero φ s p q s' ht u‖ ≤ C * (t : ℝ) ^ (-σ) * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_heatSemigroupOfNeZero_le φ hσ
  refine ⟨C, hC0, fun {s s' p q} _ _ hs' t ht ht1 u ↦ (hC hs' ht u).trans_eq ?_⟩
  rw [max_eq_right (one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity)
    (by exact_mod_cast ht1) (neg_nonpos.2 hσ))]

end BesovSpace

end TauCeti.UnitAddTorus
