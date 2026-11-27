/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
public import TauCeti.Analysis.Fourier.Torus.Multiplier
public import TauCeti.Analysis.Fourier.Torus.SchwartzMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Normed.Module.Ball

/-!
# The periodic Littlewood–Paley decomposition of the torus

Let `φ` be a smooth bump function on `EuclideanSpace ℝ d` and let `ψ₀ = φ, ψ₁, ψ₂, …` be the
inhomogeneous Littlewood–Paley partition of unity built from it
(`ContDiffBump.inhomogeneousLittlewoodPaley`), so that `ψ₀` is supported in the ball of radius
`φ.rOut` and `ψⱼ`, `j ≥ 1`, in the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`. On the torus
`𝕋ᵈ = UnitAddTorus d` the frequencies are the lattice points `n ∈ ℤᵈ`, and the **periodic
Littlewood–Paley blocks** are the Fourier multipliers

`(Δⱼ f)^(n) = ψⱼ(n) f̂(n)`

on `L²(𝕋ᵈ)` (`TauCeti.UnitAddTorus.littlewoodPaleyBlock`). This is the periodic counterpart of the
decomposition of tempered distributions on `ℝᵈ` into the blocks
`TemperedDistribution.littlewoodPaleyBlock`, with the Fourier transform replaced by Fourier series.

The blocks have the following properties.

* **Spectral localization.** `Δⱼ f` has no Fourier coefficients outside the support of `ψⱼ`. Only
  finitely many lattice points lie in a ball, so `Δⱼ f` is a trigonometric polynomial, with
  frequencies in a finite set depending only on `j` and `φ`
  (`TauCeti.UnitAddTorus.exists_finset_littlewoodPaleyBlock_eq_sum`).
* **Reconstruction.** The partial sums `∑_{j ≤ N} Δⱼ` are the Fourier multipliers with the
  low-pass symbols `n ↦ φ(2^{-N} n)`, and `∑ⱼ Δⱼ f = f` in `L²(𝕋ᵈ)`
  (`TauCeti.UnitAddTorus.tendsto_sum_littlewoodPaleyBlock`).
* **Almost orthogonality.** There is `L`, depending only on `φ`, with `Δⱼ Δₖ = 0` whenever
  `|j - k| ≥ L`; more generally the blocks `Δⱼ` of `φ` and `Δ'ₖ` of a second bump function `φ'`
  satisfy `Δⱼ Δ'ₖ = Δ'ₖ Δⱼ = 0` whenever `j + L ≤ k`, for some `L` depending on `φ` and `φ'`
  (`TauCeti.UnitAddTorus.exists_littlewoodPaleyBlock_comp_eq_zero`).
* **The `L²` square function.** By Parseval's identity,
  `∑ⱼ ‖Δⱼ f‖² = ∑ₙ (∑ⱼ ψⱼ(n)²) ‖f̂(n)‖²`
  (`TauCeti.UnitAddTorus.hasSum_norm_sq_littlewoodPaleyBlock`), and the weight `∑ⱼ ψⱼ(n)²` is
  bounded above and below by positive constants depending only on `φ`. Hence the square function
  `(∑ⱼ ‖Δⱼ f‖²)^{1/2}` is equivalent to `‖f‖` on `L²(𝕋ᵈ)`. The weight need not be identically `1`,
  since the `ψⱼ` form a partition of unity rather than a partition of unity of squares.
* **Uniform `Lᵖ` bounds.** For `1 ≤ p ≤ ∞`, `‖Δⱼ f‖_p ≤ ‖𝓕⁻ ψⱼ‖_{L¹(ℝᵈ)} ‖f‖_p`
  (`TauCeti.UnitAddTorus.eLpNorm_littlewoodPaleyBlock_le`), the bound of the corresponding block on
  `Lᵖ(ℝᵈ)`. The kernels `𝓕⁻ ψⱼ`, `j ≥ 1`, are `L¹`-normalised dilates of one another, so the blocks
  are bounded on `Lᵖ` uniformly in `j`
  (`TauCeti.UnitAddTorus.exists_eLpNorm_littlewoodPaleyBlock_le`), and the low-pass partial sums
  `∑_{j ≤ N} Δⱼ` uniformly in `N`, by `‖𝓕⁻ φ‖_{L¹(ℝᵈ)}`
  (`TauCeti.UnitAddTorus.eLpNorm_sum_littlewoodPaleyBlock_range_le`).

As in Mathlib's `UnitAddTorus.mFourierBasis`, `L²(𝕋ᵈ)` is taken for the product of the Haar
probability measures on the circle factors.

## Main declarations

* `TauCeti.UnitAddTorus.littlewoodPaleySymbol`, `TauCeti.UnitAddTorus.littlewoodPaleyBlock`: the
  symbol `n ↦ ψⱼ(n)` and the block `Δⱼ`.
* `TauCeti.UnitAddTorus.mFourierCoeff_littlewoodPaleyBlock`: `(Δⱼ f)^(n) = ψⱼ(n) f̂(n)`.
* `TauCeti.UnitAddTorus.isSelfAdjoint_littlewoodPaleyBlock`: the blocks are self-adjoint.
* `TauCeti.UnitAddTorus.exists_finset_littlewoodPaleyBlock_eq_sum`: the blocks are trigonometric
  polynomials of bounded degree.
* `TauCeti.UnitAddTorus.mFourierCoeff_sum_littlewoodPaleyBlock_range` and
  `TauCeti.UnitAddTorus.tendsto_sum_littlewoodPaleyBlock`: the low-pass partial sums and
  `∑ⱼ Δⱼ f = f`.
* `TauCeti.UnitAddTorus.mFourierCoeff_sum_littlewoodPaleyBlock_range_eq_zero`: the low-pass
  partial sums are trigonometric polynomials.
* `TauCeti.UnitAddTorus.exists_littlewoodPaleyBlock_comp_eq_zero`: almost orthogonality.
* `TauCeti.UnitAddTorus.sum_littlewoodPaleyBlock_littlewoodPaleyBlock`: the blocks of nearby index
  reproduce `Δⱼ`.
* `TauCeti.UnitAddTorus.hasSum_norm_sq_littlewoodPaleyBlock`,
  `TauCeti.UnitAddTorus.summable_tsum_inhomogeneousLittlewoodPaley_sq_mul_norm_sq_mFourierCoeff`,
  `TauCeti.UnitAddTorus.exists_tsum_norm_sq_littlewoodPaleyBlock_le` and
  `TauCeti.UnitAddTorus.exists_norm_sq_le_mul_tsum_norm_sq_littlewoodPaleyBlock`: the `L²` square
  function.
* `TauCeti.UnitAddTorus.eLpNorm_littlewoodPaleyBlock_le`,
  `TauCeti.UnitAddTorus.exists_eLpNorm_littlewoodPaleyBlock_le` and
  `TauCeti.UnitAddTorus.eLpNorm_sum_littlewoodPaleyBlock_range_le`: the uniform `Lᵖ` bounds.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.2.
* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 6.1 (Littlewood–Paley theory) and Section 4.3 (multipliers on the
  torus).
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped lp ENNReal NNReal FourierTransform SchwartzMap

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- Mathlib's Fourier basis `mFourierBasis` lives on `L²` for the product of the Haar probability
-- measures on the circle factors, given by this instance; use it here so that the blocks act on
-- that same space.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable (φ : ContDiffBump (0 : EuclideanSpace ℝ d))

/-! ### The blocks -/

/-- The symbol of the `j`-th periodic Littlewood–Paley block: the piece `ψⱼ` of the inhomogeneous
Littlewood–Paley partition built from `φ`, evaluated at the frequencies `n ∈ ℤᵈ`. -/
def littlewoodPaleySymbol (j : ℕ) : ℓ^∞(d → ℤ, ℂ) :=
  ⟨fun n ↦ (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ), memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    simpa using φ.abs_inhomogeneousLittlewoodPaley_le_one j (latticePoint n)⟩⟩

@[simp]
theorem littlewoodPaleySymbol_apply (j : ℕ) (n : d → ℤ) :
    littlewoodPaleySymbol φ j n = (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) :=
  (rfl)

/-- The symbol of every periodic Littlewood–Paley block is bounded by `1`. -/
theorem norm_littlewoodPaleySymbol_le (j : ℕ) : ‖littlewoodPaleySymbol φ j‖ ≤ 1 :=
  lp.norm_le_of_forall_le zero_le_one fun n ↦ by
    simpa using φ.abs_inhomogeneousLittlewoodPaley_le_one j (latticePoint n)

/-- The `j`-th **periodic Littlewood–Paley block** `Δⱼ` on `L²(𝕋ᵈ)`: the Fourier multiplier
multiplying the `n`-th Fourier coefficient by `ψⱼ(n)`, where `ψ₀ = φ, ψ₁, ψ₂, …` is the
inhomogeneous Littlewood–Paley partition built from `φ`. -/
def littlewoodPaleyBlock (j : ℕ) : L²(UnitAddTorus d) →L[ℂ] L²(UnitAddTorus d) :=
  fourierMultiplier (littlewoodPaleySymbol φ j)

/-- A periodic Littlewood–Paley block is the Fourier multiplier with symbol
`TauCeti.UnitAddTorus.littlewoodPaleySymbol φ j`. -/
theorem littlewoodPaleyBlock_eq_fourierMultiplier (j : ℕ) :
    littlewoodPaleyBlock φ j = fourierMultiplier (littlewoodPaleySymbol φ j) :=
  (rfl)

/-- The Fourier coefficients of a periodic Littlewood–Paley block: `(Δⱼ f)^(n) = ψⱼ(n) f̂(n)`. -/
@[simp]
theorem mFourierCoeff_littlewoodPaleyBlock (j : ℕ) (f : L²(UnitAddTorus d)) (n : d → ℤ) :
    mFourierCoeff (littlewoodPaleyBlock φ j f) n =
      φ.inhomogeneousLittlewoodPaley j (latticePoint n) * mFourierCoeff f n := by
  simp [littlewoodPaleyBlock_eq_fourierMultiplier]

/-- A periodic Littlewood–Paley block multiplies the Fourier mode `e_n` by `ψⱼ(n)`. -/
@[simp]
theorem littlewoodPaleyBlock_mFourierLp (j : ℕ) (n : d → ℤ) :
    littlewoodPaleyBlock φ j (mFourierLp 2 n) =
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) • mFourierLp 2 n := by
  simp [littlewoodPaleyBlock_eq_fourierMultiplier]

/-- Every periodic Littlewood–Paley block has operator norm at most `1`. -/
theorem norm_littlewoodPaleyBlock_le (j : ℕ) : ‖littlewoodPaleyBlock φ j‖ ≤ 1 := by
  rw [littlewoodPaleyBlock_eq_fourierMultiplier, norm_fourierMultiplier]
  exact norm_littlewoodPaleySymbol_le φ j

/-- The periodic Littlewood–Paley blocks are self-adjoint, since their symbols are real:
`⟪Δⱼ a, b⟫ = ⟪a, Δⱼ b⟫`. -/
theorem isSelfAdjoint_littlewoodPaleyBlock (j : ℕ) : IsSelfAdjoint (littlewoodPaleyBlock φ j) := by
  rw [littlewoodPaleyBlock_eq_fourierMultiplier]
  exact isSelfAdjoint_fourierMultiplier <| lp.ext <| funext fun n ↦ by
    simp [lp.star_apply, littlewoodPaleySymbol_apply]

/-! ### Spectral localization -/

/-- `Δⱼ f` has no Fourier coefficients at frequencies of norm at least `2^j φ.rOut`. -/
theorem mFourierCoeff_littlewoodPaleyBlock_eq_zero_of_le_norm {j : ℕ} {n : d → ℤ}
    (hn : 2 ^ j * φ.rOut ≤ ‖latticePoint n‖) (f : L²(UnitAddTorus d)) :
    mFourierCoeff (littlewoodPaleyBlock φ j f) n = 0 := by
  simp [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hn]

/-- For every `j`, `Δ_{j+1} f` has no Fourier coefficients at frequencies of norm at most
`2^j φ.rIn`. -/
theorem mFourierCoeff_littlewoodPaleyBlock_succ_eq_zero_of_norm_le {j : ℕ} {n : d → ℤ}
    (hn : ‖latticePoint n‖ ≤ 2 ^ j * φ.rIn) (f : L²(UnitAddTorus d)) :
    mFourierCoeff (littlewoodPaleyBlock φ (j + 1) f) n = 0 := by
  simp [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le hn]

/-- **The blocks are trigonometric polynomials.** There is a finite set `s` of frequencies,
depending only on `φ` and `j`, such that `Δⱼ f = ∑_{n ∈ s} ψⱼ(n) f̂(n) e_n` for every `f`. -/
theorem exists_finset_littlewoodPaleyBlock_eq_sum (j : ℕ) :
    ∃ s : Finset (d → ℤ), ∀ f : L²(UnitAddTorus d),
      littlewoodPaleyBlock φ j f =
        ∑ n ∈ s, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) * mFourierCoeff f n) •
          mFourierLp 2 n := by
  set s := (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ j * φ.rOut)).toFinset
  refine ⟨s, fun f ↦ ?_⟩
  have h : HasSum (fun n ↦
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) * mFourierCoeff f n) • mFourierLp 2 n)
      (∑ n ∈ s, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) * mFourierCoeff f n) •
        mFourierLp 2 n) :=
    hasSum_sum_of_ne_finset_zero fun n hn ↦ by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hn
      simp [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hn.le]
  rw [littlewoodPaleyBlock_eq_fourierMultiplier]
  exact (hasSum_fourierMultiplier _ f).unique (by simpa using h)

/-! ### Reconstruction -/

/-- The partial sums of the periodic Littlewood–Paley blocks are the low-pass multipliers:
`(∑_{j ≤ N} Δⱼ f)^(n) = φ(2^{-N} n) f̂(n)`. -/
theorem mFourierCoeff_sum_littlewoodPaleyBlock_range (N : ℕ) (f : L²(UnitAddTorus d))
    (n : d → ℤ) :
    mFourierCoeff ((∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock φ j) f) n =
      φ (((2 : ℝ) ^ N)⁻¹ • latticePoint n) * mFourierCoeff f n := by
  simp only [littlewoodPaleyBlock_eq_fourierMultiplier, ← map_sum,
    mFourierCoeff_fourierMultiplier, lp.coeFn_sum, Finset.sum_apply, littlewoodPaleySymbol_apply]
  rw [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range]

/-- The low-pass truncation `∑_{k ≤ M} Δₖ f` has no Fourier coefficients at frequencies of norm
greater than `2^M φ.rOut`. -/
theorem mFourierCoeff_sum_littlewoodPaleyBlock_range_eq_zero (M : ℕ) (f : L²(UnitAddTorus d)) :
    ∀ n ∉ (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ M * φ.rOut)).toFinset,
      mFourierCoeff ((∑ k ∈ Finset.range (M + 1), littlewoodPaleyBlock φ k) f) n = 0 := by
  intro n hn
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hn
  rw [mFourierCoeff_sum_littlewoodPaleyBlock_range, φ.zero_of_le_dist, Complex.ofReal_zero,
    zero_mul]
  rw [dist_zero_right, norm_inv_smul_of_nonneg (by positivity), le_div_iff₀ (by positivity),
    mul_comm]
  exact hn.le

/-- **Littlewood–Paley reconstruction on the torus.** For every `f ∈ L²(𝕋ᵈ)`, the partial sums
`∑_{j < N} Δⱼ f` converge to `f` in `L²(𝕋ᵈ)`. -/
theorem tendsto_sum_littlewoodPaleyBlock (f : L²(UnitAddTorus d)) :
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N, littlewoodPaleyBlock φ j f) atTop (𝓝 f) := by
  have hsum : ∀ N, ∑ j ∈ Finset.range N, littlewoodPaleyBlock φ j f =
      fourierMultiplier (∑ j ∈ Finset.range N, littlewoodPaleySymbol φ j) f := fun N ↦ by
    simp [littlewoodPaleyBlock_eq_fourierMultiplier, map_sum]
  have hbound : ∀ N, ‖∑ j ∈ Finset.range N, littlewoodPaleySymbol φ j‖ ≤ 1 := fun N ↦ by
    refine lp.norm_le_of_forall_le zero_le_one fun n ↦ ?_
    rcases N with _ | N
    · simp
    · simp only [lp.coeFn_sum, Finset.sum_apply, littlewoodPaleySymbol_apply,
        ← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (φ.nonneg)]
      exact φ.le_one
  simp_rw [hsum]
  simpa using tendsto_fourierMultiplier_apply (m₀ := 1) (Eventually.of_forall hbound)
    (fun n ↦ ((Complex.continuous_ofReal.tendsto 1).comp
        (φ.hasSum_inhomogeneousLittlewoodPaley (latticePoint n)).tendsto_sum_nat).congr fun N ↦ by
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp) f

/-! ### Almost orthogonality -/

/-- **Almost orthogonality.** For two bump functions `φ` and `φ'` there is `L` with
`Δⱼ Δ'ₖ = Δ'ₖ Δⱼ = 0` whenever `j + L ≤ k`, where `Δⱼ` are the blocks of `φ` and `Δ'ₖ` those of
`φ'`. For `φ' = φ` this is the almost orthogonality of a single family of blocks. -/
theorem exists_littlewoodPaleyBlock_comp_eq_zero (φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    ∃ L : ℕ, ∀ j k : ℕ, j + L ≤ k →
      littlewoodPaleyBlock φ j ∘L littlewoodPaleyBlock φ' k = 0 ∧
        littlewoodPaleyBlock φ' k ∘L littlewoodPaleyBlock φ j = 0 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ'
  refine ⟨L, fun j k hjk ↦ ?_⟩
  have h : littlewoodPaleySymbol φ j * littlewoodPaleySymbol φ' k = 0 := by
    ext n
    simp [← Complex.ofReal_mul, hL j k hjk]
  simp only [littlewoodPaleyBlock_eq_fourierMultiplier, ← ContinuousLinearMap.mul_def, ← map_mul,
    h, mul_comm (littlewoodPaleySymbol φ' k), map_zero, and_self]

/-- **The blocks of nearby index reproduce `Δⱼ`.** If `ψⱼ ψₖ = 0` whenever `j + L ≤ k`, then
`∑_{k ∈ [j + 1 - L, j + L)} Δₖ Δⱼ f = Δⱼ f`. -/
theorem sum_littlewoodPaleyBlock_littlewoodPaleyBlock
    {L : ℕ} (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : EuclideanSpace ℝ d,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (j : ℕ) (f : L²(UnitAddTorus d)) :
    ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), littlewoodPaleyBlock φ k (littlewoodPaleyBlock φ j f) =
      littlewoodPaleyBlock φ j f := by
  have hsym : (∑ k ∈ Finset.Ico (j + 1 - L) (j + L), littlewoodPaleySymbol φ k) *
      littlewoodPaleySymbol φ j = littlewoodPaleySymbol φ j := by
    ext n
    simp only [lp.infty_coeFn_mul, Pi.mul_apply, lp.coeFn_sum, Finset.sum_apply,
      littlewoodPaleySymbol_apply, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
      ← φ.enlargedLittlewoodPaley_apply,
      φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL]
  conv_rhs => rw [littlewoodPaleyBlock_eq_fourierMultiplier, ← hsym, map_mul, map_sum]
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    FunLike.coe_sum, Finset.sum_apply, littlewoodPaleyBlock_eq_fourierMultiplier]

/-! ### The `L²` square function -/

/-- **The `L²` square function on the torus.** The squared norms of the periodic Littlewood–Paley
blocks of `f` sum to `∑ₙ (∑ⱼ ψⱼ(n)²) ‖f̂(n)‖²`. -/
theorem hasSum_norm_sq_littlewoodPaleyBlock (f : L²(UnitAddTorus d)) :
    HasSum (fun j ↦ ‖littlewoodPaleyBlock φ j f‖ ^ 2)
      (∑' n, (∑' j, φ.inhomogeneousLittlewoodPaley j (latticePoint n) ^ 2) *
        ‖mFourierCoeff f n‖ ^ 2) := by
  obtain ⟨L, hL⟩ := φ.exists_sum_sq_inhomogeneousLittlewoodPaley_le
  set b : ℕ → (d → ℤ) → ℝ := fun j n ↦
    φ.inhomogeneousLittlewoodPaley j (latticePoint n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2
  have hb0 : 0 ≤ Function.uncurry b := fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hparseval := hasSum_norm_sq_mFourierCoeff f
  -- Parseval's identity for each block.
  have hrow : ∀ j, HasSum (b j) (‖littlewoodPaleyBlock φ j f‖ ^ 2) := fun j ↦ by
    simpa [b, mul_pow] using hasSum_norm_sq_mFourierCoeff (littlewoodPaleyBlock φ j f)
  -- The partial sums over the blocks are bounded by `L ‖f‖²`.
  have hcol : Summable fun j ↦ ‖littlewoodPaleyBlock φ j f‖ ^ 2 := by
    refine summable_of_sum_le (c := L * ‖f‖ ^ 2) (fun _ ↦ sq_nonneg _) fun s ↦ ?_
    rw [← hparseval.tsum_eq, ← tsum_mul_left]
    calc ∑ j ∈ s, ‖littlewoodPaleyBlock φ j f‖ ^ 2 = ∑ j ∈ s, ∑' n, b j n :=
          Finset.sum_congr rfl fun j _ ↦ (hrow j).tsum_eq.symm
      _ = ∑' n, ∑ j ∈ s, b j n := (Summable.tsum_finsetSum fun j _ ↦ (hrow j).summable).symm
      _ ≤ ∑' n, (L : ℝ) * ‖mFourierCoeff f n‖ ^ 2 := by
          refine Summable.tsum_le_tsum (fun n ↦ ?_)
            (summable_sum fun j _ ↦ (hrow j).summable) (hparseval.summable.mul_left _)
          simp only [b, ← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hL s _) (sq_nonneg _)
  have hprod : Summable (Function.uncurry b) :=
    (summable_prod_of_nonneg hb0).2 ⟨fun j ↦ (hrow j).summable,
      hcol.congr fun j ↦ (hrow j).tsum_eq.symm⟩
  have hswap := Summable.tsum_comm' hprod (fun j ↦ (hrow j).summable) fun n ↦
    hprod.prod_symm.prod_factor n
  convert hcol.hasSum using 1
  simp_rw [← tsum_mul_right]
  exact hswap.trans (tsum_congr fun j ↦ (hrow j).tsum_eq)

/-- The frequency series `∑ₙ (∑ⱼ ψⱼ(n)²) ‖f̂(n)‖²` of the `L²` square function converges: its
weight is bounded uniformly in `n`. -/
theorem summable_tsum_inhomogeneousLittlewoodPaley_sq_mul_norm_sq_mFourierCoeff
    (f : L²(UnitAddTorus d)) :
    Summable fun n ↦ (∑' j, φ.inhomogeneousLittlewoodPaley j (latticePoint n) ^ 2) *
      ‖mFourierCoeff f n‖ ^ 2 := by
  obtain ⟨L, hL⟩ := φ.exists_tsum_inhomogeneousLittlewoodPaley_sq_le
  exact ((hasSum_norm_sq_mFourierCoeff f).summable.mul_left (L : ℝ)).of_nonneg_of_le
    (fun n ↦ mul_nonneg (tsum_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _))
    fun n ↦ mul_le_mul_of_nonneg_right (hL _) (sq_nonneg _)

/-- **The `L²` square function is bounded.** There is `C`, depending only on `φ`, with
`∑ⱼ ‖Δⱼ f‖² ≤ C ‖f‖²` for every `f ∈ L²(𝕋ᵈ)`. -/
theorem exists_tsum_norm_sq_littlewoodPaleyBlock_le :
    ∃ C : ℝ, ∀ f : L²(UnitAddTorus d),
      ∑' j, ‖littlewoodPaleyBlock φ j f‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  obtain ⟨L, hL⟩ := φ.exists_tsum_inhomogeneousLittlewoodPaley_sq_le
  refine ⟨L, fun f ↦ ?_⟩
  have hparseval := hasSum_norm_sq_mFourierCoeff f
  rw [(hasSum_norm_sq_littlewoodPaleyBlock φ f).tsum_eq, ← hparseval.tsum_eq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n ↦ mul_le_mul_of_nonneg_right (hL _) (sq_nonneg _))
    (summable_tsum_inhomogeneousLittlewoodPaley_sq_mul_norm_sq_mFourierCoeff φ f)
    (hparseval.summable.mul_left _)

/-- **The `L²` square function is bounded below.** There is `C`, depending only on `φ`, with
`‖f‖² ≤ C ∑ⱼ ‖Δⱼ f‖²` for every `f ∈ L²(𝕋ᵈ)`. -/
theorem exists_norm_sq_le_mul_tsum_norm_sq_littlewoodPaleyBlock :
    ∃ C : ℝ, ∀ f : L²(UnitAddTorus d),
      ‖f‖ ^ 2 ≤ C * ∑' j, ‖littlewoodPaleyBlock φ j f‖ ^ 2 := by
  obtain ⟨L, -, hL⟩ := φ.exists_one_le_mul_sum_sq_inhomogeneousLittlewoodPaley
  refine ⟨L, fun f ↦ ?_⟩
  have hparseval := hasSum_norm_sq_mFourierCoeff f
  rw [(hasSum_norm_sq_littlewoodPaleyBlock φ f).tsum_eq, ← hparseval.tsum_eq, ← tsum_mul_left]
  -- At each frequency `n`, the weight `∑ⱼ ψⱼ(n)²` is at least `1 / L`.
  have hw : ∀ n, 1 ≤ L * ∑' j, φ.inhomogeneousLittlewoodPaley j (latticePoint n) ^ 2 := fun n ↦ by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖latticePoint n‖ / φ.rIn) (one_lt_two (α := ℝ))
    refine (hL N _ ((div_lt_iff₀ φ.rIn_pos).1 hN).le).trans ?_
    exact mul_le_mul_of_nonneg_left
      ((φ.summable_inhomogeneousLittlewoodPaley_sq _).sum_le_tsum _ fun _ _ ↦ sq_nonneg _)
      (Nat.cast_nonneg L)
  refine Summable.tsum_le_tsum (fun n ↦ ?_) hparseval.summable ?_
  · calc ‖mFourierCoeff f n‖ ^ 2 ≤ (L * ∑' j, φ.inhomogeneousLittlewoodPaley j
          (latticePoint n) ^ 2) * ‖mFourierCoeff f n‖ ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) (hw n)
      _ = L * ((∑' j, φ.inhomogeneousLittlewoodPaley j (latticePoint n) ^ 2) *
          ‖mFourierCoeff f n‖ ^ 2) := mul_assoc _ _ _
  · exact (summable_tsum_inhomogeneousLittlewoodPaley_sq_mul_norm_sq_mFourierCoeff φ f).mul_left _

/-! ### `Lᵖ` bounds -/

/-- **The `Lᵖ` bound for a periodic Littlewood–Paley block.** For `1 ≤ p ≤ ∞` and `f ∈ L²(𝕋ᵈ)`,
`‖Δⱼ f‖_p ≤ ‖𝓕⁻ ψⱼ‖_{L¹(ℝᵈ)} ‖f‖_p`, the bound of the corresponding block on `Lᵖ(ℝᵈ)`. -/
theorem eLpNorm_littlewoodPaleyBlock_le (j : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : L²(UnitAddTorus d)) :
    eLpNorm (littlewoodPaleyBlock φ j f) p volume ≤
      ENNReal.ofReal (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖) *
        eLpNorm f p volume := by
  have h := eLpNorm_fourierMultiplier_le (φ.inhomogeneousLittlewoodPaleySchwartz j)
    (m := littlewoodPaleySymbol φ j) (fun n ↦ by simp) hp f
  rwa [φ.coe_inhomogeneousLittlewoodPaleySchwartz] at h

/-- **The periodic Littlewood–Paley blocks are bounded on `Lᵖ` uniformly in `j`.** There is `C`,
depending only on `φ`, with `‖Δⱼ f‖_p ≤ C ‖f‖_p` for every `j`, every `1 ≤ p ≤ ∞` and every
`f ∈ L²(𝕋ᵈ)`. The kernels `𝓕⁻ ψⱼ`, `j ≥ 1`, are `L¹`-normalised dilates of `𝓕⁻ ψ₁`. -/
theorem exists_eLpNorm_littlewoodPaleyBlock_le :
    ∃ C : ℝ≥0, ∀ (j : ℕ) {p : ℝ≥0∞}, 1 ≤ p → ∀ f : L²(UnitAddTorus d),
      eLpNorm (littlewoodPaleyBlock φ j f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ := φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 0
  refine ⟨C, fun j p hp f ↦ (eLpNorm_littlewoodPaleyBlock_le φ j hp f).trans ?_⟩
  gcongr
  exact (ENNReal.ofReal_le_ofReal (by simpa using hC j)).trans_eq ENNReal.ofReal_coe_nnreal

/-- **The periodic low-pass truncations are bounded on `Lᵖ` uniformly in `N`.** For
`1 ≤ p ≤ ∞` and `f ∈ L²(𝕋ᵈ)`, the truncation `S_N f = ∑_{j ≤ N} Δⱼ f` satisfies
`‖S_N f‖_p ≤ ‖𝓕⁻ φ‖_{L¹(ℝᵈ)} ‖f‖_p`. The truncation is the multiplier with symbol `φ (2^{-N} ·)`,
whose kernel is an `L¹`-normalised dilate of `𝓕⁻ φ`. -/
theorem eLpNorm_sum_littlewoodPaleyBlock_range_le (N : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : L²(UnitAddTorus d)) :
    eLpNorm ((∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock φ j) f) p volume ≤
      ENNReal.ofReal (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * eLpNorm f p volume := by
  have hc : ((2 : ℝ) ^ N)⁻¹ ≠ 0 := by positivity
  -- The symbol `φ (2^{-N} ·) = ∑_{j ≤ N} ψⱼ` is a sum of the Schwartz pieces of the partition.
  set σ : 𝓢(EuclideanSpace ℝ d, ℂ) :=
    ∑ j ∈ Finset.range (N + 1), φ.inhomogeneousLittlewoodPaleySchwartz j
  have hσ : (σ : EuclideanSpace ℝ d → ℂ) = fun ξ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ) := by
    ext ξ
    simp [σ, ← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range]
  have h := eLpNorm_fourierMultiplier_le σ
    (m := ∑ j ∈ Finset.range (N + 1), littlewoodPaleySymbol φ j) (fun n ↦ by
      rw [hσ, lp.coeFn_sum, Finset.sum_apply]
      simp [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range]) hp f
  rw [hσ, TauCeti.integral_norm_fourierInv_comp_smul (fun ξ ↦ (φ ξ : ℂ)) hc] at h
  simpa only [littlewoodPaleyBlock_eq_fourierMultiplier, map_sum] using h

end TauCeti.UnitAddTorus
