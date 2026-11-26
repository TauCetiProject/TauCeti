/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Fourier.Torus.LittlewoodPaley
import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Bernstein
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Periodic Besov spaces

Let `φ` be a smooth bump function on `EuclideanSpace ℝ d` and let `ψ₀ = φ, ψ₁, ψ₂, …` be the
inhomogeneous Littlewood–Paley partition of unity built from it
(`ContDiffBump.inhomogeneousLittlewoodPaley`). On the torus `𝕋ᵈ = UnitAddTorus d` a periodic
distribution is determined by its Fourier coefficients `c : ℤᵈ → ℂ`, and its **periodic
Littlewood–Paley blocks** are the trigonometric polynomials

`Δⱼ c = ∑ₙ ψⱼ(n) c(n) eₙ`

(`TauCeti.UnitAddTorus.littlewoodPaleyBlockLp`), a finite sum for every `c`, since `ψⱼ` vanishes
outside a ball. For `s : ℝ` and `1 ≤ p, q ≤ ∞` the **periodic Besov space** `B^s_{p,q}(𝕋ᵈ)`
consists of the formal Fourier series `c` with

`‖c‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ c‖_p)ⱼ‖_{ℓ^q} < ∞`.

The ambient space is the space `ℤᵈ → ℂ` of all formal Fourier series. Not every formal series is a
periodic distribution: the periodic distributions are the series whose coefficients have polynomial
growth. Membership in `B^s_{p,q}(𝕋ᵈ)` forces this growth. By
`TauCeti.UnitAddTorus.BesovSpace.norm_coeff_le`, `|c(n)|` is at most `∑_{j ≤ N} 2^{-js}` times the
Besov norm of `c` whenever `‖n‖ ≤ 2^N φ.rIn`. For the least such `N`, `2^N` is at most a constant
times `1 + ‖n‖`, so this factor, at most `(N + 1) max 1 2^{-Ns}`, is at most a constant times a
power of `1 + ‖n‖`. So every element of a periodic Besov space is a periodic distribution: the Besov
condition itself selects them inside the ambient space of formal series.
Each block is a trigonometric polynomial, so it lies in every `Lᵖ(𝕋ᵈ)`. When `c = mFourierCoeff f`
for some `f ∈ L²(𝕋ᵈ)`, the blocks in `L²(𝕋ᵈ)` are the periodic Littlewood–Paley blocks
`TauCeti.UnitAddTorus.littlewoodPaleyBlock φ j f`
(`TauCeti.UnitAddTorus.littlewoodPaleyBlockLp_mFourierCoeff`).

This is the periodic counterpart of the Besov spaces `TauCeti.BesovSpace` of tempered distributions
on `ℝᵈ`, with the Fourier transform replaced by Fourier series. As there, the norm is encoded
through the sequence of weighted blocks `(2^{js} Δⱼ c)ⱼ`, an element of `ℓ^q(ℕ, Lᵖ)`, and the
coefficients are recovered from the blocks: `c(n) = ∑_{j ≤ N} (Δⱼ c)^(n)` as soon as
`‖n‖ ≤ 2^N φ.rIn` (`TauCeti.UnitAddTorus.sum_mFourierCoeff_littlewoodPaleyBlockLp`), since the
`ψⱼ` sum to one.

## Main declarations

* `TauCeti.UnitAddTorus.littlewoodPaleyBlockLp`: the block `Δⱼ c` as an element of `Lᵖ(𝕋ᵈ)`, with
  Fourier coefficients `ψⱼ(n) c(n)` (`TauCeti.UnitAddTorus.mFourierCoeff_littlewoodPaleyBlockLp`).
* `TauCeti.UnitAddTorus.MemBesov φ s p q c`: the predicate `c ∈ B^s_{p,q}(𝕋ᵈ)`, closed under the
  linear operations; trigonometric polynomials lie in every periodic Besov space
  (`TauCeti.UnitAddTorus.memBesov_of_finite_support`), and the scale is monotone
  (`TauCeti.UnitAddTorus.MemBesov.mono`, `TauCeti.UnitAddTorus.MemBesov.of_lt`).
* `TauCeti.UnitAddTorus.BesovSpace φ s p q`: the bundled space, a complex normed space for
  `1 ≤ q` whose norm is induced by the linear isometry
  `TauCeti.UnitAddTorus.BesovSpace.weightedBlocksₗᵢ` into `ℓ^q(ℕ, Lᵖ)`, with the formulas
  `TauCeti.UnitAddTorus.BesovSpace.norm_eq_tsum_rpow` (`q < ∞`) and
  `TauCeti.UnitAddTorus.BesovSpace.norm_eq_ciSup` (`q = ∞`).
* `TauCeti.UnitAddTorus.BesovSpace.norm_le_mul_norm_of_forall_rpow_mul_norm_le`: a bound on the
  weighted blocks of one element by a multiple of those of another bounds the norms.
* `TauCeti.UnitAddTorus.BesovSpace.coeffCLM`: each Fourier coefficient is a continuous linear
  functional on `B^s_{p,q}(𝕋ᵈ)`, bounded by `TauCeti.UnitAddTorus.BesovSpace.norm_coeff_le`.
* The instance `CompleteSpace (TauCeti.UnitAddTorus.BesovSpace φ s p q)`: `B^s_{p,q}(𝕋ᵈ)` is a
  Banach space. The weighted blocks of its elements form a closed subset of `ℓ^q(ℕ, Lᵖ)`
  (`TauCeti.UnitAddTorus.BesovSpace.isClosed_range_weightedBlocks`): a sequence `G` of `Lᵖ`
  functions is a sequence of weighted blocks exactly when `Gⱼ = 2^{js} Δⱼ c` for the coefficients
  `c` recovered from `G`, which depend continuously on `G`, since every Fourier coefficient is a
  continuous functional on `Lᵖ(𝕋ᵈ)` (`TauCeti.UnitAddTorus.mFourierCoeffCLM`).
* `TauCeti.UnitAddTorus.MemBesov.of_bump` and `TauCeti.UnitAddTorus.BesovSpace.bumpEquiv`: the
  periodic Besov space does not depend on the bump function. The blocks `Δ'ⱼ` of a second bump
  function only meet the blocks `Δₖ` of nearby index
  (`TauCeti.UnitAddTorus.exists_littlewoodPaleyBlockLp_eq_sum_Ico`), and they are bounded on `Lᵖ`
  uniformly in `j` (`TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_mul_le`, from
  `TauCeti.UnitAddTorus.exists_eLpNorm_littlewoodPaleyBlock_le`), so `2^{js} ‖Δ'ⱼ c‖_p` is at most
  a constant times a window sum of the `2^{ks} ‖Δₖ c‖_p`.
* `TauCeti.UnitAddTorus.norm_littlewoodPaleyBlockLp_le_of_mul_eq`: a block whose coefficients are
  those of a Schwartz multiplier `σ` applied to `f ∈ Lᵖ(𝕋ᵈ)` is bounded by `‖𝓕⁻ σ‖₁ ‖f‖_p`, so the
  blocks of the Fourier coefficients of `f ∈ Lᵖ(𝕋ᵈ)` are bounded by `‖f‖_p`, uniformly in `j` and
  `p` (`TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_mFourierCoeff_le`).
* `TauCeti.UnitAddTorus.BesovSpace.inclusion` and `TauCeti.UnitAddTorus.BesovSpace.inclusionOfLT`:
  the inclusions `B^s_{p,q}(𝕋ᵈ) ⊆ B^{s'}_{p,q'}(𝕋ᵈ)` for `s' ≤ s` and `q ≤ q'`, of norm at most
  one, and for `s' < s` and arbitrary `q, q'`, as continuous linear maps.
* `TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_le_of_le`: **Bernstein's inequality
  for the blocks**, `‖Δⱼ c‖_r ≤ C 2^{j d (1/p - 1/r)} ‖Δⱼ c‖_p` for `p ≤ r`, from Nikol'skii's
  inequality on the torus
  (`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm`).
* `TauCeti.UnitAddTorus.MemBesov.mono_exponent` and
  `TauCeti.UnitAddTorus.BesovSpace.inclusionOfExponentLE`: the **Bernstein embedding**
  `B^s_{p,q}(𝕋ᵈ) ⊆ B^{s - d (1/p - 1/r)}_{r,q}(𝕋ᵈ)` for `p ≤ r`, whose norm is bounded uniformly
  in `s` and `q` (`TauCeti.UnitAddTorus.BesovSpace.exists_norm_inclusionOfExponentLE_le`).

As in `TauCeti.UnitAddTorus.littlewoodPaleyBlock`, `Lᵖ(𝕋ᵈ)` is taken for the product of the Haar
probability measures on the circle factors.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (periodic distributions and the periodic Besov spaces).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7 (the
  Besov spaces on `ℝᵈ`, whose definition and basic properties are followed here).
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped lp ENNReal NNReal FourierTransform SchwartzMap

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Littlewood–Paley blocks and Mathlib's monomials `mFourierLp` live on `Lᵖ` for the
-- product of the Haar probability measures on the circle factors, given by this instance; use it
-- here so that the Besov spaces are built on that same space.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable (φ : ContDiffBump (0 : EuclideanSpace ℝ d))

/-! ### The blocks of a formal Fourier series -/

/-- The `j`-th **periodic Littlewood–Paley block** of a formal Fourier series with coefficients
`c : ℤᵈ → ℂ`: the trigonometric polynomial `Δⱼ c = ∑ₙ ψⱼ(n) c(n) eₙ`, as an element of
`Lᵖ(𝕋ᵈ)`. Here `ψⱼ` is the `j`-th piece of the inhomogeneous Littlewood–Paley partition built
from `φ`, which vanishes outside the ball of radius `2^j φ.rOut`, so the sum is finite whatever the
growth of `c`. When `c` is the coefficient sequence `mFourierCoeff f` of some `f ∈ L²(𝕋ᵈ)`, on
`L²(𝕋ᵈ)` it is the block `TauCeti.UnitAddTorus.littlewoodPaleyBlock φ j f`
(`TauCeti.UnitAddTorus.littlewoodPaleyBlockLp_mFourierCoeff`). -/
def littlewoodPaleyBlockLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) :
    ((d → ℤ) → ℂ) →ₗ[ℂ] Lp ℂ p (volume : Measure (UnitAddTorus d)) where
  toFun c := ∑ n ∈ (finite_setOf_norm_latticePoint_le (2 ^ j * φ.rOut)).toFinset,
    ((φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n) • mFourierLp p n
  map_add' c c' := by simp [mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul, mul_left_comm]

variable {φ}

/-- `ψⱼ` vanishes outside the finite set of frequencies of norm at most `2^j φ.rOut`, the
frequencies summed over in the definition of `littlewoodPaleyBlockLp`. -/
theorem inhomogeneousLittlewoodPaley_eq_zero_of_notMem (j : ℕ) {n : d → ℤ}
    (hn : n ∉ (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ j * φ.rOut)).toFinset) :
    φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0 := by
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hn
  exact φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hn.le

/-- The block `Δⱼ c` is the sum of `ψⱼ(n) c(n) eₙ` over any finite set of frequencies outside of
which `ψⱼ` vanishes. -/
theorem littlewoodPaleyBlockLp_eq_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] {j : ℕ} {s : Finset (d → ℤ)}
    (hs : ∀ n ∉ s, φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0) (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ p j c =
      ∑ n ∈ s, ((φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n) •
        mFourierLp p n := by
  classical
  set t := (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ j * φ.rOut)).toFinset
  have h₁ := Finset.sum_subset (Finset.subset_union_right (s₁ := s) (s₂ := t))
    (f := fun n ↦ ((φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n) •
      mFourierLp p n) fun n _ hn ↦ by simp [inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn]
  have h₂ := Finset.sum_subset (Finset.subset_union_left (s₁ := s) (s₂ := t))
    (f := fun n ↦ ((φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n) •
      mFourierLp p n) fun n _ hn ↦ by simp [hs n hn]
  exact h₁.trans h₂.symm

/-- The block `Δⱼ c` agrees almost everywhere with the trigonometric polynomial
`∑ₙ ψⱼ(n) c(n) eₙ`, the sum taken over any finite set of frequencies outside of which `ψⱼ`
vanishes. -/
theorem coeFn_littlewoodPaleyBlockLp {p : ℝ≥0∞} [Fact (1 ≤ p)] {j : ℕ} {s : Finset (d → ℤ)}
    (hs : ∀ n ∉ s, φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0) (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ p j c =ᵐ[volume] fun x ↦
      ∑ n ∈ s, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n * mFourier n x := by
  rw [littlewoodPaleyBlockLp_eq_sum hs]
  exact coeFn_sum_smul_mFourierLp p s _

/-- The Fourier coefficients of the block `Δⱼ c` are `ψⱼ(n) c(n)`. -/
@[simp]
theorem mFourierCoeff_littlewoodPaleyBlockLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ)
    (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    mFourierCoeff (littlewoodPaleyBlockLp φ p j c) n =
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n := by
  have hs := fun n ↦ inhomogeneousLittlewoodPaley_eq_zero_of_notMem (φ := φ) j (n := n)
  have h : mFourierCoeff (littlewoodPaleyBlockLp φ p j c) n =
      mFourierCoeff (fun x ↦ ∑ m ∈ (finite_setOf_norm_latticePoint_le (ι := d)
        (2 ^ j * φ.rOut)).toFinset,
          (φ.inhomogeneousLittlewoodPaley j (latticePoint m) : ℂ) * c m * mFourier m x) n :=
    congrFun (mFourierCoeff_congr_ae (coeFn_littlewoodPaleyBlockLp (p := p) hs c)) n
  rw [h, mFourierCoeff_sum_mul_mFourier]
  split_ifs with hn
  · rfl
  · simp [hs n hn]

/-- The block `Δⱼ c` only depends on the products `ψⱼ(n) c(n)`. -/
theorem littlewoodPaleyBlockLp_congr {p : ℝ≥0∞} [Fact (1 ≤ p)] {j : ℕ} {c c' : (d → ℤ) → ℂ}
    (h : ∀ n, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n =
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c' n) :
    littlewoodPaleyBlockLp φ p j c = littlewoodPaleyBlockLp φ p j c' := by
  have hs := fun n ↦ inhomogeneousLittlewoodPaley_eq_zero_of_notMem (φ := φ) j (n := n)
  rw [littlewoodPaleyBlockLp_eq_sum hs, littlewoodPaleyBlockLp_eq_sum hs]
  simp only [h]

/-- The blocks of `c` in `Lᵖ` and in `Lʳ` are the same function: both are the trigonometric
polynomial `∑ₙ ψⱼ(n) c(n) eₙ`. -/
theorem coeFn_littlewoodPaleyBlockLp_ae_eq (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] (j : ℕ)
    (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ p j c =ᵐ[volume] littlewoodPaleyBlockLp φ r j c := by
  have hs := fun n ↦ inhomogeneousLittlewoodPaley_eq_zero_of_notMem (φ := φ) j (n := n)
  exact (coeFn_littlewoodPaleyBlockLp hs c).trans (coeFn_littlewoodPaleyBlockLp hs c).symm

/-- On `L²(𝕋ᵈ)` the block of the Fourier coefficients of `f` is the periodic Littlewood–Paley
block `Δⱼ f`. -/
@[simp]
theorem littlewoodPaleyBlockLp_mFourierCoeff (j : ℕ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    littlewoodPaleyBlockLp φ 2 j (mFourierCoeff f) = littlewoodPaleyBlock φ j f := by
  refine mFourierBasis.repr.injective (lp.ext (funext fun n ↦ ?_))
  simp [mFourierBasis_repr]

/-- The blocks depend continuously on the coefficients, for the topology of pointwise
convergence: each block only involves finitely many of them. -/
theorem continuous_littlewoodPaleyBlockLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) :
    Continuous (littlewoodPaleyBlockLp φ p j) := by
  simp only [littlewoodPaleyBlockLp, LinearMap.coe_mk, AddHom.coe_mk]
  fun_prop

/-- For `j ≥ 1`, the block `Δⱼ c` vanishes as soon as `c` vanishes on the frequencies `n` with
`2^{j-1} φ.rIn < ‖n‖`. -/
theorem littlewoodPaleyBlockLp_succ_eq_zero {p : ℝ≥0∞} [Fact (1 ≤ p)] {j : ℕ} {c : (d → ℤ) → ℂ}
    (hc : ∀ n, 2 ^ j * φ.rIn < ‖latticePoint n‖ → c n = 0) :
    littlewoodPaleyBlockLp φ p (j + 1) c = 0 := by
  rw [← map_zero (littlewoodPaleyBlockLp φ p (j + 1))]
  refine littlewoodPaleyBlockLp_congr fun n ↦ ?_
  rcases le_or_gt ‖latticePoint n‖ (2 ^ j * φ.rIn) with hn | hn
  · simp [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le hn]
  · simp [hc n hn]

/-! ### Recovering the coefficients from the blocks -/

/-- **Reconstruction of the coefficients.** If `‖n‖ ≤ 2^N φ.rIn`, then
`c(n) = ∑_{j ≤ N} (Δⱼ c)^(n)`: the pieces `ψⱼ(n)`, `j ≤ N`, sum to `φ(2^{-N} n) = 1`. -/
theorem sum_mFourierCoeff_littlewoodPaleyBlockLp {p : ℝ≥0∞} [Fact (1 ≤ p)] {N : ℕ}
    {n : d → ℤ} (hn : ‖latticePoint n‖ ≤ 2 ^ N * φ.rIn) (c : (d → ℤ) → ℂ) :
    ∑ j ∈ Finset.range (N + 1), mFourierCoeff (littlewoodPaleyBlockLp φ p j c) n = c n := by
  simp only [mFourierCoeff_littlewoodPaleyBlockLp, ← Finset.sum_mul, ← Complex.ofReal_sum,
    φ.sum_inhomogeneousLittlewoodPaley_range]
  rw [φ.one_of_mem_closedBall (by simpa [norm_smul, inv_mul_le_iff₀] using hn),
    Complex.ofReal_one, one_mul]

omit [Fintype d] in
variable (φ) in
/-- Every radius is at most `2^N φ.rIn` for some `N`. -/
private theorem exists_le_two_pow_mul_rIn (r : ℝ) : ∃ N : ℕ, r ≤ 2 ^ N * φ.rIn := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (r / φ.rIn) (one_lt_two (α := ℝ))
  exact ⟨N, ((div_lt_iff₀ φ.rIn_pos).1 hN).le⟩

/-- A formal Fourier series is determined by its blocks in any `Lᵖ`. -/
theorem eq_of_forall_littlewoodPaleyBlockLp_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] {c c' : (d → ℤ) → ℂ}
    (h : ∀ j, littlewoodPaleyBlockLp φ p j c = littlewoodPaleyBlockLp φ p j c') : c = c' := by
  funext n
  obtain ⟨N, hN⟩ := exists_le_two_pow_mul_rIn φ ‖latticePoint n‖
  rw [← sum_mFourierCoeff_littlewoodPaleyBlockLp (p := p) hN c,
    ← sum_mFourierCoeff_littlewoodPaleyBlockLp (p := p) hN c']
  simp only [h]

/-! ### Change of bump function -/

/-- **Change of bump function.** The blocks `Δⱼ` and `Δ'ₖ` built from two bump functions `φ` and
`φ'` interact only at nearby indices: there is `L`, depending only on `φ` and `φ'`, such that
`Δ'ⱼ c = ∑_{j - L ≤ k < j + L} Δ'ⱼ (ψₖ c)` for every `j` and every `c`, where `ψₖ c` is the
sequence `n ↦ ψₖ(n) c(n)` of Fourier coefficients of `Δₖ c`. -/
theorem exists_littlewoodPaleyBlockLp_eq_sum_Ico (φ φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    ∃ L : ℕ, ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (c : (d → ℤ) → ℂ),
      littlewoodPaleyBlockLp φ' p j c = ∑ k ∈ Finset.Ico (j - L) (j + L),
        littlewoodPaleyBlockLp φ' p j
          (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * c n) := by
  obtain ⟨L₁, hL₁⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ'
  obtain ⟨L₂, hL₂⟩ := φ'.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  refine ⟨max L₁ L₂, fun p _ j c ↦ ?_⟩
  rw [← map_sum]
  refine littlewoodPaleyBlockLp_congr fun n ↦ ?_
  set ξ := latticePoint n
  -- `ψ'ⱼ = ∑ₖ ψ'ⱼ ψₖ`, and only the indices `k` near `j` contribute.
  have hsum : HasSum (fun k ↦ φ'.inhomogeneousLittlewoodPaley j ξ *
      φ.inhomogeneousLittlewoodPaley k ξ) (φ'.inhomogeneousLittlewoodPaley j ξ) := by
    simpa using (φ.hasSum_inhomogeneousLittlewoodPaley ξ).mul_left
      (φ'.inhomogeneousLittlewoodPaley j ξ)
  have hfin : HasSum (fun k ↦ φ'.inhomogeneousLittlewoodPaley j ξ *
      φ.inhomogeneousLittlewoodPaley k ξ) (∑ k ∈ Finset.Ico (j - max L₁ L₂) (j + max L₁ L₂),
        φ'.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ) := by
    refine hasSum_sum_of_ne_finset_zero fun k hk ↦ ?_
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
    rcases hk with hk | hk
    · rw [mul_comm]
      exact hL₁ k j (by omega) ξ
    · exact hL₂ j k (by omega) ξ
  have key : (φ'.inhomogeneousLittlewoodPaley j ξ : ℂ) =
      ∑ k ∈ Finset.Ico (j - max L₁ L₂) (j + max L₁ L₂),
        (φ'.inhomogeneousLittlewoodPaley j ξ : ℂ) * φ.inhomogeneousLittlewoodPaley k ξ := by
    exact_mod_cast hsum.unique hfin
  rw [Finset.sum_apply, Finset.mul_sum]
  nth_rw 1 [key]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **Uniform `Lᵖ` bounds across bump functions.** There is `C`, depending only on `φ'`, such
that `‖Δ'ⱼ (ψₖ c)‖_p ≤ C ‖Δₖ c‖_p` for every bump function `φ`, every `j`, `k`, `1 ≤ p ≤ ∞` and
`c`, where the blocks `Δₖ` are built from `φ` and `Δ'ⱼ` from `φ'`. -/
theorem exists_norm_littlewoodPaleyBlockLp_mul_le (φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (j k : ℕ) (c : (d → ℤ) → ℂ),
      ‖littlewoodPaleyBlockLp φ' p j
          (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * c n)‖ ≤
        C * ‖littlewoodPaleyBlockLp φ p k c‖ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_littlewoodPaleyBlock_le φ'
  refine ⟨C, C.coe_nonneg, fun φ p _ j k c ↦ ?_⟩
  -- Apply the `Lᵖ` bound of the `L²` block `Δ'ⱼ` to the trigonometric polynomial `f = Δₖ c`.
  set f := littlewoodPaleyBlockLp φ 2 k c
  have hf : littlewoodPaleyBlock φ' j f = littlewoodPaleyBlockLp φ' 2 j
      (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * c n) := by
    rw [← littlewoodPaleyBlockLp_mFourierCoeff]
    congr 1
    funext n
    exact mFourierCoeff_littlewoodPaleyBlockLp k c n
  have h := hC j (Fact.out : (1 : ℝ≥0∞) ≤ p) f
  rw [hf, eLpNorm_congr_ae (coeFn_littlewoodPaleyBlockLp_ae_eq 2 p j _),
    eLpNorm_congr_ae (coeFn_littlewoodPaleyBlockLp_ae_eq 2 p k c)] at h
  simpa [Lp.norm_def, ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top _)) h

/-! ### Schwartz multipliers on the blocks -/

/-- **Schwartz multipliers on the periodic blocks.** If the coefficients `ψⱼ(n) c(n)` of the block
`Δⱼ c` are the multiplied coefficients `σ(n) f̂(n)` of a function `f ∈ Lᵖ(𝕋ᵈ)`, `1 ≤ p ≤ ∞`, for a
Schwartz function `σ` on `ℝᵈ`, then `‖Δⱼ c‖_p ≤ ‖𝓕⁻ σ‖_{L¹(ℝᵈ)} ‖f‖_p`. -/
theorem norm_littlewoodPaleyBlockLp_le_of_mul_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : (d → ℤ) → ℂ}
    (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) (j : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d)))
    (h : ∀ n, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n =
      σ (latticePoint n) * mFourierCoeff f n) :
    ‖littlewoodPaleyBlockLp φ p j c‖ ≤
      (∫ x, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) x‖) * ‖f‖ := by
  -- `ψⱼ` vanishes outside a finite set of frequencies `S`, on which the block is a finite sum.
  set S := (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ j * φ.rOut)).toFinset
  have hS (n : d → ℤ) (hn : n ∉ S) : φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0 :=
    inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn
  have heq : (fun x ↦ ∑ n ∈ S,
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n * mFourier n x) =
      fun x ↦ ∑' n : d → ℤ, σ (latticePoint n) * mFourierCoeff f n * mFourier n x := by
    funext x
    rw [tsum_eq_sum fun n hn ↦ by rw [← h n, hS n hn, Complex.ofReal_zero, zero_mul, zero_mul]]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [h n]
  have hb := eLpNorm_tsum_mul_mFourierCoeff_mul_mFourier_le σ Fact.out (Lp.memLp f)
  rw [← heq, ← eLpNorm_congr_ae (coeFn_littlewoodPaleyBlockLp (p := p) hS c)] at hb
  rw [Lp.norm_def, Lp.norm_def]
  calc (eLpNorm (littlewoodPaleyBlockLp φ p j c) p volume).toReal
      ≤ (ENNReal.ofReal (∫ x, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) x‖) *
          eLpNorm f p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) hb
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]

variable (φ) in
/-- **The periodic blocks are bounded on `Lᵖ(𝕋ᵈ)`.** There is `C ≥ 0`, depending only on `φ`,
such that for every `1 ≤ p ≤ ∞`, every `j` and every `f ∈ Lᵖ(𝕋ᵈ)`, the block `Δⱼ f̂` of the Fourier
coefficients of `f` satisfies `‖Δⱼ f̂‖_p ≤ C ‖f‖_p`. -/
theorem exists_norm_littlewoodPaleyBlockLp_mFourierCoeff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ)
      (f : Lp ℂ p (volume : Measure (UnitAddTorus d))),
      ‖littlewoodPaleyBlockLp φ p j (mFourierCoeff f)‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 0
  refine ⟨C, C.coe_nonneg, fun p _ j f ↦ ?_⟩
  refine (norm_littlewoodPaleyBlockLp_le_of_mul_eq (φ.inhomogeneousLittlewoodPaleySchwartz j) j f
    fun n ↦ by simp).trans ?_
  gcongr
  simpa [ContDiffBump.coe_inhomogeneousLittlewoodPaleySchwartz] using hC j

/-! ### Bernstein's inequality for the blocks -/

/-- `ψⱼ` vanishes at the lattice points `n` with `2^j max 1 φ.rOut < ‖n‖`, for the supremum norm
of `n : ℤᵈ`, which is at most the Euclidean norm of `n`. -/
private theorem inhomogeneousLittlewoodPaley_latticePoint_eq_zero {j : ℕ} {n : d → ℤ}
    (hn : 2 ^ j * max 1 φ.rOut < ‖n‖) :
    φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0 := by
  refine φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm ?_
  calc 2 ^ j * φ.rOut ≤ 2 ^ j * max 1 φ.rOut := by gcongr; exact le_max_right _ _
    _ ≤ ‖latticePoint n‖ := hn.le.trans (norm_le_norm_latticePoint n)

variable (φ) in
/-- **Bernstein's inequality for the periodic blocks.** There is `C ≥ 0`, depending only on `d` and
`φ`, such that for `1 ≤ p ≤ r ≤ ∞`, every `j` and every formal Fourier series `c`,

`‖Δⱼ c‖_r ≤ C 2^{j d (1/p - 1/r)} ‖Δⱼ c‖_p`,

where `d` is the dimension of the torus and `1/∞ = 0`. The block `Δⱼ c` is a trigonometric
polynomial with frequencies of size at most `2^j φ.rOut`, so this is Nikol'skii's inequality
`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm` at that scale. -/
theorem exists_norm_littlewoodPaleyBlockLp_le_of_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)], p ≤ r →
      ∀ (j : ℕ) (c : (d → ℤ) → ℂ), ‖littlewoodPaleyBlockLp φ r j c‖ ≤
        C * 2 ^ (Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹) * j) *
          ‖littlewoodPaleyBlockLp φ p j c‖ := by
  obtain ⟨C₀, hC₀, hN⟩ := exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm (d := d)
  set M : ℝ := max 1 φ.rOut
  have hM : 1 ≤ M := le_max_left _ _
  refine ⟨C₀ * M ^ (Fintype.card d : ℝ), by positivity, fun p r _ _ hpr j c ↦ ?_⟩
  set a : ℝ := Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)
  set f := littlewoodPaleyBlockLp φ p j c
  -- Nikol'skii's inequality at the radius `R = 2^j M ≥ 1`, beyond which `f̂` vanishes. It is
  -- stated for the global volume on the torus; `volume_eq_pi_haarAddCircle` rewrites that to
  -- `Measure.pi fun _ ↦ haarAddCircle`, which is by definition the file-local `volume` given by
  -- `instMeasureSpaceUnitAddCircle`. The instance, the integrability side goal and `h` below
  -- use this definitional identification.
  have hR : 1 ≤ 2 ^ j * M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hM
  have : IsFiniteMeasure (volume : Measure (UnitAddTorus d)) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ ↦ AddCircle.haarAddCircle))
  have h := hN (p := p) (q := r) Fact.out hpr hR (f := (f : UnitAddTorus d → ℂ))
    (by rw [volume_eq_pi_haarAddCircle]; exact (Lp.memLp f).integrable Fact.out)
    fun n hn ↦ by
      rw [mFourierCoeff_littlewoodPaleyBlockLp,
        inhomogeneousLittlewoodPaley_latticePoint_eq_zero hn, Complex.ofReal_zero, zero_mul]
  rw [volume_eq_pi_haarAddCircle] at h
  -- `R^a ≤ M^d 2^{a j}`, since `M ≥ 1` and `a ≤ d`.
  have ha : a ≤ Fintype.card d :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) (ENNReal.toReal_inv_sub_toReal_inv_le_one Fact.out r)
  have hRa : (2 ^ j * M) ^ a ≤ M ^ (Fintype.card d : ℝ) * 2 ^ (a * j) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul zero_le_two,
      mul_comm (j : ℝ) a, mul_comm]
    gcongr
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_littlewoodPaleyBlockLp_ae_eq r p j c)]
  calc (eLpNorm f r volume).toReal
      ≤ (ENNReal.ofReal (C₀ * (2 ^ j * M) ^ a) * eLpNorm f p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) h
    _ = C₀ * (2 ^ j * M) ^ a * (eLpNorm f p volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ C₀ * (M ^ (Fintype.card d : ℝ) * 2 ^ (a * j)) * (eLpNorm f p volume).toReal := by
        gcongr
    _ = _ := by ring

variable (φ) in
/-- The weighted form of `exists_norm_littlewoodPaleyBlockLp_le_of_le`: the weight `2^{j s}` of
`B^s_{p,q}(𝕋ᵈ)` controls the weight `2^{j (s - d (1/p - 1/r))}` of the `r`-th block norms. -/
private theorem exists_rpow_sub_mul_norm_littlewoodPaleyBlockLp_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)], p ≤ r →
      ∀ (j : ℕ) (c : (d → ℤ) → ℂ),
        2 ^ ((s - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) * j) *
            ‖littlewoodPaleyBlockLp φ r j c‖ ≤
          C * (2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖) := by
  obtain ⟨C, hC, h⟩ := exists_norm_littlewoodPaleyBlockLp_le_of_le φ
  refine ⟨C, hC, fun s p r _ _ hpr j c ↦ ?_⟩
  set a : ℝ := Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)
  rw [← Real.rpow_sub_mul_mul_rpow_mul two_pos s a j]
  calc 2 ^ ((s - a) * j) * ‖littlewoodPaleyBlockLp φ r j c‖
      ≤ 2 ^ ((s - a) * j) * (C * 2 ^ (a * j) * ‖littlewoodPaleyBlockLp φ p j c‖) := by
        gcongr
        exact h p r hpr j c
    _ = C * (2 ^ ((s - a) * j) * 2 ^ (a * j) * ‖littlewoodPaleyBlockLp φ p j c‖) := by ring

/-! ### Membership in a periodic Besov space -/

section MemBesov

variable (φ) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A formal Fourier series with coefficients `c : ℤᵈ → ℂ` lies in the **periodic Besov space**
`B^s_{p,q}(𝕋ᵈ)` built from the Littlewood–Paley partition of `φ` if the weighted `Lᵖ` norms
`2^{js} ‖Δⱼ c‖_p` of its blocks form an `ℓ^q` sequence. -/
def MemBesov (c : (d → ℤ) → ℂ) : Prop :=
  Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖) q

variable {φ s p q}

theorem memBesov_def {c : (d → ℤ) → ℂ} :
    MemBesov φ s p q c ↔
      Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖) q :=
  Iff.rfl

theorem MemBesov.zero : MemBesov φ s p q 0 := by
  simp only [memBesov_def, map_zero, norm_zero, mul_zero]
  exact zero_mem_ℓp'

theorem MemBesov.add {c c' : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c)
    (hc' : MemBesov φ s p q c') : MemBesov φ s p q (c + c') := by
  refine (Memℓp.add hc hc').mono fun j ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply, ← mul_add, map_add]
  gcongr
  exact norm_add_le _ _

theorem MemBesov.smul {c : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c) (a : ℂ) :
    MemBesov φ s p q (a • c) := by
  refine (Memℓp.const_mul hc ‖a‖).mono fun j ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), map_smul, norm_smul]
  exact (mul_left_comm _ _ _).le

theorem MemBesov.neg {c : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c) : MemBesov φ s p q (-c) := by
  simpa using hc.smul (-1)

theorem MemBesov.sub {c c' : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c)
    (hc' : MemBesov φ s p q c') : MemBesov φ s p q (c - c') := by
  simpa [sub_eq_add_neg] using hc.add hc'.neg

/-- **Trigonometric polynomials lie in every periodic Besov space.** A formal Fourier series with
finitely many nonzero coefficients has only finitely many nonzero blocks. -/
theorem memBesov_of_finite_support {c : (d → ℤ) → ℂ} (hc : (Function.support c).Finite) :
    MemBesov φ s p q c := by
  obtain ⟨R, hR⟩ := (hc.image fun n ↦ ‖latticePoint n‖).bddAbove
  obtain ⟨N, hN'⟩ := exists_le_two_pow_mul_rIn φ R
  refine (memℓp_zero ((Finset.range (N + 1)).finite_toSet.subset fun j hj ↦ ?_)).of_exponent_ge
    bot_le
  by_contra hjN
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hjN
  obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := Nat.exists_eq_add_one.2 (by omega)
  refine hj ?_
  rw [littlewoodPaleyBlockLp_succ_eq_zero fun n hn ↦ ?_, norm_zero, mul_zero]
  by_contra hcn
  have hle : ‖latticePoint n‖ ≤ R := hR ⟨n, hcn, rfl⟩
  have hpow : (2 : ℝ) ^ N ≤ 2 ^ j := pow_le_pow_right₀ one_le_two (by omega)
  have := mul_le_mul_of_nonneg_right hpow φ.rIn_pos.le
  linarith

/-- **Monotonicity of the Besov scale.** `B^s_{p,q}(𝕋ᵈ) ⊆ B^{s'}_{p,q'}(𝕋ᵈ)` for `s' ≤ s` and
`q ≤ q'`. -/
theorem MemBesov.mono {c : (d → ℤ) → ℂ} {s' : ℝ} {q' : ℝ≥0∞} (hc : MemBesov φ s p q c)
    (hs : s' ≤ s) (hq : q ≤ q') : MemBesov φ s' p q' c :=
  Memℓp.two_rpow_mul_mono hc (fun _ ↦ norm_nonneg _) hs hq

/-- **Strict monotonicity of the Besov scale.** `B^s_{p,q}(𝕋ᵈ) ⊆ B^{s'}_{p,q'}(𝕋ᵈ)` for `s' < s`,
every `q` and every `q' ≠ 0`: the weighted blocks for `s'` decay geometrically. -/
theorem MemBesov.of_lt {c : (d → ℤ) → ℂ} {s' : ℝ} {q' : ℝ≥0∞} (hc : MemBesov φ s p q c)
    (hs : s' < s) (hq' : q' ≠ 0) : MemBesov φ s' p q' c :=
  Memℓp.two_rpow_mul_of_lt hc (fun _ ↦ norm_nonneg _) hs hq'

/-- **The weighted blocks of another bump function.** There are `K ≥ 0` and `L`, depending only
on `φ`, `φ'` and `s`, with
`2^{js} ‖Δ'ⱼ c‖_p ≤ K ∑_{j - L ≤ k < j + L} 2^{ks} ‖Δₖ c‖_p` for every `j`, `p` and `c`. -/
theorem exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_sum_Ico
    (φ φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) (s : ℝ) :
    ∃ K : ℝ, ∃ L : ℕ, 0 ≤ K ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (c : (d → ℤ) → ℂ),
      2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ' p j c‖ ≤
        K * ∑ k ∈ Finset.Ico (j - L) (j + L), 2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k c‖ := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlockLp_eq_sum_Ico φ φ'
  obtain ⟨C, hC0, hC⟩ := exists_norm_littlewoodPaleyBlockLp_mul_le φ'
  refine ⟨C * 2 ^ (|s| * L), L, by positivity, fun p _ j c ↦ ?_⟩
  rw [hL p j c]
  have h := TauCeti.two_rpow_mul_norm_sum_Ico_le s
    (g := fun k ↦ littlewoodPaleyBlockLp φ' p j
      (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * c n))
    (x := fun k ↦ littlewoodPaleyBlockLp φ p k c) (fun k ↦ hC φ p j k c) j L
  rwa [max_eq_left hC0] at h

/-- **Independence of the bump function.** A formal Fourier series in the periodic Besov space
`B^s_{p,q}(𝕋ᵈ)` built from the Littlewood–Paley partition of `φ` lies in the periodic Besov space
`B^s_{p,q}(𝕋ᵈ)` built from any other bump function `φ'`. -/
theorem MemBesov.of_bump {c : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c)
    (φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) : MemBesov φ' s p q c := by
  obtain ⟨K, L, _, hKL⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_sum_Ico φ φ' s
  refine ((Memℓp.sum_Ico_sub_add hc L).const_mul K).mono fun j ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hKL p j c

/-- **The Bernstein embedding.** For `p ≤ r`,
`B^s_{p,q}(𝕋ᵈ) ⊆ B^{s - d (1/p - 1/r)}_{r,q}(𝕋ᵈ)`, where `d` is the dimension of the torus and
`1/∞ = 0`: raising the integrability exponent of the blocks from `p` to `r` costs `d (1/p - 1/r)`
orders of smoothness. -/
theorem MemBesov.mono_exponent {c : (d → ℤ) → ℂ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hc : MemBesov φ s p q c) (hpr : p ≤ r) :
    MemBesov φ (s - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) r q c := by
  obtain ⟨C, -, h⟩ := exists_rpow_sub_mul_norm_littlewoodPaleyBlockLp_le φ
  refine (hc.const_mul C).mono fun j ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact h s p r hpr j c

end MemBesov

/-! ### The bundled periodic Besov space -/

variable (φ) in
/-- The **periodic Besov space** `B^s_{p,q}(𝕋ᵈ)` built from the Littlewood–Paley partition of the
bump function `φ`: the formal Fourier series `c : ℤᵈ → ℂ` whose blocks `Δⱼ c` have weighted `Lᵖ`
norms `2^{js} ‖Δⱼ c‖_p` forming an `ℓ^q` sequence. For `1 ≤ q` it is a Banach space with
`‖c‖ = ‖(2^{js} ‖Δⱼ c‖_p)ⱼ‖_{ℓ^q}`. -/
structure BesovSpace (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] where
  /-- The Fourier coefficients of an element of the periodic Besov space. -/
  coeff : (d → ℤ) → ℂ
  /-- The coefficients lie in the periodic Besov space. -/
  memBesov_coeff : MemBesov φ s p q coeff

namespace BesovSpace

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An element of a periodic Besov space is determined by its Fourier coefficients. -/
@[ext]
theorem ext {u v : BesovSpace φ s p q} (h : u.coeff = v.coeff) : u = v := by
  cases u
  cases v
  congr

theorem coeff_injective : Function.Injective (coeff : BesovSpace φ s p q → _) :=
  fun _ _ ↦ ext

instance : Zero (BesovSpace φ s p q) where
  zero := ⟨0, .zero⟩

instance : Add (BesovSpace φ s p q) where
  add u v := ⟨u.coeff + v.coeff, u.memBesov_coeff.add v.memBesov_coeff⟩

instance : Neg (BesovSpace φ s p q) where
  neg u := ⟨-u.coeff, u.memBesov_coeff.neg⟩

instance : Sub (BesovSpace φ s p q) where
  sub u v := ⟨u.coeff - v.coeff, u.memBesov_coeff.sub v.memBesov_coeff⟩

instance : SMul ℂ (BesovSpace φ s p q) where
  smul a u := ⟨a • u.coeff, u.memBesov_coeff.smul a⟩

instance : SMul ℕ (BesovSpace φ s p q) where
  smul n u := (n : ℂ) • u

instance : SMul ℤ (BesovSpace φ s p q) where
  smul n u := (n : ℂ) • u

@[simp]
theorem coeff_zero : (0 : BesovSpace φ s p q).coeff = 0 := (rfl)

@[simp]
theorem coeff_add (u v : BesovSpace φ s p q) : (u + v).coeff = u.coeff + v.coeff := (rfl)

@[simp]
theorem coeff_neg (u : BesovSpace φ s p q) : (-u).coeff = -u.coeff := (rfl)

@[simp]
theorem coeff_sub (u v : BesovSpace φ s p q) : (u - v).coeff = u.coeff - v.coeff := (rfl)

@[simp]
theorem coeff_smul (a : ℂ) (u : BesovSpace φ s p q) : (a • u).coeff = a • u.coeff := (rfl)

@[simp]
theorem coeff_nsmul (n : ℕ) (u : BesovSpace φ s p q) : (n • u).coeff = n • u.coeff :=
  Nat.cast_smul_eq_nsmul ℂ n u.coeff

@[simp]
theorem coeff_zsmul (n : ℤ) (u : BesovSpace φ s p q) : (n • u).coeff = n • u.coeff :=
  Int.cast_smul_eq_zsmul ℂ n u.coeff

instance : AddCommGroup (BesovSpace φ s p q) :=
  fast_instance% coeff_injective.addCommGroup _ coeff_zero coeff_add coeff_neg coeff_sub
    (fun u n ↦ coeff_nsmul n u) fun u n ↦ coeff_zsmul n u

instance : Module ℂ (BesovSpace φ s p q) :=
  fast_instance% coeff_injective.module ℂ
    (⟨⟨coeff, coeff_zero⟩, coeff_add⟩ : BesovSpace φ s p q →+ ((d → ℤ) → ℂ)) coeff_smul

variable (φ s p q) in
/-- The Fourier coefficients of an element of `B^s_{p,q}(𝕋ᵈ)`, as an injective linear map. -/
def coeffₗ : BesovSpace φ s p q →ₗ[ℂ] (d → ℤ) → ℂ where
  toFun := coeff
  map_add' := coeff_add
  map_smul' := coeff_smul

@[simp]
theorem coeffₗ_apply (u : BesovSpace φ s p q) : coeffₗ φ s p q u = u.coeff := (rfl)

/-- The weighted blocks `(2^{js} Δⱼ u)ⱼ` of an element `u` of `B^s_{p,q}(𝕋ᵈ)`, an `ℓ^q` sequence of
`Lᵖ` functions. -/
def weightedBlocks (u : BesovSpace φ s p q) :
    lp (fun _ : ℕ ↦ Lp ℂ p (volume : Measure (UnitAddTorus d))) q :=
  ⟨fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • littlewoodPaleyBlockLp φ p j u.coeff,
    Memℓp.mono u.memBesov_coeff fun j ↦ by
      rw [norm_smul, Complex.norm_of_nonneg (by positivity)]⟩

theorem weightedBlocks_apply (u : BesovSpace φ s p q) (j : ℕ) :
    u.weightedBlocks j = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • littlewoodPaleyBlockLp φ p j u.coeff :=
  (rfl)

theorem norm_weightedBlocks_apply (u : BesovSpace φ s p q) (j : ℕ) :
    ‖u.weightedBlocks j‖ = 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖ := by
  rw [weightedBlocks_apply, norm_smul, Complex.norm_of_nonneg (by positivity)]

@[simp]
theorem weightedBlocks_add (u v : BesovSpace φ s p q) :
    (u + v).weightedBlocks = u.weightedBlocks + v.weightedBlocks := by
  ext1
  funext j
  simp [weightedBlocks_apply, smul_add]

@[simp]
theorem weightedBlocks_smul (a : ℂ) (u : BesovSpace φ s p q) :
    (a • u).weightedBlocks = a • u.weightedBlocks := by
  ext1
  funext j
  simp only [weightedBlocks_apply, coeff_smul, map_smul, lp.coeFn_smul, Pi.smul_apply]
  exact smul_comm _ _ _

/-- An element of a periodic Besov space is determined by its weighted blocks. -/
theorem weightedBlocks_injective :
    Function.Injective (weightedBlocks : BesovSpace φ s p q → _) := by
  intro u v h
  refine ext (eq_of_forall_littlewoodPaleyBlockLp_eq (φ := φ) (p := p) fun j ↦
    smul_right_injective _ (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos two_pos (s * j)).ne') ?_)
  simp only [← weightedBlocks_apply, h]

variable (φ s p q) in
/-- The weighted blocks `u ↦ (2^{js} Δⱼ u)ⱼ`, as an injective linear map into `ℓ^q(ℕ, Lᵖ)`. -/
def weightedBlocksₗ :
    BesovSpace φ s p q →ₗ[ℂ] lp (fun _ : ℕ ↦ Lp ℂ p (volume : Measure (UnitAddTorus d))) q where
  toFun := weightedBlocks
  map_add' := weightedBlocks_add
  map_smul' := weightedBlocks_smul

@[simp]
theorem weightedBlocksₗ_apply (u : BesovSpace φ s p q) :
    weightedBlocksₗ φ s p q u = u.weightedBlocks := (rfl)

/-- The `n`-th Fourier coefficient recovered from the weighted blocks:
`c(n) = ∑_{j ≤ N} 2^{-js} (2^{js} Δⱼ c)^(n)` as soon as `‖n‖ ≤ 2^N φ.rIn`. -/
private theorem coeff_eq_sum_weightedBlocks (u : BesovSpace φ s p q) {N : ℕ} {n : d → ℤ}
    (hn : ‖latticePoint n‖ ≤ 2 ^ N * φ.rIn) :
    u.coeff n = ∑ j ∈ Finset.range (N + 1),
      ((((2 : ℝ) ^ (s * j))⁻¹ : ℝ) : ℂ) * mFourierCoeffCLM p n (u.weightedBlocks j) := by
  rw [← sum_mFourierCoeff_littlewoodPaleyBlockLp (p := p) hn u.coeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  rw [weightedBlocks_apply, map_smul, mFourierCoeffCLM_apply, smul_eq_mul, Complex.ofReal_inv,
    inv_mul_cancel_left₀ h]

section Normed

variable [Fact (1 ≤ q)]

instance : NormedAddCommGroup (BesovSpace φ s p q) :=
  fast_instance% NormedAddCommGroup.induced _ _ (weightedBlocksₗ φ s p q)
    (by exact weightedBlocks_injective)

/-- The norm of `u ∈ B^s_{p,q}(𝕋ᵈ)` is the `ℓ^q(ℕ, Lᵖ)` norm of its weighted blocks. -/
@[simp]
theorem norm_weightedBlocks (u : BesovSpace φ s p q) : ‖u.weightedBlocks‖ = ‖u‖ := (rfl)

instance : NormedSpace ℂ (BesovSpace φ s p q) where
  norm_smul_le a u := by simp [← norm_weightedBlocks, norm_smul]

variable (φ s p q) in
/-- The weighted blocks `u ↦ (2^{js} Δⱼ u)ⱼ`, as a linear isometry into `ℓ^q(ℕ, Lᵖ)`: the norm of
`B^s_{p,q}(𝕋ᵈ)` is the norm induced by the weighted blocks. -/
def weightedBlocksₗᵢ :
    BesovSpace φ s p q →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ Lp ℂ p (volume : Measure (UnitAddTorus d))) q where
  toLinearMap := weightedBlocksₗ φ s p q
  norm_map' := norm_weightedBlocks

@[simp]
theorem weightedBlocksₗᵢ_apply (u : BesovSpace φ s p q) :
    weightedBlocksₗᵢ φ s p q u = u.weightedBlocks := (rfl)

/-- **The single-block bound.** Each weighted block `2^{js} ‖Δⱼ u‖_p` is at most `‖u‖`. -/
theorem rpow_mul_norm_littlewoodPaleyBlockLp_le (u : BesovSpace φ s p q) (j : ℕ) :
    2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖ ≤ ‖u‖ := by
  rw [← norm_weightedBlocks_apply, ← norm_weightedBlocks]
  exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ j

/-- **A blockwise bound gives a norm bound.** If `B ≥ 0` and the weighted blocks of
`v ∈ B^{s'}_{p,q}(𝕋ᵈ)` are bounded by `B` times those of `u ∈ B^s_{p,q}(𝕋ᵈ)`, that is
`2^{js'} ‖Δⱼ v‖_p ≤ B 2^{js} ‖Δⱼ u‖_p` for every `j`, then `‖v‖ ≤ B ‖u‖`. -/
theorem norm_le_mul_norm_of_forall_rpow_mul_norm_le {s' B : ℝ} (hB : 0 ≤ B)
    {u : BesovSpace φ s p q} {v : BesovSpace φ s' p q}
    (h : ∀ j : ℕ, 2 ^ (s' * j) * ‖littlewoodPaleyBlockLp φ p j v.coeff‖ ≤
      B * (2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖)) :
    ‖v‖ ≤ B * ‖u‖ := by
  rw [← norm_weightedBlocks, ← norm_weightedBlocks, ← Complex.norm_of_nonneg hB, ← norm_smul]
  refine lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ ?_
  rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_of_nonneg hB,
    norm_weightedBlocks_apply, norm_weightedBlocks_apply]
  exact h j

/-- For `q < ∞` the norm of `B^s_{p,q}(𝕋ᵈ)` is `(∑ⱼ (2^{js} ‖Δⱼ u‖_p)^q)^{1/q}`. -/
theorem norm_eq_tsum_rpow (hq : q ≠ ∞) (u : BesovSpace φ s p q) :
    ‖u‖ = (∑' j : ℕ, (2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖) ^ q.toReal) ^
      (1 / q.toReal) := by
  rw [← norm_weightedBlocks,
    lp.norm_eq_tsum_rpow (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq)]
  simp_rw [norm_weightedBlocks_apply]

/-- For `q = ∞` the norm of `B^s_{p,∞}(𝕋ᵈ)` is `supⱼ 2^{js} ‖Δⱼ u‖_p`. -/
theorem norm_eq_ciSup (u : BesovSpace φ s p ∞) :
    ‖u‖ = ⨆ j : ℕ, 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖ := by
  rw [← norm_weightedBlocks, lp.norm_eq_ciSup]
  simp_rw [norm_weightedBlocks_apply]

/-- **The coefficients are tempered.** If `‖n‖ ≤ 2^N φ.rIn`, the `n`-th Fourier coefficient of
`u ∈ B^s_{p,q}(𝕋ᵈ)` is bounded by `∑_{j ≤ N} 2^{-js} ‖u‖`. -/
theorem norm_coeff_le (u : BesovSpace φ s p q) {N : ℕ} {n : d → ℤ}
    (hn : ‖latticePoint n‖ ≤ 2 ^ N * φ.rIn) :
    ‖u.coeff n‖ ≤ (∑ j ∈ Finset.range (N + 1), ((2 : ℝ) ^ (s * j))⁻¹) * ‖u‖ := by
  rw [← sum_mFourierCoeff_littlewoodPaleyBlockLp (p := p) hn u.coeff, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  refine (norm_mFourierCoeff_le_norm _ n).trans ?_
  rw [inv_mul_eq_div, le_div_iff₀' (by positivity)]
  exact rpow_mul_norm_littlewoodPaleyBlockLp_le u j

variable (φ s p q) in
/-- The `n`-th Fourier coefficient on `B^s_{p,q}(𝕋ᵈ)`, as a continuous linear functional. -/
def coeffCLM (n : d → ℤ) : BesovSpace φ s p q →L[ℂ] ℂ :=
  LinearMap.mkContinuous ((LinearMap.proj n).comp (coeffₗ φ s p q))
    (∑ j ∈ Finset.range ((exists_le_two_pow_mul_rIn φ ‖latticePoint n‖).choose + 1),
      ((2 : ℝ) ^ (s * j))⁻¹)
    fun u ↦ norm_coeff_le u (exists_le_two_pow_mul_rIn φ ‖latticePoint n‖).choose_spec

@[simp]
theorem coeffCLM_apply (n : d → ℤ) (u : BesovSpace φ s p q) :
    coeffCLM φ s p q n u = u.coeff n := (rfl)

/-- The weighted blocks of the elements of `B^s_{p,q}(𝕋ᵈ)` form a closed subset of
`ℓ^q(ℕ, Lᵖ)`: a sequence `G` of `Lᵖ` functions is a sequence of weighted blocks exactly when
`Gⱼ = 2^{js} Δⱼ c` for the coefficients `c` recovered from `G` by
`TauCeti.UnitAddTorus.sum_mFourierCoeff_littlewoodPaleyBlockLp`, a condition continuous in `G`. -/
theorem isClosed_range_weightedBlocks :
    IsClosed (Set.range (weightedBlocks : BesovSpace φ s p q → _)) := by
  choose N hN using fun n : d → ℤ ↦ exists_le_two_pow_mul_rIn φ ‖latticePoint n‖
  -- The coefficients recovered from a sequence of `Lᵖ` functions.
  set Λ : lp (fun _ : ℕ ↦ Lp ℂ p (volume : Measure (UnitAddTorus d))) q → (d → ℤ) → ℂ :=
    fun G n ↦ ∑ j ∈ Finset.range (N n + 1),
      ((((2 : ℝ) ^ (s * j))⁻¹ : ℝ) : ℂ) * mFourierCoeffCLM p n (G j)
  have hΛ : Continuous Λ := continuous_pi fun n ↦ continuous_finsetSum _ fun j _ ↦
    continuous_const.mul ((mFourierCoeffCLM p n).cont.comp (lp.evalCLM ℂ _ q j).cont)
  have hrange : Set.range (weightedBlocks : BesovSpace φ s p q → _) =
      ⋂ j : ℕ, {G | G j = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • littlewoodPaleyBlockLp φ p j (Λ G)} := by
    ext G
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, rfl⟩ j
      have hu : Λ u.weightedBlocks = u.coeff := funext fun n ↦
        (coeff_eq_sum_weightedBlocks u (hN n)).symm
      rw [hu, weightedBlocks_apply]
    · intro hG
      have hmem : MemBesov φ s p q (Λ G) := (lp.memℓp G).norm.mono fun j ↦ by
        rw [Real.norm_of_nonneg (by positivity), hG j, norm_smul,
          Complex.norm_of_nonneg (by positivity)]
      exact ⟨⟨Λ G, hmem⟩, lp.ext (funext fun j ↦ (hG j).symm)⟩
  rw [hrange]
  exact isClosed_iInter fun j ↦ isClosed_eq (lp.evalCLM ℂ _ q j).cont
    (((continuous_littlewoodPaleyBlockLp (φ := φ) p j).comp hΛ).const_smul
      ((((2 : ℝ) ^ (s * j) : ℝ) : ℂ)))

/-- **Completeness.** The periodic Besov space `B^s_{p,q}(𝕋ᵈ)` is a Banach space. -/
instance : CompleteSpace (BesovSpace φ s p q) := by
  rw [completeSpace_iff_isComplete_range (weightedBlocksₗᵢ φ s p q).isometry.isUniformInducing]
  exact isClosed_range_weightedBlocks.isComplete

/-- **Window bounds.** If each weighted block `2^{js} ‖Δ'ⱼ v‖` of `v`, taken in a periodic Besov
space built from a bump function `φ'`, is at most `K` times the sum of the weighted blocks
`2^{ks} ‖Δₖ u‖` of `u` over the window `j - L ≤ k < j + L`, then `‖v‖ ≤ K (2 L) ‖u‖`. -/
theorem norm_le_of_rpow_mul_norm_le_sum_Ico {φ' : ContDiffBump (0 : EuclideanSpace ℝ d)}
    {K : ℝ} (hK : 0 ≤ K) {L : ℕ} (u : BesovSpace φ s p q) (v : BesovSpace φ' s p q)
    (h : ∀ j : ℕ, 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ' p j v.coeff‖ ≤
      K * ∑ k ∈ Finset.Ico (j - L) (j + L), 2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k u.coeff‖) :
    ‖v‖ ≤ K * (2 * L) * ‖u‖ := by
  -- The weighted block norms of `u`, and their window sums, as elements of `ℓ^q`.
  set b := lp.normSeq u.weightedBlocks
  obtain ⟨w, hw, hwn⟩ := lp.exists_eq_sum_Ico_sub_add_and_norm_le b L
  rw [← norm_weightedBlocks]
  calc ‖v.weightedBlocks‖
      ≤ ‖K • w‖ := lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ by
        rw [norm_weightedBlocks_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hw]
        refine (h j).trans ((le_of_eq ?_).trans (Real.le_norm_self _))
        simp only [b, lp.normSeq_apply, norm_weightedBlocks_apply]
    _ = K * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hK]
    _ ≤ K * (2 * L * ‖b‖) := by gcongr
    _ = K * (2 * L) * ‖u‖ := by rw [lp.norm_normSeq, norm_weightedBlocks, mul_assoc K]

/-- The norms of `B^s_{p,q}(𝕋ᵈ)` built from two bump functions are comparable: there is `C`,
depending only on `φ`, `φ'` and `s`, with `‖u‖_{B'} ≤ C ‖u‖_B` for all `1 ≤ p, q ≤ ∞`. -/
private theorem exists_norm_of_bump_le (φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    ∃ C : ℝ, ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace φ s p q),
      ‖(⟨u.coeff, u.memBesov_coeff.of_bump φ'⟩ : BesovSpace φ' s p q)‖ ≤ C * ‖u‖ := by
  obtain ⟨K, L, hK, hKL⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_sum_Ico φ φ' s
  exact ⟨K * (2 * L), fun p q _ _ u ↦ norm_le_of_rpow_mul_norm_le_sum_Ico hK u _
    fun j ↦ hKL p j u.coeff⟩

/-- **Independence of the bump function.** The periodic Besov spaces `B^s_{p,q}(𝕋ᵈ)` built from
the Littlewood–Paley partitions of two bump functions `φ` and `φ'` consist of the same formal
Fourier series, with equivalent norms: the identity on Fourier coefficients is an isomorphism of
normed spaces between them. -/
def bumpEquiv (φ φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] : BesovSpace φ s p q ≃L[ℂ] BesovSpace φ' s p q :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun u := ⟨u.coeff, u.memBesov_coeff.of_bump φ'⟩
      invFun v := ⟨v.coeff, v.memBesov_coeff.of_bump φ⟩
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl
      left_inv _ := ext rfl
      right_inv _ := ext rfl }
    _ _ ((exists_norm_of_bump_le (φ := φ) (s := s) φ').choose_spec p q)
    ((exists_norm_of_bump_le (φ := φ') (s := s) φ).choose_spec p q)

@[simp]
theorem coeff_bumpEquiv (φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) (u : BesovSpace φ s p q) :
    (bumpEquiv φ φ' s p q u).coeff = u.coeff := (rfl)

@[simp]
theorem bumpEquiv_symm (φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    (bumpEquiv φ φ' s p q).symm = bumpEquiv φ' φ s p q := by
  ext u
  rfl

/-! ### Inclusions -/

section Inclusion

variable {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')]

/-- For `s' ≤ s` and `q ≤ q'`, the `B^{s'}_{p,q'}(𝕋ᵈ)` norm of a formal Fourier series is at most
its `B^s_{p,q}(𝕋ᵈ)` norm. -/
private theorem norm_le_of_coeff_eq_of_le (hs : s' ≤ s) (hq : q ≤ q')
    {u : BesovSpace φ s p q} {v : BesovSpace φ s' p q'} (h : u.coeff = v.coeff) :
    ‖v‖ ≤ ‖u‖ := by
  rw [← norm_weightedBlocks, ← norm_weightedBlocks]
  refine lp.norm_le_norm_of_exponent_le (zero_lt_one.trans_le Fact.out).ne' hq fun j ↦ ?_
  rw [norm_weightedBlocks_apply, norm_weightedBlocks_apply, h]
  gcongr
  exact one_le_two

/-- For `s' < s`, the `B^{s'}_{p,q'}(𝕋ᵈ)` norm of a formal Fourier series is at most
`(1 - 2^{s' - s})⁻¹` times its `B^s_{p,q}(𝕋ᵈ)` norm. -/
private theorem norm_le_of_coeff_eq_of_lt (hs : s' < s) {u : BesovSpace φ s p q}
    {v : BesovSpace φ s' p q'} (h : u.coeff = v.coeff) :
    ‖v‖ ≤ (1 - 2 ^ (s' - s))⁻¹ * ‖u‖ := by
  rw [← norm_weightedBlocks, mul_comm]
  refine lp.norm_le_of_norm_le_geometric (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.2 hs)) fun j ↦ ?_
  rw [norm_weightedBlocks_apply, ← h, ← Real.rpow_sub_pow_mul_rpow_mul_natCast two_pos s' s j,
    mul_assoc, mul_comm ‖u‖]
  exact mul_le_mul_of_nonneg_left (rpow_mul_norm_littlewoodPaleyBlockLp_le u j) (by positivity)

variable (φ p) in
/-- **Monotonicity of the periodic Besov scale.** For `s' ≤ s` and `q ≤ q'`,
`B^s_{p,q}(𝕋ᵈ) ⊆ B^{s'}_{p,q'}(𝕋ᵈ)` with `‖u‖_{B^{s'}_{p,q'}} ≤ ‖u‖_{B^s_{p,q}}`. At the level of
the predicate this is `TauCeti.UnitAddTorus.MemBesov.mono`. -/
def inclusion (hs : s' ≤ s) (hq : q ≤ q') : BesovSpace φ s p q →L[ℂ] BesovSpace φ s' p q' :=
  LinearMap.mkContinuous
    { toFun u := ⟨u.coeff, u.memBesov_coeff.mono hs hq⟩
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl }
    1 fun _ ↦ (norm_le_of_coeff_eq_of_le hs hq rfl).trans_eq (one_mul _).symm

@[simp]
theorem coeff_inclusion (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace φ s p q) :
    (inclusion φ p hs hq u).coeff = u.coeff := (rfl)

theorem norm_inclusion_le (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace φ s p q) :
    ‖inclusion φ p hs hq u‖ ≤ ‖u‖ :=
  norm_le_of_coeff_eq_of_le hs hq (coeff_inclusion hs hq u).symm

variable (φ p q q') in
/-- **Strict monotonicity of the periodic Besov scale.** For `s' < s` and arbitrary fine indices
`q, q'`, `B^s_{p,q}(𝕋ᵈ) ⊆ B^{s'}_{p,q'}(𝕋ᵈ)` with
`‖u‖_{B^{s'}_{p,q'}} ≤ (1 - 2^{s' - s})⁻¹ ‖u‖_{B^s_{p,q}}`: a loss of smoothness absorbs every
change of the fine index. At the level of the predicate this is
`TauCeti.UnitAddTorus.MemBesov.of_lt`. -/
def inclusionOfLT (hs : s' < s) : BesovSpace φ s p q →L[ℂ] BesovSpace φ s' p q' :=
  LinearMap.mkContinuous
    { toFun u := ⟨u.coeff, u.memBesov_coeff.of_lt hs (zero_lt_one.trans_le Fact.out).ne'⟩
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl }
    (1 - 2 ^ (s' - s))⁻¹ fun _ ↦ norm_le_of_coeff_eq_of_lt hs rfl

@[simp]
theorem coeff_inclusionOfLT (hs : s' < s) (u : BesovSpace φ s p q) :
    (inclusionOfLT φ p q q' hs u).coeff = u.coeff := (rfl)

theorem norm_inclusionOfLT_le (hs : s' < s) (u : BesovSpace φ s p q) :
    ‖inclusionOfLT φ p q q' hs u‖ ≤ (1 - 2 ^ (s' - s))⁻¹ * ‖u‖ :=
  norm_le_of_coeff_eq_of_lt hs (coeff_inclusionOfLT hs u).symm

end Inclusion

/-! ### The Bernstein embedding -/

section Bernstein

variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- For `p ≤ r` there is `C`, independent of `s` and `q`, such that the
`B^{s - d (1/p - 1/r)}_{r,q}(𝕋ᵈ)` norm of a formal Fourier series is at most `C` times its
`B^s_{p,q}(𝕋ᵈ)` norm. -/
private theorem exists_norm_le_of_coeff_eq_of_exponent_le (hpr : p ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] {u : BesovSpace φ s p q}
      {v : BesovSpace φ (s - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) r q},
      u.coeff = v.coeff → ‖v‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hB⟩ := exists_rpow_sub_mul_norm_littlewoodPaleyBlockLp_le φ
  refine ⟨C, hC, fun {s q} _ {u v} h ↦ ?_⟩
  rw [← norm_weightedBlocks, ← norm_weightedBlocks]
  calc ‖v.weightedBlocks‖ ≤ ‖(C : ℂ) • u.weightedBlocks‖ :=
        lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ ?_
    _ = C * ‖u.weightedBlocks‖ := by
        rw [lp.norm_const_smul (zero_lt_one.trans_le Fact.out).ne', Complex.norm_of_nonneg hC]
  rw [norm_weightedBlocks_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
    Complex.norm_of_nonneg hC, norm_weightedBlocks_apply, ← h]
  exact hB s p r hpr j u.coeff

variable (φ q) in
/-- **The Bernstein embedding.** For `p ≤ r`,
`B^s_{p,q}(𝕋ᵈ) ⊆ B^{s - d (1/p - 1/r)}_{r,q}(𝕋ᵈ)` continuously, where `d` is the dimension of the
torus and `1/∞ = 0`. The norm of the inclusion is bounded independently of `s` and `q`
(`TauCeti.UnitAddTorus.BesovSpace.exists_norm_inclusionOfExponentLE_le`). At the level of the
predicate this is `TauCeti.UnitAddTorus.MemBesov.mono_exponent`. -/
def inclusionOfExponentLE (hpr : p ≤ r) :
    BesovSpace φ s p q →L[ℂ]
      BesovSpace φ (s - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) r q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := ⟨u.coeff, u.memBesov_coeff.mono_exponent hpr⟩
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl } <| by
    obtain ⟨C, -, hC⟩ := exists_norm_le_of_coeff_eq_of_exponent_le (φ := φ) hpr
    exact ⟨C, fun _ ↦ hC rfl⟩

@[simp]
theorem coeff_inclusionOfExponentLE (hpr : p ≤ r) (u : BesovSpace φ s p q) :
    (inclusionOfExponentLE φ q hpr u).coeff = u.coeff := (rfl)

variable (φ) in
/-- **The Bernstein embedding is bounded uniformly in `s` and `q`.** For `p ≤ r` there is `C`,
depending only on `d`, `p`, `r` and `φ`, with
`‖u‖_{B^{s - d (1/p - 1/r)}_{r,q}(𝕋ᵈ)} ≤ C ‖u‖_{B^s_{p,q}(𝕋ᵈ)}` for every `s`, every `q ≥ 1` and
every `u ∈ B^s_{p,q}(𝕋ᵈ)`. -/
theorem exists_norm_inclusionOfExponentLE_le (hpr : p ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : BesovSpace φ s p q),
      ‖inclusionOfExponentLE φ q hpr u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_le_of_coeff_eq_of_exponent_le (φ := φ) hpr
  exact ⟨C, hC, fun u ↦ h (coeff_inclusionOfExponentLE hpr u).symm⟩

end Bernstein

end Normed

end BesovSpace

end TauCeti.UnitAddTorus
