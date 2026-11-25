/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus.Basic
import TauCeti.Analysis.Fourier.Torus.Multiplier
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# The periodic Besov space `B^s_{2,2}(𝕋ᵈ)` is the Sobolev space `H^s(𝕋ᵈ)`

The periodic Sobolev space `H^s(𝕋ᵈ)` consists of the formal Fourier series `c : ℤᵈ → ℂ` with

`∑ₙ (1 + ‖n‖²)^s ‖c(n)‖² < ∞`,

normed by the square root of this sum; multiplying the coefficients by `(1 + ‖n‖²)^{s/2}` is an
isometry from `H^s(𝕋ᵈ)` onto `ℓ²(ℤᵈ)`. This file proves that the periodic Besov space
`B^s_{2,2}(𝕋ᵈ)` (`TauCeti.UnitAddTorus.BesovSpace φ s 2 2`) is this space, with equivalent
norms, for every `s : ℝ` and every bump function `φ`.

By Parseval's identity the `L²` norm of a block is `‖Δⱼ c‖₂² = ∑ₙ ψⱼ(n)² ‖c(n)‖²`, so exchanging
the sums over blocks and frequencies gives the exact identity

`‖c‖²_{B^s_{2,2}} = ∑ⱼ 2^{2js} ‖Δⱼ c‖₂² = ∑ₙ (∑ⱼ (2^{js} ψⱼ(n))²) ‖c(n)‖²`.

On the support of `ψⱼ` the dyadic weight `2^{2js}` is comparable to `(1 + ‖n‖²)^s`, and at most
boundedly many `ψⱼ(n)` are nonzero, with `∑ⱼ ψⱼ(n)² ≍ 1`; so the weight `∑ⱼ (2^{js} ψⱼ(n))²` is
comparable to `(1 + ‖n‖²)^s`, by
`ContDiffBump.exists_tsum_two_rpow_mul_inhomogeneousLittlewoodPaley_sq_le` and
`ContDiffBump.exists_one_add_norm_sq_rpow_le_mul_tsum_two_rpow_mul_inhomogeneousLittlewoodPaley_sq`.

## Main declarations

* `TauCeti.UnitAddTorus.hasSum_norm_sq_littlewoodPaleyBlockLp`: Parseval's identity for a block,
  `‖Δⱼ c‖₂² = ∑ₙ ψⱼ(n)² ‖c(n)‖²`.
* `TauCeti.UnitAddTorus.hasSum_rpow_mul_norm_littlewoodPaleyBlockLp_sq_iff`: the identity
  `∑ⱼ 2^{2js} ‖Δⱼ c‖₂² = ∑ₙ (∑ⱼ (2^{js} ψⱼ(n))²) ‖c(n)‖²`, including convergence of either side.
* `TauCeti.UnitAddTorus.memBesov_two_two_iff`: `c ∈ B^s_{2,2}(𝕋ᵈ)` if and only if
  `∑ₙ (1 + ‖n‖²)^s ‖c(n)‖² < ∞`, that is, `B^s_{2,2}(𝕋ᵈ) = H^s(𝕋ᵈ)` as sets of formal Fourier
  series.
* `TauCeti.UnitAddTorus.BesovSpace.hasSum_norm_sq`: the norm of `B^s_{2,2}(𝕋ᵈ)` in terms of the
  Fourier coefficients.
* `TauCeti.UnitAddTorus.BesovSpace.sobolevEquiv`: the isomorphism of normed spaces
  `B^s_{2,2}(𝕋ᵈ) ≃ ℓ²(ℤᵈ)`, `c ↦ ((1 + ‖n‖²)^{s/2} c(n))ₙ`, which identifies the norm of
  `B^s_{2,2}(𝕋ᵈ)` with the `H^s(𝕋ᵈ)` norm up to constants
  (`TauCeti.UnitAddTorus.BesovSpace.hasSum_norm_sobolevEquiv_sq`).

As in `TauCeti.UnitAddTorus.littlewoodPaleyBlockLp`, `L²(𝕋ᵈ)` is taken for the product of the
Haar probability measures on the circle factors.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Section 3.5.4 (the periodic spaces `B^s_{2,2}` and `H^s` coincide).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Proposition 2.10
  and Section 2.7 (the same identification on `ℝᵈ`, whose proof is followed here).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Littlewood–Paley blocks and Mathlib's Parseval identity on the torus live on `L²`
-- for the product of the Haar probability measures on the circle factors, given by this instance.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable {φ : ContDiffBump (0 : EuclideanSpace ℝ d)} {s : ℝ}

/-- **Parseval's identity for a block.** The squared `L²` norm of the block `Δⱼ c` is
`∑ₙ ψⱼ(n)² ‖c(n)‖²`. -/
theorem hasSum_norm_sq_littlewoodPaleyBlockLp (j : ℕ) (c : (d → ℤ) → ℂ) :
    HasSum (fun n ↦ φ.inhomogeneousLittlewoodPaley j (latticePoint n) ^ 2 * ‖c n‖ ^ 2)
      (‖littlewoodPaleyBlockLp φ 2 j c‖ ^ 2) := by
  simpa [mul_pow] using hasSum_norm_sq_mFourierCoeff (littlewoodPaleyBlockLp φ 2 j c)

/-- **The `B^s_{2,2}` norm in terms of the Fourier coefficients.** The squared weighted block norms
`(2^{js} ‖Δⱼ c‖₂)²` sum to `x` exactly when the weighted coefficients
`(∑ⱼ (2^{js} ψⱼ(n))²) ‖c(n)‖²` sum to `x`: both are the sums of the same nonnegative double series
`(2^{js} ψⱼ(n))² ‖c(n)‖²`, by Parseval's identity for each block. -/
theorem hasSum_rpow_mul_norm_littlewoodPaleyBlockLp_sq_iff (c : (d → ℤ) → ℂ) (x : ℝ) :
    HasSum (fun j : ℕ ↦ (2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ 2 j c‖) ^ 2) x ↔
      HasSum (fun n ↦ (∑' j : ℕ,
        (2 ^ (s * j) * φ.inhomogeneousLittlewoodPaley j (latticePoint n)) ^ 2) * ‖c n‖ ^ 2) x := by
  refine hasSum_rows_iff_hasSum_cols_of_nonneg
    (a := fun (j : ℕ) n ↦
      (2 ^ (s * j) * φ.inhomogeneousLittlewoodPaley j (latticePoint n)) ^ 2 * ‖c n‖ ^ 2)
    (fun _ _ ↦ by positivity) (fun j ↦ ?_)
    fun n ↦ (φ.summable_two_rpow_mul_inhomogeneousLittlewoodPaley_sq s _).hasSum.mul_right _
  -- The sum of each row is a weighted block norm, by Parseval's identity.
  convert (hasSum_norm_sq_littlewoodPaleyBlockLp (φ := φ) j c).mul_left
    (((2 : ℝ) ^ (s * j)) ^ 2) using 1
  · funext n
    ring
  · ring

/-- On each frequency, the Sobolev weight `(1 + ‖n‖²)^s` and the dyadic weight
`∑ⱼ (2^{js} ψⱼ(n))²`, multiplied by `‖z‖²`, are comparable with constants independent of `n`
and `z`. -/
private theorem exists_one_add_norm_sq_rpow_mul_le_and_le :
    ∃ C, 0 ≤ C ∧ ∀ (n : d → ℤ) (z : ℂ),
      (1 + ‖latticePoint n‖ ^ 2) ^ s * ‖z‖ ^ 2 ≤ C * ((∑' j : ℕ,
        (2 ^ (s * j) * φ.inhomogeneousLittlewoodPaley j (latticePoint n)) ^ 2) * ‖z‖ ^ 2) ∧
      (∑' j : ℕ, (2 ^ (s * j) * φ.inhomogeneousLittlewoodPaley j (latticePoint n)) ^ 2) *
        ‖z‖ ^ 2 ≤ C * ((1 + ‖latticePoint n‖ ^ 2) ^ s * ‖z‖ ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := φ.exists_tsum_two_rpow_mul_inhomogeneousLittlewoodPaley_sq_le s
  obtain ⟨C₂, -, h₂⟩ :=
    φ.exists_one_add_norm_sq_rpow_le_mul_tsum_two_rpow_mul_inhomogeneousLittlewoodPaley_sq s
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun n z ↦ ⟨?_, ?_⟩⟩ <;> rw [← mul_assoc]
  · exact mul_le_mul_of_nonneg_right ((h₂ _).trans (mul_le_mul_of_nonneg_right
      (le_max_right _ _) (tsum_nonneg fun _ ↦ sq_nonneg _))) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right ((h₁ _).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (by positivity))) (sq_nonneg _)

/-- **`B^s_{2,2}(𝕋ᵈ) = H^s(𝕋ᵈ)`.** A formal Fourier series `c` lies in the periodic Besov space
`B^s_{2,2}(𝕋ᵈ)` if and only if `∑ₙ (1 + ‖n‖²)^s ‖c(n)‖² < ∞`, that is, if and only if it lies in
the periodic Sobolev space `H^s(𝕋ᵈ)`. -/
theorem memBesov_two_two_iff {c : (d → ℤ) → ℂ} :
    MemBesov φ s 2 2 c ↔
      Summable fun n ↦ (1 + ‖latticePoint n‖ ^ 2) ^ s * ‖c n‖ ^ 2 := by
  obtain ⟨C, -, h⟩ := exists_one_add_norm_sq_rpow_mul_le_and_le (φ := φ) (s := s)
  rw [memBesov_def, memℓp_gen_iff (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · have hw := ((hasSum_rpow_mul_norm_littlewoodPaleyBlockLp_sq_iff c _).1 h'.hasSum).summable
    exact (hw.mul_left C).of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ (h n (c n)).1
  · have hw : Summable fun n ↦ (∑' j : ℕ,
        (2 ^ (s * j) * φ.inhomogeneousLittlewoodPaley j (latticePoint n)) ^ 2) * ‖c n‖ ^ 2 :=
      (h'.mul_left C).of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ (h n (c n)).2
    exact ((hasSum_rpow_mul_norm_littlewoodPaleyBlockLp_sq_iff c _).2 hw.hasSum).summable

namespace BesovSpace

/-- **The norm of `B^s_{2,2}(𝕋ᵈ)` in terms of the Fourier coefficients.**
`‖u‖² = ∑ₙ (∑ⱼ (2^{js} ψⱼ(n))²) ‖u(n)‖²`. -/
theorem hasSum_norm_sq (u : BesovSpace φ s 2 2) :
    HasSum (fun n ↦ (∑' j : ℕ,
      (2 ^ (s * j) * φ.inhomogeneousLittlewoodPaley j (latticePoint n)) ^ 2) * ‖u.coeff n‖ ^ 2)
      (‖u‖ ^ 2) := by
  refine (hasSum_rpow_mul_norm_littlewoodPaleyBlockLp_sq_iff u.coeff _).1 ?_
  have h := lp.hasSum_norm (p := 2) (by simp) u.weightedBlocks
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_weightedBlocks_apply,
    norm_weightedBlocks] using h

/-- The weight `(1 + ‖n‖²)^{s/2}` of the frequency `n` in the Sobolev space `H^s(𝕋ᵈ)`. -/
private def sobolevWeight (s : ℝ) (n : d → ℤ) : ℝ :=
  (1 + ‖latticePoint n‖ ^ 2) ^ (s / 2)

private theorem sobolevWeight_pos (s : ℝ) (n : d → ℤ) : 0 < sobolevWeight s n := by
  unfold sobolevWeight
  positivity

private theorem sobolevWeight_sq (s : ℝ) (n : d → ℤ) :
    sobolevWeight s n ^ 2 = (1 + ‖latticePoint n‖ ^ 2) ^ s := by
  rw [sobolevWeight, ← Real.rpow_mul_natCast (by positivity)]
  norm_num

/-- `g ∈ ℓ²(ℤᵈ)` exactly when the coefficients `(1 + ‖n‖²)^{-s/2} g(n)` lie in `H^s(𝕋ᵈ)`. -/
private theorem memℓp_two_iff_memBesov_inv_sobolevWeight_mul {g : (d → ℤ) → ℂ} :
    Memℓp g 2 ↔ MemBesov φ s 2 2 fun n ↦ ((sobolevWeight s n)⁻¹ : ℂ) * g n := by
  rw [memBesov_two_two_iff, memℓp_gen_iff (by simp)]
  refine summable_congr fun n ↦ ?_
  have h := (sobolevWeight_pos s n).ne'
  simp [mul_pow, ← sobolevWeight_sq]
  field_simp

/-- `c ∈ H^s(𝕋ᵈ)` exactly when the weighted coefficients `(1 + ‖n‖²)^{s/2} c(n)` lie in
`ℓ²(ℤᵈ)`. -/
private theorem memBesov_iff_memℓp_two_sobolevWeight_mul {c : (d → ℤ) → ℂ} :
    MemBesov φ s 2 2 c ↔ Memℓp (fun n ↦ (sobolevWeight s n : ℂ) * c n) 2 := by
  rw [memℓp_two_iff_memBesov_inv_sobolevWeight_mul (φ := φ) (s := s)]
  refine iff_of_eq (congrArg _ (funext fun n ↦ ?_))
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sobolevWeight_pos s n).ne', Complex.ofReal_one, one_mul]

variable (φ s) in
/-- The weighted coefficients `c ↦ ((1 + ‖n‖²)^{s/2} c(n))ₙ`, as a linear equivalence between
`B^s_{2,2}(𝕋ᵈ)` and `ℓ²(ℤᵈ)`. -/
private def sobolevEquivₗ : BesovSpace φ s 2 2 ≃ₗ[ℂ] lp (fun _ : d → ℤ ↦ ℂ) 2 where
  toFun u := ⟨fun n ↦ (sobolevWeight s n : ℂ) * u.coeff n,
    memBesov_iff_memℓp_two_sobolevWeight_mul.1 u.memBesov_coeff⟩
  invFun g := ⟨fun n ↦ ((sobolevWeight s n)⁻¹ : ℂ) * g n,
    memℓp_two_iff_memBesov_inv_sobolevWeight_mul.1 (lp.memℓp g)⟩
  map_add' u v := lp.ext (funext fun n ↦ mul_add _ _ _)
  map_smul' a u := lp.ext (funext fun n ↦ mul_left_comm _ _ _)
  left_inv u := ext (funext fun n ↦ by
    have h : (sobolevWeight s n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sobolevWeight_pos s n).ne'
    simp [inv_mul_cancel_left₀ h])
  right_inv g := lp.ext (funext fun n ↦ by
    have h : (sobolevWeight s n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sobolevWeight_pos s n).ne'
    simp [mul_inv_cancel_left₀ h])

private theorem sobolevEquivₗ_apply (u : BesovSpace φ s 2 2) (n : d → ℤ) :
    sobolevEquivₗ φ s u n = (sobolevWeight s n : ℂ) * u.coeff n := (rfl)

private theorem sobolevEquivₗ_symm_coeff (g : lp (fun _ : d → ℤ ↦ ℂ) 2) (n : d → ℤ) :
    ((sobolevEquivₗ φ s).symm g).coeff n = ((sobolevWeight s n)⁻¹ : ℂ) * g n := (rfl)

/-- The squared `ℓ²` norm of the weighted coefficients `(1 + ‖n‖²)^{s/2} c(n)` is the squared
`H^s(𝕋ᵈ)` norm `∑ₙ (1 + ‖n‖²)^s ‖c(n)‖²`. -/
private theorem hasSum_norm_sq_of_apply_eq {g : lp (fun _ : d → ℤ ↦ ℂ) 2} {c : (d → ℤ) → ℂ}
    (hg : ∀ n, g n = (sobolevWeight s n : ℂ) * c n) :
    HasSum (fun n ↦ (1 + ‖latticePoint n‖ ^ 2) ^ s * ‖c n‖ ^ 2) (‖g‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by simp) g
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hg, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (sobolevWeight_pos s _).le, sobolevWeight_sq] at h
  exact h

/-- The two sides of `B^s_{2,2}(𝕋ᵈ) = H^s(𝕋ᵈ)`: there is `C ≥ 0` with `‖u‖_{H^s}² ≤ C ‖u‖²` and
`‖u‖² ≤ C ‖u‖_{H^s}²`, where `‖u‖_{H^s}` is the `ℓ²` norm of the weighted coefficients. -/
private theorem exists_norm_sq_le_and_le :
    ∃ C, 0 ≤ C ∧ ∀ u : BesovSpace φ s 2 2,
      ‖sobolevEquivₗ φ s u‖ ^ 2 ≤ C * ‖u‖ ^ 2 ∧ ‖u‖ ^ 2 ≤ C * ‖sobolevEquivₗ φ s u‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_one_add_norm_sq_rpow_mul_le_and_le (φ := φ) (s := s)
  refine ⟨C, hC, fun u ↦ ⟨?_, ?_⟩⟩
  all_goals
    have hH := hasSum_norm_sq_of_apply_eq (sobolevEquivₗ_apply u)
    have hB := hasSum_norm_sq u
    rw [← hH.tsum_eq, ← hB.tsum_eq, ← tsum_mul_left]
  · exact hH.summable.tsum_le_tsum (fun n ↦ (h n _).1) (hB.summable.mul_left _)
  · exact hB.summable.tsum_le_tsum (fun n ↦ (h n _).2) (hH.summable.mul_left _)

/-- The bounds of `sobolevEquivₗ φ s` in both directions: there is `C` with
`‖sobolevEquivₗ φ s u‖ ≤ C ‖u‖` and `‖u‖ ≤ C ‖sobolevEquivₗ φ s u‖`. -/
private theorem exists_norm_le_and_le :
    ∃ C, ∀ u : BesovSpace φ s 2 2,
      ‖sobolevEquivₗ φ s u‖ ≤ C * ‖u‖ ∧ ‖u‖ ≤ C * ‖sobolevEquivₗ φ s u‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_sq_le_and_le (φ := φ) (s := s)
  -- From `‖x‖² ≤ C ‖y‖²` to `‖x‖ ≤ √C ‖y‖`.
  have hsqrt : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x ^ 2 ≤ C * y ^ 2 → x ≤ √C * y := fun hx hy hxy ↦
    ((Real.le_sqrt hx (mul_nonneg hC (sq_nonneg _))).2 hxy).trans_eq
      (by rw [Real.sqrt_mul hC, Real.sqrt_sq hy])
  exact ⟨√C, fun u ↦ ⟨hsqrt (norm_nonneg _) (norm_nonneg _) (h u).1,
    hsqrt (norm_nonneg _) (norm_nonneg _) (h u).2⟩⟩

variable (φ s) in
/-- **`B^s_{2,2}(𝕋ᵈ) = H^s(𝕋ᵈ)` with equivalent norms.** Multiplying the Fourier coefficients by
`(1 + ‖n‖²)^{s/2}` is an isomorphism of normed spaces from the periodic Besov space
`B^s_{2,2}(𝕋ᵈ)` onto `ℓ²(ℤᵈ)`; the norm it transports is the `H^s(𝕋ᵈ)` norm
`(∑ₙ (1 + ‖n‖²)^s ‖c(n)‖²)^{1/2}` (`TauCeti.UnitAddTorus.BesovSpace.hasSum_norm_sobolevEquiv_sq`).
-/
def sobolevEquiv : BesovSpace φ s 2 2 ≃L[ℂ] lp (fun _ : d → ℤ ↦ ℂ) 2 :=
  (sobolevEquivₗ φ s).toContinuousLinearEquivOfBounds exists_norm_le_and_le.choose
    exists_norm_le_and_le.choose (fun u ↦ (exists_norm_le_and_le.choose_spec u).1) fun g ↦ by
      simpa using (exists_norm_le_and_le.choose_spec ((sobolevEquivₗ φ s).symm g)).2

-- `LinearEquiv.toContinuousLinearEquivOfBounds` keeps the underlying linear equivalence.
private theorem toLinearEquiv_sobolevEquiv :
    (sobolevEquiv φ s).toLinearEquiv = sobolevEquivₗ φ s := rfl

@[simp]
theorem sobolevEquiv_apply (u : BesovSpace φ s 2 2) (n : d → ℤ) :
    sobolevEquiv φ s u n = ((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) * u.coeff n := by
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv, toLinearEquiv_sobolevEquiv,
    sobolevEquivₗ_apply, sobolevWeight]

@[simp]
theorem coeff_sobolevEquiv_symm_apply (g : lp (fun _ : d → ℤ ↦ ℂ) 2) (n : d → ℤ) :
    ((sobolevEquiv φ s).symm g).coeff n =
      ((((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))⁻¹ * g n := by
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv, toLinearEquiv_sobolevEquiv,
    sobolevEquivₗ_symm_coeff, sobolevWeight]

/-- **The `H^s(𝕋ᵈ)` norm.** The squared norm of the weighted coefficients `sobolevEquiv φ s u` is
`∑ₙ (1 + ‖n‖²)^s ‖u(n)‖²`. -/
theorem hasSum_norm_sobolevEquiv_sq (u : BesovSpace φ s 2 2) :
    HasSum (fun n ↦ (1 + ‖latticePoint n‖ ^ 2) ^ s * ‖u.coeff n‖ ^ 2)
      (‖sobolevEquiv φ s u‖ ^ 2) :=
  hasSum_norm_sq_of_apply_eq (sobolevEquiv_apply u)

end BesovSpace

end TauCeti.UnitAddTorus
