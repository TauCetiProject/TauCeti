/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.GaussianEnsemble
public import TauCeti.Analysis.Matrix.Eigenvalues.Derivative
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Coordinate variation of sorted eigenvalues for Gaussian ensembles

This file combines Hadamard's first and second eigenvalue variation formulas with the explicit
entry parameterization of the Gaussian orthogonal and unitary ensembles (`gaussianEnsemble β n g`
for `β = 1` and `β = 2`) to compute the deterministic differential invariants that drive Dyson
Brownian motion via Itô's formula on the open simple-spectrum chamber:

* Linearity, coordinate basis expansion, symmetry (for `β = 1`), and continuous `ℝ`-linear bundling
  (`gaussianEnsembleSelfAdjointCLM`) of `g ↦ gaussianEnsemble β n g` into
  `selfAdjoint (Matrix (Fin n) (Fin n) ℂ)`.
* Quadratic Casimir and trace inner-product identities over the canonical coordinates
  `Eₚ := gaussianEnsemble β n (Pi.single p 1)` (`p : Fin n × Fin n`):
  `∑ p, Eₚ * M * Eₚ = (n⁻¹ * M.trace) • 1` for `β ≠ 1`, and
  `∑ p, Eₚ * M * Eₚ = n⁻¹ • (M.trace • 1 + Mᵀ)` for `β = 1`.
* Smoothness (`C^r` for all `r : ℕ∞ω`), coordinate gradient bracket
  `∑ p, ∂ₚλₖ * ∂ₚλₘ = (2 / (β * n)) * δₖₘ` (the martingale quadratic-variation coefficient), and
  coordinate half-Laplacian `(1 / 2) * ∑ p, ∂ₚ²λₖ = n⁻¹ * ∑ j ≠ k, (λₖ - λⱼ)⁻¹` (the repulsive
  Dyson drift) for `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` at simple eigenvalues.

## Main definitions

* `TauCeti.Probability.gaussianEnsembleSelfAdjointCLM`: continuous `ℝ`-linear map bundling
  `gaussianEnsemble β n` into `selfAdjoint (Matrix (Fin n) (Fin n) ℂ)`.

## Main results

* `TauCeti.Probability.sum_gaussianEnsemble_single_mul_self_of_ne_one` and
  `TauCeti.Probability.sum_gaussianEnsemble_single_mul_self_of_eq_one`: quadratic Casimir sums over
  the coordinate basis matrices `gaussianEnsemble β n (Pi.single p 1)`.
* `TauCeti.Probability.sum_re_trace_mul_gaussianEnsemble_single_of_ne_one` and
  `TauCeti.Probability.sum_re_trace_mul_gaussianEnsemble_single_of_eq_one`: real-trace inner
  product sums over the coordinate basis matrices.
* `TauCeti.Probability.contDiffAt_eigenvalues₀_add_gaussianEnsemble`: `C^r` smoothness of a simple
  sorted eigenvalue with respect to the Gaussian array `g`.
* `TauCeti.Probability.sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul`: coordinate gradient
  bracket `∑ p, ∂ₚλₖ * ∂ₚλₘ = if k = m then 2 / (β * n) else 0` for `β = 1` (with symmetric `A`)
  and `β = 2`.
* `TauCeti.Probability.half_sum_iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble`: coordinate
  half-Laplacian `(1 / 2) * ∑ p, ∂ₚ²λₖ = n⁻¹ * ∑ j ≠ k, (λₖ - λⱼ)⁻¹` for both `β ≠ 1` and `β = 1`
  (with symmetric `A`).

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1, Theorem 4.3.2 and Lemma 4.3.4.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §1.3.4 and §3.1.
-/

public section

noncomputable section

open Matrix Topology
open scoped ContDiff Matrix.Norms.L2Operator

namespace TauCeti

namespace Probability

/-- Local `ℝ`-normed algebra structure on `Matrix (Fin n) (Fin n) ℂ` from the `L²` operator norm. -/
local instance matrixFinNormedAlgebraReal {n : ℕ} : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.l2OpNormedAlgebraReal

/-! ### Linearity, symmetry, and continuous linear bundling of `gaussianEnsemble` -/

/-- The Gaussian ensemble of the zero array is the zero matrix. -/
@[simp]
theorem gaussianEnsemble_zero (β n : ℕ) : gaussianEnsemble β n 0 = 0 := by
  ext i j
  rw [gaussianEnsemble_apply]
  split_ifs <;> simp

/-- `gaussianEnsemble β n` is additive in the real array `g`. -/
theorem gaussianEnsemble_add (β n : ℕ) (g₁ g₂ : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (g₁ + g₂) = gaussianEnsemble β n g₁ + gaussianEnsemble β n g₂ := by
  ext i j
  simp only [gaussianEnsemble_apply, Matrix.add_apply, Pi.add_apply, Complex.ofReal_add]
  split_ifs <;> push_cast <;> ring

/-- `gaussianEnsemble β n` commutes with real scalar multiplication. -/
theorem gaussianEnsemble_smul (β n : ℕ) (c : ℝ) (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (c • g) = c • gaussianEnsemble β n g := by
  ext i j
  simp only [gaussianEnsemble_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  split_ifs <;> push_cast <;> ring

private theorem gaussianEnsemble_sum {ι : Type*} (β n : ℕ) (s : Finset ι)
    (f : ι → Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (∑ x ∈ s, f x) = ∑ x ∈ s, gaussianEnsemble β n (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, gaussianEnsemble_add, ih, Finset.sum_insert ha]

/-- Coordinate basis expansion of `gaussianEnsemble β n g` along `Pi.single p 1`. -/
theorem gaussianEnsemble_eq_sum_single (β n : ℕ) (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n g =
      ∑ p : Fin n × Fin n, g p • gaussianEnsemble β n (Pi.single p 1) := by
  conv_lhs => rw [pi_eq_sum_univ' g]
  rw [gaussianEnsemble_sum]
  exact Finset.sum_congr rfl fun p _ ↦ gaussianEnsemble_smul β n (g p) (Pi.single p 1)

/-- For `β = 1` (the GOE parameterization), `gaussianEnsemble β n g` is a symmetric matrix. -/
theorem isSymm_gaussianEnsemble_of_eq_one {β n : ℕ} (hβ : β = 1) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsemble β n g).IsSymm := by
  ext i j
  rw [transpose_apply, gaussianEnsemble_apply, gaussianEnsemble_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hβ, hij, hij.ne, hij.not_gt, hij.ne']
  · simp [hβ]
  · simp [hβ, hji, hji.ne, hji.not_gt, hji.ne']

/-- `gaussianEnsemble 1 n g` is symmetric for every array `g`. -/
theorem isSymm_gaussianEnsemble_one (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsemble 1 n g).IsSymm :=
  isSymm_gaussianEnsemble_of_eq_one rfl g

/-- Continuous `ℝ`-linear map bundling `gaussianEnsemble β n` into the real Banach space
`selfAdjoint (Matrix (Fin n) (Fin n) ℂ)`. -/
def gaussianEnsembleSelfAdjointCLM (β n : ℕ) :
    (Fin n × Fin n → ℝ) →L[ℝ] selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
  ∑ p : Fin n × Fin n,
    (ContinuousLinearMap.proj (R := ℝ) p).smulRight
      ⟨gaussianEnsemble β n (Pi.single p 1),
        (isHermitian_gaussianEnsemble β n (Pi.single p 1)).isSelfAdjoint⟩

/-- Coercing `gaussianEnsembleSelfAdjointCLM β n g` to a matrix recovers
`gaussianEnsemble β n g`. -/
@[simp]
theorem gaussianEnsembleSelfAdjointCLM_apply_coe (β n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsembleSelfAdjointCLM β n g : Matrix (Fin n) (Fin n) ℂ) =
      gaussianEnsemble β n g := by
  rw [gaussianEnsembleSelfAdjointCLM, sum_apply,
    ← selfAdjoint.subtypeL_apply (R := ℝ), map_sum, gaussianEnsemble_eq_sum_single]
  rfl

/-! ### Explicit basis matrices and index-pair summation helpers -/

private def upperPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p ↦ p.1 < p.2

private def lowerPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p ↦ p.2 < p.1

private def diagPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p ↦ p.1 = p.2

private theorem sum_diagPairs {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n × Fin n → M) :
    ∑ p ∈ diagPairs n, f p = ∑ a : Fin n, f (a, a) := by
  symm
  refine Finset.sum_bij (fun (a : Fin n) _ ↦ (a, a)) ?_ ?_ ?_ ?_
  · intro a _
    simp [diagPairs]
  · intro a₁ _ a₂ _ h
    exact (Prod.mk.inj h).1
  · rintro ⟨a, b⟩ hp
    simp only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact ⟨a, Finset.mem_univ a, Prod.ext rfl hp⟩
  · intro _ _
    rfl

private theorem sum_lowerPairs {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n × Fin n → M) :
    ∑ p ∈ lowerPairs n, f p = ∑ p ∈ upperPairs n, f (p.2, p.1) := by
  refine Finset.sum_bij (fun (p : Fin n × Fin n) _ ↦ (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [lowerPairs, upperPairs] using hp
  · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    cases h
    rfl
  · rintro ⟨a, b⟩ hp
    exact ⟨(b, a), by simpa [lowerPairs, upperPairs] using hp, rfl⟩
  · intro _ _
    rfl

private theorem sum_prod_eq_diag_add_upper {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : Fin n × Fin n → M) :
    ∑ p : Fin n × Fin n, f p =
      (∑ a : Fin n, f (a, a)) + ∑ p ∈ upperPairs n, (f p + f (p.2, p.1)) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n ↦ p.1 = p.2)]
  have hd : Finset.univ.filter (fun p : Fin n × Fin n ↦ p.1 = p.2) = diagPairs n := rfl
  rw [hd, sum_diagPairs,
    ← Finset.sum_filter_add_sum_filter_not _ (fun p : Fin n × Fin n ↦ p.1 < p.2)]
  have hu : (Finset.univ.filter fun p : Fin n × Fin n ↦ ¬p.1 = p.2).filter
      (fun p ↦ p.1 < p.2) = upperPairs n := by
    ext ⟨a, b⟩
    simp only [upperPairs, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    exact ne_of_lt
  have hl : (Finset.univ.filter fun p : Fin n × Fin n ↦ ¬p.1 = p.2).filter
      (fun p ↦ ¬p.1 < p.2) = lowerPairs n := by
    ext ⟨a, b⟩
    simp only [lowerPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hne, hlt⟩ ↦ (lt_or_gt_of_ne hne).resolve_left hlt,
      fun hba ↦ ⟨hba.ne', hba.not_gt⟩⟩
  rw [hu, hl, sum_lowerPairs, Finset.sum_add_distrib]

private theorem sum_upperPairs_of_symm {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (g : Fin n → Fin n → M) (hg : ∀ a b, g a b = g b a) :
    ∑ p ∈ upperPairs n, g p.1 p.2 =
      (2 : ℂ)⁻¹ • ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, g a b := by
  let f : Fin n × Fin n → M := fun p ↦ if p.1 = p.2 then 0 else g p.1 p.2
  have hprod : ∑ p : Fin n × Fin n, f p = ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, g a b := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    simp only [f, ↓reduceIte, zero_add]
    exact Finset.sum_congr rfl fun b hb ↦ by simp [(Finset.mem_erase.mp hb).1.symm]
  have hsplit := sum_prod_eq_diag_add_upper f
  have hdiag : ∑ a : Fin n, f (a, a) = 0 := by simp [f]
  have hup : ∑ p ∈ upperPairs n, (f p + f (p.2, p.1)) =
      (2 : ℂ) • ∑ p ∈ upperPairs n, g p.1 p.2 := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ⟨a, b⟩ hp ↦ ?_
    have hab : a < b := (Finset.mem_filter.mp hp).2
    simp only [f, hab.ne, hab.ne', ↓reduceIte, hg b a, two_smul ℂ]
  rw [hprod, hdiag, zero_add, hup] at hsplit
  rw [hsplit, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- Combining half the diagonal sum with the strict-upper sum of a symmetric kernel `g` recovers
half the full double sum over `Fin n × Fin n`. -/
private theorem half_diag_add_sum_upperPairs_of_symm {M : Type*} [AddCommGroup M] [Module ℂ M]
    {n : ℕ} (g : Fin n → Fin n → M) (hg : ∀ a b, g a b = g b a) :
    (2 : ℂ)⁻¹ • (∑ a : Fin n, g a a) + ∑ p ∈ upperPairs n, g p.1 p.2 =
      (2 : ℂ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n, g a b := by
  rw [sum_upperPairs_of_symm g hg, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ ↦ Finset.add_sum_erase _ (fun b ↦ g a b) (Finset.mem_univ a)

private theorem gaussianEnsemble_single_diag_of_eq_one {β n : ℕ} (hβ : β = 1) (a : Fin n) :
    gaussianEnsemble β n (Pi.single (a, a) 1) =
      (((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ))) • Matrix.single a a 1 := by
  ext i j
  simp only [gaussianEnsemble_apply, hβ, ↓reduceIte, Pi.single_apply, Prod.mk.injEq,
    Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, Complex.ofReal_mul]
  split_ifs <;> first | (push_cast; ring1) | omega

private theorem gaussianEnsemble_single_lt_of_eq_one {β n : ℕ} (hβ : β = 1) {a b : Fin n}
    (hab : a < b) :
    gaussianEnsemble β n (Pi.single (a, b) 1) =
      ((Real.sqrt n : ℂ)⁻¹) • (Matrix.single a b 1 + Matrix.single b a 1) := by
  ext i j
  simp only [gaussianEnsemble_apply, hβ, ↓reduceIte, Pi.single_apply, Prod.mk.injEq,
    Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs <;> first | (push_cast; ring1) | omega

private theorem gaussianEnsemble_single_gt_of_eq_one {β n : ℕ} (hβ : β = 1) {a b : Fin n}
    (hab : a < b) :
    gaussianEnsemble β n (Pi.single (b, a) 1) = 0 := by
  ext i j
  simp only [gaussianEnsemble_apply, hβ, ↓reduceIte, Pi.single_apply, Prod.mk.injEq,
    Matrix.zero_apply]
  split_ifs <;> first | (push_cast; ring1) | omega

private theorem gaussianEnsemble_single_diag_of_ne_one {β n : ℕ} (hβ : β ≠ 1) (a : Fin n) :
    gaussianEnsemble β n (Pi.single (a, a) 1) =
      ((Real.sqrt n : ℂ)⁻¹) • Matrix.single a a 1 := by
  ext i j
  simp only [gaussianEnsemble_apply, hβ, ↓reduceIte, Pi.single_apply, Prod.mk.injEq,
    Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, div_eq_mul_inv]
  split_ifs <;> first | (push_cast; ring1) | omega

private theorem gaussianEnsemble_single_lt_of_ne_one {β n : ℕ} (hβ : β ≠ 1) {a b : Fin n}
    (hab : a < b) :
    gaussianEnsemble β n (Pi.single (a, b) 1) =
      ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) •
        (Matrix.single a b 1 + Matrix.single b a 1) := by
  ext i j
  simp only [gaussianEnsemble_apply, hβ, ↓reduceIte, Pi.single_apply, Prod.mk.injEq,
    Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul, div_eq_mul_inv]
  split_ifs <;> first | (push_cast; ring1) | omega

private theorem gaussianEnsemble_single_gt_of_ne_one {β n : ℕ} (hβ : β ≠ 1) {a b : Fin n}
    (hab : a < b) :
    gaussianEnsemble β n (Pi.single (b, a) 1) =
      (Complex.I * ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹)) •
        (Matrix.single a b 1 - Matrix.single b a 1) := by
  ext i j
  simp only [gaussianEnsemble_apply, hβ, ↓reduceIte, Pi.single_apply, Prod.mk.injEq,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul, div_eq_mul_inv]
  split_ifs <;> first | (push_cast; ring1) | omega

/-! ### Elementary `Matrix.single` product and trace identities -/

private theorem single_one_mul_mul_single_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * M * Matrix.single c d (1 : ℂ) =
      M b c • Matrix.single a d (1 : ℂ) := by
  rw [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem smul_mul_mul_smul {n : ℕ} (c d : ℂ)
    (A M B : Matrix (Fin n) (Fin n) ℂ) :
    (c • A) * M * (d • B) = (c * d) • (A * M * B) := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem trace_mul_single_one {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (X * Matrix.single a b (1 : ℂ)).trace = X b a := by
  simp [Matrix.trace_mul_single]

private theorem inv_sqrt_nat_sq (n : ℕ) :
    (Real.sqrt n : ℂ)⁻¹ * (Real.sqrt n : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n),
    Complex.ofReal_natCast]

private theorem inv_sqrt_two_sq :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_ofNat]

private theorem sqrt_two_sq :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_ofNat]

private theorem inv_sqrt_nat_two_sq_mul_two (n : ℕ) :
    ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
      ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * 2 = (n : ℂ)⁻¹ := by
  calc ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
        ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * 2
      = ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt n : ℂ)⁻¹) *
          ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2) := by ring
    _ = (n : ℂ)⁻¹ := by
          rw [inv_sqrt_nat_sq, inv_sqrt_two_sq, inv_mul_cancel₀ two_ne_zero, mul_one]

private theorem sum_sum_diag_smul_single (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a : Fin n, ∑ b : Fin n, M b b • Matrix.single a a (1 : ℂ) =
      M.trace • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hinner : ∀ a : Fin n,
      ∑ b : Fin n, M b b • Matrix.single a a (1 : ℂ) = M.trace • Matrix.single a a 1 := fun a ↦ by
    rw [← Finset.sum_smul]; rfl
  rw [Finset.sum_congr rfl fun a _ ↦ hinner a, ← Finset.smul_sum, Matrix.sum_single_one]

private theorem sum_sum_herm_trace {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a : Fin n, ∑ b : Fin n, (X b a * Y a b + X a b * Y b a) = 2 * (X * Y).trace := by
  have htr : ∑ a : Fin n, ∑ b : Fin n, X a b * Y b a = (X * Y).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  have htr' : ∑ a : Fin n, ∑ b : Fin n, X b a * Y a b = (X * Y).trace := by
    rw [Finset.sum_comm]; exact htr
  simp_rw [Finset.sum_add_distrib]
  rw [htr', htr]
  ring

private theorem sum_sum_symm_trace {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a : Fin n, ∑ b : Fin n, (X b a + X a b) * (Y b a + Y a b) =
      2 * ((X * Y).trace + (X * Yᵀ).trace) := by
  have hXY : ∑ a : Fin n, ∑ b : Fin n, X a b * Y b a = (X * Y).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  have hXY' : ∑ a : Fin n, ∑ b : Fin n, X b a * Y a b = (X * Y).trace := by
    rw [Finset.sum_comm]; exact hXY
  have hXYt : ∑ a : Fin n, ∑ b : Fin n, X a b * Y a b = (X * Yᵀ).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have hXYt' : ∑ a : Fin n, ∑ b : Fin n, X b a * Y b a = (X * Yᵀ).trace := by
    rw [Finset.sum_comm]; exact hXYt
  have hexp : ∀ a b : Fin n, (X b a + X a b) * (Y b a + Y a b) =
      X b a * Y b a + X b a * Y a b + X a b * Y b a + X a b * Y a b := fun a b ↦ by ring
  simp_rw [hexp, Finset.sum_add_distrib]
  rw [hXYt', hXY', hXY, hXYt]
  ring

/-! ### Quadratic Casimir and trace inner-product sums over `Pi.single p 1` -/

private theorem symm_anti_sandwich {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Matrix.single a b (1 : ℂ) + Matrix.single b a 1) * M *
        (Matrix.single a b 1 + Matrix.single b a 1) -
      (Matrix.single a b 1 - Matrix.single b a 1) * M *
        (Matrix.single a b 1 - Matrix.single b a 1) =
      (2 : ℂ) • (M b b • Matrix.single a a 1 + M a a • Matrix.single b b 1) := by
  simp only [add_mul, sub_mul, mul_add, mul_sub, single_one_mul_mul_single_one]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem symm_sandwich {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Matrix.single a b (1 : ℂ) + Matrix.single b a 1) * M *
        (Matrix.single a b 1 + Matrix.single b a 1) =
      M b a • Matrix.single a b 1 + M b b • Matrix.single a a 1 +
        M a a • Matrix.single b b 1 + M a b • Matrix.single b a 1 := by
  simp only [add_mul, mul_add, single_one_mul_mul_single_one]
  abel

private theorem sum_sum_symm_sandwich {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a : Fin n, ∑ b : Fin n,
        ((Matrix.single a b (1 : ℂ) + Matrix.single b a 1) * M *
          (Matrix.single a b 1 + Matrix.single b a 1)) =
      (2 : ℂ) • (M.trace • (1 : Matrix (Fin n) (Fin n) ℂ) + Mᵀ) := by
  simp_rw [symm_sandwich, Finset.sum_add_distrib]
  have h1 : ∑ a : Fin n, ∑ b : Fin n, M b a • Matrix.single a b (1 : ℂ) = Mᵀ := by
    simp_rw [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.sum_sum_single (fun a b ↦ M b a)
  have h2 := sum_sum_diag_smul_single n M
  have h3 : ∑ a : Fin n, ∑ b : Fin n, M a a • Matrix.single b b (1 : ℂ) =
      M.trace • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Finset.sum_comm]; exact h2
  have h4 : ∑ a : Fin n, ∑ b : Fin n, M a b • Matrix.single b a (1 : ℂ) = Mᵀ := by
    rw [Finset.sum_comm]; exact h1
  rw [h1, h2, h3, h4, two_smul]
  abel

/-- **GUE Casimir identity**: for `β ≠ 1` (in particular `β = 2`) and any complex `n × n` matrix
`M`, summing `Eₚ * M * Eₚ` over the canonical coordinates
`Eₚ = gaussianEnsemble β n (Pi.single p 1)` yields `(n⁻¹ * M.trace) • 1`. -/
theorem sum_gaussianEnsemble_single_mul_self_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      ((n : ℂ)⁻¹ * M.trace) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  let K : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b ↦
    M b b • Matrix.single a a 1 + M a a • Matrix.single b b 1
  rw [sum_prod_eq_diag_add_upper]
  have hdiag : ∑ a : Fin n,
      gaussianEnsemble β n (Pi.single (a, a) 1) * M *
        gaussianEnsemble β n (Pi.single (a, a) 1) =
      (n : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ a : Fin n, K a a) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [gaussianEnsemble_single_diag_of_ne_one hβ, smul_mul_mul_smul, single_one_mul_mul_single_one,
      inv_sqrt_nat_sq]
    dsimp only [K]
    rw [← two_smul ℂ (M a a • Matrix.single a a (1 : ℂ)), smul_smul (2 : ℂ)⁻¹,
      inv_mul_cancel₀ two_ne_zero, one_smul]
  have hup_term : ∀ p ∈ upperPairs n,
      gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) +
        gaussianEnsemble β n (Pi.single (p.2, p.1) 1) * M *
          gaussianEnsemble β n (Pi.single (p.2, p.1) 1) =
      (n : ℂ)⁻¹ • K p.1 p.2 := by
    rintro ⟨a, b⟩ hp
    have hab : a < b := (Finset.mem_filter.mp hp).2
    rw [gaussianEnsemble_single_lt_of_ne_one hβ hab, gaussianEnsemble_single_gt_of_ne_one hβ hab,
      smul_mul_mul_smul, smul_mul_mul_smul]
    let s : ℂ := (Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹
    have hI : (Complex.I * s) * (Complex.I * s) = -(s * s) := by
      calc (Complex.I * s) * (Complex.I * s)
          = (Complex.I * Complex.I) * (s * s) := by ring
        _ = -(s * s) := by rw [Complex.I_mul_I, neg_one_mul]
    rw [hI, neg_smul, ← sub_eq_add_neg, ← smul_sub, symm_anti_sandwich, smul_smul,
      inv_sqrt_nat_two_sq_mul_two n]
  rw [hdiag, Finset.sum_congr rfl hup_term, ← Finset.smul_sum, ← smul_add,
    half_diag_add_sum_upperPairs_of_symm K (fun a b ↦ add_comm _ _)]
  have hfull : ∑ a : Fin n, ∑ b : Fin n, K a b =
      (2 : ℂ) • (M.trace • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    have hL := sum_sum_diag_smul_single n M
    have hR : ∑ a : Fin n, ∑ b : Fin n, M a a • Matrix.single b b (1 : ℂ) =
        M.trace • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Finset.sum_comm]; exact hL
    dsimp only [K]; simp_rw [Finset.sum_add_distrib]; rw [hL, hR, two_smul]
  rw [hfull, smul_smul (2 : ℂ)⁻¹, inv_mul_cancel₀ two_ne_zero, one_smul, smul_smul]

/-- **GOE Casimir identity**: for `β = 1` and any complex `n × n` matrix `M`, summing `Eₚ * M * Eₚ`
over `Eₚ = gaussianEnsemble β n (Pi.single p 1)` yields `n⁻¹ • (M.trace • 1 + Mᵀ)`. -/
theorem sum_gaussianEnsemble_single_mul_self_of_eq_one {β n : ℕ} (hβ : β = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (M.trace • (1 : Matrix (Fin n) (Fin n) ℂ) + Mᵀ) := by
  let K : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b ↦
    (Matrix.single a b (1 : ℂ) + Matrix.single b a 1) * M *
      (Matrix.single a b 1 + Matrix.single b a 1)
  rw [sum_prod_eq_diag_add_upper]
  have hdiag : ∑ a : Fin n,
      gaussianEnsemble β n (Pi.single (a, a) 1) * M *
        gaussianEnsemble β n (Pi.single (a, a) 1) =
      (n : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ a : Fin n, K a a) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [gaussianEnsemble_single_diag_of_eq_one hβ, smul_mul_mul_smul, single_one_mul_mul_single_one,
      smul_smul]
    have hKaa : K a a = ((4 : ℂ) * M a a) • Matrix.single a a 1 := by
      dsimp only [K]
      rw [← two_smul ℂ (Matrix.single a a (1 : ℂ)), smul_mul_mul_smul,
        single_one_mul_mul_single_one, smul_smul]
      ring_nf
    rw [hKaa, smul_smul, smul_smul]
    congr 1
    calc ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) *
          ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) * M a a
        = ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) *
            ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * M a a := by ring
      _ = (n : ℂ)⁻¹ * (2 : ℂ)⁻¹ * (4 * M a a) := by
            rw [inv_sqrt_nat_sq, sqrt_two_sq]; ring
  have hup_term : ∀ p ∈ upperPairs n,
      gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) +
        gaussianEnsemble β n (Pi.single (p.2, p.1) 1) * M *
          gaussianEnsemble β n (Pi.single (p.2, p.1) 1) =
      (n : ℂ)⁻¹ • K p.1 p.2 := by
    rintro ⟨a, b⟩ hp
    have hab : a < b := (Finset.mem_filter.mp hp).2
    rw [gaussianEnsemble_single_lt_of_eq_one hβ hab, gaussianEnsemble_single_gt_of_eq_one hβ hab,
      zero_mul, zero_mul, add_zero, smul_mul_mul_smul, inv_sqrt_nat_sq]
  rw [hdiag, Finset.sum_congr rfl hup_term, ← Finset.smul_sum, ← smul_add,
    half_diag_add_sum_upperPairs_of_symm K (fun a b ↦ by dsimp only [K]; rw [add_comm]),
    sum_sum_symm_sandwich, smul_smul (2 : ℂ)⁻¹, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- **GUE trace inner-product identity**: for `β ≠ 1` and any complex `n × n` matrices `X, Y`,
`∑ p, (X * Eₚ).trace * (Y * Eₚ).trace = n⁻¹ * (X * Y).trace`. -/
theorem sum_trace_mul_gaussianEnsemble_single_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      (n : ℂ)⁻¹ * (X * Y).trace := by
  let K : Fin n → Fin n → ℂ := fun a b ↦ X b a * Y a b + X a b * Y b a
  rw [sum_prod_eq_diag_add_upper]
  have hdiag : ∑ a : Fin n,
      (X * gaussianEnsemble β n (Pi.single (a, a) 1)).trace *
        (Y * gaussianEnsemble β n (Pi.single (a, a) 1)).trace =
      (n : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * ∑ a : Fin n, K a a) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [gaussianEnsemble_single_diag_of_ne_one hβ, Matrix.mul_smul, Matrix.mul_smul, trace_smul,
      trace_smul, trace_mul_single_one, trace_mul_single_one, smul_eq_mul, smul_eq_mul]
    dsimp only [K]
    calc ((Real.sqrt ↑n : ℂ)⁻¹ * X a a) * ((Real.sqrt ↑n : ℂ)⁻¹ * Y a a)
        = ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) * (X a a * Y a a) := by ring
      _ = (n : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (X a a * Y a a + X a a * Y a a)) := by
            rw [inv_sqrt_nat_sq]; ring
  have hup_term : ∀ p ∈ upperPairs n,
      (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace +
        (X * gaussianEnsemble β n (Pi.single (p.2, p.1) 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single (p.2, p.1) 1)).trace =
      (n : ℂ)⁻¹ * K p.1 p.2 := by
    rintro ⟨a, b⟩ hp
    have hab : a < b := (Finset.mem_filter.mp hp).2
    rw [gaussianEnsemble_single_lt_of_ne_one hβ hab, gaussianEnsemble_single_gt_of_ne_one hβ hab]
    simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub, trace_smul, trace_add, trace_sub,
      trace_mul_single_one, smul_eq_mul]
    dsimp only [K]
    calc ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * (X b a + X a b)) *
            ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * (Y b a + Y a b)) +
          (Complex.I * ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * (X b a - X a b)) *
            (Complex.I * ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * (Y b a - Y a b))
        = ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) *
            ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
            ((X b a + X a b) * (Y b a + Y a b) +
              (Complex.I * Complex.I) * ((X b a - X a b) * (Y b a - Y a b))) := by ring
      _ = (n : ℂ)⁻¹ * (X b a * Y a b + X a b * Y b a) := by
            rw [inv_sqrt_nat_sq, inv_sqrt_two_sq, Complex.I_mul_I]; ring
  rw [hdiag, Finset.sum_congr rfl hup_term, ← Finset.mul_sum, ← mul_add]
  have hcomb := half_diag_add_sum_upperPairs_of_symm K (fun a b ↦ add_comm _ _)
  simp only [smul_eq_mul] at hcomb
  rw [hcomb, sum_sum_herm_trace]
  ring

/-- **GOE trace inner-product identity**: for `β = 1` and any complex `n × n` matrices `X, Y`,
`∑ p, (X * Eₚ).trace * (Y * Eₚ).trace = n⁻¹ * ((X * Y).trace + (X * Yᵀ).trace)`. -/
theorem sum_trace_mul_gaussianEnsemble_single_of_eq_one {β n : ℕ} (hβ : β = 1)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      (n : ℂ)⁻¹ * ((X * Y).trace + (X * Yᵀ).trace) := by
  let K : Fin n → Fin n → ℂ := fun a b ↦ (X b a + X a b) * (Y b a + Y a b)
  rw [sum_prod_eq_diag_add_upper]
  have hdiag : ∑ a : Fin n,
      (X * gaussianEnsemble β n (Pi.single (a, a) 1)).trace *
        (Y * gaussianEnsemble β n (Pi.single (a, a) 1)).trace =
      (n : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * ∑ a : Fin n, K a a) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [gaussianEnsemble_single_diag_of_eq_one hβ, Matrix.mul_smul, Matrix.mul_smul, trace_smul,
      trace_smul, trace_mul_single_one, trace_mul_single_one, smul_eq_mul, smul_eq_mul]
    dsimp only [K]
    calc ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ) * X a a) *
          ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt 2 : ℂ) * Y a a)
        = ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) *
            ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (X a a * Y a a) := by ring
      _ = (n : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * ((X a a + X a a) * (Y a a + Y a a))) := by
            rw [inv_sqrt_nat_sq, sqrt_two_sq]; ring
  have hup_term : ∀ p ∈ upperPairs n,
      (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace +
        (X * gaussianEnsemble β n (Pi.single (p.2, p.1) 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single (p.2, p.1) 1)).trace =
      (n : ℂ)⁻¹ * K p.1 p.2 := by
    rintro ⟨a, b⟩ hp
    have hab : a < b := (Finset.mem_filter.mp hp).2
    rw [gaussianEnsemble_single_lt_of_eq_one hβ hab, gaussianEnsemble_single_gt_of_eq_one hβ hab]
    simp only [mul_zero, trace_zero, add_zero, Matrix.mul_smul, Matrix.mul_add, trace_smul,
      trace_add, trace_mul_single_one, smul_eq_mul]
    dsimp only [K]
    calc ((Real.sqrt ↑n : ℂ)⁻¹ * (X b a + X a b)) * ((Real.sqrt ↑n : ℂ)⁻¹ * (Y b a + Y a b))
        = ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) *
            ((X b a + X a b) * (Y b a + Y a b)) := by ring
      _ = (n : ℂ)⁻¹ * ((X b a + X a b) * (Y b a + Y a b)) := by rw [inv_sqrt_nat_sq]
  rw [hdiag, Finset.sum_congr rfl hup_term, ← Finset.mul_sum, ← mul_add]
  have hcomb := half_diag_add_sum_upperPairs_of_symm K
    (fun a b ↦ by dsimp only [K]; rw [add_comm (X b a), add_comm (Y b a)])
  simp only [smul_eq_mul] at hcomb
  rw [hcomb, sum_sum_symm_trace]
  ring

private theorem ofReal_re_trace_mul_of_isHermitian {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (((X * Y).trace).re : ℂ) = (X * Y).trace := by
  have hconj : star (X * Y).trace = (X * Y).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hX.eq, hY.eq, trace_mul_comm]
  have him : ((X * Y).trace).im = 0 := by
    have h := congrArg Complex.im hconj
    simp only [RCLike.star_def, Complex.conj_im] at h
    linarith
  exact Complex.ext rfl him.symm

/-- Real-part GUE trace inner-product identity for Hermitian matrices `X, Y`. -/
theorem sum_re_trace_mul_gaussianEnsemble_single_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (n : ℝ)⁻¹ * (X * Y).trace.re := by
  have h := congrArg Complex.re (sum_trace_mul_gaussianEnsemble_single_of_ne_one hβ X Y)
  have hlhs : (∑ p : Fin n × Fin n,
      (X * gaussianEnsemble β n (Pi.single p 1)).trace *
        (Y * gaussianEnsemble β n (Pi.single p 1)).trace).re =
      ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hE := isHermitian_gaussianEnsemble β n (Pi.single p 1)
    conv_lhs =>
      rw [← ofReal_re_trace_mul_of_isHermitian hX hE, ← ofReal_re_trace_mul_of_isHermitian hY hE]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hrhs : ((n : ℂ)⁻¹ * (X * Y).trace).re = (n : ℝ)⁻¹ * (X * Y).trace.re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  exact hlhs ▸ hrhs ▸ h

/-- Real-part GOE trace inner-product identity for Hermitian matrices `X, Y`. -/
theorem sum_re_trace_mul_gaussianEnsemble_single_of_eq_one {β n : ℕ} (hβ : β = 1)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (n : ℝ)⁻¹ * ((X * Y).trace.re + (X * Yᵀ).trace.re) := by
  have h := congrArg Complex.re (sum_trace_mul_gaussianEnsemble_single_of_eq_one hβ X Y)
  have hlhs : (∑ p : Fin n × Fin n,
      (X * gaussianEnsemble β n (Pi.single p 1)).trace *
        (Y * gaussianEnsemble β n (Pi.single p 1)).trace).re =
      ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hE := isHermitian_gaussianEnsemble β n (Pi.single p 1)
    conv_lhs =>
      rw [← ofReal_re_trace_mul_of_isHermitian hX hE, ← ofReal_re_trace_mul_of_isHermitian hY hE]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hrhs : ((n : ℂ)⁻¹ * ((X * Y).trace + (X * Yᵀ).trace)).re =
      (n : ℝ)⁻¹ * ((X * Y).trace.re + (X * Yᵀ).trace.re) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.add_re]
  exact hlhs ▸ hrhs ▸ h

/-! ### Smoothness, gradient bracket, and Dyson repulsion drift of sorted eigenvalues -/

private theorem eigenvalues₀_congr_mat {n : ℕ} {M₁ M₂ : Matrix (Fin n) (Fin n) ℂ}
    (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂)
    (k : Fin (Fintype.card (Fin n))) :
    h₁.eigenvalues₀ k = h₂.eigenvalues₀ k := by
  subst h; rfl

private theorem eigenvalues₀_add_gaussianEnsemble_line_eq {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v : Fin n × Fin n → ℝ)
    (k : Fin (Fintype.card (Fin n))) :
    (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k) =
      fun t : ℝ ↦ ((hA.add (isHermitian_gaussianEnsemble β n g)).add
        ((isHermitian_gaussianEnsemble β n v).smul (IsSelfAdjoint.all t))).eigenvalues₀ k :=
  funext fun t ↦ eigenvalues₀_congr_mat _ _
    (by rw [gaussianEnsemble_add, gaussianEnsemble_smul, add_assoc]) k

/-- At any Gaussian array `g` where the `k`-th sorted eigenvalue of `A + gaussianEnsemble β n g` is
simple, the map `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` is `C^r` (for every
`r : ℕ∞ω`, including `∞` and real-analytic `ω`). -/
theorem contDiffAt_eigenvalues₀_add_gaussianEnsemble {β n : ℕ} {r : ℕ∞ω}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    ContDiffAt ℝ r
      (fun g' : Fin n × Fin n → ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g := by
  let A' : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) := ⟨A, hA.isSelfAdjoint⟩
  let Φ : (Fin n × Fin n → ℝ) → selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
    fun g' ↦ A' + gaussianEnsembleSelfAdjointCLM β n g'
  have hΦ_coe : ∀ g', (Φ g' : Matrix (Fin n) (Fin n) ℂ) = A + gaussianEnsemble β n g' :=
    fun g' ↦ by simp [Φ, A']
  have hfn : (fun g' : Fin n × Fin n → ℝ ↦
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) =
      (fun X : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) ↦ X.2.isHermitian.eigenvalues₀ k) ∘ Φ :=
    funext fun g' ↦ eigenvalues₀_congr_mat _ (Φ g').2.isHermitian (hΦ_coe g').symm k
  have hk' : ∀ j ≠ k, (Φ g).2.isHermitian.eigenvalues₀ j ≠ (Φ g).2.isHermitian.eigenvalues₀ k := by
    intro j hj
    rw [eigenvalues₀_congr_mat (Φ g).2.isHermitian
        (hA.add (isHermitian_gaussianEnsemble β n g)) (hΦ_coe g) j,
      eigenvalues₀_congr_mat (Φ g).2.isHermitian
        (hA.add (isHermitian_gaussianEnsemble β n g)) (hΦ_coe g) k]
    exact hk j hj
  rw [hfn]
  have hΦ_diff : ContDiff ℝ r Φ :=
    contDiff_const.add (gaussianEnsembleSelfAdjointCLM β n).contDiff
  exact (contDiffAt_eigenvalues₀ hk').comp g hΦ_diff.contDiffAt

/-- Directional derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k` at
`t = 0` when the `k`-th eigenvalue at `g` is simple. -/
theorem hasDerivAt_eigenvalues₀_add_gaussianEnsemble {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    HasDerivAt
      (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k)
      ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
        gaussianEnsemble β n v).trace.re 0 := by
  rw [eigenvalues₀_add_gaussianEnsemble_line_eq hA g v k]
  exact (hA.add (isHermitian_gaussianEnsemble β n g)).hasDerivAt_add_smul_eigenvalues₀
    (isHermitian_gaussianEnsemble β n v) hk

/-- Directional second derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k` at
`t = 0` when the `k`-th eigenvalue at `g` is simple. -/
theorem iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    iteratedDeriv 2
      (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k,
        ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k -
          (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j)⁻¹ *
          ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
            gaussianEnsemble β n v *
            (hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ j *
            gaussianEnsemble β n v).trace.re := by
  rw [eigenvalues₀_add_gaussianEnsemble_line_eq hA g v k]
  exact (hA.add (isHermitian_gaussianEnsemble β n g)).iteratedDeriv_two_add_smul_eigenvalues₀
    (isHermitian_gaussianEnsemble β n v) hk

/-- **GUE coordinate gradient bracket**: for `β ≠ 1` (in particular `β = 2`) and simple sorted
eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g`, the inner product of their coordinate
gradients is `n⁻¹ * δₖₘ`. -/
theorem sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ)
    {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      if k = m then (n : ℝ)⁻¹ else 0 := by
  set hH := hA.add (isHermitian_gaussianEnsemble β n g)
  have hterm : ∀ p : Fin n × Fin n,
      deriv (fun t : ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
      deriv (fun t : ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1)).trace.re *
        (hH.eigenprojector₀ m * gaussianEnsemble β n (Pi.single p 1)).trace.re := fun p ↦ by
    rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single p 1) hk).deriv,
      (hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single p 1) hm).deriv]
  simp_rw [hterm]
  rw [sum_re_trace_mul_gaussianEnsemble_single_of_ne_one hβ (hH.isHermitian_eigenprojector₀ k)
    (hH.isHermitian_eigenprojector₀ m)]
  by_cases hkm : k = m
  · subst hkm
    simp only [↓reduceIte]
    rw [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀, Complex.one_re, mul_one]
  · simp only [hkm, ↓reduceIte]
    rw [hH.eigenprojector₀_mul_of_ne hkm, trace_zero, Complex.zero_re, mul_zero]

/-- **GOE coordinate gradient bracket**: for `β = 1`, symmetric `A`, and simple sorted eigenvalues
`λₖ, λₘ` of `A + gaussianEnsemble β n g`, the inner product of their coordinate gradients is
`2 * n⁻¹ * δₖₘ`. -/
theorem sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_eq_one {β n : ℕ} (hβ : β = 1)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hA_symm : A.IsSymm)
    (g : Fin n × Fin n → ℝ) {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      if k = m then 2 * (n : ℝ)⁻¹ else 0 := by
  set hH := hA.add (isHermitian_gaussianEnsemble β n g)
  have hH_symm : (A + gaussianEnsemble β n g).IsSymm :=
    hA_symm.add (isSymm_gaussianEnsemble_of_eq_one hβ g)
  have hPm_symm : (hH.eigenprojector₀ m).IsSymm := hH.isSymm_eigenprojector₀ hH_symm hm
  have hterm : ∀ p : Fin n × Fin n,
      deriv (fun t : ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
      deriv (fun t : ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1)).trace.re *
        (hH.eigenprojector₀ m * gaussianEnsemble β n (Pi.single p 1)).trace.re := fun p ↦ by
    rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single p 1) hk).deriv,
      (hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single p 1) hm).deriv]
  simp_rw [hterm]
  rw [sum_re_trace_mul_gaussianEnsemble_single_of_eq_one hβ (hH.isHermitian_eigenprojector₀ k)
    (hH.isHermitian_eigenprojector₀ m), hPm_symm.eq]
  by_cases hkm : k = m
  · subst hkm
    simp only [↓reduceIte]
    rw [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀, Complex.one_re]
    ring
  · simp only [hkm, ↓reduceIte]
    rw [hH.eigenprojector₀_mul_of_ne hkm, trace_zero, Complex.zero_re]
    ring

/-- **Dyson Brownian motion diffusion bracket** (Anderson–Guionnet–Zeitouni Theorem 4.3.2): for
both the GOE (`β = 1` with symmetric `A`) and the GUE (`β = 2`), the coordinate gradient bracket of
simple sorted eigenvalues `λₖ, λₘ` equals `if k = m then 2 / (β * n) else 0`. -/
theorem sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hβ : (β = 1 ∧ A.IsSymm) ∨ β = 2) (g : Fin n × Fin n → ℝ)
    {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      if k = m then 2 / ((β : ℝ) * n) else 0 := by
  rcases hβ with ⟨hβ1, hA_symm⟩ | rfl
  · rw [sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_eq_one hβ1 hA hA_symm g hk hm, hβ1]
    split_ifs <;> simp [div_eq_mul_inv]
  · rw [sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_ne_one (by decide) hA g hk hm]
    split_ifs
    · push_cast
      rw [div_mul_eq_div_div, div_self two_ne_zero, one_div]
    · rfl

/-- **Dyson repulsion drift (coordinate half-Laplacian)** (Anderson–Guionnet–Zeitouni Theorem 4.3.2
and Lemma 4.3.4): for both `β ≠ 1` (in particular GUE `β = 2`, for any Hermitian `A`) and `β = 1`
(GOE, for Hermitian symmetric `A`), half the coordinate Laplacian of a simple sorted eigenvalue
`λₖ` of `H = A + gaussianEnsemble β n g` equals the electrostatic repulsion sum
`n⁻¹ * ∑ j ≠ k, (λₖ(H) - λⱼ(H))⁻¹`. -/
theorem half_sum_iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hβ : β ≠ 1 ∨ A.IsSymm)
    (g : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    (2 : ℝ)⁻¹ * ∑ p : Fin n × Fin n,
        iteratedDeriv 2 (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 =
      (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase k,
        ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k -
          (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j)⁻¹ := by
  set hH := hA.add (isHermitian_gaussianEnsemble β n g)
  have h2 : ∀ p : Fin n × Fin n,
      iteratedDeriv 2 (fun t : ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k, (hH.eigenvalues₀ k - hH.eigenvalues₀ j)⁻¹ *
        (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1) *
          hH.eigenprojector₀ j * gaussianEnsemble β n (Pi.single p 1)).trace.re :=
    fun p ↦ iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single p 1) hk
  simp_rw [h2, ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  rw [← Finset.mul_sum]
  have hsum_re : ∑ p : Fin n × Fin n,
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1) *
        hH.eigenprojector₀ j * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (hH.eigenprojector₀ k * ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * hH.eigenprojector₀ j *
          gaussianEnsemble β n (Pi.single p 1)).trace.re := by
    rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by simp only [Matrix.mul_assoc]
  rw [hsum_re]
  have hinner : (hH.eigenprojector₀ k * ∑ p : Fin n × Fin n,
      gaussianEnsemble β n (Pi.single p 1) * hH.eigenprojector₀ j *
        gaussianEnsemble β n (Pi.single p 1)).trace.re = (n : ℝ)⁻¹ := by
    by_cases hβ1 : β = 1
    · have hA_symm : A.IsSymm := hβ.resolve_left (not_not.mpr hβ1)
      have hH_symm : (A + gaussianEnsemble β n g).IsSymm :=
        hA_symm.add (isSymm_gaussianEnsemble_of_eq_one hβ1 g)
      have hPk_symm : (hH.eigenprojector₀ k).IsSymm := hH.isSymm_eigenprojector₀ hH_symm hk
      have hvanish : (hH.eigenprojector₀ k * (hH.eigenprojector₀ j)ᵀ).trace = 0 := by
        rw [← hPk_symm.eq, ← transpose_mul, trace_transpose, hH.eigenprojector₀_mul_of_ne hjk,
          trace_zero]
      rw [sum_gaussianEnsemble_single_mul_self_of_eq_one hβ1, hH.trace_eigenprojector₀ j, one_smul,
        Matrix.mul_smul, mul_add, mul_one, trace_smul, trace_add, hH.trace_eigenprojector₀ k,
        hvanish, add_zero, smul_eq_mul, mul_one, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        Complex.ofReal_re]
    · rw [sum_gaussianEnsemble_single_mul_self_of_ne_one hβ1, hH.trace_eigenprojector₀ j, mul_one,
        Matrix.mul_smul, mul_one, trace_smul, hH.trace_eigenprojector₀ k, smul_eq_mul, mul_one,
        ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [hinner, mul_comm]

end Probability

end TauCeti
