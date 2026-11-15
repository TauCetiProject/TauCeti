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

This file combines Hadamard's first and second eigenvalue variation formulas with the entry
parameterization of the GOE and GUE (`gaussianEnsemble β n g` for `β = 1, 2`) to compute the
deterministic differential invariants driving Dyson Brownian motion on the simple-spectrum chamber.

## Main definitions and results

* `TauCeti.Probability.gaussianEnsembleSelfAdjointCLM`: continuous `ℝ`-linear map bundling
  `gaussianEnsemble β n` into `selfAdjoint (Matrix (Fin n) (Fin n) ℂ)`.
* `TauCeti.Probability.sum_gaussianEnsemble_single_mul_self_of_ne_one` and
  `TauCeti.Probability.sum_gaussianEnsemble_single_mul_self_of_eq_one`: quadratic Casimir sums.
* `TauCeti.Probability.sum_re_trace_mul_gaussianEnsemble_single_of_ne_one` and
  `TauCeti.Probability.sum_re_trace_mul_gaussianEnsemble_single_of_eq_one`: real-trace inner sums.
* `TauCeti.Probability.contDiffAt_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul`, and
  `TauCeti.Probability.half_sum_iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices* (2010), §4.3.1.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §1.3.4 and §3.1.
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

/-- The Gaussian ensemble of the zero array is the zero matrix. -/
@[simp] theorem gaussianEnsemble_zero (β n : ℕ) : gaussianEnsemble β n 0 = 0 := by
  ext i j; rw [gaussianEnsemble_apply]; split_ifs <;> simp

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
  ext i j; rw [transpose_apply, gaussianEnsemble_apply, gaussianEnsemble_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hβ, hij, hij.ne, hij.not_gt, hij.ne']
  · simp [hβ]
  · simp [hβ, hji, hji.ne, hji.not_gt, hji.ne']

/-- `gaussianEnsemble 1 n g` is symmetric for every array `g`. -/
theorem isSymm_gaussianEnsemble_one (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsemble 1 n g).IsSymm := isSymm_gaussianEnsemble_of_eq_one rfl g

/-- Continuous `ℝ`-linear map bundling `gaussianEnsemble β n` into the real Banach space
`selfAdjoint (Matrix (Fin n) (Fin n) ℂ)`. -/
def gaussianEnsembleSelfAdjointCLM (β n : ℕ) :
    (Fin n × Fin n → ℝ) →L[ℝ] selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
  ∑ p : Fin n × Fin n, (ContinuousLinearMap.proj (R := ℝ) p).smulRight
    ⟨gaussianEnsemble β n (Pi.single p 1),
      (isHermitian_gaussianEnsemble β n (Pi.single p 1)).isSelfAdjoint⟩

/-- Coercing `gaussianEnsembleSelfAdjointCLM β n g` to a matrix recovers
`gaussianEnsemble β n g`. -/
@[simp] theorem gaussianEnsembleSelfAdjointCLM_apply_coe (β n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsembleSelfAdjointCLM β n g : Matrix (Fin n) (Fin n) ℂ) =
      gaussianEnsemble β n g := by
  rw [gaussianEnsembleSelfAdjointCLM, sum_apply,
    ← selfAdjoint.subtypeL_apply (R := ℝ), map_sum, gaussianEnsemble_eq_sum_single]; rfl

private theorem inv_sqrt_nat_sq (n : ℕ) :
    (Real.sqrt n : ℂ)⁻¹ * (Real.sqrt n : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n),
    Complex.ofReal_natCast]
private theorem inv_sqrt_two_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_ofNat]
private theorem sqrt_two_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_ofNat]

private theorem gaussianEnsemble_single_apply_eq_zero {β n : ℕ} {p : Fin n × Fin n}
    {i j : Fin n} (h1 : p ≠ (i, j)) (h2 : p ≠ (j, i)) :
    gaussianEnsemble β n (Pi.single p 1) i j = 0 := by
  rcases eq_or_ne i j with rfl | hij <;> simp [gaussianEnsemble_apply, h1.symm, h2.symm, *]

private theorem sum_gaussianEnsemble_single_apply_mul_eq_pair (β n : ℕ) (i j k l : Fin n) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l =
      ∑ p ∈ ({(i, j), (j, i)} : Finset (Fin n × Fin n)),
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l := by
  refine (Finset.sum_subset (Finset.subset_univ _) fun p _ hp ↦ ?_).symm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  rw [gaussianEnsemble_single_apply_eq_zero hp.1 hp.2, zero_mul]

private theorem sum_gaussianEnsemble_single_apply_mul_of_lt_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {i j : Fin n} (hij : i < j) (k l : Fin n) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l =
      if i = l ∧ j = k then (n : ℂ)⁻¹ else 0 := by
  rw [sum_gaussianEnsemble_single_apply_mul_eq_pair,
    Finset.sum_pair (fun h ↦ hij.ne (Prod.mk.inj h).1)]
  by_cases h1 : k = j ∧ l = i
  · rcases h1 with ⟨rfl, rfl⟩
    simp only [gaussianEnsemble_apply_of_lt_of_ne_one _ hβ hij,
      gaussianEnsemble_apply_of_gt_of_ne_one _ hβ hij, Pi.single_apply, Prod.mk.injEq, hij.ne,
      hij.ne', and_self, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_zero, mul_one,
      mul_zero, add_zero, zero_add, sub_zero, zero_sub, div_eq_mul_inv]
    linear_combination (1 - Complex.I * Complex.I) *
        ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) * inv_sqrt_two_sq + inv_sqrt_nat_sq n -
      ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) * (2 : ℂ)⁻¹ * Complex.I_mul_I
  · by_cases h2 : k = i ∧ l = j
    · rcases h2 with ⟨rfl, rfl⟩
      simp only [gaussianEnsemble_apply_of_lt_of_ne_one _ hβ hij, Pi.single_apply, Prod.mk.injEq,
        hij.ne, hij.ne', and_self, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_zero,
        mul_one, mul_zero, add_zero, zero_add, div_eq_mul_inv]
      linear_combination ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) *
        ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * Complex.I_mul_I
    · rw [gaussianEnsemble_single_apply_eq_zero
          (fun h ↦ h2 ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)
          (fun h ↦ h1 ⟨(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1.symm⟩),
        gaussianEnsemble_single_apply_eq_zero
          (fun h ↦ h1 ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)
          (fun h ↦ h2 ⟨(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1.symm⟩)]
      simp [show ¬ (i = l ∧ j = k) from fun ⟨hil, hjk⟩ ↦ h1 ⟨hjk.symm, hil.symm⟩]

private theorem sum_gaussianEnsemble_single_apply_mul_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (i j k l : Fin n) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l =
      if i = l ∧ j = k then (n : ℂ)⁻¹ else 0 := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact sum_gaussianEnsemble_single_apply_mul_of_lt_of_ne_one hβ hij k l
  · rw [sum_gaussianEnsemble_single_apply_mul_eq_pair, Finset.pair_eq_singleton,
      Finset.sum_singleton]
    by_cases hkl : k = i ∧ l = i
    · rcases hkl with ⟨rfl, rfl⟩; simp [hβ, inv_sqrt_nat_sq]
    · rw [gaussianEnsemble_single_apply_eq_zero
          (fun h ↦ hkl ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)
          (fun h ↦ hkl ⟨(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1.symm⟩), mul_zero]
      simp [show ¬ (i = l ∧ i = k) from fun ⟨hil, hik⟩ ↦ hkl ⟨hik.symm, hil.symm⟩]
  · have h := congrArg star (sum_gaussianEnsemble_single_apply_mul_of_lt_of_ne_one hβ hji l k)
    have hstar : ∀ p a b, star (gaussianEnsemble β n (Pi.single p 1) b a) =
        gaussianEnsemble β n (Pi.single p 1) a b := fun p a b ↦ by
      simpa [conjTranspose_apply] using
        congr_fun₂ (isHermitian_gaussianEnsemble β n (Pi.single p 1)).eq a b
    rw [show star (∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) j i * gaussianEnsemble β n (Pi.single p 1) l k) =
        ∑ p : Fin n × Fin n,
          gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l by
      rw [star_sum]; exact Finset.sum_congr rfl fun p _ ↦ by
        rw [star_mul', hstar, hstar, mul_comm]] at h
    refine h.trans ?_
    by_cases hc : i = l ∧ j = k
    · rcases hc with ⟨rfl, rfl⟩; simp [RCLike.star_def, ← Complex.ofReal_natCast]
    · simp [hc, show ¬ (j = k ∧ i = l) from fun ⟨h1, h2⟩ ↦ hc ⟨h2, h1⟩]

private theorem sum_gaussianEnsemble_single_apply_mul_of_lt_of_eq_one {β n : ℕ} (hβ : β = 1)
    {i j : Fin n} (hij : i < j) (k l : Fin n) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l =
      (n : ℂ)⁻¹ * ((if i = l ∧ j = k then 1 else 0) + (if i = k ∧ j = l then 1 else 0)) := by
  rw [sum_gaussianEnsemble_single_apply_mul_eq_pair,
    Finset.sum_pair (fun h ↦ hij.ne (Prod.mk.inj h).1)]
  have hzero : gaussianEnsemble β n (Pi.single (j, i) 1) i j = 0 := by
    simp [gaussianEnsemble_apply_of_lt_of_eq_one _ hβ hij, hij.ne]
  rw [hzero, zero_mul, add_zero]
  by_cases h1 : k = j ∧ l = i
  · rcases h1 with ⟨rfl, rfl⟩
    simp [gaussianEnsemble_apply_of_lt_of_eq_one _ hβ hij,
      gaussianEnsemble_apply_of_gt_of_eq_one _ hβ hij, hij.ne, inv_sqrt_nat_sq]
  · by_cases h2 : k = i ∧ l = j
    · rcases h2 with ⟨rfl, rfl⟩
      simp [gaussianEnsemble_apply_of_lt_of_eq_one _ hβ hij, hij.ne, inv_sqrt_nat_sq]
    · rw [gaussianEnsemble_single_apply_eq_zero
          (fun h ↦ h2 ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)
          (fun h ↦ h1 ⟨(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1.symm⟩), mul_zero]
      simp [show ¬ (i = l ∧ j = k) from fun ⟨hil, hjk⟩ ↦ h1 ⟨hjk.symm, hil.symm⟩,
        show ¬ (i = k ∧ j = l) from fun ⟨hik, hjl⟩ ↦ h2 ⟨hik.symm, hjl.symm⟩]

private theorem sum_gaussianEnsemble_single_apply_mul_of_eq_one {β n : ℕ} (hβ : β = 1)
    (i j k l : Fin n) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l =
      (n : ℂ)⁻¹ * ((if i = l ∧ j = k then 1 else 0) + (if i = k ∧ j = l then 1 else 0)) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact sum_gaussianEnsemble_single_apply_mul_of_lt_of_eq_one hβ hij k l
  · rw [sum_gaussianEnsemble_single_apply_mul_eq_pair, Finset.pair_eq_singleton,
      Finset.sum_singleton]
    by_cases hkl : k = i ∧ l = i
    · rcases hkl with ⟨rfl, rfl⟩
      simp only [gaussianEnsemble_apply_self_of_eq_one _ hβ, Pi.single_eq_same, mul_one,
        and_self, ↓reduceIte]
      linear_combination (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * inv_sqrt_nat_sq n +
        (n : ℂ)⁻¹ * sqrt_two_sq
    · rw [gaussianEnsemble_single_apply_eq_zero
          (fun h ↦ hkl ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)
          (fun h ↦ hkl ⟨(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1.symm⟩), mul_zero]
      simp [show ¬ (i = l ∧ i = k) from fun ⟨hil, hik⟩ ↦ hkl ⟨hik.symm, hil.symm⟩,
        show ¬ (i = k ∧ i = l) from fun ⟨hik, hil⟩ ↦ hkl ⟨hik.symm, hil.symm⟩]
  · simp_rw [show ∀ p, gaussianEnsemble β n (Pi.single p 1) i j =
        gaussianEnsemble β n (Pi.single p 1) j i from
      fun p ↦ (isSymm_gaussianEnsemble_of_eq_one hβ (Pi.single p 1)).apply j i]
    rw [sum_gaussianEnsemble_single_apply_mul_of_lt_of_eq_one hβ hji k l, add_comm]
    congr 2 <;> exact if_congr and_comm rfl rfl

private theorem sum_sum_ite_eq' {n : ℕ} (a b : Fin n) (f : Fin n → Fin n → ℂ) :
    (∑ k : Fin n, ∑ l : Fin n, if a = k ∧ b = l then f k l else 0) = f a b := by
  rw [Finset.sum_eq_single a (fun k _ hk ↦ Finset.sum_eq_zero fun l _ ↦ by simp [hk.symm])
    (fun h ↦ (h (Finset.mem_univ a)).elim),
    Finset.sum_eq_single b (fun l _ hl ↦ by simp [hl.symm])
    (fun h ↦ (h (Finset.mem_univ b)).elim)]; simp

private theorem sum_sum_ite_eq {n : ℕ} (a b : Fin n) (f : Fin n → Fin n → ℂ) :
    (∑ k : Fin n, ∑ l : Fin n, if b = l ∧ a = k then f k l else 0) = f a b := by
  simp_rw [and_comm (a := b = _)]; exact sum_sum_ite_eq' a b f

private theorem trace_mul_eq_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A * B).trace = ∑ i : Fin n, ∑ j : Fin n, A j i * B i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]; exact Finset.sum_comm

private theorem sum_single_mul_self_apply (β n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (i l : Fin n) :
    (∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1)) i l =
      ∑ j : Fin n, ∑ k : Fin n, M j k * ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm.trans <| Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun p _ ↦ by ring).trans Finset.sum_comm

/-- **GUE Casimir identity**: for `β ≠ 1` and any `M`, `∑ p, Eₚ * M * Eₚ = (n⁻¹ * M.trace) • 1`. -/
theorem sum_gaussianEnsemble_single_mul_self_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      ((n : ℂ)⁻¹ * M.trace) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i l; rw [sum_single_mul_self_apply]
  simp_rw [sum_gaussianEnsemble_single_apply_mul_of_ne_one hβ]
  by_cases hil : i = l <;> simp [hil, Matrix.trace, Finset.mul_sum, mul_comm]

/-- **GOE Casimir identity**: for `β = 1` and any `M`,
`∑ p, Eₚ * M * Eₚ = n⁻¹ • (M.trace • 1 + Mᵀ)`. -/
theorem sum_gaussianEnsemble_single_mul_self_of_eq_one {β n : ℕ} (hβ : β = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (M.trace • (1 : Matrix (Fin n) (Fin n) ℂ) + Mᵀ) := by
  ext i l; rw [sum_single_mul_self_apply]
  simp_rw [sum_gaussianEnsemble_single_apply_mul_of_eq_one hβ, ← mul_assoc,
    mul_comm (M _ _) (n : ℂ)⁻¹, mul_assoc, ← Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  have h1 : (∑ j : Fin n, ∑ k : Fin n, M j k * if i = l ∧ j = k then (1 : ℂ) else 0) =
      if i = l then M.trace else 0 := by by_cases hil : i = l <;> simp [hil, Matrix.trace]
  have h2 : (∑ j : Fin n, ∑ k : Fin n, M j k * if i = k ∧ j = l then (1 : ℂ) else 0) = M l i := by
    simp_rw [mul_ite, mul_one, mul_zero, eq_comm (a := _) (b := l)]
    exact sum_sum_ite_eq l i M
  rw [h1, h2]; simp [Matrix.one_apply]

private theorem sum_trace_mul_eq_sum_cov (β n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (X j i * Y l k) * ∑ p : Fin n × Fin n,
          gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l := by
  have hexp : ∀ p : Fin n × Fin n,
      (X * gaussianEnsemble β n (Pi.single p 1)).trace *
        (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, (X j i * Y l k) *
        (gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l) :=
    fun p ↦ by
      rw [trace_mul_eq_sum, trace_mul_eq_sum, Finset.sum_mul]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  simp_rw [hexp, Finset.mul_sum]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm.trans <| Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm

/-- **GUE trace inner-product identity** for `β ≠ 1`. -/
theorem sum_trace_mul_gaussianEnsemble_single_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      (n : ℂ)⁻¹ * (X * Y).trace := by
  rw [sum_trace_mul_eq_sum_cov]
  have hinner : ∀ i j : Fin n, (∑ k : Fin n, ∑ l : Fin n, (X j i * Y l k) *
      ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l) =
      (n : ℂ)⁻¹ * (X j i * Y i j) := fun i j ↦ by
    simp_rw [sum_gaussianEnsemble_single_apply_mul_of_ne_one hβ, mul_ite, mul_zero]
    rw [sum_sum_ite_eq j i (fun k l ↦ X j i * Y l k * (n : ℂ)⁻¹)]; ring
  simp_rw [hinner, ← Finset.mul_sum, trace_mul_eq_sum]

/-- **GOE trace inner-product identity** for `β = 1`. -/
theorem sum_trace_mul_gaussianEnsemble_single_of_eq_one {β n : ℕ} (hβ : β = 1)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      (n : ℂ)⁻¹ * ((X * Y).trace + (X * Yᵀ).trace) := by
  rw [sum_trace_mul_eq_sum_cov]
  have hinner : ∀ i j : Fin n, (∑ k : Fin n, ∑ l : Fin n, (X j i * Y l k) *
      ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) i j * gaussianEnsemble β n (Pi.single p 1) k l) =
      (n : ℂ)⁻¹ * (X j i * Y i j + X j i * Y j i) := fun i j ↦ by
    simp_rw [sum_gaussianEnsemble_single_apply_mul_of_eq_one hβ, ← mul_assoc,
      mul_comm (X j i * Y _ _) (n : ℂ)⁻¹, mul_assoc, ← Finset.mul_sum, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [sum_sum_ite_eq j i (fun k l ↦ Y l k), sum_sum_ite_eq' i j (fun k l ↦ Y l k)]; ring
  simp_rw [hinner, ← Finset.mul_sum, Finset.sum_add_distrib, trace_mul_eq_sum, transpose_apply]

private theorem re_sum_trace_mul_gaussianEnsemble_single (β n : ℕ)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace).re =
      ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re := by
  have hreal : ∀ {A B : Matrix (Fin n) (Fin n) ℂ}, A.IsHermitian → B.IsHermitian →
      (((A * B).trace).re : ℂ) = (A * B).trace := fun hA hB ↦
    RCLike.conj_eq_iff_re.mp (by
      rw [← RCLike.star_def, ← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq,
        trace_mul_comm])
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hE := isHermitian_gaussianEnsemble β n (Pi.single p 1)
  conv_lhs => rw [← hreal hX hE, ← hreal hY hE]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Real-part GUE trace inner-product identity for Hermitian matrices `X, Y`. -/
theorem sum_re_trace_mul_gaussianEnsemble_single_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
           (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (n : ℝ)⁻¹ * (X * Y).trace.re := by
  rw [← re_sum_trace_mul_gaussianEnsemble_single β n hX hY,
    sum_trace_mul_gaussianEnsemble_single_of_ne_one hβ, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul]

/-- Real-part GOE trace inner-product identity for Hermitian matrices `X, Y`. -/
theorem sum_re_trace_mul_gaussianEnsemble_single_of_eq_one {β n : ℕ} (hβ : β = 1)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (n : ℝ)⁻¹ * ((X * Y).trace.re + (X * Yᵀ).trace.re) := by
  rw [← re_sum_trace_mul_gaussianEnsemble_single β n hX hY,
    sum_trace_mul_gaussianEnsemble_single_of_eq_one hβ, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.add_re]

private theorem eigenvalues₀_congr_mat {n : ℕ} {M₁ M₂ : Matrix (Fin n) (Fin n) ℂ}
    (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂)
    (k : Fin (Fintype.card (Fin n))) : h₁.eigenvalues₀ k = h₂.eigenvalues₀ k := by subst h; rfl

private theorem eigenvalues₀_add_gaussianEnsemble_line_eq {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v : Fin n × Fin n → ℝ)
    (k : Fin (Fintype.card (Fin n))) :
    (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k) =
      fun t : ℝ ↦ ((hA.add (isHermitian_gaussianEnsemble β n g)).add
        ((isHermitian_gaussianEnsemble β n v).smul (IsSelfAdjoint.all t))).eigenvalues₀ k :=
  funext fun t ↦ eigenvalues₀_congr_mat _ _
    (by rw [gaussianEnsemble_add, gaussianEnsemble_smul, add_assoc]) k

/-- At any `g` where `λₖ(A + gaussianEnsemble β n g)` is simple,
`g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` is `C^r` for every `r : ℕ∞ω`. -/
theorem contDiffAt_eigenvalues₀_add_gaussianEnsemble {β n : ℕ} {r : ℕ∞ω}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    ContDiffAt ℝ r (fun g' : Fin n × Fin n → ℝ ↦
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g := by
  let Φ : (Fin n × Fin n → ℝ) → selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
    fun g' ↦ ⟨A, hA.isSelfAdjoint⟩ + gaussianEnsembleSelfAdjointCLM β n g'
  have h_eq : ∀ g' j, (Φ g').2.isHermitian.eigenvalues₀ j =
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ j :=
    fun g' j ↦ eigenvalues₀_congr_mat (Φ g').2.isHermitian
      (hA.add (isHermitian_gaussianEnsemble β n g')) (by simp [Φ]) j
  rw [show (fun g' ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) =
      (fun X : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) ↦ X.2.isHermitian.eigenvalues₀ k) ∘ Φ from
    funext fun g' ↦ (h_eq g' k).symm]
  exact (contDiffAt_eigenvalues₀ fun j hj ↦ by rw [h_eq, h_eq]; exact hk j hj).comp g
    (contDiff_const.add (gaussianEnsembleSelfAdjointCLM β n).contDiff).contDiffAt

/-- Directional derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k` at `0`. -/
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
`0`. -/
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

/-- **GUE coordinate gradient bracket**: for `β ≠ 1` and simple sorted eigenvalues `λₖ, λₘ` of
`A + gaussianEnsemble β n g`, the inner product of their coordinate gradients is `n⁻¹ * δₖₘ`. -/
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
  simp_rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hk).deriv,
    (hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hm).deriv]
  rw [sum_re_trace_mul_gaussianEnsemble_single_of_ne_one hβ (hH.isHermitian_eigenprojector₀ k)
    (hH.isHermitian_eigenprojector₀ m)]
  by_cases hkm : k = m
  · subst hkm; simp [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀]
  · simp [hkm, hH.eigenprojector₀_mul_of_ne hkm]

/-- **GOE coordinate gradient bracket**: for `β = 1`, symmetric `A`, and simple sorted eigenvalues
`λₖ, λₘ` of `A + gaussianEnsemble β n g`, the gradient inner product is `2 * n⁻¹ * δₖₘ`. -/
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
  have hPm_symm : (hH.eigenprojector₀ m).IsSymm :=
    hH.isSymm_eigenprojector₀ (hA_symm.add (isSymm_gaussianEnsemble_of_eq_one hβ g)) hm
  simp_rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hk).deriv,
    (hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hm).deriv]
  rw [sum_re_trace_mul_gaussianEnsemble_single_of_eq_one hβ (hH.isHermitian_eigenprojector₀ k)
    (hH.isHermitian_eigenprojector₀ m), hPm_symm.eq]
  by_cases hkm : k = m
  · subst hkm; simp [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀]; ring
  · simp [hkm, hH.eigenprojector₀_mul_of_ne hkm]

/-- **Dyson Brownian motion diffusion bracket** (Anderson–Guionnet–Zeitouni Theorem 4.3.2): for
GOE (`β = 1`, symmetric `A`) and GUE (`β = 2`), the bracket equals `(2 / (β * n)) * δₖₘ`. -/
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
    · push_cast; rw [div_mul_eq_div_div, div_self two_ne_zero, one_div]
    · rfl

/-- **Dyson repulsion drift (coordinate half-Laplacian)** (Anderson–Guionnet–Zeitouni Theorem 4.3.2
and Lemma 4.3.4): `(1 / 2) * ∑ p, ∂ₚ²λₖ = n⁻¹ * ∑ j ≠ k, (λₖ - λⱼ)⁻¹`. -/
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
  simp_rw [iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hk,
    ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  suffices ∑ p : Fin n × Fin n,
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1) *
        hH.eigenprojector₀ j * gaussianEnsemble β n (Pi.single p 1)).trace.re = (n : ℝ)⁻¹ by
    rw [← Finset.mul_sum, this, mul_comm]
  rw [show ∑ p : Fin n × Fin n,
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1) *
        hH.eigenprojector₀ j * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (hH.eigenprojector₀ k * ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * hH.eigenprojector₀ j *
          gaussianEnsemble β n (Pi.single p 1)).trace.re by
    rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by simp only [Matrix.mul_assoc]]
  by_cases hβ1 : β = 1
  · have hPk_symm : (hH.eigenprojector₀ k).IsSymm := hH.isSymm_eigenprojector₀
      ((hβ.resolve_left (not_not.mpr hβ1)).add (isSymm_gaussianEnsemble_of_eq_one hβ1 g)) hk
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

end Probability

end TauCeti
