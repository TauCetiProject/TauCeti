/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Cartier
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.ZMod
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Residue averaging on power series

The residue averaging operator on `𝔽_p⟦X⟧` is the alternating sum of the `p` Cartier
components. It is linear and continuous for the coefficientwise topology, and is a left
inverse of Frobenius. Its semilinearity computes it on every natural power of `1 + X`:
only powers divisible by `p` survive.

The operator and its identities follow Rodrigues Jacinto–Williams, *An Introduction to
$p$-adic $L$-functions*, §3.5.3–5 and Lemma 12.13. Its Cartier presentation follows
Rowland–Stipulanti–Yassawi, *An elementary proof of Bridy's theorem*, Section 3
(<https://arxiv.org/html/2308.10977v2>), and uses `PowerSeries.cartier`.
-/

public section

namespace TauCeti.IwasawaResidue

open PowerSeries

/-- Residue averaging modulo `p`, the alternating sum of the Cartier components. -/
noncomputable def residuePsi (p : ℕ) :
    PowerSeries (ZMod p) →ₗ[ZMod p] PowerSeries (ZMod p) :=
  ∑ i ∈ Finset.range p, (-1 : ZMod p) ^ i • cartier (ZMod p) p i

/-- The coefficient formula for residue averaging. -/
@[simp]
theorem coeff_residuePsi (p n : ℕ) (F : PowerSeries (ZMod p)) :
    (residuePsi p F).coeff n =
      ∑ i ∈ Finset.range p, (-1 : ZMod p) ^ i * F.coeff (p * n + i) := by
  simp [residuePsi]

@[simp]
theorem residuePsi_zero (p : ℕ) : residuePsi p 0 = 0 := map_zero _

@[simp]
theorem residuePsi_add (p : ℕ) (F G : PowerSeries (ZMod p)) :
    residuePsi p (F + G) = residuePsi p F + residuePsi p G := map_add _ _ _

theorem residuePsi_smul (p : ℕ) (a : ZMod p) (F : PowerSeries (ZMod p)) :
    residuePsi p (a • F) = a • residuePsi p F := map_smul _ _ _

open scoped PowerSeries.WithPiTopology

/-- Residue averaging is continuous for the coefficientwise topology. -/
theorem continuous_residuePsi (p : ℕ) : Continuous (residuePsi p) := by
  rw [continuous_iff_continuousAt]
  intro F
  apply (WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr
  intro n
  simp only [coeff_residuePsi]
  exact tendsto_finsetSum _ fun i _ ↦
    tendsto_const_nhds.mul (WithPiTopology.continuous_coeff (ZMod p) (p * n + i)).continuousAt

/-- Below degree `p`, residue averaging is evaluation at `-1`, as a constant series. -/
theorem residuePsi_coe_polynomial_of_natDegree_lt (p : ℕ) (P : Polynomial (ZMod p))
    (hP : P.natDegree < p) :
    residuePsi p (P : PowerSeries (ZMod p)) = C (P.eval (-1)) := by
  ext n
  rw [coeff_residuePsi]
  rcases n with _ | n
  · simp only [Nat.mul_zero, zero_add, Polynomial.coeff_coe, coeff_C, ↓reduceIte]
    rw [Polynomial.eval_eq_sum_range' hP]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  · rw [coeff_C, ite_eq_right (Nat.succ_ne_zero n)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    nlinarith

variable {p : ℕ} [Fact p.Prime]

/-- A monomial retains its quotient exponent, weighted by the parity of its residue. -/
@[simp]
theorem residuePsi_monomial (m : ℕ) (a : ZMod p) :
    residuePsi p (monomial m a) =
      monomial (m / p) ((-1 : ZMod p) ^ (m % p) * a) := by
  classical
  simp only [residuePsi, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun i hi ↦ congrArg (fun F ↦ (-1 : ZMod p) ^ i • F)
    (cartier_monomial p i m (Fact.out : p.Prime).ne_zero (Finset.mem_range.mp hi) a)]
  simp [Nat.mod_lt m (Fact.out : p.Prime).pos, ← map_smul]

/-- Residue averaging fixes the constant series one. -/
@[simp]
theorem residuePsi_one : residuePsi p 1 = 1 := by
  simpa using residuePsi_monomial (p := p) 0 1

/-- Multiplication by a series expanded by `p` passes through residue averaging. -/
theorem residuePsi_expand_mul (F G : PowerSeries (ZMod p)) :
    residuePsi p (expand p (Fact.out : p.Prime).ne_zero F * G) =
      F * residuePsi p G := by
  classical
  simp only [residuePsi, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cartier_expand_mul p i (Fact.out : p.Prime).ne_zero (Finset.mem_range.mp hi)]
  exact (mul_smul_comm _ _ _).symm

/-- Residue averaging is a left inverse to expansion by `p`. -/
@[simp]
theorem residuePsi_expand (F : PowerSeries (ZMod p)) :
    residuePsi p (expand p (Fact.out : p.Prime).ne_zero F) = F := by
  simpa using residuePsi_expand_mul F 1

/-- Frobenius semilinearity of residue averaging over the prime field. -/
theorem residuePsi_pow_mul (F G : PowerSeries (ZMod p)) :
    residuePsi p (F ^ p * G) = F * residuePsi p G := by
  have h := FiniteField.PowerSeries.expand_card F
  simp only [ZMod.card] at h
  rw [← h]
  exact residuePsi_expand_mul F G

/-- Residue averaging is a left inverse to Frobenius. -/
@[simp]
theorem residuePsi_pow (F : PowerSeries (ZMod p)) : residuePsi p (F ^ p) = F := by
  simpa using residuePsi_pow_mul F 1

/-- Among the powers of `1 + X` with exponent below `p`, only the constant survives. -/
@[simp]
theorem residuePsi_one_add_X_pow_of_lt (i : ℕ) (hi : i < p) :
    residuePsi p ((1 + X : PowerSeries (ZMod p)) ^ i) = if i = 0 then 1 else 0 := by
  have hdeg : ((1 + Polynomial.X : Polynomial (ZMod p)) ^ i).natDegree < p := by
    simpa using hi
  simpa [zero_pow_eq] using residuePsi_coe_polynomial_of_natDegree_lt p
    ((1 + Polynomial.X : Polynomial (ZMod p)) ^ i) hdeg

/-- Residue averaging divides an exponent of `1 + X` by `p` when divisible, and is zero
otherwise. -/
@[simp]
theorem residuePsi_one_add_X_pow (n : ℕ) :
    residuePsi p ((1 + X : PowerSeries (ZMod p)) ^ n) =
      if p ∣ n then (1 + X) ^ (n / p) else 0 := by
  conv_lhs => rw [← Nat.mod_add_div n p, pow_add, Nat.mul_comm p, pow_mul, mul_comm]
  rw [residuePsi_pow_mul, residuePsi_one_add_X_pow_of_lt _
    (Nat.mod_lt n (Fact.out : p.Prime).pos)]
  simp [Nat.dvd_iff_mod_eq_zero]

/-! These examples distinguish the weighted operator from the residue-zero Cartier operator,
and check the characteristic-two boundary. -/

example : residuePsi 3 ((X : PowerSeries (ZMod 3)) ^ 3) = X := by simp

example : residuePsi 3 ((X : PowerSeries (ZMod 3)) ^ 2) = 1 := by simp [X_pow_eq]

example : residuePsi 3 (X : PowerSeries (ZMod 3)) = -1 := by simp [X_eq]

example : residuePsi 2 (X : PowerSeries (ZMod 2)) = 1 := by simp [X_eq]

end TauCeti.IwasawaResidue
