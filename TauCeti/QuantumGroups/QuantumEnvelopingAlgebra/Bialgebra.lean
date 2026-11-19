/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumEnvelopingAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Hom

import TauCeti.Algebra.BigOperators.NatAntidiagonal
import TauCeti.QuantumGroups.QuantumInteger.Laurent.Vandermonde
import Mathlib.Tactic.Module

/-!
# The bialgebra structure on `QuantumEnvelopingAlgebra`

For a symmetrizable Cartan datum `D` and **any** `q` in a field `K` (including roots of unity,
`q = ±1`, and `q = 0`), we construct the unconditional Drinfeld–Jimbo counit `counit D q`, coproduct
`comul D q`, `Bialgebra` instance, power coproducts `comul_e_pow` / `comul_f_pow`, divided-power
coproducts `comul_quantumDividedPower_e` / `comul_quantumDividedPower_f`, and `mapBialgHom`.

Because `QuantumEnvelopingAlgebra D q` uses the denominator-free quantum-binomial Serre relations
`serreElement`, coproduct compatibility uses only the integral multinomial interchange
`quantumBinomial_mul_mul_comm` and alternating Gaussian vanishing sums, with no quantum-factorial
nonvanishing hypothesis.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* G. Lusztig, *Quantum groups at roots of 1*, Geom. Dedicata 35 (1990), Proposition 4.8.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  278 (2015), Theorem 3.3.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti.QuantumEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

section Counit
variable (D : CartanDatum ι X Y) (q : K)
/-- The unconditional augmentation `ε : QuantumEnvelopingAlgebra D q →ₐ[K] K`. -/
def counit : QuantumEnvelopingAlgebra D q →ₐ[K] K :=
  lift
    { e _ := 0, f _ := 0, k _ := 1, k_zero := rfl, k_mul_k _ _ := mul_one 1
      k_mul_e _ _ := by simp, k_mul_f _ _ := by simp
      e_mul_f_sub_f_mul_e_self _ := by simp, e_mul_f_of_ne _ := rfl
      serre_e _ := serreElement_zero_right _ _ _, serre_f _ := serreElement_zero_right _ _ _ }
theorem counit_apply_e (i : ι) : counit D q (e D q i) = 0 := by simp [counit]
theorem counit_apply_f (i : ι) : counit D q (f D q i) = 0 := by simp [counit]
theorem counit_apply_k (y : Y) : counit D q (k D q y) = 1 := by simp [counit]
end Counit

/-- Symmetrizability cancellation `(q ^ dⱼ)^aⱼᵢ * (q ^ dᵢ)^(-aᵢⱼ) = 1` for `q ≠ 0`. -/
theorem pow_symmetrizer_zpow_cartan_mul_neg {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    (i j : ι) :
    (q ^ D.symmetrizer j) ^ D.cartan j i * (q ^ D.symmetrizer i) ^ (-D.cartan i j) = 1 := by
  rw [← zpow_natCast q, ← zpow_natCast q, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq,
    ← D.symmetrizer_mul_cartan, mul_neg, add_neg_cancel, zpow_zero]

section Coproduct
open Finset TensorProduct
open Algebra.TensorProduct (one_def tmul_mul_tmul tmul_pow)

private abbrev comulEGen (D : CartanDatum ι X Y) (q : K) (i : ι) :=
  e D q i ⊗ₜ[K] (1 : QuantumEnvelopingAlgebra D q) + simpleK D q i ⊗ₜ[K] e D q i
private abbrev comulETerm (D : CartanDatum ι X Y) (q : K) (i : ι) (a b : ℕ) :=
  (q ^ D.symmetrizer i) ^ (a * b) • ((e D q i ^ a * simpleK D q i ^ b) ⊗ₜ[K] (e D q i ^ b))

private theorem pow_mul_pow_mul_zpow {qᵢ : K} (hqᵢ : qᵢ ≠ 0) (m n : ℕ) (z w₁ w₂ : ℤ)
    (h : (m : ℤ) + n + z = w₁ + w₂) : qᵢ ^ m * qᵢ ^ n * qᵢ ^ z = qᵢ ^ w₁ * qᵢ ^ w₂ := by
  rw [← zpow_natCast qᵢ m, ← zpow_natCast qᵢ n, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ,
    ← zpow_add₀ hqᵢ, h]

private theorem comulEGen_pow {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    comulEGen D q i ^ r = ∑ p ∈ antidiagonal r,
      quantumBinomial (q ^ D.symmetrizer i) r p.1 • comulETerm D q i p.1 p.2 := by
  rcases eq_or_ne q 0 with rfl | hq
  · rcases r with _ | r
    · simp [comulETerm, one_def]
    · simp only [comulEGen, e_zero, zero_tmul, tmul_zero, add_zero, zero_pow r.succ_ne_zero]
      refine (sum_eq_zero fun p hp ↦ ?_).symm
      rcases eq_or_ne p.1 0 with h1 | h1
      · simp [comulETerm, zero_pow (by have := mem_antidiagonal.mp hp; omega : p.2 ≠ 0)]
      · simp [comulETerm, zero_pow h1]
  · have hcomm : (simpleK D q i ⊗ₜ[K] e D q i) *
        (e D q i ⊗ₜ[K] (1 : QuantumEnvelopingAlgebra D q)) =
        (q ^ D.symmetrizer i) ^ 2 • ((e D q i ⊗ₜ[K] 1) * (simpleK D q i ⊗ₜ[K] e D q i)) := by
      rw [tmul_mul_tmul, tmul_mul_tmul, mul_one, one_mul, simpleK_mul_e_self, smul_tmul']
    rw [comulEGen, add_pow_of_mul_eq_smul_mul (pow_ne_zero _ hq) hcomm,
      Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact sum_congr rfl fun _ _ ↦ by
      rw [comulETerm, tmul_pow, one_pow, tmul_pow, tmul_mul_tmul, one_mul, smul_smul, mul_comm]

private theorem simpleK_pow_mul_e_mul_e_pow {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    (i j : ι) (b₁ a₂ : ℕ) : simpleK D q i ^ b₁ * e D q j * e D q i ^ a₂ =
      (q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * D.cartan i j + 2 * (a₂ : ℤ) * b₁) •
        (e D q j * e D q i ^ a₂ * simpleK D q i ^ b₁) := by
  have hexp : (b₁ : ℤ) * ((D.symmetrizer i : ℤ) * D.cartan i j) +
      (a₂ : ℤ) * ((b₁ : ℤ) * (2 * (D.symmetrizer i : ℤ))) =
      (D.symmetrizer i : ℤ) * ((b₁ : ℤ) * D.cartan i j + 2 * (a₂ : ℤ) * b₁) := by ring
  rw [k_pow, k_mul_e, smul_mul_assoc, mul_assoc, k_mul_e_pow, mul_smul_comm, smul_smul,
    ← zpow_add₀ hq, ← k_pow, ← mul_assoc, map_nsmul, map_nsmul, D.pairing_root_simpleTorus,
    ← D.symmetrizer_mul_cartan, D.pairing_root_simpleTorus_self, nsmul_eq_mul, nsmul_eq_mul,
    hexp, zpow_mul, zpow_natCast]

private theorem simpleK_pow_mul_simpleK_mul_e_pow {D : CartanDatum ι X Y} {q : K}
    (i j : ι) (b₁ a₂ : ℕ) : simpleK D q i ^ b₁ * simpleK D q j * e D q i ^ a₂ =
      (q ^ D.symmetrizer i) ^ ((a₂ : ℤ) * (2 * (b₁ : ℤ) + D.cartan i j)) •
        (e D q i ^ a₂ * (simpleK D q j * simpleK D q i ^ b₁)) := by
  have hexp : (a₂ : ℤ) * ((b₁ : ℤ) * (2 * (D.symmetrizer i : ℤ)) +
      (D.symmetrizer i : ℤ) * D.cartan i j) =
      (D.symmetrizer i : ℤ) * ((a₂ : ℤ) * (2 * (b₁ : ℤ) + D.cartan i j)) := by ring
  rw [k_pow, k_mul_k, k_mul_e_pow, map_add, map_nsmul, D.pairing_root_simpleTorus_self,
    D.pairing_root_simpleTorus, nsmul_eq_mul, add_comm (b₁ • D.simpleTorus i), ← k_mul_k,
    ← k_pow, hexp, zpow_mul, zpow_natCast]

private theorem serreElement_comulE_eq_sum {D : CartanDatum ι X Y} {q : K} (i : ι) (N : ℕ)
    (z : QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q) :
    serreElement (q ^ D.symmetrizer i) N (comulEGen D q i) z =
      ∑ p ∈ antidiagonal N, quantumBinomial (q ^ D.symmetrizer i) N p.1 •
        ∑ u ∈ antidiagonal p.1, ∑ v ∈ antidiagonal p.2,
          ((-1 : K) ^ (u.1 + v.1) * quantumBinomial (q ^ D.symmetrizer i) p.1 u.1 *
            quantumBinomial (q ^ D.symmetrizer i) p.2 v.1) •
            (comulETerm D q i u.1 v.1 * z * comulETerm D q i u.2 v.2) := by
  set qᵢ : K := q ^ D.symmetrizer i; rw [serreElement_def]
  trans ∑ p ∈ antidiagonal N, ∑ u ∈ antidiagonal p.1, ∑ v ∈ antidiagonal p.2,
      ((-1 : K) ^ (u.1 + u.2) * quantumBinomial qᵢ (u.1 + u.2 + (v.1 + v.2)) (u.1 + u.2) *
        quantumBinomial qᵢ (u.1 + u.2) u.1 * quantumBinomial qᵢ (v.1 + v.2) v.1) •
        (comulETerm D q i u.1 u.2 * z * comulETerm D q i v.1 v.2)
  · refine sum_congr rfl fun p hp ↦ ?_
    rw [comulEGen_pow, comulEGen_pow, sum_mul, sum_mul, smul_sum]
    refine sum_congr rfl fun u hu ↦ ?_; rw [mul_sum, smul_sum]
    refine sum_congr rfl fun v hv ↦ ?_
    rw [mem_antidiagonal.mp hu, mem_antidiagonal.mp hv, mem_antidiagonal.mp hp]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; congr 1; ring
  · refine (Nat.sum_antidiagonal_sum_antidiagonal_comm N fun a₁ b₁ a₂ b₂ ↦
      ((-1 : K) ^ (a₁ + b₁) * quantumBinomial qᵢ (a₁ + b₁ + (a₂ + b₂)) (a₁ + b₁) *
        quantumBinomial qᵢ (a₁ + b₁) a₁ * quantumBinomial qᵢ (a₂ + b₂) a₂) •
        (comulETerm D q i a₁ b₁ * z * comulETerm D q i a₂ b₂)).trans ?_
    refine sum_congr rfl fun p hp ↦ ?_; rw [smul_sum]
    refine sum_congr rfl fun u hu ↦ ?_; rw [smul_sum]
    refine sum_congr rfl fun v hv ↦ ?_; rw [smul_smul]; congr 1
    have hcomm := quantumBinomial_mul_mul_comm qᵢ u.1 v.1 u.2 v.2
    rw [mem_antidiagonal.mp hu, mem_antidiagonal.mp hv, mem_antidiagonal.mp hp] at hcomm
    linear_combination (-1 : K) ^ (u.1 + v.1) * hcomm

private theorem comul_serreE_left {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (comulEGen D q i)
      (e D q j ⊗ₜ[K] (1 : QuantumEnvelopingAlgebra D q)) = 0 := by
  set qᵢ : K := q ^ D.symmetrizer i; have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  rw [serreElement_comulE_eq_sum]
  refine sum_eq_zero fun ⟨c, b⟩ hp ↦ (congrArg _ ?_).trans (smul_zero _)
  have hcb : c + b = serreLength D i j := mem_antidiagonal.mp hp
  trans (∑ v ∈ antidiagonal b, (-1 : K) ^ v.1 * qᵢ ^ (-((v.1 : ℤ) * ((b : ℤ) - 1))) *
        quantumBinomial qᵢ b v.1) •
      ∑ u ∈ antidiagonal c, ((-1 : K) ^ u.1 * quantumBinomial qᵢ c u.1 * qᵢ ^ ((u.2 : ℤ) * b)) •
        ((e D q i ^ u.1 * e D q j * e D q i ^ u.2 * simpleK D q i ^ b) ⊗ₜ[K] (e D q i ^ b))
  · rw [smul_sum]; refine sum_congr rfl fun ⟨a₁, a₂⟩ ha ↦ ?_
    rw [sum_smul]; refine sum_congr rfl fun ⟨b₁, b₂⟩ hb ↦ ?_
    have ha' : a₁ + a₂ = c := mem_antidiagonal.mp ha
    have hb' : b₁ + b₂ = b := mem_antidiagonal.mp hb
    simp only [comulETerm, smul_mul_assoc, mul_smul_comm, tmul_mul_tmul, mul_one, smul_smul]
    rw [mul_assoc (e D q i ^ a₁), mul_assoc (e D q i ^ a₁), ← mul_assoc (simpleK D q i ^ b₁ * _),
      simpleK_pow_mul_e_mul_e_pow hq, smul_mul_assoc, mul_smul_comm, mul_assoc (e D q j * _),
      ← pow_add (simpleK D q i), hb', ← pow_add (e D q i), hb', ← mul_assoc (e D q i ^ a₁),
      ← mul_assoc (e D q i ^ a₁), ← smul_tmul', smul_smul]; congr 1
    have hqpow := pow_mul_pow_mul_zpow hqᵢ (a₁ * b₁) (a₂ * b₂)
      ((b₁ : ℤ) * D.cartan i j + 2 * (a₂ : ℤ) * b₁) (-((b₁ : ℤ) * ((b : ℤ) - 1))) ((a₂ : ℤ) * b)
      (by rw [cartan_eq_one_sub_serreLength D hij, ← hcb, ← ha', ← hb']; push_cast; ring)
    rw [pow_add (-1 : K)]; dsimp only [qᵢ] at hqpow ⊢
    linear_combination ((-1 : K) ^ a₁ * (-1 : K) ^ b₁ *
      quantumBinomial (q ^ D.symmetrizer i) c a₁ *
      quantumBinomial (q ^ D.symmetrizer i) b b₁) * hqpow
  · rcases Nat.eq_zero_or_pos b with rfl | hb_pos
    · obtain rfl : c = serreLength D i j := by simpa using hcb
      simp only [Nat.cast_zero, mul_zero, zpow_zero, mul_one, pow_zero, smul_tmul', ← sum_tmul]
      rw [← serreElement_def, serre_e hij, smul_zero, zero_tmul]
    · rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        sum_neg_one_pow_mul_zpow_neg_mul_quantumBinomial hqᵢ hb_pos, zero_smul]

private theorem comul_serreE_right {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (comulEGen D q i)
      (simpleK D q j ⊗ₜ[K] e D q j) = 0 := by
  set qᵢ : K := q ^ D.symmetrizer i; have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  rw [serreElement_comulE_eq_sum]
  refine sum_eq_zero fun ⟨c, b⟩ hp ↦ (congrArg _ ?_).trans (smul_zero _)
  have hcb : c + b = serreLength D i j := mem_antidiagonal.mp hp
  rw [sum_comm]
  trans (∑ u ∈ antidiagonal c, (-1 : K) ^ u.1 * qᵢ ^ ((u.1 : ℤ) * ((c : ℤ) - 1)) *
        quantumBinomial qᵢ c u.1) •
      ∑ v ∈ antidiagonal b, ((-1 : K) ^ v.1 * quantumBinomial qᵢ b v.1 *
        qᵢ ^ ((c : ℤ) * ((v.1 : ℤ) + 1 - c))) •
        ((e D q i ^ c * (simpleK D q j * simpleK D q i ^ b)) ⊗ₜ[K]
          (e D q i ^ v.1 * e D q j * e D q i ^ v.2))
  · rw [smul_sum]; refine sum_congr rfl fun ⟨b₁, b₂⟩ hb ↦ ?_
    rw [sum_smul]; refine sum_congr rfl fun ⟨a₁, a₂⟩ ha ↦ ?_
    have ha' : a₁ + a₂ = c := mem_antidiagonal.mp ha
    have hb' : b₁ + b₂ = b := mem_antidiagonal.mp hb
    simp only [comulETerm, smul_mul_assoc, mul_smul_comm, tmul_mul_tmul, smul_smul]
    rw [mul_assoc (e D q i ^ a₁), mul_assoc (e D q i ^ a₁), ← mul_assoc (simpleK D q i ^ b₁ * _),
      simpleK_pow_mul_simpleK_mul_e_pow, smul_mul_assoc, mul_smul_comm, mul_assoc (e D q i ^ a₂),
      ← mul_assoc (e D q i ^ a₁), ← pow_add (e D q i), ha', mul_assoc (simpleK D q j),
      ← pow_add (simpleK D q i), hb', ← smul_tmul', smul_smul]; congr 1
    have hqpow := pow_mul_pow_mul_zpow hqᵢ (a₁ * b₁) (a₂ * b₂)
      ((a₂ : ℤ) * (2 * (b₁ : ℤ) + D.cartan i j)) ((a₁ : ℤ) * ((c : ℤ) - 1))
      ((c : ℤ) * ((b₁ : ℤ) + 1 - c))
      (by rw [cartan_eq_one_sub_serreLength D hij, ← hcb, ← ha', ← hb']; push_cast; ring)
    rw [pow_add (-1 : K)]; dsimp only [qᵢ] at hqpow ⊢
    linear_combination ((-1 : K) ^ a₁ * (-1 : K) ^ b₁ *
      quantumBinomial (q ^ D.symmetrizer i) c a₁ *
      quantumBinomial (q ^ D.symmetrizer i) b b₁) * hqpow
  · rcases Nat.eq_zero_or_pos c with rfl | hc_pos
    · obtain rfl : b = serreLength D i j := by simpa using hcb
      simp only [Nat.cast_zero, zero_mul, zpow_zero, mul_one, pow_zero, one_mul, ← tmul_smul,
        ← tmul_sum]
      rw [← serreElement_def, serre_e hij, smul_zero, tmul_zero]
    · rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        sum_neg_one_pow_mul_zpow_mul_quantumBinomial hqᵢ hc_pos, zero_smul]

variable (D : CartanDatum ι X Y) (q : K)

private theorem comul_serreE {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j)
      (comulEGen D q i) (comulEGen D q j) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [comulEGen]
  · rw [serreElement_add_right, comul_serreE_left hq hij, comul_serreE_right hq hij, add_zero]

private def swapChevalley :
    QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q ≃ₐ[K]
      QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q :=
  (Algebra.TensorProduct.comm K _ _).trans
    (Algebra.TensorProduct.congr (chevalleyEquiv D q) (chevalleyEquiv D q))

private theorem comul_serreF {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j)
      (f D q i ⊗ₜ[K] simpleKInv D q i + (1 : QuantumEnvelopingAlgebra D q) ⊗ₜ[K] f D q i)
      (f D q j ⊗ₜ[K] simpleKInv D q j + (1 : QuantumEnvelopingAlgebra D q) ⊗ₜ[K] f D q j) = 0 := by
  have hs : ∀ m, swapChevalley D q (comulEGen D q m) =
      f D q m ⊗ₜ[K] simpleKInv D q m + 1 ⊗ₜ[K] f D q m :=
    fun m ↦ by simp [swapChevalley, comulEGen, add_comm]
  rw [← hs i, ← hs j, ← map_serreElement (swapChevalley D q), comul_serreE D q hij, map_zero]

/-- The unconditional Drinfeld–Jimbo coproduct `Δ : U →ₐ[K] U ⊗[K] U`. -/
def comul : QuantumEnvelopingAlgebra D q →ₐ[K]
    QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q :=
  lift
    { e i := comulEGen D q i, f i := f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i
      k y := k D q y ⊗ₜ[K] k D q y, k_zero := by simp [one_def]
      k_mul_k y₁ y₂ := by simp [tmul_mul_tmul, k_mul_k]
      k_mul_e y i := by
        simp [comulEGen, mul_add, add_mul, tmul_mul_tmul, k_mul_e, (commute_k _ _).eq,
          smul_tmul', tmul_smul, smul_add]
      k_mul_f y i := by
        simp [mul_add, add_mul, tmul_mul_tmul, k_mul_f, (commute_k _ _).eq, smul_tmul',
          tmul_smul, smul_add]
      e_mul_f_sub_f_mul_e_self i := by
        rcases eq_or_ne q 0 with rfl | hq
        · simp [comulEGen, zero_pow (D.symmetrizer_pos i).ne']
        · simp only [comulEGen, mul_add, add_mul, tmul_mul_tmul, one_mul, mul_one]
          rw [simpleK_mul_f_self, e_mul_simpleKInv_self]
          simp only [smul_tmul, tmul_smul, smul_smul, inv_pow,
            mul_inv_cancel₀ (pow_ne_zero 2 (pow_ne_zero _ hq)), one_smul]
          trans (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] simpleKInv D q i +
              simpleK D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i)
          · simp only [sub_tmul, tmul_sub]; abel
          · rw [e_mul_f_sub_f_mul_e_self]
            simp only [smul_tmul, tmul_smul, sub_tmul, tmul_sub, smul_sub]; module
      e_mul_f_of_ne hij := by
        rcases eq_or_ne q 0 with rfl | hq
        · simp [comulEGen]
        · simp only [comulEGen, mul_add, add_mul, tmul_mul_tmul, one_mul, mul_one]
          rw [e_mul_f_of_ne hij, simpleK_mul_f, e_mul_simpleKInv]
          simp only [smul_tmul', tmul_smul, smul_smul]
          rw [pow_symmetrizer_zpow_cartan_mul_neg hq, one_smul]; abel
      serre_e hij := comul_serreE D q hij, serre_f hij := comul_serreF D q hij }

instance instBialgebra : Bialgebra K (QuantumEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comul D q) (counit D q)
    (by ext <;> simp [comul, comulEGen, tmul_add, add_tmul, add_assoc, one_def])
    (by ext <;> simp [comul, comulEGen, counit_apply_e, counit_apply_f, counit_apply_k])
    (by ext <;> simp [comul, comulEGen, counit_apply_e, counit_apply_f, counit_apply_k])

@[simp] theorem comul_apply (x : QuantumEnvelopingAlgebra D q) :
    comul D q x = Coalgebra.comul (R := K) x := (rfl)
@[simp] theorem counit_apply (x : QuantumEnvelopingAlgebra D q) :
    counit D q x = Coalgebra.counit (R := K) x := (rfl)
@[simp] theorem comul_e (i : ι) :
    Coalgebra.comul (R := K) (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i := by
  simp [← comul_apply, comul, comulEGen]
@[simp] theorem comul_f (i : ι) :
    Coalgebra.comul (R := K) (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i := by
  simp [← comul_apply, comul]
@[simp] theorem comul_k (y : Y) :
    Coalgebra.comul (R := K) (k D q y) = k D q y ⊗ₜ[K] k D q y := by simp [← comul_apply, comul]
@[simp] theorem counit_e (i : ι) : Coalgebra.counit (R := K) (e D q i) = 0 := counit_apply_e D q i
@[simp] theorem counit_f (i : ι) : Coalgebra.counit (R := K) (f D q i) = 0 := counit_apply_f D q i
@[simp] theorem counit_k (y : Y) : Coalgebra.counit (R := K) (k D q y) = 1 := counit_apply_k D q y

theorem comul_chevalleyEquiv (x : QuantumEnvelopingAlgebra D q) :
    Coalgebra.comul (R := K) (chevalleyEquiv D q x) =
      (Algebra.TensorProduct.comm K _ _).trans
        (Algebra.TensorProduct.congr (chevalleyEquiv D q) (chevalleyEquiv D q))
        (Coalgebra.comul (R := K) x) := by
  have h : (Bialgebra.comulAlgHom K (QuantumEnvelopingAlgebra D q)).comp
      (chevalleyEquiv D q).toAlgHom =
      (swapChevalley D q).toAlgHom.comp (Bialgebra.comulAlgHom K _) := by
    ext <;> simp [swapChevalley, add_comm]
  exact AlgHom.congr_fun h x

/-- Unconditional coproduct of `Eᵢ ^ r` for any `q : K` and `r : ℕ`. -/
theorem comul_e_pow (i : ι) (r : ℕ) :
    Coalgebra.comul (R := K) (e D q i ^ r) = ∑ p ∈ antidiagonal r,
      ((q ^ D.symmetrizer i) ^ (p.1 * p.2) * quantumBinomial (q ^ D.symmetrizer i) r p.1) •
        ((e D q i ^ p.1 * simpleK D q i ^ p.2) ⊗ₜ[K] (e D q i ^ p.2)) := by
  rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply, comul_e]
  simpa [comulETerm, smul_smul, mul_comm] using comulEGen_pow (D := D) (q := q) i r

/-- Unconditional coproduct of `Fᵢ ^ r` for any `q : K` and `r : ℕ`. -/
theorem comul_f_pow (i : ι) (r : ℕ) :
    Coalgebra.comul (R := K) (f D q i ^ r) = ∑ p ∈ antidiagonal r,
      ((q ^ D.symmetrizer i) ^ (p.1 * p.2) * quantumBinomial (q ^ D.symmetrizer i) r p.1) •
        ((f D q i ^ p.1) ⊗ₜ[K] (f D q i ^ p.2 * simpleKInv D q i ^ p.1)) := by
  have he : chevalleyEquiv D q (e D q i ^ r) = f D q i ^ r := by simp
  rw [← he, comul_chevalleyEquiv, comul_e_pow, map_sum, ← Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun p hp ↦ ?_
  have hps := mem_antidiagonal.mp hp
  have hsym := quantumBinomial_symm (q ^ D.symmetrizer i) (by omega : p.1 ≤ r)
  rw [← hps, Nat.add_sub_cancel_left, hps] at hsym; simp [hsym, mul_comm p.2 p.1]

theorem comul_quantumDividedPower_e {D : CartanDatum ι X Y} {q : K} {i : ι} {r : ℕ}
    (hr : quantumFactorial (q ^ D.symmetrizer i) r ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
      ∑ p ∈ antidiagonal r, (q ^ D.symmetrizer i) ^ (p.1 * p.2) •
        ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) p.1 * simpleK D q i ^ p.2) ⊗ₜ[K]
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) p.2) := by
  rw [quantumDividedPower_def, map_smul, comul_e_pow, smul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  have hps := mem_antidiagonal.mp hp
  simp only [quantumDividedPower_def, smul_mul_assoc, ← smul_tmul', tmul_smul, smul_smul]; congr 1
  rw [quantumBinomial_eq_div hr (by omega : p.1 ≤ r), ← hps, Nat.add_sub_cancel_left, hps,
    div_eq_mul_inv, mul_inv, mul_left_comm ((q ^ D.symmetrizer i) ^ _), ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ hr, one_mul]; ring

theorem comul_quantumDividedPower_f {D : CartanDatum ι X Y} {q : K} {i : ι} {r : ℕ}
    (hr : quantumFactorial (q ^ D.symmetrizer i) r ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) =
      ∑ p ∈ antidiagonal r, (q ^ D.symmetrizer i) ^ (p.1 * p.2) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) p.1 ⊗ₜ[K]
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) p.2 * simpleKInv D q i ^ p.1)) := by
  have he : chevalleyEquiv D q (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
      quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r := by simp
  rw [← he, comul_chevalleyEquiv, comul_quantumDividedPower_e hr, map_sum,
    ← Nat.sum_antidiagonal_swap]
  exact sum_congr rfl fun p _ ↦ by simp [mul_comm p.2 p.1]
end Coproduct

section Functoriality
variable {X' Y' X'' Y'' : Type*} [AddCommGroup X'] [AddCommGroup Y']
  [AddCommGroup X''] [AddCommGroup Y'']
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}
/-- Functorial bialgebra homomorphism induced by `φ : CartanDatum.Hom D D'`. -/
def mapBialgHom (φ : CartanDatum.Hom D D') (q : K) :
    QuantumEnvelopingAlgebra D q →ₐc[K] QuantumEnvelopingAlgebra D' q :=
  BialgHom.ofAlgHom (map φ q) (by ext <;> simp) (by ext <;> simp [φ.map_simpleTorus])
@[simp] theorem mapBialgHom_toAlgHom (φ : CartanDatum.Hom D D') (q : K) :
    (mapBialgHom φ q : QuantumEnvelopingAlgebra D q →ₐ[K] QuantumEnvelopingAlgebra D' q) =
      map φ q := (rfl)
@[simp] theorem mapBialgHom_apply (φ : CartanDatum.Hom D D') (q : K)
    (x : QuantumEnvelopingAlgebra D q) : mapBialgHom φ q x = map φ q x := (rfl)
@[simp] theorem mapBialgHom_id (D : CartanDatum ι X Y) (q : K) :
    mapBialgHom (CartanDatum.Hom.id D) q = BialgHom.id K (QuantumEnvelopingAlgebra D q) := by
  ext x; rw [mapBialgHom_apply, map_id]; rfl
theorem mapBialgHom_comp (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') (q : K) :
    mapBialgHom (ψ.comp φ) q = (mapBialgHom ψ q).comp (mapBialgHom φ q) := by
  ext x; simp [map_comp]
end Functoriality
end TauCeti.QuantumEnvelopingAlgebra
