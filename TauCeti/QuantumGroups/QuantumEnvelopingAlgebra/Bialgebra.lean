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

For a symmetrizable Cartan datum `D` and `q` in a field `K`, we define the unconditional counit
`counit D q` and, under the sharp condition `IsSerreRegular D q` (`q = 0` or `[1 - aᵢⱼ]_{qᵢ}! ≠ 0`
for `i ≠ j`), construct the Drinfeld–Jimbo coproduct `comul D q`, `Bialgebra` instance,
divided-power coproducts `comul_quantumDividedPower_e` / `comul_quantumDividedPower_f`, and
`mapBialgHom`.

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

/-- The unconditional augmentation `ε : QuantumEnvelopingAlgebra D q →ₐ[K] K`. -/
def counit (D : CartanDatum ι X Y) (q : K) : QuantumEnvelopingAlgebra D q →ₐ[K] K :=
  lift
    { e _ := 0, f _ := 0, k _ := 1
      k_zero := rfl
      k_mul_k _ _ := mul_one 1
      k_mul_e _ _ := by simp
      k_mul_f _ _ := by simp
      e_mul_f_sub_f_mul_e_self _ := by simp
      e_mul_f_of_ne _ := rfl
      serre_e _ := serreElement_zero_right _ _ _
      serre_f _ := serreElement_zero_right _ _ _ }

@[simp] theorem counit_apply_e (D : CartanDatum ι X Y) (q : K) (i : ι) :
    counit D q (e D q i) = 0 := by simp [counit]
@[simp] theorem counit_apply_f (D : CartanDatum ι X Y) (q : K) (i : ι) :
    counit D q (f D q i) = 0 := by simp [counit]
@[simp] theorem counit_apply_k (D : CartanDatum ι X Y) (q : K) (y : Y) :
    counit D q (k D q y) = 1 := by simp [counit]

/-- Symmetrizability cancellation `(q ^ dⱼ)^aⱼᵢ * (q ^ dᵢ)^(-aᵢⱼ) = 1` for `q ≠ 0`. -/
theorem pow_symmetrizer_zpow_cartan_mul_neg {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    (i j : ι) :
    (q ^ D.symmetrizer j) ^ D.cartan j i * (q ^ D.symmetrizer i) ^ (-D.cartan i j) = 1 := by
  rw [← zpow_natCast q, ← zpow_natCast q, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq,
    ← D.symmetrizer_mul_cartan, mul_neg, add_neg_cancel, zpow_zero]

/-- Sharp regularity condition on `(D, q)` under which `Δ` respects the quantum Serre relations:
either `q = 0` or every off-diagonal Serre factorial `[1 - aᵢⱼ]_{qᵢ}!` is nonzero. -/
class IsSerreRegular (D : CartanDatum ι X Y) (q : K) : Prop where
  /-- Either `q = 0` or `[serreLength D i j]_{qᵢ}! ≠ 0` for all `i ≠ j`. -/
  out : q = 0 ∨ ∀ ⦃i j : ι⦄, i ≠ j →
    quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0

instance instIsSerreRegularZero (D : CartanDatum ι X Y) : IsSerreRegular D (0 : K) := ⟨Or.inl rfl⟩
instance instIsSerreRegularOfSubsingleton (D : CartanDatum ι X Y) (q : K) [Subsingleton ι] :
    IsSerreRegular D q := ⟨Or.inr fun _ _ hij ↦ (hij (Subsingleton.elim _ _)).elim⟩

theorem IsSerreRegular.of_isGenericQuantumParameter (D : CartanDatum ι X Y) {q : K}
    (hq : IsGenericQuantumParameter q) : IsSerreRegular D q :=
  ⟨Or.inr fun i _ _ ↦ quantumFactorial_ne_zero (hq.pow (D.symmetrizer_pos i)) _⟩

instance instIsSerreRegularOfGeneric (D : CartanDatum ι X Y) (q : K)
    [Fact (IsGenericQuantumParameter q)] : IsSerreRegular D q :=
  .of_isGenericQuantumParameter D Fact.out

instance instIsSerreRegularOfNat [CharZero K] (D : CartanDatum ι X Y) (n : ℕ) [n.AtLeastTwo] :
    IsSerreRegular D (OfNat.ofNat n : K) := by
  refine .of_isGenericQuantumParameter D
    (isGenericQuantumParameter_iff.mpr ⟨OfNat.ofNat_ne_zero n, fun r hr hpow ↦ ?_⟩)
  rw [← Nat.cast_ofNat, ← Nat.cast_pow, ← Nat.cast_one, Nat.cast_inj] at hpow
  exact (Nat.one_lt_pow hr.ne' Nat.AtLeastTwo.prop).ne' hpow

theorem IsSerreRegular.of_hom {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (q : K)
    [IsSerreRegular D q] : IsSerreRegular D' q := by
  rcases IsSerreRegular.out (D := D) (q := q) with rfl | h
  · exact ⟨Or.inl rfl⟩
  · refine ⟨Or.inr fun i j hij ↦ ?_⟩
    rw [φ.symmetrizer_eq, ← serreLength_eq_of_hom φ]; exact h hij

section Coproduct

private abbrev eDP (D : CartanDatum ι X Y) (q : K) (i : ι) (r : ℕ) :=
  quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r

private abbrev comulEGen (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q :=
  e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i

private abbrev comulETerm (D : CartanDatum ι X Y) (q : K) (i : ι) (a b : ℕ) :
    QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q :=
  (q ^ D.symmetrizer i) ^ (a * b) • ((eDP D q i a * simpleK D q i ^ b) ⊗ₜ[K] eDP D q i b)

private theorem pow_mul_pow_mul_zpow {qᵢ : K} (hqᵢ : qᵢ ≠ 0) (m n : ℕ) (z w₁ w₂ : ℤ)
    (h : (m : ℤ) + n + z = w₁ + w₂) : qᵢ ^ m * qᵢ ^ n * qᵢ ^ z = qᵢ ^ w₁ * qᵢ ^ w₂ := by
  rw [← zpow_natCast qᵢ m, ← zpow_natCast qᵢ n, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ,
    ← zpow_add₀ hqᵢ, h]

private theorem quantumDividedPower_comulE {D : CartanDatum ι X Y} {q : K} {i : ι} {r : ℕ}
    (hr : quantumFactorial (q ^ D.symmetrizer i) r ≠ 0) :
    quantumDividedPower (q ^ D.symmetrizer i) (comulEGen D q i) r =
      ∑ p ∈ Finset.antidiagonal r, comulETerm D q i p.1 p.2 := by
  have hcomm : (simpleK D q i ⊗ₜ[K] e D q i) * (e D q i ⊗ₜ[K] (1 : QuantumEnvelopingAlgebra D q)) =
      (q ^ D.symmetrizer i) ^ 2 • ((e D q i ⊗ₜ[K] 1) * (simpleK D q i ⊗ₜ[K] e D q i)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, simpleK_mul_e_self, TensorProduct.smul_tmul']
  rw [comulEGen, quantumDividedPower_add hcomm hr]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg _ ?_
  rw [quantumDividedPower_def, quantumDividedPower_def, Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_pow, TensorProduct.smul_tmul', ← TensorProduct.tmul_smul,
    ← quantumDividedPower_def, ← quantumDividedPower_def, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]

private theorem simpleK_pow_mul_e_mul_eDP {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    (i j : ι) (b₁ a₂ : ℕ) :
    simpleK D q i ^ b₁ * e D q j * eDP D q i a₂ =
      (q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * D.cartan i j + 2 * (a₂ : ℤ) * b₁) •
        (e D q j * eDP D q i a₂ * simpleK D q i ^ b₁) := by
  have hexp : (b₁ : ℤ) * ((D.symmetrizer i : ℤ) * D.cartan i j) +
      (a₂ : ℤ) * ((b₁ : ℤ) * (2 * (D.symmetrizer i : ℤ))) =
      (D.symmetrizer i : ℤ) * ((b₁ : ℤ) * D.cartan i j + 2 * (a₂ : ℤ) * b₁) := by ring
  rw [k_pow, k_mul_e, smul_mul_assoc, mul_assoc, k_mul_quantumDividedPower_e, mul_smul_comm,
    smul_smul, ← zpow_add₀ hq, ← k_pow, ← mul_assoc, map_nsmul, map_nsmul,
    D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, D.pairing_root_simpleTorus_self,
    nsmul_eq_mul, nsmul_eq_mul, hexp, zpow_mul, zpow_natCast]

private theorem simpleK_pow_mul_simpleK_mul_eDP {D : CartanDatum ι X Y} {q : K}
    (i j : ι) (b₁ a₂ : ℕ) :
    simpleK D q i ^ b₁ * simpleK D q j * eDP D q i a₂ =
      (q ^ D.symmetrizer i) ^ ((a₂ : ℤ) * (2 * (b₁ : ℤ) + D.cartan i j)) •
        (eDP D q i a₂ * (simpleK D q j * simpleK D q i ^ b₁)) := by
  have hexp : (a₂ : ℤ) * ((b₁ : ℤ) * (2 * (D.symmetrizer i : ℤ)) +
      (D.symmetrizer i : ℤ) * D.cartan i j) =
      (D.symmetrizer i : ℤ) * ((a₂ : ℤ) * (2 * (b₁ : ℤ) + D.cartan i j)) := by ring
  rw [k_pow, k_mul_k, k_mul_quantumDividedPower_e, map_add, map_nsmul,
    D.pairing_root_simpleTorus_self, D.pairing_root_simpleTorus, nsmul_eq_mul,
    add_comm (b₁ • D.simpleTorus i), ← k_mul_k, ← k_pow, hexp, zpow_mul, zpow_natCast]

private theorem serreElement_comulE_eq_sum {D : CartanDatum ι X Y} {q : K} {i : ι} {N : ℕ}
    (hN : quantumFactorial (q ^ D.symmetrizer i) N ≠ 0)
    (z : QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q) :
    serreElement (q ^ D.symmetrizer i) N (comulEGen D q i) z =
      ∑ p ∈ Finset.antidiagonal N, ∑ u ∈ Finset.antidiagonal p.1, ∑ v ∈ Finset.antidiagonal p.2,
        (-1 : K) ^ (u.1 + v.1) • (comulETerm D q i u.1 v.1 * z * comulETerm D q i u.2 v.2) := by
  rw [serreElement_def]
  have hexpand : ∀ p ∈ Finset.antidiagonal N,
      (-1 : K) ^ p.1 • (quantumDividedPower (q ^ D.symmetrizer i) (comulEGen D q i) p.1 * z *
        quantumDividedPower (q ^ D.symmetrizer i) (comulEGen D q i) p.2) =
      ∑ u ∈ Finset.antidiagonal p.1, ∑ v ∈ Finset.antidiagonal p.2,
        (-1 : K) ^ (u.1 + u.2) • (comulETerm D q i u.1 u.2 * z * comulETerm D q i v.1 v.2) := by
    intro p hp; have := Finset.mem_antidiagonal.mp hp
    rw [quantumDividedPower_comulE (quantumFactorial_ne_zero_of_le (by omega) hN),
      quantumDividedPower_comulE (quantumFactorial_ne_zero_of_le (by omega) hN),
      Finset.sum_mul, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [Finset.mul_sum, Finset.smul_sum, Finset.mem_antidiagonal.mp hu]
  rw [Finset.sum_congr rfl hexpand]
  exact Finset.Nat.sum_antidiagonal_sum_antidiagonal_comm N fun a₁ b₁ a₂ b₂ ↦
    (-1 : K) ^ (a₁ + b₁) • (comulETerm D q i a₁ b₁ * z * comulETerm D q i a₂ b₂)

private theorem comul_serreE_left {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    {i j : ι} (hij : i ≠ j)
    (hN : quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (comulEGen D q i)
      (e D q j ⊗ₜ[K] (1 : QuantumEnvelopingAlgebra D q)) = 0 := by
  set qᵢ : K := q ^ D.symmetrizer i
  have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  rw [serreElement_comulE_eq_sum hN]
  refine Finset.sum_eq_zero fun ⟨c, b⟩ hp ↦ ?_
  have hcb : c + b = serreLength D i j := Finset.mem_antidiagonal.mp hp
  have hbf : quantumFactorial qᵢ b ≠ 0 := quantumFactorial_ne_zero_of_le (by omega) hN
  have hinner : ∀ u ∈ Finset.antidiagonal c,
      ∑ v ∈ Finset.antidiagonal b,
        (-1 : K) ^ (u.1 + v.1) • (comulETerm D q i u.1 v.1 * (e D q j ⊗ₜ[K] 1) *
          comulETerm D q i u.2 v.2) =
      (∑ v ∈ Finset.antidiagonal b,
          (-1 : K) ^ v.1 * qᵢ ^ (-((v.1 : ℤ) * ((b : ℤ) - 1))) * quantumBinomial qᵢ b v.1) •
        (((-1 : K) ^ u.1 * qᵢ ^ ((u.2 : ℤ) * b)) •
          ((eDP D q i u.1 * e D q j * eDP D q i u.2 * simpleK D q i ^ b) ⊗ₜ[K] eDP D q i b)) := by
    rintro ⟨a₁, a₂⟩ ha; rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun ⟨b₁, b₂⟩ hb ↦ ?_
    have ha' : a₁ + a₂ = c := Finset.mem_antidiagonal.mp ha
    have hb' : b₁ + b₂ = b := Finset.mem_antidiagonal.mp hb
    simp only [comulETerm, smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, smul_smul]
    have hleft : eDP D q i a₁ * simpleK D q i ^ b₁ * e D q j * (eDP D q i a₂ * simpleK D q i ^ b₂) =
        qᵢ ^ ((b₁ : ℤ) * D.cartan i j + 2 * (a₂ : ℤ) * b₁) •
          (eDP D q i a₁ * e D q j * eDP D q i a₂ * simpleK D q i ^ b) := by
      rw [mul_assoc (eDP D q i a₁), mul_assoc (eDP D q i a₁), ← mul_assoc (simpleK D q i ^ b₁ * _),
        simpleK_pow_mul_e_mul_eDP hq, smul_mul_assoc, mul_smul_comm]
      simp only [mul_assoc, ← pow_add, hb']; rfl
    rw [hleft, quantumDividedPower_mul_quantumDividedPower _ (hb'.symm ▸ hbf), hb',
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_smul]; congr 1
    have hqpow := pow_mul_pow_mul_zpow hqᵢ (a₁ * b₁) (a₂ * b₂)
      ((b₁ : ℤ) * D.cartan i j + 2 * (a₂ : ℤ) * b₁) (-((b₁ : ℤ) * ((b : ℤ) - 1))) ((a₂ : ℤ) * b)
      (by rw [cartan_eq_one_sub_serreLength D hij, ← hcb, ← ha', ← hb']; push_cast; ring)
    rw [pow_add (-1 : K)]
    linear_combination ((-1 : K) ^ a₁ * (-1 : K) ^ b₁ * quantumBinomial qᵢ b b₁) * hqpow
  rw [Finset.sum_congr rfl hinner, ← Finset.smul_sum]
  rcases Nat.eq_zero_or_pos b with rfl | hb_pos
  · obtain rfl : c = serreLength D i j := by simpa using hcb
    simp only [eDP, Nat.cast_zero, mul_zero, zpow_zero, mul_one, pow_zero, quantumDividedPower_zero,
      TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
    rw [← serreElement_def, serre_e hij, smul_zero, TensorProduct.zero_tmul]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_neg_one_pow_mul_zpow_neg_mul_quantumBinomial hqᵢ hb_pos, zero_smul]

private theorem comul_serreE_right {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0)
    {i j : ι} (hij : i ≠ j)
    (hN : quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (comulEGen D q i)
      (simpleK D q j ⊗ₜ[K] e D q j) = 0 := by
  set qᵢ : K := q ^ D.symmetrizer i
  have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  rw [serreElement_comulE_eq_sum hN]
  refine Finset.sum_eq_zero fun ⟨c, b⟩ hp ↦ ?_
  have hcb : c + b = serreLength D i j := Finset.mem_antidiagonal.mp hp
  have hcf : quantumFactorial qᵢ c ≠ 0 := quantumFactorial_ne_zero_of_le (by omega) hN
  rw [Finset.sum_comm]
  have hinner : ∀ v ∈ Finset.antidiagonal b,
      ∑ u ∈ Finset.antidiagonal c,
        (-1 : K) ^ (u.1 + v.1) • (comulETerm D q i u.1 v.1 * (simpleK D q j ⊗ₜ[K] e D q j) *
          comulETerm D q i u.2 v.2) =
      (∑ u ∈ Finset.antidiagonal c,
          (-1 : K) ^ u.1 * qᵢ ^ ((u.1 : ℤ) * ((c : ℤ) - 1)) * quantumBinomial qᵢ c u.1) •
        (((-1 : K) ^ v.1 * qᵢ ^ ((c : ℤ) * ((v.1 : ℤ) + 1 - c))) •
          ((eDP D q i c * (simpleK D q j * simpleK D q i ^ b)) ⊗ₜ[K]
            (eDP D q i v.1 * e D q j * eDP D q i v.2))) := by
    rintro ⟨b₁, b₂⟩ hb; rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun ⟨a₁, a₂⟩ ha ↦ ?_
    have ha' : a₁ + a₂ = c := Finset.mem_antidiagonal.mp ha
    have hb' : b₁ + b₂ = b := Finset.mem_antidiagonal.mp hb
    simp only [comulETerm, smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
      smul_smul]
    have hleft : eDP D q i a₁ * simpleK D q i ^ b₁ * simpleK D q j *
          (eDP D q i a₂ * simpleK D q i ^ b₂) =
        (qᵢ ^ ((a₂ : ℤ) * (2 * (b₁ : ℤ) + D.cartan i j)) * quantumBinomial qᵢ c a₁) •
          (eDP D q i c * (simpleK D q j * simpleK D q i ^ b)) := by
      rw [mul_assoc (eDP D q i a₁), mul_assoc (eDP D q i a₁), ← mul_assoc (simpleK D q i ^ b₁ * _),
        simpleK_pow_mul_simpleK_mul_eDP, smul_mul_assoc, mul_smul_comm,
        mul_assoc (eDP D q i a₂), ← mul_assoc (eDP D q i a₁),
        quantumDividedPower_mul_quantumDividedPower _ (ha'.symm ▸ hcf), ha', smul_mul_assoc,
        smul_smul]; simp only [mul_assoc, ← pow_add, hb']; rfl
    rw [hleft, ← TensorProduct.smul_tmul', smul_smul]; congr 1
    have hqpow := pow_mul_pow_mul_zpow hqᵢ (a₁ * b₁) (a₂ * b₂)
      ((a₂ : ℤ) * (2 * (b₁ : ℤ) + D.cartan i j)) ((a₁ : ℤ) * ((c : ℤ) - 1))
      ((c : ℤ) * ((b₁ : ℤ) + 1 - c))
      (by rw [cartan_eq_one_sub_serreLength D hij, ← hcb, ← ha', ← hb']; push_cast; ring)
    rw [pow_add (-1 : K)]
    linear_combination ((-1 : K) ^ a₁ * (-1 : K) ^ b₁ * quantumBinomial qᵢ c a₁) * hqpow
  rw [Finset.sum_congr rfl hinner, ← Finset.smul_sum]
  rcases Nat.eq_zero_or_pos c with rfl | hc_pos
  · obtain rfl : b = serreLength D i j := by simpa using hcb
    simp only [eDP, Nat.cast_zero, zero_mul, zpow_zero, mul_one, quantumDividedPower_zero, one_mul,
      ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum]
    rw [← serreElement_def, serre_e hij, smul_zero, TensorProduct.tmul_zero]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_neg_one_pow_mul_zpow_mul_quantumBinomial hqᵢ hc_pos, zero_smul]

variable (D : CartanDatum ι X Y) (q : K) [IsSerreRegular D q]

private theorem comul_serreE {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j)
      (comulEGen D q i) (comulEGen D q j) = 0 := by
  rcases IsSerreRegular.out (D := D) (q := q) with rfl | hreg
  · simp [comulEGen]
  · rcases eq_or_ne q 0 with rfl | hq
    · simp [comulEGen]
    · have hj : comulEGen D q j = e D q j ⊗ₜ[K] 1 + simpleK D q j ⊗ₜ[K] e D q j := rfl
      rw [hj, serreElement_add_right, comul_serreE_left hq hij (hreg hij),
        comul_serreE_right hq hij (hreg hij), add_zero]

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

/-- The Drinfeld–Jimbo coproduct `Δ : U →ₐ[K] U ⊗[K] U` under `[IsSerreRegular D q]`. -/
def comul :
    QuantumEnvelopingAlgebra D q →ₐ[K]
      QuantumEnvelopingAlgebra D q ⊗[K] QuantumEnvelopingAlgebra D q :=
  lift
    { e i := comulEGen D q i
      f i := f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i
      k y := k D q y ⊗ₜ[K] k D q y
      k_zero := by simp [Algebra.TensorProduct.one_def]
      k_mul_k y₁ y₂ := by simp [Algebra.TensorProduct.tmul_mul_tmul, k_mul_k]
      k_mul_e y i := by
        simp [comulEGen, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, k_mul_e,
          (commute_k _ _).eq, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
      k_mul_f y i := by
        simp [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, k_mul_f, (commute_k _ _).eq,
          TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
      e_mul_f_sub_f_mul_e_self i := by
        rcases eq_or_ne q 0 with rfl | hq
        · simp [comulEGen, zero_pow (D.symmetrizer_pos i).ne']
        · simp only [comulEGen, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            mul_one]
          rw [simpleK_mul_f_self, e_mul_simpleKInv_self]
          simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, inv_pow,
            mul_inv_cancel₀ (pow_ne_zero 2 (pow_ne_zero _ hq)), one_smul]
          calc _ = (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] simpleKInv D q i +
                  simpleK D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i) := by
                simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
            _ = _ := by
                rw [e_mul_f_sub_f_mul_e_self]
                simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.sub_tmul,
                  TensorProduct.tmul_sub, smul_sub]; module
      e_mul_f_of_ne hij := by
        rcases eq_or_ne q 0 with rfl | hq
        · simp [comulEGen]
        · simp only [comulEGen, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            mul_one]
          rw [e_mul_f_of_ne hij, simpleK_mul_f, e_mul_simpleKInv]
          simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
          rw [pow_symmetrizer_zpow_cartan_mul_neg hq, one_smul]; abel
      serre_e hij := comul_serreE D q hij
      serre_f hij := comul_serreF D q hij }

@[local simp] private theorem comul_eAux (i : ι) :
    comul D q (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i := by
  simp [comul, comulEGen]
@[local simp] private theorem comul_fAux (i : ι) :
    comul D q (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i := by simp [comul]
@[local simp] private theorem comul_kAux (y : Y) :
    comul D q (k D q y) = k D q y ⊗ₜ[K] k D q y := by simp [comul]
instance instBialgebra : Bialgebra K (QuantumEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comul D q) (counit D q)
    (by ext <;> simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
      Algebra.TensorProduct.one_def])
    (by ext <;> simp) (by ext <;> simp)
@[simp] theorem comul_e (i : ι) :
    Coalgebra.comul (R := K) (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i :=
  comul_eAux D q i
@[simp] theorem comul_f (i : ι) :
    Coalgebra.comul (R := K) (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i :=
  comul_fAux D q i
@[simp] theorem comul_k (y : Y) :
    Coalgebra.comul (R := K) (k D q y) = k D q y ⊗ₜ[K] k D q y := comul_kAux D q y
@[simp] theorem counit_e (i : ι) : Coalgebra.counit (R := K) (e D q i) = 0 := counit_apply_e D q i
@[simp] theorem counit_f (i : ι) : Coalgebra.counit (R := K) (f D q i) = 0 := counit_apply_f D q i
@[simp] theorem counit_k (y : Y) : Coalgebra.counit (R := K) (k D q y) = 1 := counit_apply_k D q y
@[simp] theorem comul_apply (x : QuantumEnvelopingAlgebra D q) :
    comul D q x = Coalgebra.comul (R := K) x := (rfl)
@[simp] theorem counit_apply (x : QuantumEnvelopingAlgebra D q) :
    counit D q x = Coalgebra.counit (R := K) x := (rfl)

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

theorem comul_quantumDividedPower_e {D : CartanDatum ι X Y} {q : K} [IsSerreRegular D q]
    {i : ι} {r : ℕ} (hr : quantumFactorial (q ^ D.symmetrizer i) r ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
      ∑ p ∈ Finset.antidiagonal r, (q ^ D.symmetrizer i) ^ (p.1 * p.2) •
        ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) p.1 * simpleK D q i ^ p.2) ⊗ₜ[K]
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) p.2) := by
  rw [← Bialgebra.comulAlgHom_apply, map_quantumDividedPower, Bialgebra.comulAlgHom_apply, comul_e]
  exact quantumDividedPower_comulE hr

theorem comul_quantumDividedPower_f {D : CartanDatum ι X Y} {q : K} [IsSerreRegular D q]
    {i : ι} {r : ℕ} (hr : quantumFactorial (q ^ D.symmetrizer i) r ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) =
      ∑ p ∈ Finset.antidiagonal r, (q ^ D.symmetrizer i) ^ (p.1 * p.2) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) p.1 ⊗ₜ[K]
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) p.2 * simpleKInv D q i ^ p.1)) := by
  have he : chevalleyEquiv D q (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
      quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r := by simp
  rw [← he, comul_chevalleyEquiv, comul_quantumDividedPower_e hr, map_sum,
    ← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.sum_congr rfl fun p _ ↦ by simp [mul_comm p.2 p.1]
end Coproduct

section Functoriality
variable {X' Y' X'' Y'' : Type*} [AddCommGroup X'] [AddCommGroup Y']
  [AddCommGroup X''] [AddCommGroup Y'']
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}
/-- Functorial bialgebra homomorphism induced by `φ : CartanDatum.Hom D D'`. -/
def mapBialgHom (φ : CartanDatum.Hom D D') (q : K) [IsSerreRegular D q] [IsSerreRegular D' q] :
    QuantumEnvelopingAlgebra D q →ₐc[K] QuantumEnvelopingAlgebra D' q :=
  BialgHom.ofAlgHom (map φ q) (by ext <;> simp) (by ext <;> simp [φ.map_simpleTorus])
@[simp] theorem mapBialgHom_toAlgHom (φ : CartanDatum.Hom D D') (q : K)
    [IsSerreRegular D q] [IsSerreRegular D' q] :
    (mapBialgHom φ q : QuantumEnvelopingAlgebra D q →ₐ[K] QuantumEnvelopingAlgebra D' q) =
      map φ q := (rfl)
@[simp] theorem mapBialgHom_apply (φ : CartanDatum.Hom D D') (q : K)
    [IsSerreRegular D q] [IsSerreRegular D' q] (x : QuantumEnvelopingAlgebra D q) :
    mapBialgHom φ q x = map φ q x := (rfl)
@[simp] theorem mapBialgHom_id (D : CartanDatum ι X Y) (q : K) [IsSerreRegular D q] :
    mapBialgHom (CartanDatum.Hom.id D) q = BialgHom.id K (QuantumEnvelopingAlgebra D q) := by
  ext x; rw [mapBialgHom_apply, map_id]; rfl
theorem mapBialgHom_comp (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') (q : K)
    [IsSerreRegular D q] [IsSerreRegular D' q] [IsSerreRegular D'' q] :
    mapBialgHom (ψ.comp φ) q = (mapBialgHom ψ q).comp (mapBialgHom φ q) := by
  ext x; simp [map_comp]
end Functoriality
end TauCeti.QuantumEnvelopingAlgebra
