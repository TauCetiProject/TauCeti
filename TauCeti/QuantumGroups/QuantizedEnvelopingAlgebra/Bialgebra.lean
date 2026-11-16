/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# The bialgebra structure on a quantized enveloping algebra

This file constructs the counit and coproduct of `TauCeti.QuantizedEnvelopingAlgebra D q`:

* `ε(Eᵢ) = 0`, `ε(Fᵢ) = 0`, `ε(K_y) = 1` (unconditional on `q`);
* `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, `Δ(K_y) = K_y ⊗ K_y`.

Whenever the Serre-degree quantum factorials `[1 - aᵢⱼ]_(qᵢ)!` (`i ≠ j`) are nonzero (including
`q = 0`, where `Eᵢ = Fᵢ = 0`), `comulAlgHom` descends through the divided-power presentation and
equips `QuantizedEnvelopingAlgebra D q` with a `Bialgebra` structure (`bialgebra`, and the
canonical instance `instBialgebra` at `[Fact (IsGenericQuantumParameter q)]`). We also derive the
divided-power coproducts `comulAlgHom_eDividedPower`/`comul_eDividedPower` and
`comulAlgHom_fDividedPower`/`comul_fDividedPower`, the Kashiwara-normalized operators
`normalizedE = Kᵢ⁻¹ Eᵢ` and `normalizedF = Fᵢ Kᵢ`, and `mapBialgHom`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, GSM 6, AMS, 1996, §§4.8–4.9.
* M. Kashiwara, *On crystal bases of the `q`-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), §1.2, for the normalized generators `eᵢ = Kᵢ⁻¹ Eᵢ`, `fᵢ = Fᵢ Kᵢ` and
  their coproduct convention.
* The `counit`, `comulTuple`, and `Bialgebra.ofAlgHom` construction adapts
  `TauCeti.QuantumGroups.UqSl2.Hopf`.
-/

public section

open Finset
open scoped TensorProduct

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]

/-! ### Unconditional counit and Kashiwara-normalized operators -/

section Counit

/-- The unconditional augmentation `ε : QuantizedEnvelopingAlgebra D q →ₐ[K] K`, sending `Eᵢ` and
`Fᵢ` to `0` and every `K_y` to `1`. -/
noncomputable def counit (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] K :=
  lift
    { e _ := 0, f _ := 0, k _ := 1
      k_zero := rfl, k_mul_k _ _ := mul_one 1
      k_mul_e _ _ := by simp, k_mul_f _ _ := by simp
      e_mul_f_sub_f_mul_e_self _ := by simp, e_mul_f_sub_f_mul_e_of_ne _ := by simp
      serre_e _ := by simp, serre_f _ := by simp }

variable {D : CartanDatum ι X Y} {q : K}

@[simp] theorem counit_apply_e (i : ι) : counit D q (e D q i) = 0 := lift_e _ i
@[simp] theorem counit_apply_f (i : ι) : counit D q (f D q i) = 0 := lift_f _ i
@[simp] theorem counit_apply_k (y : Y) : counit D q (k D q y) = 1 := lift_k _ y
theorem counit_apply_ki (i : ι) : counit D q (ki D q i) = 1 := counit_apply_k (D.simpleTorus i)
theorem counit_apply_kiInv (i : ι) : counit D q (kiInv D q i) = 1 :=
  counit_apply_k (-D.simpleTorus i)

@[simp] theorem counit_apply_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) :
    counit D q (chevalleyInvolution D q x) = counit D q x := by
  have h : (counit D q).comp (chevalleyInvolution D q).toAlgHom = counit D q := by ext <;> simp
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using AlgHom.congr_fun h x

@[simp] theorem counit_apply_map {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (x : QuantizedEnvelopingAlgebra D q) :
    counit D' q (map φ x) = counit D q x := by
  have h : (counit D' q).comp (map φ) = counit D q := by ext <;> simp
  simpa only [AlgHom.comp_apply] using AlgHom.congr_fun h x

/-- The Kashiwara-normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`. -/
noncomputable def normalizedE (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q := kiInv D q i * e D q i
/-- The Kashiwara-normalized lowering operator `fᵢ = Fᵢ Kᵢ`. -/
noncomputable def normalizedF (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q := f D q i * ki D q i

theorem normalizedE_def (i : ι) : normalizedE D q i = kiInv D q i * e D q i := (rfl)
theorem normalizedF_def (i : ι) : normalizedF D q i = f D q i * ki D q i := (rfl)
@[simp] theorem counit_apply_normalizedE (i : ι) : counit D q (normalizedE D q i) = 0 := by
  simp [normalizedE_def]
@[simp] theorem counit_apply_normalizedF (i : ι) : counit D q (normalizedF D q i) = 0 := by
  simp [normalizedF_def]

end Counit

/-! ### Coproduct -/

section Comul

variable (D : CartanDatum ι X Y) {q : K}

private lemma comulE_comm (i : ι) :
    (ki D q i ⊗ₜ[K] e D q i) * (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) =
      (q ^ D.symmetrizer i) ^ 2 •
        ((e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) * (ki D q i ⊗ₜ[K] e D q i)) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ki_mul_e,
    D.cartan_apply_self, zpow_two, ← sq, TensorProduct.smul_tmul']

private lemma quantumDividedPower_comulE (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    quantumDividedPower (q ^ D.symmetrizer i)
        (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q i ⊗ₜ[K] e D q i) n =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        ((eDividedPower D q i a * ki D q i ^ (n - a)) ⊗ₜ[K] eDividedPower D q i (n - a)) := by
  rw [quantumDividedPower_add (comulE_comm D i) hn]
  refine sum_congr rfl fun a _ ↦ congrArg _ ?_
  simp only [eDividedPower, quantumDividedPower_def, Algebra.TensorProduct.tmul_pow, one_pow,
    smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]

private lemma ki_pow_mul_e (i j : ι) (u : ℕ) :
    ki D q i ^ u * e D q j =
      (q ^ D.symmetrizer i) ^ ((u : ℤ) * D.cartan i j) • (e D q j * ki D q i ^ u) := by
  rw [ki, k_pow, k_mul_e, map_nsmul, D.pairing_root_simpleTorus, nsmul_eq_mul,
    show (u : ℤ) * (D.symmetrizer j * D.cartan j i) = D.symmetrizer i * ((u : ℤ) * D.cartan i j) by
      linear_combination (u : ℤ) * D.symmetrizer_mul_cartan j i, zpow_mul, zpow_natCast]

private lemma ki_pow_mul_eDividedPower (i : ι) (u c : ℕ) :
    ki D q i ^ u * eDividedPower D q i c =
      (q ^ D.symmetrizer i) ^ (2 * (c : ℤ) * (u : ℤ)) • (eDividedPower D q i c * ki D q i ^ u) := by
  rw [ki, k_pow, k_mul_eDividedPower, map_nsmul, D.pairing_root_simpleTorus_self, nsmul_eq_mul,
    show (c : ℤ) * ((u : ℤ) * (2 * D.symmetrizer i)) =
      D.symmetrizer i * (2 * (c : ℤ) * (u : ℤ)) by ring, zpow_mul, zpow_natCast]

private lemma ki_pow_mul_kj_mul_eDividedPower (i j : ι) (u c : ℕ) :
    ki D q i ^ u * ki D q j * eDividedPower D q i c =
      (q ^ D.symmetrizer i) ^ (2 * (c : ℤ) * (u : ℤ) + (c : ℤ) * D.cartan i j) •
        (eDividedPower D q i c * (ki D q j * ki D q i ^ u)) := by
  rw [ki, ki, k_pow, k_mul_k, k_mul_eDividedPower, map_add, map_nsmul,
    D.pairing_root_simpleTorus_self, D.pairing_root_simpleTorus, nsmul_eq_mul,
    ← k_mul_k, (commute_k_k (u • D.simpleTorus i) (D.simpleTorus j)).eq,
    show (c : ℤ) * ((u : ℤ) * (2 * D.symmetrizer i) + D.symmetrizer i * D.cartan i j) =
      D.symmetrizer i * (2 * (c : ℤ) * (u : ℤ) + (c : ℤ) * D.cartan i j) by ring,
    zpow_mul, zpow_natCast]

private lemma sum_range_comulE_serre_expand {i : ι} {m : ℕ}
    (hfac : quantumFactorial (q ^ D.symmetrizer i) m ≠ 0)
    (M₁ M₂ : QuantizedEnvelopingAlgebra D q) :
    ∑ r ∈ range (m + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q i ⊗ₜ[K] e D q i) r *
        (M₁ ⊗ₜ[K] M₂) *
        quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) =
    ∑ p ∈ range (m + 1), ∑ a ∈ range (p + 1), ∑ u ∈ range (m - p + 1),
      ((-1 : K) ^ (a + u) * (q ^ D.symmetrizer i) ^ (a * u) *
          (q ^ D.symmetrizer i) ^ ((p - a) * (m - p - u))) •
        ((eDividedPower D q i a * (ki D q i ^ u *
            (M₁ * (eDividedPower D q i (p - a) * ki D q i ^ (m - p - u))))) ⊗ₜ[K]
          (eDividedPower D q i u * (M₂ * eDividedPower D q i (m - p - u)))) := by
  set qi := q ^ D.symmetrizer i
  trans ∑ r ∈ range (m + 1), ∑ a ∈ range (r + 1), ∑ c ∈ range (m - r + 1),
    ((-1 : K) ^ r * qi ^ (a * (r - a)) * qi ^ (c * (m - r - c))) •
      ((eDividedPower D q i a * (ki D q i ^ (r - a) *
          (M₁ * (eDividedPower D q i c * ki D q i ^ (m - r - c))))) ⊗ₜ[K]
        (eDividedPower D q i (r - a) * (M₂ * eDividedPower D q i (m - r - c))))
  · refine sum_congr rfl fun r hr ↦ ?_
    rw [quantumDividedPower_comulE D i
        (quantumFactorial_ne_zero_of_le (Nat.lt_succ_iff.mp (mem_range.mp hr)) hfac),
      quantumDividedPower_comulE D i (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hfac),
      sum_mul, sum_mul, smul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [mul_sum, smul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    simp only [smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, smul_smul,
      mul_assoc]
    exact congrArg (· • _) (by ring)
  · rw [sum_triple_reindex]
    refine sum_congr rfl fun p _ ↦ sum_congr rfl fun a ha ↦ sum_congr rfl fun u _ ↦ ?_
    have ha' := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [Nat.add_sub_cancel_left, show m - (a + u) - (p - a) = m - p - u by omega]

/-- The `Eⱼ ⊗ 1` half of the Serre-relation coproduct vanishes: for `p < m`, the inner `u`-sum
vanishes by the `q`-binomial identity; at `p = m`, the `a`-sum is `serre_e hij ⊗ 1`. -/
private lemma comul_serre_e_left (hq : q ≠ 0) {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q i ⊗ₜ[K] e D q i) r *
        (e D q j ⊗ₜ[K] 1) *
        quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (serreLength D i j - r)) = 0 := by
  rw [sum_range_comulE_serre_expand D hfac (e D q j) 1]
  set m := serreLength D i j; set qi := q ^ D.symmetrizer i
  have hqi : qi ≠ 0 := pow_ne_zero _ hq
  -- Factor each summand into an `(a, p)` prefactor times the `q`-binomial `u`-weight.
  trans ∑ p ∈ range (m + 1), ∑ a ∈ range (p + 1), ∑ u ∈ range (m - p + 1),
    ((-1 : K) ^ a * qi ^ ((p - a) * (m - p))) •
      (((-1 : K) ^ u * qi⁻¹ ^ ((u : ℤ) * ((m - p : ℕ) - 1)) * quantumBinomial qi⁻¹ (m - p) u) •
        ((eDividedPower D q i a * e D q j * eDividedPower D q i (p - a) *
            ki D q i ^ (m - p)) ⊗ₜ[K] eDividedPower D q i (m - p)))
  · refine sum_congr rfl fun p hp ↦ sum_congr rfl fun a ha ↦ sum_congr rfl fun u hu ↦ ?_
    have hp' := Nat.lt_succ_iff.mp (mem_range.mp hp)
    have ha' := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have hu' := Nat.lt_succ_iff.mp (mem_range.mp hu)
    have huv : u + (m - p - u) = m - p := Nat.add_sub_of_le hu'
    rw [one_mul, ← mul_assoc (ki D q i ^ u), ki_pow_mul_e, smul_mul_assoc, mul_assoc (e D q j),
      ← mul_assoc (ki D q i ^ u), ki_pow_mul_eDividedPower, smul_mul_assoc,
      mul_assoc (eDividedPower D q i (p - a)), ← pow_add, huv, eDividedPower, eDividedPower,
      quantumDividedPower_mul_quantumDividedPower _
        (huv.symm ▸ quantumFactorial_ne_zero_of_le (Nat.sub_le m p) hfac),
      huv, ← quantumBinomial_inv, ← eDividedPower]
    simp only [mul_smul_comm, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
      mul_assoc]
    refine congrArg (· • _) ?_
    have hpow : qi ^ (a * u) * qi ^ ((p - a) * (m - p - u)) *
        (qi ^ ((u : ℤ) * D.cartan i j) * qi ^ (2 * (((p - a : ℕ) : ℤ) * (u : ℤ)))) =
        qi ^ ((p - a) * (m - p)) * qi⁻¹ ^ ((u : ℤ) * ((m - p : ℕ) - 1)) := by
      simp only [← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_add₀ hqi]
      refine congrArg (qi ^ ·) ?_
      rw [cartan_eq_one_sub_serreLength D hij]
      push_cast; rw [Nat.cast_sub hu', Nat.cast_sub hp', Nat.cast_sub ha']; ring
    rw [pow_add (-1 : K)]
    linear_combination (quantumBinomial qi⁻¹ (m - p) u * (-1 : K) ^ a * (-1 : K) ^ u) * hpow
  -- Vanish `p < m` via the alternating `q`-binomial sum; the remaining `p = m` term is `serre_e`.
  · rw [sum_range_succ, sum_eq_zero (fun p hp ↦ sum_eq_zero fun _ _ ↦ by
        rw [← smul_sum, ← sum_smul, sum_range_neg_one_pow_mul_zpow_mul_quantumBinomial
          (inv_ne_zero hqi) (by have := mem_range.mp hp; omega), zero_smul, smul_zero]),
      zero_add, Nat.sub_self, Nat.zero_add, range_one]
    simp only [sum_singleton, Nat.cast_zero, zero_mul, mul_zero, zpow_zero, pow_zero,
      quantumBinomial_zero_right, mul_one, one_smul, eDividedPower, quantumDividedPower_zero,
      TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
    simpa only [eDividedPower, TensorProduct.zero_tmul] using
      congrArg (· ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) (serre_e (D := D) (q := q) hij)

/-- The `Kⱼ ⊗ Eⱼ` half of the Serre-relation coproduct vanishes: swapping `a` and `u` makes the
inner `a`-sum vanish for `p > 0`, leaving `(Kⱼ Kᵢ^m) ⊗ serre_e hij` at `p = 0`. -/
private lemma comul_serre_e_right (hq : q ≠ 0) {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q i ⊗ₜ[K] e D q i) r *
        (ki D q j ⊗ₜ[K] e D q j) *
        quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (serreLength D i j - r)) = 0 := by
  rw [sum_range_comulE_serre_expand D hfac (ki D q j) (e D q j)]
  set m := serreLength D i j; set qi := q ^ D.symmetrizer i with hqi_def
  have hqi : qi ≠ 0 := pow_ne_zero _ hq
  -- Swap `a` and `u`, commute toral factors right, and collect the `q`-binomial `a`-weight.
  trans ∑ p ∈ range (m + 1), ∑ u ∈ range (m - p + 1), ∑ a ∈ range (p + 1),
    ((-1 : K) ^ u * qi ^ ((p : ℤ) * ((u : ℤ) + 1 - p))) •
      (((-1 : K) ^ a * qi ^ ((a : ℤ) * ((p : ℕ) - 1)) * quantumBinomial qi p a) •
        ((eDividedPower D q i p * (ki D q j * ki D q i ^ (m - p))) ⊗ₜ[K]
          (eDividedPower D q i u * e D q j * eDividedPower D q i (m - p - u))))
  · refine sum_congr rfl fun p hp ↦ ?_
    have hp' := Nat.lt_succ_iff.mp (mem_range.mp hp)
    rw [sum_comm]
    refine sum_congr rfl fun u hu ↦ sum_congr rfl fun a ha ↦ ?_
    have ha' := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have hu' := Nat.lt_succ_iff.mp (mem_range.mp hu)
    have huv : u + (m - p - u) = m - p := Nat.add_sub_of_le hu'
    have hac : a + (p - a) = p := Nat.add_sub_of_le ha'
    rw [← mul_assoc (ki D q i ^ u), ← mul_assoc (ki D q i ^ u * ki D q j),
      ki_pow_mul_kj_mul_eDividedPower]
    simp only [smul_mul_assoc, mul_smul_comm, ← TensorProduct.smul_tmul', smul_smul, ← mul_assoc]
    rw [eDividedPower, eDividedPower, quantumDividedPower_mul_quantumDividedPower _
        (hac.symm ▸ quantumFactorial_ne_zero_of_le hp' hfac),
      hac, ← eDividedPower]
    simp only [smul_mul_assoc, ← TensorProduct.smul_tmul', smul_smul, mul_assoc, ← pow_add, huv,
      ← hqi_def]
    rw [← mul_assoc (eDividedPower D q i u)]
    refine congrArg (· • _) ?_
    have hpow : qi ^ (a * u) * qi ^ ((p - a) * (m - p - u)) *
        qi ^ (2 * (((p - a : ℕ) : ℤ) * (u : ℤ)) + ((p - a : ℕ) : ℤ) * D.cartan i j) =
        qi ^ ((p : ℤ) * ((u : ℤ) + 1 - p)) * qi ^ ((a : ℤ) * ((p : ℕ) - 1)) := by
      simp only [← zpow_natCast, ← zpow_add₀ hqi]
      refine congrArg (qi ^ ·) ?_
      rw [cartan_eq_one_sub_serreLength D hij]
      push_cast; rw [Nat.cast_sub hu', Nat.cast_sub hp', Nat.cast_sub ha']; ring
    rw [pow_add (-1 : K)]
    linear_combination ((-1 : K) ^ a * (-1 : K) ^ u * quantumBinomial qi p a) * hpow
  -- Vanish `p > 0` via the alternating `q`-binomial sum; the remaining `p = 0` term is `serre_e`.
  · rw [sum_range_succ', sum_eq_zero (fun p _ ↦ sum_eq_zero fun _ _ ↦ by
        rw [← smul_sum, ← sum_smul,
          sum_range_neg_one_pow_mul_zpow_mul_quantumBinomial hqi (Nat.succ_ne_zero p),
          zero_smul, smul_zero]),
      zero_add, Nat.sub_zero, Nat.zero_add, range_one]
    simp only [sum_singleton, Nat.cast_zero, zero_mul, zpow_zero, pow_zero,
      quantumBinomial_zero_right, mul_one, one_smul, eDividedPower, quantumDividedPower_zero,
      one_mul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum]
    simpa only [eDividedPower, TensorProduct.tmul_zero] using
      congrArg ((ki D q j * ki D q i ^ m) ⊗ₜ[K] ·) (serre_e (D := D) (q := q) hij)

private lemma comul_serre_e {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q i ⊗ₜ[K] e D q i) r *
        (e D q j ⊗ₜ[K] 1 + ki D q j ⊗ₜ[K] e D q j) *
        quantumDividedPower (q ^ D.symmetrizer i)
          (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (serreLength D i j - r)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · simp only [mul_add, add_mul, smul_add, sum_add_distrib]
    rw [comul_serre_e_left D hq hij hfac, comul_serre_e_right D hq hij hfac, add_zero]

private noncomputable def comulTuple
    (hserre : ∀ {i j : ι}, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q) where
  e i := e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i
  f i := f D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] f D q i
  k y := k D q y ⊗ₜ[K] k D q y
  k_zero := by simp [Algebra.TensorProduct.one_def]
  k_mul_k y z := by simp [Algebra.TensorProduct.tmul_mul_tmul, k_mul_k]
  k_mul_e y i := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, k_mul_e,
      ki, (commute_k_k y (D.simpleTorus i)).eq, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      smul_add]
  k_mul_f y i := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, k_mul_f,
      kiInv, (commute_k_k y (-D.simpleTorus i)).eq, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_add]
  e_mul_f_sub_f_mul_e_self i := by
    rcases eq_or_ne q 0 with rfl | hq
    · simp [(D.symmetrizer_pos i).ne']
    · have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
      simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [ki_mul_f, e_mul_kiInv, D.cartan_apply_self]
      simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, zpow_neg, zpow_two,
        mul_inv_cancel₀ (mul_ne_zero hqi hqi), one_smul]
      calc _ = (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] kiInv D q i +
              ki D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i) := by
            simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
        _ = _ := by
            rw [e_mul_f_sub_f_mul_e_self, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
              ← smul_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub, ki, kiInv]
            congr 1; abel
  e_mul_f_sub_f_mul_e_of_ne {i j} hij := by
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    · simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [ki, kiInv, k_mul_f, e_mul_k, map_neg, neg_neg, D.pairing_root_simpleTorus,
        D.pairing_root_simpleTorus]
      simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
      rw [show q ^ (D.symmetrizer i * D.cartan i j) * q ^ (-(D.symmetrizer j * D.cartan j i)) = 1 by
        rw [← zpow_add₀ hq, D.symmetrizer_mul_cartan i j, add_neg_cancel, zpow_zero],
        one_smul, e_mul_f_of_ne hij]
      abel
  serre_e hij := comul_serre_e D hij (hserre hij)
  serre_f {i j} hij := by
    let τ := (Algebra.TensorProduct.map (chevalleyInvolution D q).toAlgHom
      (chevalleyInvolution D q).toAlgHom).comp (Algebra.TensorProduct.comm K _ _).toAlgHom
    have hτ (m : ι) : τ (e D q m ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) +
        ki D q m ⊗ₜ[K] e D q m) = f D q m ⊗ₜ[K] kiInv D q m + 1 ⊗ₜ[K] f D q m := by
      simp [τ, add_comm]
    simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, hτ, map_zero] using
      congrArg τ (comul_serre_e D hij (hserre hij))

/-- The coproduct `Δ : U →ₐ[K] U ⊗[K] U` under nonvanishing of `[1 - aᵢⱼ]_(qᵢ)!` (`i ≠ j`). -/
noncomputable def comulAlgHom
    (hserre : ∀ {i j : ι}, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  lift (comulTuple D hserre)

section ComulAlgHom

variable {D}
  (hserre : ∀ {i j : ι}, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0)

@[simp] theorem comulAlgHom_e (i : ι) :
    comulAlgHom D hserre (e D q i) = e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i := lift_e _ i
@[simp] theorem comulAlgHom_f (i : ι) :
    comulAlgHom D hserre (f D q i) = f D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] f D q i := lift_f _ i
@[simp] theorem comulAlgHom_k (y : Y) :
    comulAlgHom D hserre (k D q y) = k D q y ⊗ₜ[K] k D q y := lift_k _ y
theorem comulAlgHom_ki (i : ι) : comulAlgHom D hserre (ki D q i) = ki D q i ⊗ₜ[K] ki D q i :=
  comulAlgHom_k hserre (D.simpleTorus i)
theorem comulAlgHom_kiInv (i : ι) :
    comulAlgHom D hserre (kiInv D q i) = kiInv D q i ⊗ₜ[K] kiInv D q i :=
  comulAlgHom_k hserre (-D.simpleTorus i)

/-- The Chevalley involution is a coalgebra anti-automorphism: `Δ(ω x) = (ω ⊗ ω)(flip(Δ x))`. -/
theorem comulAlgHom_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) :
    comulAlgHom D hserre (chevalleyInvolution D q x) =
      Algebra.TensorProduct.map
        (chevalleyInvolution D q).toAlgHom (chevalleyInvolution D q).toAlgHom
        (Algebra.TensorProduct.comm K _ _ (comulAlgHom D hserre x)) := by
  have h : (comulAlgHom D hserre).comp (chevalleyInvolution D q).toAlgHom =
      (Algebra.TensorProduct.map (chevalleyInvolution D q).toAlgHom
        (chevalleyInvolution D q).toAlgHom).comp
        ((Algebra.TensorProduct.comm K _ _).toAlgHom.comp (comulAlgHom D hserre)) := by
    ext <;> simp [add_comm]
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using AlgHom.congr_fun h x

/-- `Δ(Eᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) Eᵢ^(a) Kᵢ^(n - a) ⊗ Eᵢ^(n - a)` when `[n]_(qᵢ)! ≠ 0`. -/
theorem comulAlgHom_eDividedPower (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    comulAlgHom D hserre (eDividedPower D q i n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        ((eDividedPower D q i a * ki D q i ^ (n - a)) ⊗ₜ[K] eDividedPower D q i (n - a)) := by
  rw [eDividedPower, map_quantumDividedPower, comulAlgHom_e, quantumDividedPower_comulE D i hn]

/-- `Δ(Fᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) Fᵢ^(a) ⊗ Fᵢ^(n - a) Kᵢ^(-a)` when `[n]_(qᵢ)! ≠ 0`. -/
theorem comulAlgHom_fDividedPower (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    comulAlgHom D hserre (fDividedPower D q i n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        (fDividedPower D q i a ⊗ₜ[K] (fDividedPower D q i (n - a) * kiInv D q i ^ a)) := by
  rw [← chevalleyInvolution_eDividedPower, comulAlgHom_chevalleyInvolution,
    comulAlgHom_eDividedPower hserre i hn, map_sum, map_sum, ← sum_range_reflect]
  refine sum_congr rfl fun a ha ↦ ?_
  rw [Nat.add_one_sub_one, Nat.sub_sub_self (Nat.lt_succ_iff.mp (mem_range.mp ha)),
    mul_comm (n - a) a]
  simp [map_smul, map_mul, map_pow]

/-- `Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ`. -/
@[simp] theorem comulAlgHom_normalizedE (i : ι) :
    comulAlgHom D hserre (normalizedE D q i) =
      normalizedE D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] normalizedE D q i := by
  simp [normalizedE_def, mul_add, Algebra.TensorProduct.tmul_mul_tmul, ki, kiInv]
/-- `Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`. -/
@[simp] theorem comulAlgHom_normalizedF (i : ι) :
    comulAlgHom D hserre (normalizedF D q i) =
      normalizedF D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] normalizedF D q i := by
  simp [normalizedF_def, add_mul, Algebra.TensorProduct.tmul_mul_tmul, ki, kiInv]

theorem comulAlgHom_map {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D')
    (hserre' : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D'.symmetrizer i) (serreLength D' i j) ≠ 0)
    (x : QuantizedEnvelopingAlgebra D q) :
    comulAlgHom D' hserre' (map φ x) =
      Algebra.TensorProduct.map (map φ) (map φ) (comulAlgHom D hserre x) := by
  have h : (comulAlgHom D' hserre').comp (map φ) =
      (Algebra.TensorProduct.map (map φ) (map φ)).comp (comulAlgHom D hserre) := by ext <;> simp
  simpa only [AlgHom.comp_apply] using AlgHom.congr_fun h x

end ComulAlgHom

end Comul

/-! ### Bialgebra structure and generic-parameter API -/

section Bialgebra

variable (D : CartanDatum ι X Y) {q : K}

section Explicit

variable (hserre : ∀ {i j : ι}, i ≠ j →
  quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0)

/-- Explicit-hypothesis `Bialgebra` structure on `QuantizedEnvelopingAlgebra D q`, assuming
`[1 - aᵢⱼ]_(qᵢ)! ≠ 0` for all `i ≠ j`. -/
@[expose, instance_reducible]
noncomputable def bialgebra : Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comulAlgHom D hserre) (counit D q)
    (by ext <;> simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
      Algebra.TensorProduct.one_def])
    (by ext <;> simp) (by ext <;> simp)

theorem bialgebra_comul (x : QuantizedEnvelopingAlgebra D q) :
    letI := bialgebra D hserre; Coalgebra.comul (R := K) x = comulAlgHom D hserre x := (rfl)
theorem bialgebra_counit (x : QuantizedEnvelopingAlgebra D q) :
    letI := bialgebra D hserre; Coalgebra.counit (R := K) x = counit D q x := (rfl)

end Explicit

section Generic

variable (q : K) [Fact (IsGenericQuantumParameter q)]

/-- The canonical `K`-bialgebra structure on `QuantizedEnvelopingAlgebra D q` at generic `q`. -/
noncomputable instance instBialgebra : Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  bialgebra D fun {i j} _ ↦
    quantumFactorial_ne_zero
      ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)) (serreLength D i j)

variable {D q}

@[simp] theorem comulAlgHom_apply
    (hserre : ∀ {i j : ι}, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0)
    (x : QuantizedEnvelopingAlgebra D q) :
    comulAlgHom D hserre x = Coalgebra.comul (R := K) x := (rfl)
@[simp] theorem comul_e (i : ι) :
    Coalgebra.comul (R := K) (e D q i) = e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i :=
  comulAlgHom_e _ i
@[simp] theorem comul_f (i : ι) :
    Coalgebra.comul (R := K) (f D q i) = f D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] f D q i :=
  comulAlgHom_f _ i
@[simp] theorem comul_k (y : Y) :
    Coalgebra.comul (R := K) (k D q y) = k D q y ⊗ₜ[K] k D q y := comulAlgHom_k _ y
theorem comul_ki (i : ι) : Coalgebra.comul (R := K) (ki D q i) = ki D q i ⊗ₜ[K] ki D q i :=
  comul_k (D.simpleTorus i)
theorem comul_kiInv (i : ι) :
    Coalgebra.comul (R := K) (kiInv D q i) = kiInv D q i ⊗ₜ[K] kiInv D q i :=
  comul_k (-D.simpleTorus i)

@[simp] theorem counit_e (i : ι) : Coalgebra.counit (R := K) (e D q i) = 0 := counit_apply_e i
@[simp] theorem counit_f (i : ι) : Coalgebra.counit (R := K) (f D q i) = 0 := counit_apply_f i
@[simp] theorem counit_k (y : Y) : Coalgebra.counit (R := K) (k D q y) = 1 := counit_apply_k y
theorem counit_ki (i : ι) : Coalgebra.counit (R := K) (ki D q i) = 1 := counit_apply_ki i
theorem counit_kiInv (i : ι) : Coalgebra.counit (R := K) (kiInv D q i) = 1 := counit_apply_kiInv i
@[simp] theorem counit_apply (x : QuantizedEnvelopingAlgebra D q) :
    counit D q x = Coalgebra.counit x := (rfl)
@[simp] theorem counit_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) :
    Coalgebra.counit (R := K) (chevalleyInvolution D q x) = Coalgebra.counit (R := K) x :=
  counit_apply_chevalleyInvolution x
@[simp] theorem counit_map {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (x : QuantizedEnvelopingAlgebra D q) :
    Coalgebra.counit (R := K) (map φ x) = Coalgebra.counit (R := K) x :=
  counit_apply_map φ x
theorem isGroupLikeElem_k (y : Y) : IsGroupLikeElem K (k D q y) := ⟨counit_k y, comul_k y⟩
theorem isGroupLikeElem_ki (i : ι) : IsGroupLikeElem K (ki D q i) :=
  isGroupLikeElem_k (D.simpleTorus i)
theorem isGroupLikeElem_kiInv (i : ι) : IsGroupLikeElem K (kiInv D q i) :=
  isGroupLikeElem_k (-D.simpleTorus i)

theorem comul_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) :
    Coalgebra.comul (R := K) (chevalleyInvolution D q x) = Algebra.TensorProduct.map
      (chevalleyInvolution D q).toAlgHom (chevalleyInvolution D q).toAlgHom
      (Algebra.TensorProduct.comm K _ _ (Coalgebra.comul x)) := comulAlgHom_chevalleyInvolution _ x

/-- `Δ(Eᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) Eᵢ^(a) Kᵢ^(n - a) ⊗ Eᵢ^(n - a)`. -/
theorem comul_eDividedPower (i : ι) (n : ℕ) :
    Coalgebra.comul (R := K) (eDividedPower D q i n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        ((eDividedPower D q i a * ki D q i ^ (n - a)) ⊗ₜ[K] eDividedPower D q i (n - a)) :=
  comulAlgHom_eDividedPower _ i <| quantumFactorial_ne_zero
    ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)) n
/-- `Δ(Fᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) Fᵢ^(a) ⊗ Fᵢ^(n - a) Kᵢ^(-a)`. -/
theorem comul_fDividedPower (i : ι) (n : ℕ) :
    Coalgebra.comul (R := K) (fDividedPower D q i n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        (fDividedPower D q i a ⊗ₜ[K] (fDividedPower D q i (n - a) * kiInv D q i ^ a)) :=
  comulAlgHom_fDividedPower _ i <| quantumFactorial_ne_zero
    ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)) n

@[simp] theorem counit_normalizedE (i : ι) : Coalgebra.counit (R := K) (normalizedE D q i) = 0 :=
  counit_apply_normalizedE i
@[simp] theorem counit_normalizedF (i : ι) : Coalgebra.counit (R := K) (normalizedF D q i) = 0 :=
  counit_apply_normalizedF i
/-- `Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ`. -/
@[simp] theorem comul_normalizedE (i : ι) :
    Coalgebra.comul (R := K) (normalizedE D q i) =
      normalizedE D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] normalizedE D q i := comulAlgHom_normalizedE _ i
/-- `Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`. -/
@[simp] theorem comul_normalizedF (i : ι) :
    Coalgebra.comul (R := K) (normalizedF D q i) =
      normalizedF D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] normalizedF D q i := comulAlgHom_normalizedF _ i

/-- Functoriality of the bialgebra structure along a morphism `φ : CartanDatum.Hom D D'`. -/
noncomputable def mapBialgHom {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') :
    QuantizedEnvelopingAlgebra D q →ₐc[K] QuantizedEnvelopingAlgebra D' q :=
  BialgHom.ofAlgHom (map φ) (by ext <;> simp) (by ext <;> simp [Bialgebra.comulAlgHom_apply])

@[simp] theorem mapBialgHom_apply {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (x : QuantizedEnvelopingAlgebra D q) :
    mapBialgHom φ x = map φ x := BialgHom.ofAlgHom_apply _ _ _ x
@[simp] theorem mapBialgHom_toAlgHom {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') :
    (mapBialgHom (q := q) φ).toAlgHom = map φ := AlgHom.ext fun x ↦ mapBialgHom_apply φ x

end Generic

end Bialgebra

end TauCeti.QuantizedEnvelopingAlgebra
