/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
public import TauCeti.NumberTheory.ModularForms.QExpansion.Positive
import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector
import TauCeti.NumberTheory.ArithmeticFunction.PrimeRecurrence

/-!
# The coefficient characterization of normalized modular eigenforms

A modular form of nebentypus `χ` with first Fourier coefficient `1` is an eigenform for every
positive-index Hecke operator if and only if its coefficients are multiplicative at coprime
indices and satisfy the prime-power Hecke recurrence. This includes noncuspidal forms and bad
primes: the character in the recurrence is Mathlib's zero-extension `MulChar.ofUnitHom χ`.

Only positive coefficients are used in the converse. Their uniqueness at nonzero weight
recovers the constant-term equation, rather than adding it as an extra hypothesis. Normalization
already excludes weight zero and the zero form. The eigenvalues are the Fourier coefficients,
so the statement needs neither a bundled eigenvalue function nor choices of scalars.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Proposition 5.8.5.
-/

public noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

private lemma prime_eq_coeff_smul_of_relations (F : modFormCharSpace k χ)
    (hk : k ≠ 0)
    (hmul : ∀ u v : ℕ, Nat.Coprime u v →
      (qExpansion 1 F.val).coeff (u * v) =
        (qExpansion 1 F.val).coeff u * (qExpansion 1 F.val).coeff v)
    (hpow : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      (qExpansion 1 F.val).coeff (p ^ (r + 2)) =
        (qExpansion 1 F.val).coeff p * (qExpansion 1 F.val).coeff (p ^ (r + 1)) -
          (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
            (qExpansion 1 F.val).coeff (p ^ r))
    {p : ℕ} (hp : p.Prime) :
    heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N p) F =
      (qExpansion 1 F.val).coeff p • F := by
  have : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  rw [heckeTCompositeGamma0_prime N hp,
    coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp, Submodule.coe_smul]
  apply ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
    (one_mem_strictPeriods_Gamma1_map N) hk
  intro m hm
  have hrec := prime_mul_eq_of_prime_pow_recurrence_of_coprime_mul_eq
    (a := fun n ↦ (qExpansion 1 F.val).coeff n) (L := 1) hp
    (Nat.coprime_one_right p) (fun u v huv _ _ ↦ hmul u v huv) (hpow p hp) m hm.ne'
    (Nat.coprime_one_right m)
  rw [FunLike.coe_smul, _root_.ModularForm.qExpansion_smul one_pos
    (one_mem_strictPeriods_Gamma1_map N), map_smul, smul_eq_mul]
  by_cases hpN : Nat.Coprime p N
  · rw [heckeTNat_def,
      qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace
        k hp hpN χ F.2]
    rw [← ZMod.coe_unitOfCoprime p hpN, MulChar.ofUnitHom_coe] at hrec
    linear_combination hrec
  · have hχ : (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p = 0 :=
      MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
    rw [qExpansion_coeff_heckeTNat_of_primeFactors_subset k p
      (Nat.primeFactors_mono ((hp.dvd_iff_not_coprime).mpr hpN) (NeZero.ne N))]
    simpa only [hχ, zero_mul, ite_self, sub_zero, mul_comm p m] using hrec

private lemma primePower_eq_coeff_smul_of_relations (F : modFormCharSpace k χ)
    (h₁ : (qExpansion 1 F.val).coeff 1 = 1)
    {p : ℕ} (hp : p.Prime)
    (hprime : heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N p) F =
      (qExpansion 1 F.val).coeff p • F)
    (hpow : ∀ r : ℕ,
      (qExpansion 1 F.val).coeff (p ^ (r + 2)) =
        (qExpansion 1 F.val).coeff p * (qExpansion 1 F.val).coeff (p ^ (r + 1)) -
          (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
            (qExpansion 1 F.val).coeff (p ^ r)) (v : ℕ) :
    heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p v) F =
      (qExpansion 1 F.val).coeff (p ^ v) • F := by
  induction v using Nat.twoStepInduction with
  | zero => simp [heckeTGeneratorRecGamma0_zero, h₁]
  | one => simpa [heckeTCompositeGamma0_prime, hp, heckeTGeneratorRecGamma0_one] using hprime
  | more r ih₁ ih₂ =>
    rw [hpow r]
    by_cases hpN : Nat.Coprime p N
    · rw [heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ k χ hp.pos hpN]
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        ih₁, ih₂, map_smul, ← heckeTCompositeGamma0_prime N hp, hprime,
        smul_smul, sub_smul, ← ZMod.coe_unitOfCoprime p hpN, MulChar.ofUnitHom_coe]
      ring_nf
    · have hχ : (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p = 0 :=
        MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [heckeTGeneratorRecGamma0_succ_succ, heckeTScalarGamma0_of_not_coprime N hpN]
      simp only [smul_zero, zero_mul, sub_zero, map_mul, Module.End.mul_apply, ih₂,
        map_smul, ← heckeTCompositeGamma0_prime N hp, hprime, smul_smul, hχ]
      rw [mul_comm]

/-- **Diamond–Shurman, Proposition 5.8.5, on `M_k(N, χ)`.** A modular form with `a₁ = 1` is
an eigenform for all positive-index Hecke operators exactly when its Fourier coefficients are
multiplicative at coprime indices and satisfy the Hecke recurrence at every prime. The character
is extended by zero at the bad primes; no constant-term condition or cuspidality is assumed. -/
theorem forall_heckeTCompositeGamma0_eq_coeff_smul_iff
    (F : modFormCharSpace k χ) (h₁ : (qExpansion 1 F.val).coeff 1 = 1) :
    (∀ n : ℕ, n ≠ 0 → heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F =
      (qExpansion 1 F.val).coeff n • F) ↔
      (∀ u v : ℕ, Nat.Coprime u v →
        (qExpansion 1 F.val).coeff (u * v) =
          (qExpansion 1 F.val).coeff u * (qExpansion 1 F.val).coeff v) ∧
      ∀ p : ℕ, p.Prime → ∀ r : ℕ,
        (qExpansion 1 F.val).coeff (p ^ (r + 2)) =
          (qExpansion 1 F.val).coeff p * (qExpansion 1 F.val).coeff (p ^ (r + 1)) -
            (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
              (qExpansion 1 F.val).coeff (p ^ r) := by
  constructor
  · intro heig
    constructor
    · intro u v huv
      rcases eq_or_ne u 0 with rfl | _
      · have hv : v = 1 := by simpa using huv
        simp [hv, h₁]
      rcases eq_or_ne v 0 with rfl | hv
      · have hu : u = 1 := by simpa using huv
        simp [hu, h₁]
      have h := qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime hv F huv
      rw [heig v hv, Submodule.coe_smul, FunLike.coe_smul,
        _root_.ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
        map_smul, smul_eq_mul] at h
      exact h.symm.trans (mul_comm _ _)
    · intro p hp r
      have : NeZero p := ⟨hp.ne_zero⟩
      have hT := heckeTNat_eq_smul_of_heckeRingHomCharSpace_heckeTCompositeGamma0_eq_smul
        hp (heig p hp.ne_zero)
      have hrec := (heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom
        hp F.2 _).mp hT (p ^ (r + 1))
      have hd : p ∣ p ^ (r + 1) := dvd_pow_self p (by omega)
      rw [ite_eq_left hd, pow_succ, Nat.mul_div_cancel _ hp.pos] at hrec
      simpa only [pow_succ, mul_comm p (p ^ r * p), Nat.add_assoc] using hrec
  · rintro ⟨hmul, hpow⟩
    have hk := ModularForm.weight_ne_zero_of_pos_qExpansion_coeff_ne_zero one_pos
      (one_mem_strictPeriods_Gamma1_map N) (f := F.val) one_pos (h₁ ▸ one_ne_zero)
    have hprime {p : ℕ} (hp : p.Prime) := prime_eq_coeff_smul_of_relations F hk hmul hpow hp
    intro n hn
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => exact (hn rfl).elim
    | one => simp [heckeTCompositeGamma0_one, h₁]
    | prime_pow p v hp _ =>
      rw [heckeTCompositeGamma0_prime_pow N hp]
      exact primePower_eq_coeff_smul_of_relations F h₁ hp (hprime hp) (hpow p hp) v
    | coprime a b ha hb hab iha ihb =>
      rw [heckeTCompositeGamma0_mul_of_coprime N hab, map_mul, Module.End.mul_apply,
        ihb (by omega), map_smul, iha (by omega), smul_smul, hmul a b hab, mul_comm]

end TauCeti
