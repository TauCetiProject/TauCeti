/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Eigenvector

/-!
# Eigenvectors of Hecke operators at bad primes

At a bad prime `p ∣ N`, the operator is the alias `U_p = T_p`, and the level-supported
coefficient characterization in `HeckeSlash/LevelSupported.lean` becomes the familiar
criterion `U_p f = c f ↔ a_{pm}(f) = c a_m(f)`. This is the bad-prime counterpart of the
good-prime criterion in `HeckeSlash/Nebentypus/Eigenvector.lean`. On a nebentypus space the two
criteria combine into one statement at every prime: with the nebentypus extended by zero,
`χ(p) = 0` for `p ∣ N` (Mathlib's `MulChar.ofUnitHom`),

`T_p F = c F ↔ a_{pm}(F) = c a_m(F) − χ(p) p^{k−1} a_{m/p}(F)` for every `m`,

the last term present only when `p ∣ m`. This turns the prime-power and coprime-product
recurrences of a normalized form into eigenvector equations at every prime.

## Main results

* `HeckeRing.GL2.heckeUNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul` and its cusp-form
  counterpart give the criterion in the standard bad-prime notation.
* `HeckeRing.GL2.heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom` and its
  cusp-form counterpart give the criterion at every prime, with the zero-extended nebentypus.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Propositions 5.2.1–5.2.2 and Proposition 5.8.5.
* T. Miyake, *Modular forms*, §4.5, Lemma 4.5.7.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] (k : ℤ)

/-- **The bad-prime coefficient characterization `U_p F = c • F`**, on modular forms. For a
prime `p ∣ N`, the relation holds exactly when `a_{pm}(F) = c a_m(F)` for every `m`. -/
theorem heckeUNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul
    (hp : p.Prime) (hpN : p ∣ N)
    {F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (c : ℂ) :
    heckeUNat (N := N) k p hp hpN F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (p * m) = c * (qExpansion 1 F).coeff m := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  exact heckeTNat_eq_smul_iff_forall_qExpansion_coeff_mul_of_primeFactors_subset k
    (Nat.primeFactors_mono hpN (NeZero.ne N)) c

/-- **The bad-prime coefficient characterization `U_p F = c • F`**, on cusp forms. For a
prime `p ∣ N`, the relation holds exactly when `a_{pm}(F) = c a_m(F)` for every `m`. -/
theorem heckeUCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul
    (hp : p.Prime) (hpN : p ∣ N)
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (c : ℂ) :
    heckeUCuspNat (N := N) k p hp hpN F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (p * m) = c * (qExpansion 1 F).coeff m := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  exact heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_mul_of_primeFactors_subset k
    (Nat.primeFactors_mono hpN (NeZero.ne N)) c

/-! ### The criterion at every prime -/

variable {k} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **The coefficient characterization of `T_p F = c • F` at every prime**, on `M_k(N, χ)`.
With the nebentypus extended by zero to the residues not prime to `N`, the relation holds exactly
when `a_{pm}(F) = c a_m(F) − χ(p) p^{k−1} a_{m/p}(F)` for every `m`, the last term present only
when `p ∣ m`. At a good prime this is
`heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`; at a prime dividing the level
`χ(p) = 0` and it is `heckeUNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`. -/
theorem heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom
    (hp : p.Prime) {F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ modFormCharSpace k χ) (c : ℂ) :
    heckeTNat k p (_hn := ⟨hp.ne_zero⟩) F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (p * m) =
        c * (qExpansion 1 F).coeff m -
          if p ∣ m then (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
            (qExpansion 1 F).coeff (m / p) else 0 := by
  by_cases hpN : Nat.Coprime p N
  · rw [← ZMod.coe_unitOfCoprime p hpN, MulChar.ofUnitHom_coe]
    exact heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul hp hpN hF c
  · have hχ : (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p = 0 :=
      MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
    simp only [hχ, zero_mul, ite_self, sub_zero]
    exact heckeUNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul k hp
      ((Nat.Prime.dvd_iff_not_coprime hp).2 hpN) c

/-- **The coefficient characterization of `T_p F = c • F` at every prime**, on `S_k(N, χ)`: the
cusp-form case of `heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom`. -/
theorem heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom
    (hp : p.Prime) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ cuspFormCharSpace k χ) (c : ℂ) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (p * m) =
        c * (qExpansion 1 F).coeff m -
          if p ∣ m then (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
            (qExpansion 1 F).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [heckeTCuspNat_eq_smul_iff_heckeTNat_eq_smul]
  simpa only [ModularFormClass.coe_modularForm] using
    heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom hp
      ((coe_mem_modFormCharSpace_iff k χ F).mpr hF) c

end HeckeRing.GL2

end
