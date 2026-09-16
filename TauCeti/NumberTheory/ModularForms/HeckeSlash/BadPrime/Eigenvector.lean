/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported

/-!
# Eigenvectors of Hecke operators at bad primes

At a bad prime `p ∣ N`, the operator is the alias `U_p = T_p`, and the level-supported
coefficient characterization in `HeckeSlash/LevelSupported.lean` becomes the familiar
criterion `U_p f = c f ↔ a_{pm}(f) = c a_m(f)`. This is the bad-prime counterpart of the
good-prime criterion in `HeckeSlash/Nebentypus/Eigenvector.lean`; together the two criteria turn
the prime-power and coprime-product recurrences of a normalized form into eigenvector equations
at every prime.

## Main results

* `HeckeRing.GL2.heckeUNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul` and its cusp-form
  counterpart give the criterion in the standard bad-prime notation.

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

end HeckeRing.GL2

end
