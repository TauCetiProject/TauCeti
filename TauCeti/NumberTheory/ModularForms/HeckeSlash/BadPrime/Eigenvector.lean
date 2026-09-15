/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported

/-!
# Eigenvectors of Hecke operators supported on the level

At an index `n` all of whose prime factors divide the level, the Fourier coefficients of the
Hecke operator satisfy `a_m(T_n f) = a_{nm}(f)`. Consequently the eigen-relation
`T_n f = c • f` is equivalent to the coefficient recurrence

`a_{nm}(f) = c a_m(f)` for every `m`.

At a bad prime `p ∣ N`, the operator is the alias `U_p = T_p`, so this becomes the familiar
criterion `U_p f = c f ↔ a_{pm}(f) = c a_m(f)`. This is the bad-prime counterpart of the
good-prime criterion in `HeckeSlash/Nebentypus/Eigenvector.lean`; together the two criteria turn
the prime-power and coprime-product recurrences of a normalized form into eigenvector equations
at every prime.

## Main results

* `HeckeRing.GL2.heckeTNat_eq_smul_iff_forall_qExpansion_coeff_mul_of_primeFactors_subset` and
  its cusp-form counterpart characterize the eigen-relation at every level-supported index.
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

variable {N n p : ℕ} [NeZero N] (k : ℤ)

/-- **The coefficient characterization of an eigen-relation at a level-supported index**, on
modular forms. If every prime factor of `n` divides `N`, then `T_n F = c • F` if and only if
`a_{nm}(F) = c a_m(F)` for every `m`.

No nonvanishing hypothesis on `F` is needed: this characterizes an equation rather than the
property of being an eigenvector. -/
theorem heckeTNat_eq_smul_iff_forall_qExpansion_coeff_mul_of_primeFactors_subset [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    {F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (c : ℂ) :
    heckeTNat (N := N) k n F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (n * m) = c * (qExpansion 1 F).coeff m := by
  have hT : ∀ m : ℕ, (qExpansion 1 (heckeTNat (N := N) k n F)).coeff m =
      (qExpansion 1 F).coeff (n * m) :=
    qExpansion_coeff_heckeTNat_of_primeFactors_subset k n hn F
  have hsmul : ∀ m : ℕ,
      (qExpansion 1 (c • F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
        c * (qExpansion 1 F).coeff m := fun m ↦ by
    rw [FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
      map_smul, smul_eq_mul]
  constructor
  · intro heig m
    rw [← hT m, heig, hsmul m]
  · intro hcoeff
    refine (ModularForm.qExpansion_inj one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _)).1 (PowerSeries.ext fun m ↦ ?_)
    rw [hT m, hsmul m, hcoeff m]

/-- **The coefficient characterization of an eigen-relation at a level-supported index**, on
cusp forms. If every prime factor of `n` divides `N`, then `T_n F = c • F` if and only if
`a_{nm}(F) = c a_m(F)` for every `m`. -/
theorem heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_mul_of_primeFactors_subset [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (c : ℂ) :
    heckeTCuspNat (N := N) k n F = c • F ↔
      ∀ m : ℕ, (qExpansion 1 F).coeff (n * m) = c * (qExpansion 1 F).coeff m := by
  have hop : ((heckeTNat (N := N) k n
      (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      ((heckeTCuspNat (N := N) k n F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) := by
    simp [coe_heckeTNat, coe_heckeTCuspNat]
  have key := heckeTNat_eq_smul_iff_forall_qExpansion_coeff_mul_of_primeFactors_subset k hn
    (F := (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) c
  simp only [ModularFormClass.coe_modularForm] at key
  rw [← key]
  constructor
  · intro hT
    refine DFunLike.ext _ _ fun τ ↦ ?_
    have := DFunLike.congr_fun hT τ
    simpa [hop] using this
  · intro hT
    refine CuspForm.toModularFormₗ_injective (DFunLike.ext _ _ fun τ ↦ ?_)
    have := DFunLike.congr_fun hT τ
    simpa [CuspForm.toModularFormₗ_eq_coe, hop] using this

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
