/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composite
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar

/-!
# Fourier coefficients of composite Hecke operators

For an index `n` coprime to the level, every positive Fourier coefficient of the action of the
composite Hecke-ring element `T_n` on `M_k(N, χ)` has the classical divisor-sum formula

`a_m(T_n F) = ∑ d ∣ gcd(m,n), χ(d) d^{k−1} a_{mn/d²}(F)`.

The proof reads the coefficient at `m` as the first coefficient of `T_m T_n F`, applies the
global multiplication table in the `Γ₀(N)` Hecke ring, and evaluates its scalar cosets. This
avoids a second induction over the prime factorisation: the ring multiplication table already
contains exactly the divisor arithmetic of the coefficient formula.

The character is written through `MulChar.ofUnitHom`, Mathlib's zero-extension of a unit
homomorphism to a Dirichlet character. Every divisor occurring here is coprime to `N`, so the
formula agrees with evaluation of `χ` on `ZMod.unitOfCoprime`.

## Main results

* `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_ne_zero`: the
  divisor-sum formula at positive indices on `M_k(N, χ)`.
* `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0`: its
  cusp-form specialization.

## Provenance

The statement is the coefficient formula `fourierCoeff_heckeT_n_period_one` from the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`), file
`LeanModularForms/HeckeRIngs/GL2/FourierHecke.lean`. The proof here instead derives it from Tau
Ceti's Hecke-ring multiplication table.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.3.1.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- At a prime dividing the level, the recurrence block `T_{p^r}` shifts every Fourier
coefficient by `p^r`. This is the bad-prime counterpart of
`qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_not_dvd`. -/
private theorem qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_dvd
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (F : modFormCharSpace k χ) (m r : ℕ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ r * m) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hpc : ¬ Nat.Coprime p N := fun h ↦ (hp.coprime_iff_not_dvd.mp h) hpN
  rw [heckeTGeneratorRecGamma0_eq_generator_pow_of_not_coprime N hpc, map_pow]
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply,
        coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp]
      have hs := qExpansion_coeff_heckeTNat_of_primeFactors_subset (N := N) k p
        (Nat.primeFactors_mono hpN (NeZero.ne N))
        (((heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p)) ^ r) F :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k) m
      rw [hs, ih]
      congr 1
      simp [pow_succ', mul_assoc, mul_left_comm]

/-- The first coefficient of the action of `T_n` is the `n`-th coefficient, including when
`n` has prime factors dividing the level. This is the private normalization step needed to
read an arbitrary coefficient from the multiplication table. -/
private theorem qExpansion_coeff_one_heckeRingHomCharSpace_heckeTCompositeGamma0
    {n : ℕ} (hn : n ≠ 0) (F : modFormCharSpace k χ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 =
      (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n := by
  suffices key : ∀ n : ℕ, n ≠ 0 → ∀ m : ℕ, Nat.Coprime m n →
      (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
        (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m * n) by
    simpa using key n hn 1 (Nat.coprime_one_left n)
  clear hn n
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn m hmn
  by_cases h1 : n = 1
  · subst h1
    rw [heckeTCompositeGamma0_one, map_one, Module.End.one_apply, mul_one]
  · have hlt : 1 < n := by omega
    rw [heckeTCompositeGamma0_of_one_lt N hlt, map_mul, Module.End.mul_apply]
    have hp : n.minFac.Prime := Nat.minFac_prime h1
    have hpn : n.minFac ∣ n := Nat.minFac_dvd n
    have hv : n.factorization n.minFac ≠ 0 :=
      (hp.factorization_pos_of_dvd hn hpn).ne'
    have hnn' : n.minFac ^ n.factorization n.minFac *
        (n / n.minFac ^ n.factorization n.minFac) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n n.minFac
    have hn'0 : n / n.minFac ^ n.factorization n.minFac ≠ 0 := by
      intro h
      rw [h, mul_zero] at hnn'
      exact hn hnn'.symm
    have hn'lt : n / n.minFac ^ n.factorization n.minFac < n :=
      Nat.div_lt_self (Nat.pos_of_ne_zero hn) (Nat.one_lt_pow hv hp.one_lt)
    have hpm : ¬ n.minFac ∣ m :=
      (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_right hpn hmn).symm
    have hcop : Nat.Coprime (n.minFac ^ n.factorization n.minFac * m)
        (n / n.minFac ^ n.factorization n.minFac) :=
      Nat.Coprime.mul_left ((Nat.coprime_ordCompl hp hn).pow_left _)
        (Nat.Coprime.coprime_dvd_right (Nat.ordCompl_dvd n n.minFac) hmn)
    by_cases hpN : n.minFac ∣ N
    · rw [qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_dvd hp hpN,
        ih _ hn'lt hn'0 _ hcop, mul_comm (n.minFac ^ n.factorization n.minFac) m,
        mul_assoc, hnn']
    · have hpNc : Nat.Coprime n.minFac N := hp.coprime_iff_not_dvd.mpr hpN
      rw [qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_not_dvd hp hpNc _
          hpm,
        ih _ hn'lt hn'0 _ hcop, mul_comm (n.minFac ^ n.factorization n.minFac) m,
        mul_assoc, hnn']

/-- **The divisor-sum formula for the composite Hecke action on `M_k(N, χ)`.** If `n` is
nonzero and coprime to the level, then

`a_m(T_n F) = ∑ d ∣ gcd(m,n), χ(d) d^{k−1} a_{mn/d²}(F)`.

Here `χ(d)` is Mathlib's zero-extension `MulChar.ofUnitHom χ`; every divisor in the sum is
in fact a unit modulo `N` by the coprimality hypothesis. -/
theorem qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_ne_zero {n : ℕ}
    (hn : n ≠ 0) (hnN : Nat.Coprime n N) (F : modFormCharSpace k χ) {m : ℕ} (hm : m ≠ 0) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) d * (d : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
            (m * n / d ^ 2) := by
  rw [← qExpansion_coeff_one_heckeRingHomCharSpace_heckeTCompositeGamma0 hm]
  rw [← Module.End.mul_apply, ← map_mul,
    heckeTCompositeGamma0_mul_eq_sum_divisors_gcd N hm hn, map_sum]
  rw [LinearMap.sum_apply]
  rw [← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map _), Submodule.coe_sum, map_sum, map_sum]
  simp only [map_zsmul]
  apply Finset.sum_congr rfl
  intro d hd
  have hd_dvd : d ∣ Nat.gcd m n := Nat.dvd_of_mem_divisors hd
  have hdN : Nat.Coprime d N :=
    Nat.Coprime.coprime_dvd_left (hd_dvd.trans (Nat.gcd_dvd_right m n)) hnN
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  have hr_dvd : d ^ 2 ∣ m * n := by
    rw [pow_two]
    exact Nat.mul_dvd_mul (Nat.dvd_gcd_iff.mp hd_dvd).1 (Nat.dvd_gcd_iff.mp hd_dvd).2
  have hr : m * n / d ^ 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hm hn)) hr_dvd)
      (pow_pos hd_pos 2)).ne'
  rw [LinearMap.smul_apply, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℂ,
    Submodule.coe_smul, map_smul, map_mul, Module.End.mul_apply,
    heckeRingHomCharSpace_heckeTScalarGamma0 k χ d hd_pos hdN, LinearMap.smul_apply,
    Module.End.one_apply, Submodule.coe_smul, map_smul, map_smul, map_smul,
    TauCeti.ModularForm.qExpansionLinearMap_apply,
    qExpansion_coeff_one_heckeRingHomCharSpace_heckeTCompositeGamma0 hr]
  rw [← ZMod.coe_unitOfCoprime d hdN, MulChar.ofUnitHom_coe]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  have hk : k - 1 = k - 2 + 1 := by ring
  rw [hk, zpow_add_one₀ hd0]
  ring

/-- **The divisor-sum formula on `S_k(N, χ)`.** This is the modular-form formula transported
along the inclusion `cuspToModFormCharSpace`. -/
theorem qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 {n : ℕ}
    (hn : n ≠ 0) (hnN : Nat.Coprime n N) (F : cuspFormCharSpace k χ) (m : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) d * (d : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
            (m * n / d ^ 2) := by
  by_cases hm : m = 0
  · subst m
    rw [CuspFormClass.qExpansion_coeff_zero _ one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _)]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    rw [zero_mul, Nat.zero_div, CuspFormClass.qExpansion_coeff_zero _ one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _), mul_zero]
  · have h := qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_ne_zero hn hnN
      (cuspToModFormCharSpace k χ F) hm
    rw [heckeRingHomCharSpace_apply,
      ← cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap,
      ← heckeRingHomCuspCharSpace_apply] at h
    simp only [coe_cuspToModFormCharSpace, ModularFormClass.coe_modularForm] at h
    exact h

end HeckeRing.GL2
