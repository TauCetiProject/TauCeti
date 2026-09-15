/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composite
import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar

/-!
# Fourier coefficients of composite Hecke operators

For an index `n` coprime to the level, every positive Fourier coefficient of the action of the
composite Hecke-ring element `T_n` on `M_k(N, χ)` has the classical divisor-sum formula

`a_m(T_n F) = ∑ d ∣ gcd(m,n), χ(d) d^{k−1} a_{mn/d²}(F)`.

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
`LeanModularForms/HeckeRIngs/GL2/FourierHecke.lean`.

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
coefficient by `p^r`. This is private infrastructure for the first-coefficient normalization. -/
private theorem qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_dvd
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (F : modFormCharSpace k χ) (m r : ℕ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ r * m) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hpc : ¬ Nat.Coprime p N := fun h ↦ (hp.coprime_iff_not_dvd.mp h) hpN
  rw [heckeTGeneratorRecGamma0_eq_generator_pow_of_not_coprime N hpc, map_pow,
    heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp]
  have hpow :
      ((((heckeTNat (N := N) k p).restrict
          (fun _ hf ↦ heckeTNat_mem_modFormCharSpace k χ hp hf)) ^ r) F :
            ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
        ((heckeTNat (N := N) k p) ^ r)
          (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      change heckeTNat (N := N) k p
          ((((heckeTNat (N := N) k p).restrict
            (fun _ hf ↦ heckeTNat_mem_modFormCharSpace k χ hp hf)) ^ r) F :
              ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = _
      rw [ih]
  rw [hpow]
  rw [← heckeTNat_pow_of_dvd (k := k) hpN r]
  have hsubset : (p ^ r).primeFactors ⊆ N.primeFactors := by
    rcases r with _ | r
    · simp
    · rw [Nat.primeFactors_pow p (Nat.succ_ne_zero r)]
      exact Nat.primeFactors_mono hpN (NeZero.ne N)
  exact qExpansion_coeff_heckeTNat_of_primeFactors_subset (N := N) k (p ^ r)
    hsubset _ m

/-- The first coefficient of the action of `T_n` is the `n`-th coefficient, including when
`n` has prime factors dividing the level. This private normalization reads arbitrary
coefficients from the multiplication table. -/
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

/-- The first Fourier coefficient of `S_c T_r F`: the scalar generator contributes
`χ(c) c^{k−2}`, and the first coefficient of `T_r F` is `a_r(F)`. -/
private theorem qExpansion_coeff_one_heckeRingHomCharSpace_heckeTScalarGamma0_mul {c r : ℕ}
    (hc : 0 < c) (hcN : Nat.Coprime c N) (hr : r ≠ 0) (F : modFormCharSpace k χ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ
        (heckeTScalarGamma0 N c * heckeTCompositeGamma0 N r) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 =
      (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) c * (c : ℂ) ^ (k - 2) *
        (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff r := by
  rw [map_mul, Module.End.mul_apply, heckeRingHomCharSpace_heckeTScalarGamma0 k χ c hc hcN,
    LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, qExpansion_coeff_one_heckeRingHomCharSpace_heckeTCompositeGamma0 hr,
    smul_eq_mul, ← ZMod.coe_unitOfCoprime c hcN, MulChar.ofUnitHom_coe]

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
  rw [← qExpansion_coeff_one_heckeRingHomCharSpace_heckeTCompositeGamma0 hm,
    ← Module.End.mul_apply, ← map_mul, heckeTCompositeGamma0_mul_eq_sum_divisors_gcd N hm hn,
    ← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _)]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    natCast_zsmul, map_nsmul]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd_dvd : d ∣ Nat.gcd m n := Nat.dvd_of_mem_divisors hd
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdN : Nat.Coprime d N :=
    Nat.Coprime.coprime_dvd_left (hd_dvd.trans (Nat.gcd_dvd_right m n)) hnN
  have hr : m * n / d ^ 2 ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by positivity)
    (pow_two d ▸ Nat.mul_dvd_mul (Nat.dvd_gcd_iff.mp hd_dvd).1 (Nat.dvd_gcd_iff.mp hd_dvd).2))
    (by positivity)).ne'
  simp only [Submodule.coe_smul_of_tower, map_nsmul, TauCeti.ModularForm.qExpansionLinearMap_apply,
    qExpansion_coeff_one_heckeRingHomCharSpace_heckeTScalarGamma0_mul hd_pos hdN hr]
  rw [show k - 1 = k - 2 + 1 by ring, zpow_add_one₀ (Nat.cast_ne_zero.mpr hd_pos.ne'), nsmul_eq_mul]
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
