/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Power

/-!
# The Fourier coefficient of `T_n F` at an index coprime to `n`

The composite element `heckeTCompositeGamma0 N n` of the `Γ₀(N)` Hecke ring is the ordered
product of the prime-power blocks `heckeTGeneratorRecGamma0 N p (v_p n)` over the primes of `n`
(`HeckeRing/GL2/Gamma0/Diagonal/Composite.lean`), and each block reads the coefficient at
`p^{v_p n} m` when `p ∤ m` (`HeckeSlash/Nebentypus/Prime/Power.lean`). Peeling the blocks off one
at a time therefore gives, for `n ≠ 0` coprime to the level and `m` coprime to `n`,

`a_m(T_n F) = a_{m n}(F)`.

Coprimality of `m` and `n` is what makes the formula this simple: each block meets an index
prime to its own prime, so only the leading term of the prime-power formula survives. At `m = 1`
it says `a_1(T_n F) = a_n(F)`; read on a Hecke eigenvector, where `T_n F = λ_n F`, that is
`a_n(F) = λ_n a_1(F)` — the coefficient form of the eigenvalue system
(`Newforms/Coefficient.lean`).

## Main results

* `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime`:
  `a_m(T_n F) = a_{m n}(F)` for `n ≠ 0` coprime to `N` and `m` coprime to `n`, on `M_k(N, χ)`.
* `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_of_coprime`:
  its specialisation to `S_k(N, χ)`, along `cuspToModFormCharSpace`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/FourierHecke.lean` —
`fourierCoeff_heckeT_n_period_one`, the divisor-sum formula at a general index for the source's
concretely-defined `heckeT_n`, which at indices coprime to `n` collapses to the single
coefficient below. Here the operator is the Hecke ring's composite element
`heckeTCompositeGamma0` acting through `heckeRingHomCharSpace`, so the proof peels its
prime-power blocks instead of summing over divisors.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.3.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **The Fourier coefficient of `T_n F` at an index coprime to `n`.** For `n ≠ 0` coprime to the
level and `m` coprime to `n`, the Hecke ring's composite element reads the coefficient at `m n`:
`a_m(T_n F) = a_{m n}(F)`. -/
theorem qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime {n : ℕ}
    (hn : n ≠ 0) (hnN : Nat.Coprime n N) (F : modFormCharSpace k χ) {m : ℕ}
    (hmn : Nat.Coprime m n) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m * n) := by
  suffices key : ∀ n : ℕ, n ≠ 0 → Nat.Coprime n N → ∀ m : ℕ, Nat.Coprime m n →
      (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
        (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m * n) by
    exact key n hn hnN m hmn
  clear hmn hnN hn m n
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hnN m hmn
  by_cases h1 : n = 1
  · subst h1
    rw [heckeTCompositeGamma0_one, map_one, Module.End.one_apply, mul_one]
  · -- peel the block at the least prime factor `p` of `n`, carrying its whole multiplicity
    have hlt : 1 < n := by omega
    rw [heckeTCompositeGamma0_of_one_lt N hlt, map_mul, Module.End.mul_apply]
    have hp : (n.minFac).Prime := Nat.minFac_prime h1
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
    have hpN : Nat.Coprime n.minFac N := Nat.Coprime.coprime_dvd_left hpn hnN
    have hn'N : Nat.Coprime (n / n.minFac ^ n.factorization n.minFac) N :=
      Nat.Coprime.coprime_dvd_left (Nat.ordCompl_dvd n n.minFac) hnN
    have hpm : ¬ n.minFac ∣ m :=
      (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_right hpn hmn).symm
    have hcop : Nat.Coprime (n.minFac ^ n.factorization n.minFac * m)
        (n / n.minFac ^ n.factorization n.minFac) :=
      Nat.Coprime.mul_left ((Nat.coprime_ordCompl hp hn).pow_left _)
        (Nat.Coprime.coprime_dvd_right (Nat.ordCompl_dvd n n.minFac) hmn)
    rw [qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_not_dvd hp hpN _ hpm,
      ih _ hn'lt hn'0 hn'N _ hcop, mul_comm (n.minFac ^ n.factorization n.minFac) m, mul_assoc,
      hnn']

/-- **The Fourier coefficient of `T_n F` at an index coprime to `n`, on `S_k(N, χ)`**: the case
of `qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime` at a cusp form,
transported along the inclusion of character spaces. -/
theorem qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_of_coprime {n : ℕ}
    (hn : n ≠ 0) (hnN : Nat.Coprime n N) (F : cuspFormCharSpace k χ) {m : ℕ}
    (hmn : Nat.Coprime m n) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m * n) := by
  have h := qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime hn hnN
    (cuspToModFormCharSpace k χ F) hmn
  rw [heckeRingHomCharSpace_apply, ← cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap,
    ← heckeRingHomCuspCharSpace_apply] at h
  simp only [coe_cuspToModFormCharSpace, ModularFormClass.coe_modularForm] at h
  exact h

end HeckeRing.GL2
