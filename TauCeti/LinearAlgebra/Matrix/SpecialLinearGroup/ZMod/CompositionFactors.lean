/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.Subgroup.IsSubnormal
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Solvable
import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Composition factors of `SL₂(ℤ/Nℤ)` and non-isomorphism with alternating groups

This file classifies the nonabelian simple subnormal sections of `SL₂(ℤ/Nℤ)` (`N ≠ 0`) and rules
out alternating groups of degree `≥ 6`:

* `Matrix.ProjectiveSpecialLinearGroup.eq_of_fin_two_zmod_mulEquiv`: `PSL₂(𝔽_p) ≃* PSL₂(𝔽_q)`
  implies `p = q` for primes `p, q`.
* `Matrix.ProjectiveSpecialLinearGroup.isEmpty_alternatingGroup_mulEquiv`: no alternating group
  `A_α` with `6 ≤ Nat.card α` is isomorphic to any `PSL₂(𝔽_ℓ)`.
* `Matrix.SpecialLinearGroup.exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection`: every
  nonabelian simple subnormal section of `SL₂(ℤ/Nℤ)` (`N ≠ 0`) is isomorphic to `PSL₂(𝔽_ℓ)` for
  a prime `ℓ ≥ 5` dividing `N`.
* `Matrix.SpecialLinearGroup.not_hasSubnormalSection_alternatingGroup`: no alternating group `A_α`
  with `6 ≤ Nat.card α` occurs as a subnormal section of `SL₂(ℤ/Nℤ)` (`N ≠ 0`).

## References

* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University
  Press, 1971, §1.6.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §1.2.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

/-- **Distinct primes have non-isomorphic projective special linear groups `PSL₂(𝔽_p)`:** if
`PSL₂(𝔽_p) ≃* PSL₂(𝔽_q)` with `p, q` prime, then `p = q`. -/
theorem eq_of_fin_two_zmod_mulEquiv {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (e : PSL(2, ZMod p) ≃* PSL(2, ZMod q)) : p = q := by
  wlog hpq : p ≤ q generalizing p q
  · exact (this hq hp e.symm (by omega)).symm
  rcases hpq.eq_or_lt with rfl | hlt
  · rfl
  · exfalso
    have hcard : Nat.card PSL(2, ZMod p) = Nat.card PSL(2, ZMod q) := Nat.card_congr e.toEquiv
    have hq2 : q ≠ 2 := by have := hp.two_le; omega
    have hq_eq := two_mul_card_fin_two_zmod_prime hq hq2
    by_cases hp2 : p = 2
    · subst hp2
      rw [← hcard, card_fin_two_zmod_two] at hq_eq
      have : 3 * (3 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
      omega
    · have hp_eq := two_mul_card_fin_two_zmod_prime hp hp2
      have h1 : 1 < p ^ 2 := by nlinarith [hp.two_le]
      have h2 : p ^ 2 < q ^ 2 := by nlinarith [hp.two_le]
      have : p * (p ^ 2 - 1) < q * (q ^ 2 - 1) :=
        (Nat.mul_lt_mul_of_pos_right hlt (by omega)).trans
          (Nat.mul_lt_mul_of_pos_left (by omega) hq.pos)
      omega

/-- **No alternating group of degree `≥ 6` is isomorphic to any `PSL₂(𝔽_ℓ)`.** If `ℓ` divided
`|A_n| = n!/2`, primality would give `ℓ ≤ n`, forcing `|PSL₂(𝔽_ℓ)| = ℓ(ℓ² - 1)/2 < n³/2 ≤ n!/2`
for `n ≥ 6`. -/
theorem isEmpty_alternatingGroup_mulEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 6 ≤ Nat.card α) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    IsEmpty (alternatingGroup α ≃* PSL(2, ZMod ℓ)) := ⟨fun e ↦ by
  set n := Nat.card α
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]; omega
  have halt : 2 * Nat.card (alternatingGroup α) = n.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm]
  have hcard : Nat.card (alternatingGroup α) = Nat.card PSL(2, ZMod ℓ) := Nat.card_congr e.toEquiv
  have h6 : 720 ≤ n.factorial :=
    (by decide : 720 = (6 : ℕ).factorial).trans_le (Nat.factorial_le hα)
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2; rw [hcard, card_fin_two_zmod_two] at halt; omega
  · have hpsl := two_mul_card_fin_two_zmod_prime hℓ hℓ2
    have hℓ_le : ℓ ≤ n := hℓ.dvd_factorial.mp ⟨ℓ ^ 2 - 1, by omega⟩
    have hsub : ℓ ^ 2 - 1 < n ^ 2 := by
      have : 1 ≤ ℓ ^ 2 := Nat.one_le_pow 2 ℓ hℓ.pos
      have : ℓ ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hℓ_le 2
      omega
    have hlt_cube : ℓ * (ℓ ^ 2 - 1) < n ^ 3 := by
      calc ℓ * (ℓ ^ 2 - 1) < ℓ * n ^ 2 := Nat.mul_lt_mul_of_pos_left hsub hℓ.pos
        _ ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hℓ_le
        _ = n ^ 3 := by ring
    have hcube : ∀ m, 6 ≤ m → m ^ 3 ≤ m.factorial := fun m hm ↦ by
      induction m, hm using Nat.le_induction with
      | base => decide
      | succ k hk ih =>
        rw [Nat.factorial_succ]
        have : (k + 1) ^ 2 ≤ k ^ 3 := by nlinarith
        calc (k + 1) ^ 3 = (k + 1) * (k + 1) ^ 2 := by ring
          _ ≤ (k + 1) * k ^ 3 := Nat.mul_le_mul_left _ this
          _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left _ ih
    have := hcube n hα; omega⟩

end Matrix.ProjectiveSpecialLinearGroup

namespace Matrix.SpecialLinearGroup

/-- **Classification of nonabelian simple composition factors of `SL₂(ℤ/Nℤ)`.** For `N ≠ 0`,
every nonabelian simple group `S` occurring as a subnormal section of `SL₂(ℤ/Nℤ)` is isomorphic to
`PSL₂(𝔽_ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection {N : ℕ} (hN : N ≠ 0) {S : Type*}
    [Group S] [IsSimpleGroup S] (hnc : ¬ IsMulCommutative S)
    (hS : TauCeti.HasSubnormalSection SL(2, ZMod N) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) := by
  obtain ⟨⟨ℓ, hℓ_mem⟩, hℓ_sec⟩ := (hS.congr_left (zmodEquivPi (Fin 2) hN)).exists_of_pi
  obtain ⟨hℓ_prime, hℓ_dvd, _⟩ := Nat.mem_primeFactors.mp hℓ_mem
  have hk : 1 ≤ N.factorization ℓ :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa using hℓ_mem))
  let π : SL(2, ZMod (ℓ ^ N.factorization ℓ)) →* SL(2, ZMod ℓ) :=
    map (ZMod.castHom (dvd_pow_self ℓ (by omega)) (ZMod ℓ))
  have hSLℓ : TauCeti.HasSubnormalSection SL(2, ZMod ℓ) S := by
    rcases hℓ_sec.or_of_normal π.ker with hker | hquot
    · have := isSolvable_ker_map_zmod_prime_pow hℓ_prime hk
      exact False.elim (hnc hker.isMulCommutative_of_isSolvable)
    · exact hquot.congr_left (QuotientGroup.quotientKerEquivOfSurjective π
        (map_zmod_castHom_surjective (dvd_pow_self ℓ (by omega))))
  have : Fact ℓ.Prime := ⟨hℓ_prime⟩
  have hℓ5 : 5 ≤ ℓ := by
    by_contra! hlt5
    have hle3 : Nat.card (ZMod ℓ) ≤ 3 := by
      rw [Nat.card_zmod]; rcases hℓ_prime.eq_two_or_odd with rfl | hodd <;> omega
    have := TauCeti.Matrix.SpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three (ZMod ℓ) hle3
    exact hnc hSLℓ.isMulCommutative_of_isSolvable
  rcases hSLℓ.or_of_normal (Subgroup.center SL(2, ZMod ℓ)) with hcen | hpsl
  · exact False.elim (hnc hcen.isMulCommutative_of_isSolvable)
  · have : IsSimpleGroup PSL(2, ZMod ℓ) :=
      ProjectiveSpecialLinearGroup.isSimpleGroup_of_four_le_natCard (by rw [Nat.card_zmod]; omega)
    exact ⟨ℓ, hℓ_prime, hℓ5, hℓ_dvd, hpsl.nonempty_mulEquiv_of_isSimpleGroup⟩

/-- **No alternating group `A_α` of degree `≥ 6` occurs as a subnormal section of `SL₂(ℤ/Nℤ)`**
(`N ≠ 0`). -/
theorem not_hasSubnormalSection_alternatingGroup {N : ℕ} (hN : N ≠ 0) {α : Type*}
    [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α) :
    ¬ TauCeti.HasSubnormalSection SL(2, ZMod N) (alternatingGroup α) := fun hsec ↦ by
  have h5 : 5 ≤ Nat.card α := by omega
  have hsimp := alternatingGroup.isSimpleGroup h5
  have := hsimp.toNontrivial
  have hnc : ¬ IsMulCommutative (alternatingGroup α) := fun _ ↦
    bot_ne_top ((commutator_eq_bot (G := alternatingGroup α)).symm.trans
      (commutator_alternatingGroup_eq_top h5))
  obtain ⟨ℓ, hℓ, -, -, ⟨e⟩⟩ := exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hnc hsec
  exact (ProjectiveSpecialLinearGroup.isEmpty_alternatingGroup_mulEquiv hα hℓ).false e

end Matrix.SpecialLinearGroup
