/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.GroupTheory.Subgroup.IsSubnormal
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.Alternating
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.FinTwo.Solvable
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.CongruenceKernel
import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Composition factors of `SL₂(ℤ/Nℤ)` and non-isomorphism with alternating groups

This file classifies the nonabelian simple subnormal sections of `SL₂(ℤ/Nℤ)` (`N ≠ 0`) and rules
out alternating groups of degree `≥ 6`:

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
  have hnc : ¬ IsMulCommutative (alternatingGroup α) := fun hc ↦ by
    have := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
    omega
  obtain ⟨ℓ, hℓ, -, -, ⟨e⟩⟩ := exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hnc hsec
  exact (ProjectiveSpecialLinearGroup.isEmpty_alternatingGroup_mulEquiv hα hℓ).false e

end Matrix.SpecialLinearGroup
