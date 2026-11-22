/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Data.Nat.Prime.Factorial
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.ZMod

/-!
# Non-isomorphism between alternating groups and `PSL₂(𝔽_ℓ)`

No alternating group `A_α` of degree `≥ 6` is isomorphic to `PSL₂(𝔽_ℓ)` for any prime `ℓ`
(`Matrix.ProjectiveSpecialLinearGroup.isEmpty_alternatingGroup_mulEquiv`): if `ℓ` divided
`|A_n| = n!/2`, primality would give `ℓ ≤ n`, forcing `|PSL₂(𝔽_ℓ)| = ℓ(ℓ² - 1)/2 < n³/2 ≤ n!/2`
for `n ≥ 6`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §1.2.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

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
