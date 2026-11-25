/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Card

/-!
# The projective images of `Γ₀(N)` and `Γ(N)`

The compactified modular curve is a quotient by a subgroup of `PSL₂(ℤ)`, while congruence
subgroups are defined inside `SL₂(ℤ)`. Since `Γ₀(N)` contains the center `{±I}`, passing to its
projective image does not change its index, and lifting that image back to `SL₂(ℤ)` recovers
`Γ₀(N)`. This identifies the arithmetic index with the degree input used by the compactified
quotient map.

The principal congruence subgroup `Γ(N)` behaves differently: for `N ≥ 3` it does not contain
`-I`, so its projective image has half its index: the image of `Γ(N)` in `PSL₂(ℤ)` has index
`|SL₂(ℤ/Nℤ)| / 2`. At `N = 3` the two indices are `24` and `12`. With the order of `SL₂(ℤ/Nℤ)`
this index is `(N³/2) ∏_{p ∣ N} (1 - 1/p²)` for `N ≥ 3`, while it is `1` at `N = 1` and `6` at
`N = 2`, where `-I ∈ Γ(N)`. A subgroup of `PSL₂(ℤ)` containing the image of `Γ(N)` has index
dividing this one; at `N = 6, 8, 10, 12` it is `72, 192, 360, 576`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.2 (the index of `Γ(N)` and of `±Γ(N)`).
-/

public section

open scoped MatrixGroups

namespace TauCeti.CongruenceSubgroup

/-- The image of `Γ₀(N)` in `PSL₂(ℤ)`, the group acting effectively on the upper half-plane. -/
def Gamma0Projective (N : ℕ) : Subgroup PSL(2, ℤ) :=
  (CongruenceSubgroup.Gamma0 N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- The projective image is the image under the quotient map by the center. -/
theorem Gamma0Projective_def (N : ℕ) :
    Gamma0Projective N =
      (CongruenceSubgroup.Gamma0 N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := (rfl)

/-- The center of `SL₂(ℤ)` is contained in every congruence subgroup `Γ₀(N)`. -/
theorem center_le_Gamma0 (N : ℕ) :
    Subgroup.center SL(2, ℤ) ≤ CongruenceSubgroup.Gamma0 N :=
  Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr CongruenceSubgroup.neg_one_mem_Gamma0

/-- Membership of the image of a matrix in `Γ₀(N)` is unchanged by projectivization. -/
@[simp]
theorem mem_Gamma0Projective_mk (N : ℕ) (A : SL(2, ℤ)) :
    (↑A : PSL(2, ℤ)) ∈ Gamma0Projective N ↔
      A ∈ CongruenceSubgroup.Gamma0 N := by
  rw [Gamma0Projective_def, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    obtain ⟨C, hC, hBC⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mp hBA
    rw [← hBC]
    exact mul_mem hB (center_le_Gamma0 N hC)
  · intro hA
    exact ⟨A, hA, rfl⟩

/-- A projective element belongs to the image of `Γ₀(N)` exactly when one of its
representatives belongs to `Γ₀(N)`. -/
theorem mem_Gamma0Projective_iff (N : ℕ) (g : PSL(2, ℤ)) :
    g ∈ Gamma0Projective N ↔
    ∃ A : SL(2, ℤ), QuotientGroup.mk' (Subgroup.center SL(2, ℤ)) A = g ∧
        A ∈ CongruenceSubgroup.Gamma0 N := by
  rw [Gamma0Projective_def, Subgroup.mem_map]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, rfl, hA⟩
  · rintro ⟨A, rfl, hA⟩
    exact ⟨A, hA, rfl⟩

/-- The projective image of `Γ₀(N)` has the same index as `Γ₀(N)`: the quotient map's kernel,
the center of `SL₂(ℤ)`, is already contained in `Γ₀(N)`. -/
theorem Gamma0Projective_index (N : ℕ) :
    (Gamma0Projective N).index = (CongruenceSubgroup.Gamma0 N).index :=
  Matrix.SpecialLinearGroup.index_map_mk'_of_neg_one_mem CongruenceSubgroup.neg_one_mem_Gamma0

/-- The lift of the projective image of `Γ₀(N)` to `SL₂(ℤ)` is `Γ₀(N)`, which contains `-I`. -/
@[simp]
theorem liftSL_Gamma0Projective (N : ℕ) :
    (Gamma0Projective N).liftSL = CongruenceSubgroup.Gamma0 N :=
  Matrix.SpecialLinearGroup.liftSL_map_of_neg_one_mem CongruenceSubgroup.neg_one_mem_Gamma0

/-- **The projective index of `Γ(N)`** for `N ≥ 3`: since `-I ∉ Γ(N)`, the image of `Γ(N)` in
`PSL₂(ℤ)` has index `|SL₂(ℤ/Nℤ)| / 2`. -/
theorem two_mul_index_map_Gamma {N : ℕ} (hN : 3 ≤ N) :
    2 * ((CongruenceSubgroup.Gamma N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = Nat.card SL(2, ZMod N) := by
  rw [Matrix.SpecialLinearGroup.two_mul_index_map_mk'_of_neg_one_notMem,
    CongruenceSubgroup.index_Gamma]
  rw [CongruenceSubgroup.neg_one_mem_Gamma_iff]
  exact fun h ↦ by have := Nat.le_of_dvd two_pos h; omega

/-- The image of `Γ(3)` in `PSL₂(ℤ)` has index `12`, half the index of `Γ(3)`, since `-I ∉ Γ(3)`. -/
theorem index_map_Gamma_three :
    ((CongruenceSubgroup.Gamma 3).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 12 := by
  have h := two_mul_index_map_Gamma le_rfl
  rw [← CongruenceSubgroup.index_Gamma, CongruenceSubgroup.index_Gamma_three] at h
  omega

/-- **The order of `SL₂(ℤ/Nℤ)/{±1}`** for `N ≥ 3`: the image of `Γ(N)` in `PSL₂(ℤ)` has index
`(N³/2) ∏_{p ∣ N} (1 - 1/p²)`, here with the denominators cleared. -/
theorem two_mul_index_map_Gamma_mul_prod_primeFactors {N : ℕ} (hN : 3 ≤ N) :
    2 * ((CongruenceSubgroup.Gamma N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [two_mul_index_map_Gamma hN]
  exact natCard_SL_fin_two_zmod_mul_prod_primeFactors N

/-- The image of `Γ(1) = SL₂(ℤ)` in `PSL₂(ℤ)` is everything, of index `1`. -/
theorem index_map_Gamma_one :
    ((CongruenceSubgroup.Gamma 1).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 1 := by
  rw [CongruenceSubgroup.Gamma_one_top,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), Subgroup.index_top]

/-- The image of `Γ(2)` in `PSL₂(ℤ)` has index `6 = |SL₂(𝔽₂)|`: since `-I ∈ Γ(2)`, projecting
does not halve the index. -/
theorem index_map_Gamma_two :
    ((CongruenceSubgroup.Gamma 2).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 6 := by
  rw [Matrix.SpecialLinearGroup.index_map_mk'_of_neg_one_mem
      (CongruenceSubgroup.neg_one_mem_Gamma_iff.mpr dvd_rfl),
    CongruenceSubgroup.index_Gamma, natCard_SL_fin_two_zmod]
  norm_num

/-- The image of `Γ(6)` in `PSL₂(ℤ)` has index `72 = |SL₂(𝔽₂)| · |SL₂(𝔽₃)| / 2`. -/
theorem index_map_Gamma_six :
    ((CongruenceSubgroup.Gamma 6).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 72 := by
  have h := two_mul_index_map_Gamma (N := 6) (by norm_num)
  have hc : Nat.card SL(2, ZMod 6) = 144 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Matrix.natCard_SL_zmod_mul (by norm_num),
      natCard_SL_fin_two_zmod, natCard_SL_fin_two_zmod]
    norm_num
  omega

/-- The image of `Γ(8)` in `PSL₂(ℤ)` has index `192 = |SL₂(ℤ/8ℤ)| / 2`. -/
theorem index_map_Gamma_eight :
    ((CongruenceSubgroup.Gamma 8).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 192 := by
  have h := two_mul_index_map_Gamma (N := 8) (by norm_num)
  have hc : Nat.card SL(2, ZMod 8) = 384 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Matrix.natCard_SL_zmod_pow three_ne_zero,
      natCard_SL_fin_two_zmod, Fintype.card_fin]
    norm_num
  omega

/-- The image of `Γ(10)` in `PSL₂(ℤ)` has index `360 = |SL₂(𝔽₂)| · |SL₂(𝔽₅)| / 2`. -/
theorem index_map_Gamma_ten :
    ((CongruenceSubgroup.Gamma 10).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 360 := by
  have h := two_mul_index_map_Gamma (N := 10) (by norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : Nat.card SL(2, ZMod 10) = 720 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, Matrix.natCard_SL_zmod_mul (by norm_num),
      natCard_SL_fin_two_zmod, natCard_SL_fin_two_zmod]
    norm_num
  omega

/-- The image of `Γ(12)` in `PSL₂(ℤ)` has index `576 = |SL₂(ℤ/4ℤ)| · |SL₂(𝔽₃)| / 2`. -/
theorem index_map_Gamma_twelve :
    ((CongruenceSubgroup.Gamma 12).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 576 := by
  have h := two_mul_index_map_Gamma (N := 12) (by norm_num)
  have hc : Nat.card SL(2, ZMod 12) = 1152 := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Matrix.natCard_SL_zmod_mul (by norm_num),
      Matrix.natCard_SL_zmod_pow two_ne_zero, natCard_SL_fin_two_zmod, natCard_SL_fin_two_zmod,
      Fintype.card_fin]
    norm_num
  omega

end TauCeti.CongruenceSubgroup
