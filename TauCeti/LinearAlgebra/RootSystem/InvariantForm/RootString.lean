/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Invariant forms along root strings

This file records how an invariant bilinear form changes between consecutive roots in a root
string. It also shows that any integer-valued length function symmetrizing the Cartan integers is
quadratic along integral root relations. The results are the root-system calculation behind the
integrality of Chevalley structure constants.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.

This advances the Chevalley-basis input to the explicit Chevalley--Demazure construction in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the
`CFSGStatement` roadmap.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

section

variable {I M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

/-- A symmetrizing integer-valued length function is quadratic along integral root relations. -/
theorem _root_.RootPairing.length_of_root_eq_add_zsmul (P : RootPairing I ℤ M N)
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I) (n : ℤ) (h : P.root γ = P.root β + n • P.root α) :
    length γ = length β + n * length α * P.pairing β α + n ^ 2 * length α := by
  have hpair (j : I) : P.pairing γ j = P.pairing β j + n * P.pairing α j := by
    have hj := P.pairing_eq_add_of_root_eq_smul_add_smul (i := β) (j := j) (k := γ) (l := α)
      (x := Int.castRingHom ℤ 1) (y := Int.castRingHom ℤ n)
      (by simpa only [Int.coe_castRingHom, Int.cast_smul_eq_zsmul, one_zsmul] using h)
    simpa only [Int.coe_castRingHom, Int.cast_smul_eq_zsmul, one_zsmul, smul_eq_mul,
      Int.cast_id, one_mul] using hj
  have htwo :
      2 * length γ = 2 * (length β + n * length α * P.pairing β α + n ^ 2 * length α) := by
    calc
      2 * length γ = length γ * P.pairing γ γ := by rw [P.pairing_same]; ring
      _ = length γ * (P.pairing β γ + n * P.pairing α γ) := by rw [hpair γ]
      _ = length γ * P.pairing β γ + n * (length γ * P.pairing α γ) := by ring
      _ = length β * P.pairing γ β + n * (length α * P.pairing γ α) := by
        rw [hsym γ β, hsym γ α]
      _ = length β * (P.pairing β β + n * P.pairing α β) +
          n * (length α * (P.pairing β α + n * P.pairing α α)) := by
        rw [hpair β, hpair α]
      _ = 2 * (length β + n * length α * P.pairing β α + n ^ 2 * length α) := by
        rw [P.pairing_same, P.pairing_same]
        linear_combination -n * hsym α β
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) htwo

end

section

variable {I M N : Type*} [Finite I] [AddCommGroup M] [Module ℤ M]
  [Module.IsTorsionFree ℤ M] [AddCommGroup N] [Module ℤ N] {P : RootPairing I ℤ M N}
  [P.IsCrystallographic] [P.IsReduced]

omit [P.IsCrystallographic] [P.IsReduced] in
/-- Distinct non-opposite roots of equal positive length have Cartan pairing `-1`, `0`, or `1`
when that pairing has absolute value at most two. -/
theorem _root_.RootPairing.pairing_mem_neg_one_zero_one_of_length_eq
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β : I) (hpair : |P.pairing β α| ≤ 2)
    (hαpos : 0 < length α) (hαβ : length α = length β) (hne : β ≠ α)
    (hneg : P.root β ≠ -P.root α) :
    P.pairing β α ∈ ({-1, 0, 1} : Set ℤ) := by
  have hsym' : P.pairing β α = P.pairing α β := by
    have h := hsym α β
    rw [← hαβ] at h
    nlinarith
  have hne_two : P.pairing β α ≠ 2 := by
    intro htwo
    have : β = α := (P.pairing_two_two_iff β α).mp ⟨htwo, hsym'.symm.trans htwo⟩
    exact hne this
  have hne_neg_two : P.pairing β α ≠ -2 := by
    intro htwo
    have : P.root β = -P.root α :=
      (P.pairing_neg_two_neg_two_iff β α).mp ⟨htwo, hsym'.symm.trans htwo⟩
    exact hneg this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hbounds : -2 ≤ P.pairing β α ∧ P.pairing β α ≤ 2 := abs_le.mp hpair
  omega

omit [P.IsCrystallographic] [P.IsReduced] in
/-- An equal-length root string through non-opposite roots has no term two or more steps
in the positive direction when the resulting root has length less than three times theirs. -/
theorem _root_.RootPairing.not_root_eq_add_nsmul_of_length_eq_of_two_le
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I) (n : ℕ) (hpair : |P.pairing β α| ≤ 2)
    (hαpos : 0 < length α) (hαβ : length α = length β)
    (hγ : length γ < 3 * length α)
    (hneg : P.root β ≠ -P.root α) (hn : 2 ≤ n)
    (h : P.root γ = P.root β + (n : ℤ) • P.root α) : False := by
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hquad : 0 ≤ (n : ℤ) ^ 2 - n - 2 := by nlinarith
  have hne_or_eq : β = α ∨ β ≠ α := eq_or_ne β α
  have hp : P.pairing β α ∈ ({-1, 0, 1, 2} : Set ℤ) := by
    rcases hne_or_eq with hsame | hne
    · subst β
      simp
    · have hp' := P.pairing_mem_neg_one_zero_one_of_length_eq length hsym α β
        hpair hαpos hαβ hne hneg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp' ⊢
      rcases hp' with hp' | hp' | hp' <;> simp [hp']
  have hlen := P.length_of_root_eq_add_zsmul length hsym α β γ n h
  rw [← hαβ] at hlen
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp | hp <;>
    rw [hp] at hlen <;>
    nlinarith [mul_nonneg hquad (le_of_lt hαpos)]

omit [Finite I] [Module.IsTorsionFree ℤ M] [P.IsCrystallographic] [P.IsReduced] in
/-- If two roots of length one add to a root of length two, their Cartan pairing is zero. -/
theorem _root_.RootPairing.pairing_eq_zero_of_short_add_short_eq_long
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I) (hα : length α = 1) (hβ : length β = 1) (hγ : length γ = 2)
    (h : P.root γ = P.root β + P.root α) : P.pairing β α = 0 := by
  have hlen := P.length_of_root_eq_add_zsmul length hsym α β γ 1 (by simpa using h)
  rw [hα, hβ, hγ] at hlen
  norm_num at hlen ⊢
  omega

omit [Finite I] [Module.IsTorsionFree ℤ M] [P.IsCrystallographic] [P.IsReduced] in
/-- A positive root string from a root of length one in a length-two direction has at most one
step, and that step again has length one. -/
theorem _root_.RootPairing.n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I) (n : ℕ) (hpair : |P.pairing α β| ≤ 2)
    (hα : length α = 2) (hβ : length β = 1)
    (hγ : length γ = 1 ∨ length γ = 2) (hn : 0 < n)
    (h : P.root γ = P.root β + (n : ℤ) • P.root α) :
    n = 1 ∧ P.pairing β α = -1 ∧ length γ = 1 := by
  have hsym' : 2 * P.pairing β α = P.pairing α β := by
    have hs := hsym α β
    rw [hα, hβ, one_mul] at hs
    exact hs
  have hp : P.pairing β α ∈ ({-1, 0, 1} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hb := abs_le.mp hpair
    omega
  have hlen := P.length_of_root_eq_add_zsmul length hsym α β γ n h
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hnle : n ≤ 1 := by
    rcases hγ with hγ | hγ <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp <;>
      rcases hp with hp | hp | hp <;>
      rw [hα, hβ, hγ, hp] at hlen <;>
      norm_num at hlen <;>
      nlinarith [sq_nonneg ((n : ℤ) - 1)]
  have hn_eq : n = 1 := by omega
  subst n
  have hlen' := P.length_of_root_eq_add_zsmul length hsym α β γ 1 (by simpa using h)
  constructor
  · rfl
  rcases hγ with hγ | hγ
  · rw [hα, hβ, hγ] at hlen'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · exact ⟨hp, hγ⟩
    · rw [hp] at hlen'
      norm_num at hlen'
    · rw [hp] at hlen'
      norm_num at hlen'
  · rw [hα, hβ, hγ] at hlen'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp <;> rw [hp] at hlen' <;> norm_num at hlen'

omit [Module.IsTorsionFree ℤ M] in
/-- If two roots of length one add to a root of length two, and every root at the next positive
string position has length one or two, their descending chain coefficient is one. -/
theorem _root_.RootPairing.chainBotCoeff_eq_one_of_short_add_short_eq_long
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I)
    (hlength : ∀ δ, P.root δ = P.root β + (2 : ℤ) • P.root α →
      length δ = 1 ∨ length δ = 2)
    (hα : length α = 1) (hβ : length β = 1) (hγ : length γ = 2)
    (h : P.root γ = P.root β + P.root α) : P.chainBotCoeff α β = 1 := by
  have hrange : P.root α + P.root β ∈ Set.range P.root := by
    refine ⟨γ, ?_⟩
    rw [h, add_comm]
  have hlin := P.linearIndependent_of_add_mem_range_root' hrange
  have htop_ge := P.one_le_chainTopCoeff_of_root_add_mem hrange
  have hp := P.pairing_eq_zero_of_short_add_short_eq_long length hsym α β γ hα hβ hγ h
  have htop_le : P.chainTopCoeff α β ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ P.chainTopCoeff α β := by omega
    have hrange2 := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).2 htwo
    obtain ⟨δ, hδ⟩ := hrange2
    have hδ' : P.root δ = P.root β + (2 : ℤ) • P.root α := by
      simpa only [two_nsmul, two_zsmul] using hδ
    have hδlen := P.length_of_root_eq_add_zsmul length hsym α β δ 2 hδ'
    have hδlen' : length δ = 5 := by
      rw [hα, hβ, hp] at hδlen
      norm_num at hδlen ⊢
      exact hδlen
    rcases hlength δ hδ' with hδshort | hδlong <;> omega
  have htop : P.chainTopCoeff α β = 1 := by omega
  have hpIn : P.pairingIn ℤ β α = 0 := by
    simpa using (P.algebraMap_pairingIn ℤ β α).trans hp
  have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlin
  rw [htop] at hdiff
  norm_num at hdiff
  rw [hpIn] at hdiff
  omega

omit [Finite I] [Module.IsTorsionFree ℤ M] [P.IsCrystallographic] [P.IsReduced] in
/-- If adding twice a length-one root to a length-two root gives a root, the endpoint has length
two and the two Cartan pairings are `-2` and `-1`. -/
theorem _root_.RootPairing.pairings_of_long_add_two_short
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I)
    (hα : length α = 1) (hβ : length β = 2) (hγ : length γ = 1 ∨ length γ = 2)
    (h : P.root γ = P.root β + (2 : ℤ) • P.root α) :
    P.pairing β α = -2 ∧ P.pairing α β = -1 ∧ length γ = 2 := by
  have hlen := P.length_of_root_eq_add_zsmul length hsym α β γ 2 h
  have hsym' := hsym α β
  rcases hγ with hγ | hγ <;>
    rw [hα, hβ, hγ] at hlen <;>
    rw [hα, hβ] at hsym' <;>
    norm_num at hlen hsym' <;>
    constructor <;> omega

/-- A two-step root string from a length-two root in a length-one direction has a length-one
midpoint, and its chain coefficients are zero, two, one, and one. -/
theorem _root_.RootPairing.exists_short_midpoint_of_long_add_two_short
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I)
    (hα : length α = 1) (hβ : length β = 2) (hγ : length γ = 1 ∨ length γ = 2)
    (h : P.root γ = P.root β + (2 : ℤ) • P.root α) :
    ∃ δ : I, P.root δ = P.root β + P.root α ∧ length δ = 1 ∧
      P.chainBotCoeff α β = 0 ∧ P.chainTopCoeff α β = 2 ∧
      P.chainBotCoeff α δ = 1 ∧ P.chainTopCoeff α δ = 1 := by
  obtain ⟨hp, hp', hγ⟩ := P.pairings_of_long_add_two_short length hsym
    α β γ hα hβ hγ h
  have hne : α ≠ β := by
    intro hab
    subst β
    omega
  have hneg : P.root α ≠ -P.root β := by
    intro hneg
    have hpairs := (P.pairing_neg_two_neg_two_iff α β).2 hneg
    omega
  have hlin : LinearIndependent ℤ ![P.root α, P.root β] :=
    RootPairing.IsReduced.linearIndependent P hne hneg
  have htop_ge : 2 ≤ P.chainTopCoeff α β := by
    rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin]
    refine ⟨γ, ?_⟩
    have hcast : (2 : ℕ) • P.root α = (2 : ℤ) • P.root α := by
      simp only [two_nsmul, two_zsmul]
    rw [hcast]
    exact h
  have hpIn : P.pairingIn ℤ β α = -2 := by
    simpa using (P.algebraMap_pairingIn ℤ β α).trans hp
  have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlin
  have hsum : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 3 :=
    P.chainBotCoeff_add_chainTopCoeff_le_three
  have hbot : P.chainBotCoeff α β = 0 := by omega
  have htop : P.chainTopCoeff α β = 2 := by omega
  have hrange : P.root β + P.root α ∈ Set.range P.root := by
    have hrange' :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff (n := 1) hlin).2 (by omega)
    simpa only [one_nsmul] using hrange'
  obtain ⟨δ, hδ⟩ := hrange
  have hδlen := P.length_of_root_eq_add_zsmul length hsym α β δ 1 (by
    simpa only [one_zsmul] using hδ)
  have hδshort : length δ = 1 := by
    rw [hα, hβ, hp] at hδlen
    norm_num at hδlen
    exact hδlen
  have hδbot := P.chainBotCoeff_of_add hlin hδ
  have hδtop := P.chainTopCoeff_of_add hlin hδ
  refine ⟨δ, hδ, hδshort, hbot, htop, ?_, ?_⟩
  · omega
  · omega

omit [Module.IsTorsionFree ℤ M] [P.IsReduced] in
/-- A root edge whose source and target have the same positive length has no descending root
when every possible predecessor has length at most two. -/
theorem _root_.RootPairing.chainBotCoeff_eq_zero_of_add_of_length_eq
    (length : I → ℤ)
    (hsym : ∀ α β, length α * P.pairing β α = length β * P.pairing α β)
    (α β γ : I) (hαpos : 0 < length α)
    (hminus : ∀ δ, P.root δ = P.root β + (-1 : ℤ) • P.root α → length δ ≤ 2)
    (hβpos : 0 < length β) (hβγ : length β = length γ)
    (h : P.root γ = P.root β + P.root α) : P.chainBotCoeff α β = 0 := by
  have hlen := P.length_of_root_eq_add_zsmul length hsym α β γ 1 (by simpa only [one_zsmul] using h)
  have hpair : P.pairing β α = -1 := by
    rw [← hβγ] at hlen
    norm_num at hlen
    nlinarith
  rw [P.chainBotCoeff_eq_zero_iff]
  right
  rintro ⟨δ, hδ⟩
  have hδ' : P.root δ = P.root β + (-1 : ℤ) • P.root α := by
    simpa only [neg_one_zsmul, sub_eq_add_neg] using hδ
  have hδlen := P.length_of_root_eq_add_zsmul length hsym α β δ (-1) hδ'
  have hδbound := hminus δ hδ'
  rw [hpair] at hδlen
  norm_num at hδlen
  nlinarith [hβpos]

end

section

variable {I R M N : Type*} [Finite I] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]

/-- The lower endpoint of the root string through two roots is symmetric when their sum is a
root. -/
theorem _root_.RootPairing.chainBotCoeff_comm_of_root_add_mem {i j : I}
    (hadd : P.root i + P.root j ∈ range P.root) :
    P.chainBotCoeff i j = P.chainBotCoeff j i := by
  have hij := P.linearIndependent_of_add_mem_range_root' hadd
  have hji := P.linearIndependent_of_add_mem_range_root' (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have htop := P.one_le_chainTopCoeff_of_root_add_mem hadd
  have htop' := P.one_le_chainTopCoeff_of_root_add_mem (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
  have hlen' := P.chainBotCoeff_add_chainTopCoeff_le_three (i := j) (j := i)
  have hbot_le : P.chainBotCoeff i j ≤ 2 := by omega
  have htop_le : P.chainTopCoeff i j ≤ 3 := by omega
  have htop'_le : P.chainTopCoeff j i ≤ 3 := by omega
  have hbot : 1 ≤ P.chainBotCoeff i j ↔ 1 ≤ P.chainBotCoeff j i := by
    rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hij,
      ← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hji]
    simp only [one_smul]
    constructor
    · intro h
      have hn := (P.neg_mem_range_root_iff (x := P.root j - P.root i)).2 h
      simpa only [neg_sub] using hn
    · intro h
      have hn := (P.neg_mem_range_root_iff (x := P.root i - P.root j)).2 h
      simpa only [neg_sub] using hn
  have hpair := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have hpq := P.chainBotCoeff_sub_chainTopCoeff hij
  have hpq' := P.chainBotCoeff_sub_chainTopCoeff hji
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpair
  rcases hpair with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨h, h'⟩ <;> omega

/-- Two orthogonal roots whose sum is a root have the same squared length in every invariant
form. -/
theorem _root_.RootPairing.InvariantForm.apply_root_self_eq_of_root_add_of_pairing_eq_zero
    (B : P.InvariantForm) {i j k : I}
    (hk : P.root k = P.root i + P.root j) (hij₀ : P.pairing i j = 0) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  -- Step 1: Establish orthogonality and compute pairings with the sum root k.
  have hadd : P.root i + P.root j ∈ range P.root := ⟨k, hk⟩
  have hlin := P.linearIndependent_of_add_mem_range_root' hadd
  have hji₀ : P.pairing j i = 0 := (P.pairing_eq_zero_iff' (i := i) (j := j)).mp hij₀
  have hki : P.pairing k i = 2 := by
    rw [← P.root_coroot'_eq_pairing, hk, map_add, P.root_coroot'_eq_pairing,
      P.root_coroot'_eq_pairing, hji₀, P.pairing_same, add_zero]
  have hkj : P.pairing k j = 2 := by
    rw [← P.root_coroot'_eq_pairing, hk, map_add, P.root_coroot'_eq_pairing,
      P.root_coroot'_eq_pairing, hij₀, P.pairing_same, zero_add]
  -- Step 2: Verify that i and j are distinct from ±k to apply the pairing classification.
  have hik : P.root i ≠ P.root k := by
    intro h
    have hj₀ : P.root j = 0 := by
      calc
        P.root j = (P.root i + P.root j) - P.root i := by abel
        _ = P.root k - P.root i := by rw [hk]
        _ = 0 := sub_eq_zero.mpr h.symm
    exact P.ne_zero j hj₀
  have hjk : P.root j ≠ P.root k := by
    intro h
    have hi₀ : P.root i = 0 := by
      calc
        P.root i = (P.root i + P.root j) - P.root j := by abel
        _ = P.root k - P.root j := by rw [hk]
        _ = 0 := sub_eq_zero.mpr h.symm
    exact P.ne_zero i hi₀
  have hik' : P.root i ≠ -P.root k := by
    intro h
    have hrel : (2 : R) • P.root i + (1 : R) • P.root j = 0 := by
      rw [one_smul, two_smul, add_assoc, ← hk, h, neg_add_cancel]
    exact one_ne_zero (hlin.eq_zero_of_pair hrel).2
  have hjk' : P.root j ≠ -P.root k := by
    intro h
    have hrel : (1 : R) • P.root i + (2 : R) • P.root j = 0 := by
      rw [one_smul, two_smul, ← add_assoc, ← hk, h, add_neg_cancel]
    exact one_ne_zero (hlin.eq_zero_of_pair hrel).1
  -- Step 3: Classify integer pairings `⟨i, k⟩` and `⟨j, k⟩` using `P.pairingIn_pairingIn_mem_set`.
  have hkiℤ : P.pairingIn ℤ k i = 2 := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simpa only [P.algebraMap_pairingIn, map_ofNat] using hki
  have hkjℤ : P.pairingIn ℤ k j = 2 := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simpa only [P.algebraMap_pairingIn, map_ofNat] using hkj
  have hpik := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i k
    hik hik'
  have hpjk := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' j k
    hjk hjk'
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpik hpjk
  have hik₁ : P.pairing i k = 1 := by
    have : P.pairingIn ℤ i k = 1 := by omega
    rw [← P.algebraMap_pairingIn ℤ]
    rw [this]
    norm_num
  have hjk₁ : P.pairing j k = 1 := by
    have : P.pairingIn ℤ j k = 1 := by omega
    rw [← P.algebraMap_pairingIn ℤ]
    rw [this]
    norm_num
  -- Step 4: Combine the invariant-form swap identities `B(i, i) ⟨k, i⟩ = B(k, k) ⟨i, k⟩`.
  have hi := B.pairing_mul_eq_pairing_mul_swap i k
  have hj := B.pairing_mul_eq_pairing_mul_swap j k
  rw [hki, hik₁] at hi
  rw [hkj, hjk₁] at hj
  have htwo : (2 : R) ≠ 0 := by norm_num
  apply mul_left_cancel₀ htwo
  linear_combination hi - hj

/-- Along a root string, the squared lengths of two consecutive roots have the ratio of the
corresponding raising coefficients.  If `γ = α + β`, then

```text
q (γ, γ) = (p + 1) (β, β),
```

where `p = chainBotCoeff α β` and `q = chainTopCoeff α β`. -/
theorem _root_.RootPairing.InvariantForm.chainTopCoeff_mul_apply_root_self_eq
    (B : P.InvariantForm) {i j k : I}
    (hk : P.root k = P.root i + P.root j) :
    (P.chainTopCoeff i j : R) * B.form (P.root k) (P.root k) =
      (P.chainBotCoeff i j + 1 : ℕ) * B.form (P.root j) (P.root j) := by
  -- Step 1: Linear independence and string endpoint bounds.
  have hadd : P.root i + P.root j ∈ range P.root := ⟨k, hk⟩
  have hij := P.linearIndependent_of_add_mem_range_root' hadd
  have hji := P.linearIndependent_of_add_mem_range_root' (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have hbot := RootPairing.chainBotCoeff_comm_of_root_add_mem (P := P) hadd
  have htop := P.one_le_chainTopCoeff_of_root_add_mem hadd
  have htop' := P.one_le_chainTopCoeff_of_root_add_mem (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
  have hlen' := P.chainBotCoeff_add_chainTopCoeff_le_three (i := j) (j := i)
  have hpq := P.chainBotCoeff_sub_chainTopCoeff hij
  have hpq' := P.chainBotCoeff_sub_chainTopCoeff hji
  -- Step 2: Distinctness of roots `i` and `±j` from linear independence.
  have hne : i ≠ j := by
    intro h
    subst j
    exact one_ne_zero (hij.eq_zero_of_pair' (s := 1) (t := 1) rfl).1
  have hne' : P.root i ≠ -P.root j := by
    intro h
    exact one_ne_zero (hij.eq_zero_of_pair' (s := 1) (t := -1) (by simpa using h)).1
  have hpair := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i j
    (fun h ↦ hne (P.root.injective h)) hne'
  -- Step 3: Bilinear expansion of `B(k, k) = B(i + j, i + j)` and invariant-form swap relation.
  have hsym : B.form (P.root j) (P.root i) = B.form (P.root i) (P.root j) := by
    simpa only [RingHom.id_apply] using B.symm.eq (P.root j) (P.root i)
  have hform :
      B.form (P.root k) (P.root k) =
        B.form (P.root i) (P.root i) + 2 * B.form (P.root i) (P.root j) +
          B.form (P.root j) (P.root j) := by
    rw [hk]
    simp only [map_add, LinearMap.add_apply]
    rw [hsym]
    ring
  have hcross :
      2 * B.form (P.root i) (P.root j) =
        P.pairing j i * B.form (P.root i) (P.root i) := by
    rw [← hsym]
    exact B.two_mul_apply_root_root j i
  have hpqR : P.pairing j i =
      (P.chainBotCoeff i j : R) - P.chainTopCoeff i j := by
    rw [← P.algebraMap_pairingIn ℤ, ← hpq]
    push_cast
    rfl
  have hpqR' : P.pairing i j =
      (P.chainBotCoeff j i : R) - P.chainTopCoeff j i := by
    rw [← P.algebraMap_pairingIn ℤ, ← hpq']
    push_cast
    rfl
  have hlength := B.pairing_mul_eq_pairing_mul_swap i j
  rw [hpqR, hpqR', ← hbot] at hlength
  rw [hform, hcross, hpqR]
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpair
  -- Step 4: Case analysis on the root-pairing possibilities from the rank-2 classification.
  have hcases :
      P.chainTopCoeff i j = P.chainBotCoeff i j + 1 ∨
      (P.chainBotCoeff i j = 0 ∧ P.chainTopCoeff i j = 2 ∧
        P.chainTopCoeff j i = 1) ∨
      (P.chainBotCoeff i j = 0 ∧ P.chainTopCoeff i j = 3 ∧
        P.chainTopCoeff j i = 1) ∨
      (P.chainBotCoeff i j = 1 ∧ P.chainTopCoeff i j = 1 ∧
        P.chainTopCoeff j i = 1) ∨
      (P.chainBotCoeff i j = 2 ∧ P.chainTopCoeff i j = 1 ∧
        P.chainTopCoeff j i = 1) := by
    rcases hpair with h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨h, h'⟩ <;> omega
  rcases hcases with h | ⟨hp, hq, hq'⟩ | ⟨hp, hq, hq'⟩ |
      ⟨hp, hq, hq'⟩ | ⟨hp, hq, hq'⟩
  · rw [h]
    push_cast
    ring
  · norm_num [hp, hq, hq', hbot] at hlength ⊢
    rw [← hlength]
    ring
  · norm_num [hp, hq, hq', hbot] at hlength ⊢
    rw [← hlength]
    ring
  · have hij₀ : P.pairing i j = 0 := by
      rw [hpqR', ← hbot, hp, hq']
      norm_num
    have heq :=
      RootPairing.InvariantForm.apply_root_self_eq_of_root_add_of_pairing_eq_zero
        (P := P) B hk hij₀
    norm_num [hp, hq] at heq ⊢
    linear_combination heq
  · norm_num [hp, hq, hq', hbot] at hlength ⊢
    rw [hlength]
    ring

end

end TauCeti
