/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2

/-!
# Positive combinations of two roots outside G₂

For independent roots `α, β` in a finite crystallographic reduced root pairing without G₂,
the only roots `mα + nβ` with `m, n > 0` are among `α + β`, `2α + β`, and `α + 2β`.
Moreover, the latter two cannot both occur. These statements classify the possible root
factors in the Chevalley commutator formula without choosing a base of the rank-two subsystem.
The roots need not be positive in any previously chosen base.

`RootPairing.pos_nsmul_add_pos_nsmul_mem_range_root_iff` gives the exact membership criterion.
`RootPairing.not_double_root_add_and_root_add_double_mem` excludes simultaneous double strings.
The results use Mathlib's root-string bounds and its nonacute-angle theorem outside G₂;
no structure constants or group commutator identities are assumed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §5.2, Theorem 5.2.2.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)
  [Finite ι] [CharZero R] [IsDomain R] [P.IsNotG2]
  {α β : ι} {m n : ℕ}

/-- If a strictly positive integral combination of two independent roots is a root, their sum
is a root. This need not hold for dependent roots, for example `2α + (-α) = α`. -/
theorem root_add_mem_of_pos_nsmul_add_pos_nsmul_mem
    (hlin : LinearIndependent R ![P.root α, P.root β]) (hm : 0 < m) (hn : 0 < n)
    (h : m • P.root α + n • P.root β ∈ Set.range P.root) :
    P.root α + P.root β ∈ Set.range P.root := by
  by_contra hsum
  have hne := ((IsReduced.linearIndependent_iff P).mp hlin).2
  have hab : 0 ≤ P.pairingIn ℤ α β := by
    by_contra! hneg
    exact hsum (P.root_add_root_mem_of_pairingIn_neg hneg hne)
  have hba : 0 ≤ P.pairingIn ℤ β α := by
    by_contra! hneg
    have hne' : P.root β ≠ -P.root α := by
      intro heq
      exact hne (by simpa only [neg_neg] using (congrArg Neg.neg heq).symm)
    exact hsum (by simpa [add_comm] using P.root_add_root_mem_of_pairingIn_neg hneg hne')
  obtain ⟨γ, hγ⟩ := h
  have hγ' : P.root γ = (m : ℤ) • P.root α + (n : ℤ) • P.root β := by
    simpa only [natCast_zsmul] using hγ
  have ha := pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := α) hγ'
  have hb := pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := β) hγ'
  simp only [pairingIn_same, smul_eq_mul] at ha hb
  have hbounda := IsNotG2.pairingIn_mem_zero_one_two (P := P) γ α
  have hboundb := IsNotG2.pairingIn_mem_zero_one_two (P := P) γ β
  have hma : (m : ℤ) ≤ 1 := by
    have := mul_nonneg (Int.natCast_nonneg n) hba
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbounda
    omega
  have hnb : (n : ℤ) ≤ 1 := by
    have := mul_nonneg (Int.natCast_nonneg m) hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hboundb
    omega
  have hm1 : m = 1 := by omega
  have hn1 : n = 1 := by omega
  exact hsum (by simpa [hm1, hn1] using Set.mem_range.mpr ⟨γ, hγ⟩)

/-- Outside G₂, the strictly positive coefficients of a root in the span of two independent
roots are `(1, 1)`, `(2, 1)`, or `(1, 2)`. -/
theorem coefficients_of_pos_nsmul_add_pos_nsmul_mem
    (hlin : LinearIndependent R ![P.root α, P.root β]) (hm : 0 < m) (hn : 0 < n)
    (h : m • P.root α + n • P.root β ∈ Set.range P.root) :
    (m = 1 ∧ n = 1) ∨ (m = 2 ∧ n = 1) ∨ (m = 1 ∧ n = 2) := by
  obtain ⟨γ, hγ⟩ := P.root_add_mem_of_pos_nsmul_add_pos_nsmul_mem hlin hm hn h
  have hag : 0 ≤ P.pairingIn ℤ α γ := by
    apply P.zero_le_pairingIn_of_root_sub_mem
    convert P.neg_root_mem β using 1; rw [hγ]; abel
  have hbg : 0 ≤ P.pairingIn ℤ β γ := by
    apply P.zero_le_pairingIn_of_root_sub_mem
    convert P.neg_root_mem α using 1; rw [hγ]; abel
  have hsum : P.pairingIn ℤ α γ + P.pairingIn ℤ β γ = 2 := by
    simpa only [pairingIn_same] using
      (pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := γ) hγ).symm
  obtain ⟨δ, hδ⟩ := h
  have hδ' : P.root δ = (m : ℤ) • P.root α + (n : ℤ) • P.root β := by
    simpa only [natCast_zsmul] using hδ
  have hd := pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := γ) hδ'
  simp only [smul_eq_mul] at hd
  have hbound := IsNotG2.pairingIn_mem_zero_one_two (P := P) δ γ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbound
  have hle : P.pairingIn ℤ δ γ ≤ 2 := by omega
  have hor : m = 1 ∨ n = 1 := by
    by_contra! hne
    have hma : (2 : ℤ) ≤ m := by omega
    have hnb : (2 : ℤ) ≤ n := by omega
    nlinarith [mul_le_mul_of_nonneg_right hma hag, mul_le_mul_of_nonneg_right hnb hbg]
  have hchaina := P.chainBotCoeff_add_chainTopCoeff_le_two α β
  have hchainb := P.chainBotCoeff_add_chainTopCoeff_le_two β α
  rcases hor with rfl | rfl
  · have htop : n ≤ P.chainTopCoeff β α := by
      apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
        (LinearIndependent.pair_symm_iff.mpr hlin)).mp
      simpa only [one_smul] using Set.mem_range.mpr ⟨δ, hδ⟩
    omega
  · have htop : m ≤ P.chainTopCoeff α β := by
      apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mp
      simpa only [one_smul, add_comm] using Set.mem_range.mpr ⟨δ, hδ⟩
    omega

/-- Exact support of the positive rank-two combinations outside G₂. The three root-membership
conditions retain which of the possible factors actually occur. -/
theorem pos_nsmul_add_pos_nsmul_mem_range_root_iff
    (hlin : LinearIndependent R ![P.root α, P.root β]) (hm : 0 < m) (hn : 0 < n) :
    m • P.root α + n • P.root β ∈ Set.range P.root ↔
      (m = 1 ∧ n = 1 ∧ P.root α + P.root β ∈ Set.range P.root) ∨
      (m = 2 ∧ n = 1 ∧ 2 • P.root α + P.root β ∈ Set.range P.root) ∨
      (m = 1 ∧ n = 2 ∧ P.root α + 2 • P.root β ∈ Set.range P.root) := by
  constructor
  · intro h
    rcases P.coefficients_of_pos_nsmul_add_pos_nsmul_mem hlin hm hn h with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  · rintro (⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩) <;> simpa using h

/-- The two double-string orientations cannot occur together outside G₂. Thus a commutator
has at most two positive-root factors, even when the ambient root system has higher rank. -/
theorem not_double_root_add_and_root_add_double_mem
    (hlin : LinearIndependent R ![P.root α, P.root β]) :
    ¬ (2 • P.root α + P.root β ∈ Set.range P.root ∧
      P.root α + 2 • P.root β ∈ Set.range P.root) := by
  rintro ⟨⟨δ, hδ⟩, ⟨ε, hε⟩⟩
  have hsum : P.root α + P.root β ∈ Set.range P.root :=
    P.root_add_mem_of_pos_nsmul_add_pos_nsmul_mem hlin (by decide : 0 < 2)
      (by decide : 0 < 1) (by simpa using Set.mem_range.mpr ⟨δ, hδ⟩)
  obtain ⟨γ, hγ⟩ := hsum
  have hda : P.root δ = P.root α + P.root γ := by rw [hδ, hγ]; abel
  have heb : P.root ε = P.root β + P.root γ := by rw [hε, hγ]; abel
  have ha := P.pairingIn_le_zero_of_root_add_mem (Set.mem_range.mpr ⟨δ, hda⟩)
  have hb := P.pairingIn_le_zero_of_root_add_mem (Set.mem_range.mpr ⟨ε, heb⟩)
  have hgg := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := γ) hγ
  rw [pairingIn_same] at hgg
  omega

end RootPairing
