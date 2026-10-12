/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.IsDemushkin
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.PadicExponent.Basic

/-!
# Demushkin recognition for the dyadic word with a `2`-adic exponent

The relator `x₁^{2+α} (x₁, x₂) x₃^q (x₃, x₄) ⋯` defines a Demushkin group of rank `n`
when `n ≥ 2` is even and `α` and `q` are even. This includes both the finite levels
`q = 2^f`, `f ≥ 1`, and the infinite level `q = 0`.

Reducing the exponents modulo four identifies its degree-one class with that of an existing
natural-exponent even dyadic word. Its degree-one form is therefore nondegenerate, and Labute's
criterion `TauCeti.isDemushkin_of_nondegenerate_degreeOneForm` applies to the presented group.
When `α ∈ 4ℤ₂` and `q` is even, its torsion invariant is `q(G) = 2`: the exponent sum
`2 + α` at the first generator is divisible by two but not by four. Its canonical character
and the classification by orientation image can therefore be used without assuming that
it is Demushkin.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967),
  106–132, Proposition 3 and Theorem 3.
-/

public section

open Subgroup

namespace TauCeti

section GradedClass

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H] (hH : IsProP 2 H) {α : ℤ_[2]} {q n : ℕ}

/-- Even exponents congruent modulo four give the same degree-one class as the
natural-exponent dyadic word. -/
theorem gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordTwoEven
    (hα : 2 ∣ α) (hq : 2 ∣ q) {a f : ℕ} (ha : 2 ∣ a) (hf : 0 < f)
    (hαa : (4 : ℤ_[2]) ∣ α - a) (hqf : (4 : ℤ_[2]) ∣ (q : ℤ_[2]) - 2 ^ f)
    (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoEvenPadic hH α q n x,
        (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le
          (demushkinWordTwoEvenPadic_mem_proPFrattini hH α q n x hα hq)⟩ =
      gradedMk 2 H 1 ⟨demushkinWordTwoEven a f n x,
        demushkinWordTwoEven_mem_pLowerCentralSeries_one ha hf n x⟩ := by
  rw [gradedMk_eq_gradedMk_iff]
  simp only [← QuotientGroup.mk'_apply]
  rw [← demushkinWordTwoEvenPadic_natCast hH n x a f]
  simp only [demushkinWordTwoEvenPadic_def, map_mul]
  rw [hH.mk_padicPow_eq_of_pow_dvd_sub (x 0) 2 (v := 2 + a)
      (by simpa [show (2 : ℤ_[2]) ^ 2 = 4 by norm_num] using hαa), ← hH.padicPow_natCast (x 2) q,
    hH.mk_padicPow_eq_of_pow_dvd_sub (x 2) 2 (v := ((2 ^ f : ℕ) : ℤ_[2]))
      (by simpa [show (2 : ℤ_[2]) ^ 2 = 4 by norm_num] using hqf), hH.padicPow_natCast]

end GradedClass

section Recognition

variable {α : ℤ_[2]} {q n : ℕ}

/-- The even dyadic normal form with a genuine `2`-adic exponent defines a Demushkin group
of rank `n`, for `n ≥ 2` even and even `α` and `q`. The value `q = 0` is the infinite level. -/
theorem isDemushkin_presentedProP_demushkinWordTwoEvenPadic (hn : Even n) (hn0 : n ≠ 0)
    (hα : 2 ∣ α) (hq : 2 ∣ q) :
    IsDemushkin 2 (presentedProP 2 (Fin n)
      {demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin n)) α q n (freeProPGen 2 n)}) := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  -- Choose even natural exponents with the same residues modulo four.
  obtain ⟨β, rfl⟩ := hα
  obtain ⟨c, rfl⟩ := hq
  let a := 2 * β.appr 1
  have ha : 2 ∣ a := dvd_mul_right 2 _
  have hαa : (4 : ℤ_[2]) ∣ 2 * β - a := by
    obtain ⟨k, hk⟩ : (2 : ℤ_[2]) ∣ β - β.appr 1 := by
      simpa using PadicInt.dvd_sub_appr β 1
    refine ⟨k, ?_⟩
    dsimp [a]
    push_cast
    linear_combination 2 * hk
  obtain ⟨f, hf, hcf⟩ : ∃ f : ℕ, 0 < f ∧ (4 : ℤ) ∣ (2 * c : ℕ) - (2 : ℤ) ^ f := by
    by_cases hc : c % 2 = 0
    · refine ⟨2, by omega, Int.dvd_of_emod_eq_zero ?_⟩
      omega
    · refine ⟨1, by omega, Int.dvd_of_emod_eq_zero ?_⟩
      omega
  have hqf : (4 : ℤ_[2]) ∣ (2 * c : ℕ) - (2 : ℤ_[2]) ^ f := by
    obtain ⟨k, hk⟩ := hcf
    refine ⟨(k : ℤ_[2]), ?_⟩
    exact_mod_cast hk
  apply isDemushkin_of_nondegenerate_degreeOneForm
    (demushkinWordTwoEvenPadic_mem_proPFrattini _ _ _ _ _ (dvd_mul_right 2 β)
      (dvd_mul_right 2 c)) (ContinuousMulEquiv.refl _)
  rw [gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordTwoEven _
    (dvd_mul_right 2 β) (dvd_mul_right 2 c) ha hf hαa hqf]
  exact freeProP.nondegenerate_degreeOneForm_demushkinWordTwoEven hn ha hf

/-- The rank of a Demushkin group presented by the even `2`-adic word is the number of
generators whenever `α` and `q` are even: its presentation is minimal. -/
@[simp]
theorem demushkinRank_presentedProP_demushkinWordTwoEvenPadic (hα : 2 ∣ α) (hq : 2 ∣ q)
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n)
      {demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin n)) α q n (freeProPGen 2 n)})) :
    demushkinRank hG = n := by
  simpa using demushkinRank_presentedProP (Set.singleton_subset_iff.2
    (demushkinWordTwoEvenPadic_mem_proPFrattini _ _ _ _ _ hα hq)) hG

/-- The genuine `2`-adic normal form with `α ∈ 4ℤ₂` and even `q` has torsion invariant
`q(G) = 2`. -/
@[simp]
theorem demushkinQ_presentedProP_demushkinWordTwoEvenPadic (hα : 4 ∣ α) (hq : 2 ∣ q)
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n)
      {demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin n)) α q n (freeProPGen 2 n)})) :
    demushkinQ hG = 2 := by
  have hn : 0 < n := by simpa using hG.card_pos_presentedProP
  have hα2 : (2 : ℤ_[2]) ∣ α :=
    dvd_trans (Dvd.intro 2 (by norm_num) : (2 : ℤ_[2]) ∣ 4) hα
  have hr := demushkinWordTwoEvenPadic_mem_proPFrattini
    (isProP_freeProP 2 (Fin n)) α q n (freeProPGen 2 n) hα2 hq
  apply (demushkinQ_presentedProP_eq_iff_exists_not_dvd hG
    (freeProP.dvd_exponentSum_of_mem_proPFrattini 2 (Fin n) hr)).2
  refine ⟨⟨0, hn⟩, ?_⟩
  have hexp : (freeProP.exponentSum 2 (Fin n)
      (demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin n)) α q n
        (freeProPGen 2 n))).toAdd ⟨0, hn⟩ = 2 + α := by
    simp [demushkinWordTwoEvenPadic_def, IsProP.map_padicPow_pi,
      freeProPGen_of_lt 2 hn, map_list_prod, List.map_map, Function.comp_def]
  rw [hexp]
  intro h
  have hfour : (2 : ℤ_[2]) ^ 2 = 4 := by norm_num
  simp only [Nat.cast_ofNat, hfour] at h
  have hnot : ¬ (4 : ℤ_[2]) ∣ 2 := by
    simpa only [Nat.cast_ofNat, hfour, Int.cast_ofNat] using
      (PadicInt.pow_p_dvd_int_iff (p := 2) 2 2).not.mpr (by norm_num)
  exact hnot (by simpa using dvd_sub h hα)

end Recognition

end TauCeti
