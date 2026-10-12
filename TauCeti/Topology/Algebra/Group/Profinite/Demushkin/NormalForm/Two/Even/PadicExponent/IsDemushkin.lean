/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare
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
When `α ∈ 4ℤ₂` and `4 ∣ q`, its class agrees with that of `x₁² (x₁, x₂)(x₃, x₄) ⋯`:
the extra `2`-adic power and the tail power vanish there. Its torsion invariant is then
`q(G) = 2`, allowing its canonical character and the classification by orientation image to
be used without assuming that it is Demushkin.

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

/-- Exponents divisible by four put the dyadic word in the pro-`2` Frattini subgroup. -/
theorem demushkinWordTwoEvenPadic_mem_proPFrattini_of_four_dvd
    (hα : 4 ∣ α) (hq : 4 ∣ q) (n : ℕ) (x : ℕ → H) :
    demushkinWordTwoEvenPadic hH α q n x ∈ proPFrattini 2 H :=
  demushkinWordTwoEvenPadic_mem_proPFrattini hH α q n x
    (dvd_trans (Dvd.intro 2 (by norm_num) : (2 : ℤ_[2]) ∣ 4) hα)
    ((by norm_num : 2 ∣ 4).trans hq)

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
  have hpow (g : H) {u v : ℤ_[2]} (huv : 4 ∣ u - v) :
      QuotientGroup.mk' (pLowerCentralSeries 2 H 2) (hH.padicPow g u) =
        QuotientGroup.mk' (pLowerCentralSeries 2 H 2) (hH.padicPow g v) := by
    obtain ⟨k, hk⟩ := huv
    have hu : u = v + 4 * k := by rw [← hk]; ring
    have hfour : g ^ 4 ∈ pLowerCentralSeries 2 H 2 := by
      simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 2 g) 2
    have hkpow := hH.padicPow_mem (isClosed_pLowerCentralSeries 2) hfour k
    have hkq : QuotientGroup.mk' (pLowerCentralSeries 2 H 2)
        (hH.padicPow (g ^ 4) k) = 1 := (QuotientGroup.eq_one_iff _).2 hkpow
    rw [hu, hH.padicPow_add, hH.padicPow_mul, hH.padicPow_ofNat, map_mul, hkq, mul_one]
  rw [gradedMk_eq_gradedMk_iff]
  simp only [← QuotientGroup.mk'_apply]
  rw [← demushkinWordTwoEvenPadic_natCast hH n x a f]
  simp only [demushkinWordTwoEvenPadic_def, map_mul]
  rw [hpow (x 0) (v := 2 + a) (by simpa using hαa), ← hH.padicPow_natCast (x 2) q,
    hpow (x 2) (v := ((2 ^ f : ℕ) : ℤ_[2])) (by simpa using hqf), hH.padicPow_natCast]

/-- For `α ∈ 4ℤ₂` and `4 ∣ q`, the genuine `2`-adic even word has the same degree-one class
as `x₁² (x₁, x₂)(x₃, x₄) ⋯`, including the infinite level `q = 0`. -/
theorem gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordNeTwo
    (hα : 4 ∣ α) (hq : 4 ∣ q) (hn : 2 ≤ n) (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoEvenPadic hH α q n x,
        (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le
          (demushkinWordTwoEvenPadic_mem_proPFrattini_of_four_dvd hH hα hq n x)⟩ =
      gradedMk 2 H 1 ⟨demushkinWordNeTwo 2 n x,
        demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n x⟩ := by
  have hα2 : (2 : ℤ_[2]) ∣ α :=
    dvd_of_mul_right_dvd (a := 2) (b := 2) (by convert hα using 1; norm_num)
  have hq2 : 2 ∣ q := dvd_of_mul_right_dvd (a := 2) (b := 2) hq
  have hq4 : (4 : ℤ_[2]) ∣ (q : ℤ_[2]) := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨(k : ℤ_[2]), by push_cast; rfl⟩
  rw [gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordTwoEven hH hα2 hq2
    (a := 0) (f := 2) (dvd_zero 2) (by omega) (by simpa using hα)
    (by norm_num; exact hq4)]
  exact gradedMk_demushkinWordTwoEven_eq_gradedMk_demushkinWordNeTwo (dvd_zero 2) le_rfl hn x

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

/-- The genuine `2`-adic normal form with `α ∈ 4ℤ₂` and `4 ∣ q` has torsion invariant
`q(G) = 2`: its degree-one form is nonalternating. -/
@[simp]
theorem demushkinQ_presentedProP_demushkinWordTwoEvenPadic (hα : 4 ∣ α) (hq : 4 ∣ q)
    (hn : 2 ≤ n) (hG : IsDemushkin 2 (presentedProP 2 (Fin n)
      {demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin n)) α q n (freeProPGen 2 n)})) :
    demushkinQ hG = 2 := by
  have hr := demushkinWordTwoEvenPadic_mem_proPFrattini_of_four_dvd
    (isProP_freeProP 2 (Fin n)) hα hq n (freeProPGen 2 n)
  by_contra hq2
  have halt := (freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero hr
    (ContinuousMulEquiv.refl _)).2 (hG.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two.2 hq2)
  rw [gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordNeTwo _ hα hq hn] at halt
  exact freeProP.not_isAlt_degreeOneForm_demushkinWordNeTwo (by omega) (by norm_num) halt

end Recognition

end TauCeti
