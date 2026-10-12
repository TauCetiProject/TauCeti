/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.IsDemushkin
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.PadicExponent.Basic

/-!
# Demushkin recognition for the dyadic word with a `2`-adic exponent

The relator `x₁^{2+α} (x₁, x₂) x₃^q (x₃, x₄) ⋯` defines a Demushkin group of rank `n`
when `n ≥ 2` is even, `α ∈ 4ℤ₂`, and `4 ∣ q`. This includes both the finite levels
`q = 2^f`, `f ≥ 2`, and the infinite level `q = 0`.

Its class modulo the second lower `2`-series subgroup agrees with that of
`x₁² (x₁, x₂)(x₃, x₄) ⋯`: the extra `2`-adic power and the tail power vanish there.
Consequently its degree-one form is the existing nondegenerate form of the even dyadic word.
Apply Labute's criterion `TauCeti.isDemushkin_of_nondegenerate_degreeOneForm` to the actual
presented group. Its torsion invariant is `q(G) = 2`, allowing its canonical character and the
classification by orientation image to be used without assuming that it is Demushkin.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967),
  106–132, Proposition 3 and Theorem 3.
-/

open Subgroup

namespace TauCeti

section GradedClass

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H] (hH : IsProP 2 H) {α : ℤ_[2]} {q n : ℕ}

/-- For `α ∈ 4ℤ₂` and `4 ∣ q`, the genuine `2`-adic even word has the same degree-one class
as `x₁² (x₁, x₂)(x₃, x₄) ⋯`, including the infinite level `q = 0`. -/
theorem gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordNeTwo
    (hα : 4 ∣ α) (hq : 4 ∣ q) (hn : 2 ≤ n) (x : ℕ → H) :
    gradedMk 2 H 1 ⟨demushkinWordTwoEvenPadic hH α q n x,
        (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le
          (demushkinWordTwoEvenPadic_mem_proPFrattini hH α q n x
            (dvd_trans (Dvd.intro 2 (by norm_num) : (2 : ℤ_[2]) ∣ 4) hα)
            ((by norm_num : 2 ∣ 4).trans hq))⟩ =
      gradedMk 2 H 1 ⟨demushkinWordNeTwo 2 n x,
        demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n x⟩ := by
  have hfour (g : H) : g ^ 4 ∈ pLowerCentralSeries 2 H 2 := by
    simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 2 g) 2
  have hpow : hH.padicPow (x 0) α ∈ pLowerCentralSeries 2 H 2 := by
    obtain ⟨a, rfl⟩ := hα
    rw [hH.padicPow_mul, hH.padicPow_ofNat]
    exact hH.padicPow_mem (isClosed_pLowerCentralSeries 2) (hfour _) a
  have htail : x 2 ^ q ∈ pLowerCentralSeries 2 H 2 := by
    obtain ⟨a, rfl⟩ := hq
    rw [pow_mul]
    exact pow_mem (hfour _) a
  -- Compare in the ambient quotient, where the two extra factors are trivial.
  rw [gradedMk_eq_gradedMk_iff]
  simp only [← QuotientGroup.mk'_apply]
  have hp : QuotientGroup.mk' (pLowerCentralSeries 2 H 2) (hH.padicPow (x 0) α) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hpow
  have ht : QuotientGroup.mk' (pLowerCentralSeries 2 H 2) (x 2 ^ q) = 1 :=
    (QuotientGroup.eq_one_iff _).2 htail
  have hword := demushkinWordTwoEvenPadic_def hH α q n x
  have hbase := demushkinWordTwoEvenPadic_def hH 0 0 n x
  rw [← demushkinWordTwoEvenPadic_zero_zero hH n x hn]
  simp only [hword, hbase, hH.padicPow_add, hH.padicPow_ofNat, map_mul,
    hp, ht, mul_one, add_zero, pow_zero]

end GradedClass

section Recognition

variable {α : ℤ_[2]} {q n : ℕ}

/-- The even dyadic normal form with a genuine `2`-adic exponent defines a Demushkin group
of rank `n`, for `n ≥ 2` even, `α ∈ 4ℤ₂`, and `4 ∣ q`. The value `q = 0` is the infinite level. -/
theorem isDemushkin_presentedProP_demushkinWordTwoEvenPadic (hn : Even n) (hn0 : n ≠ 0)
    (hα : 4 ∣ α) (hq : 4 ∣ q) :
    IsDemushkin 2 (presentedProP 2 (Fin n)
      {demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin n)) α q n (freeProPGen 2 n)}) := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  apply isDemushkin_of_nondegenerate_degreeOneForm
    (demushkinWordTwoEvenPadic_mem_proPFrattini _ _ _ _ _
      (dvd_trans (Dvd.intro 2 (by norm_num) : (2 : ℤ_[2]) ∣ 4) hα) ((by norm_num : 2 ∣ 4).trans hq))
    (ContinuousMulEquiv.refl _)
  rw [gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordNeTwo _ hα hq hn2]
  exact freeProP.nondegenerate_degreeOneForm_demushkinWordNeTwo hn dvd_rfl

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
  have hr := demushkinWordTwoEvenPadic_mem_proPFrattini (isProP_freeProP 2 (Fin n)) α q n
    (freeProPGen 2 n) (dvd_trans (Dvd.intro 2 (by norm_num) : (2 : ℤ_[2]) ∣ 4) hα)
    ((by norm_num : 2 ∣ 4).trans hq)
  by_contra hq2
  have halt := (freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero hr
    (ContinuousMulEquiv.refl _)).2 (hG.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two.2 hq2)
  rw [gradedMk_demushkinWordTwoEvenPadic_eq_gradedMk_demushkinWordNeTwo _ hα hq hn] at halt
  exact freeProP.not_isAlt_degreeOneForm_demushkinWordNeTwo (by omega) (by norm_num) halt

end Recognition

end TauCeti
