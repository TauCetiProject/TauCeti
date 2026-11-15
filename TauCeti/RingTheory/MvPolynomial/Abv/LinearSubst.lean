/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Abv.Coeff
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.BlockSubst

/-!
# Coefficient bounds for linear and block-linear substitutions

Let `v` be an absolute value on a commutative semiring `R`. Substituting linear forms whose
supports have size at most `k` and whose coefficients are bounded by `B` into a monomial `a X ^ s`
produces a product of `s.degree` linear factors, so `MvPolynomial.abv_coeff_prod_le` bounds every
coefficient of the result by `(k * B) ^ s.degree * v a`, and at a nonarchimedean absolute value
the ultrametric inequality removes the factor `k`.

For a homogeneous polynomial `p` of degree `n` in `card σ` variables, the exponent vectors have
cardinality at most `(card σ).multichoose n ≤ card σ ^ n`, giving the coefficient bound
`(card σ ^ 2 * B) ^ n * C` under `MvPolynomial.linearSubst`. For a multihomogeneous polynomial `P`
of multidegree `d : κ → ℕ` under `MvPolynomial.blockSubst A`, each block variable expands into a
sum over `ι` alone rather than `κ × ι`, so the base depends only on `card ι` and not on the number
of blocks: every coefficient of `blockSubst A P` is bounded by `(card ι ^ 2 * B) ^ (∑ h, d h) * C`
in general and by `B ^ (∑ h, d h) * C` at nonarchimedean absolute values.

## Main results

* `MvPolynomial.card_support_le_pow_of_isHomogeneous`,
  `MvPolynomial.card_multiMons_le_pow`, and
  `MvPolynomial.card_support_le_pow_of_isMultiHomogeneous`: monomial-count bounds `card σ ^ n` and
  `card ι ^ ∑ h, d h`.
* `MvPolynomial.abv_coeff_aeval_monomial_le`,
  `MvPolynomial.abv_coeff_aeval_monomial_le_of_isNonarchimedean`: coefficient bounds for `aeval` on
  a monomial.
* `MvPolynomial.abv_coeff_linearSubst_monomial_le`,
  `MvPolynomial.abv_coeff_linearSubst_le_of_isHomogeneous`, and their nonarchimedean companions.
* `MvPolynomial.abv_coeff_blockSubst_monomial_le`,
  `MvPolynomial.abv_coeff_blockSubst_le_of_isMultiHomogeneous`, and their nonarchimedean
  companions.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 1.6.11 and §7.5.14.
-/

public section

open Finset

namespace MvPolynomial

section Support

private lemma multichoose_le_pow : ∀ n k : ℕ, n.multichoose k ≤ n ^ k
  | 0, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, 0 => by simp
  | n + 1, k + 1 => by
    rw [Nat.multichoose_succ_succ]
    calc n.multichoose (k + 1) + (n + 1).multichoose k
        ≤ n ^ (k + 1) + (n + 1) ^ k :=
          Nat.add_le_add (multichoose_le_pow n (k + 1)) (multichoose_le_pow (n + 1) k)
      _ ≤ n * (n + 1) ^ k + (n + 1) ^ k := by
          rw [pow_succ']
          exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.pow_le_pow_left n.le_succ k)) _
      _ = (n + 1) ^ (k + 1) := by rw [← Nat.succ_mul, pow_succ']

private lemma card_finsuppAntidiag_le_pow {σ : Type*} [DecidableEq σ] (s : Finset σ) (n : ℕ) :
    #(s.finsuppAntidiag n) ≤ (#s) ^ n := by
  rw [card_finsuppAntidiag_nat_eq_multichoose]
  exact multichoose_le_pow (#s) n

/-- A homogeneous polynomial of degree `n` in finitely many variables has at most
`card σ ^ n` monomials. -/
theorem card_support_le_pow_of_isHomogeneous {σ R : Type*} [Fintype σ] [CommSemiring R]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    #p.support ≤ Fintype.card σ ^ n := by
  classical
  have hsub : p.support ⊆ (univ : Finset σ).finsuppAntidiag n := fun s hs ↦ by
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    rw [← Finsupp.sum_fintype s (fun _ c ↦ c) (fun _ ↦ rfl)]
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using
      hp (mem_support_iff.1 hs)
  exact (card_le_card hsub).trans (by simpa using card_finsuppAntidiag_le_pow (univ : Finset σ) n)

/-- There are at most `card ι ^ ∑ h, d h` exponent vectors of multidegree `d`. -/
theorem card_multiMons_le_pow {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (d : κ → ℕ) :
    #(multiMons ι d) ≤ Fintype.card ι ^ ∑ h, d h := by
  rw [card_multiMons, ← prod_pow_eq_pow_sum]
  exact prod_le_prod fun h _ ↦
    Nat.multichoose_eq (Fintype.card ι) (d h) ▸ multichoose_le_pow (Fintype.card ι) (d h)

/-- A multihomogeneous polynomial of multidegree `d` has at most `card ι ^ ∑ h, d h` monomials. -/
theorem card_support_le_pow_of_isMultiHomogeneous {R κ ι : Type*} [CommSemiring R] [Fintype κ]
    [DecidableEq κ] [Fintype ι] {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) :
    #P.support ≤ Fintype.card ι ^ ∑ h, d h := by
  classical
  exact (card_le_card (isMultiHomogeneous_iff_support_subset.1 hP)).trans (card_multiMons_le_pow d)

end Support

section AbsoluteValue

variable {σ τ κ ι R S : Type*} [CommSemiring R]

private lemma card_support_sum_C_mul_X_le [Fintype ι] (w : ι → R) (g : ι → τ) :
    #(∑ j, C (w j) * X (g j) : MvPolynomial τ R).support ≤ Fintype.card ι := by
  classical
  have hsub : (∑ j, C (w j) * X (g j) : MvPolynomial τ R).support ⊆
      univ.image fun j ↦ Finsupp.single (g j) 1 := by
    refine support_sum.trans (biUnion_subset.2 fun j hj ↦ ?_)
    rw [X, C_mul_monomial, mul_one]
    exact support_monomial_subset.trans (singleton_subset_iff.2 (mem_image_of_mem _ hj))
  exact (card_le_card hsub).trans (card_image_le.trans_eq card_univ)

private lemma abv_coeff_sum_C_mul_X_le [Semiring S] [PartialOrder S] {v : AbsoluteValue R S}
    [Fintype ι] {w : ι → R} {g : ι → τ} (hg : Function.Injective g) {B : S} (hB0 : 0 ≤ B)
    (hw : ∀ j, v (w j) ≤ B) (m : τ →₀ ℕ) :
    v ((∑ j, C (w j) * X (g j) : MvPolynomial τ R).coeff m) ≤ B := by
  classical
  have hterm (j : ι) : (C (w j) * X (g j) : MvPolynomial τ R).coeff m =
      if Finsupp.single (g j) 1 = m then w j else 0 := by
    rw [X, C_mul_monomial, mul_one, coeff_monomial]
  rw [coeff_sum]
  simp_rw [hterm]
  by_cases hm : ∃ j, Finsupp.single (g j) 1 = m
  · obtain ⟨j₀, rfl⟩ := hm
    rw [sum_eq_single j₀]
    · simp [hw j₀]
    · intro j _ hj
      exact ite_eq_right fun h ↦ hj (hg (Finsupp.single_left_injective one_ne_zero h))
    · simp
  · push Not at hm
    rw [sum_eq_zero fun j _ ↦ ite_eq_right (hm j), map_zero]
    exact hB0

variable [Nontrivial R]

/-- Substituting polynomials `f i` with `#(f i).support ≤ k` and coefficients bounded by `B` under
`v` into `monomial s a` produces coefficients bounded by `(k * B) ^ s.degree * v a`. -/
theorem abv_coeff_aeval_monomial_le [CommSemiring S] [PartialOrder S] [IsOrderedRing S] [IsDomain S]
    {v : AbsoluteValue R S} {f : σ → MvPolynomial τ R} {k : ℕ} {B : S} {s : σ →₀ ℕ}
    (hk : ∀ i ∈ s.support, #(f i).support ≤ k)
    (hB : ∀ i ∈ s.support, ∀ m, v ((f i).coeff m) ≤ B) (a : R) (t : τ →₀ ℕ) :
    v ((aeval f (monomial s a)).coeff t) ≤ (k * B) ^ s.degree * v a := by
  classical
  let I : Finset (Σ _ : σ, ℕ) := s.support.sigma fun i ↦ range (s i)
  have hcard : #I = s.degree := by simp [I, card_sigma, Finsupp.degree_apply]
  have hprod : (s.prod fun i e ↦ f i ^ e) = ∏ q ∈ I, f q.1 := by
    simp [I, prod_sigma, Finsupp.prod]
  rw [aeval_monomial, algebraMap_eq, ← smul_eq_C_mul, coeff_smul, smul_eq_mul, map_mul,
    mul_comm (v a), hprod]
  refine mul_le_mul_of_nonneg_right ?_ (v.nonneg a)
  refine (abv_coeff_prod_le (s := I) (fun q ↦ f q.1) (C := fun _ ↦ B)
    (fun q hq ↦ hB q.1 (mem_sigma.1 hq).1) t).trans ?_
  rw [← hcard, ← prod_const]
  refine prod_le_prod₀ (fun q hq ↦ mul_nonneg (Nat.cast_nonneg _)
    ((v.nonneg _).trans (hB q.1 (mem_sigma.1 hq).1 0))) fun q hq ↦ ?_
  exact mul_le_mul_of_nonneg_right (Nat.mono_cast (hk q.1 (mem_sigma.1 hq).1))
    ((v.nonneg _).trans (hB q.1 (mem_sigma.1 hq).1 0))

/-- Nonarchimedean companion to `abv_coeff_aeval_monomial_le`, without the support-size factor. -/
theorem abv_coeff_aeval_monomial_le_of_isNonarchimedean [CommSemiring S] [LinearOrder S]
    [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S} (hv : IsNonarchimedean v)
    {f : σ → MvPolynomial τ R} {B : S} {s : σ →₀ ℕ}
    (hB : ∀ i ∈ s.support, ∀ m, v ((f i).coeff m) ≤ B) (a : R) (t : τ →₀ ℕ) :
    v ((aeval f (monomial s a)).coeff t) ≤ B ^ s.degree * v a := by
  classical
  let I : Finset (Σ _ : σ, ℕ) := s.support.sigma fun i ↦ range (s i)
  have hcard : #I = s.degree := by simp [I, card_sigma, Finsupp.degree_apply]
  have hprod : (s.prod fun i e ↦ f i ^ e) = ∏ q ∈ I, f q.1 := by
    simp [I, prod_sigma, Finsupp.prod]
  rw [aeval_monomial, algebraMap_eq, ← smul_eq_C_mul, coeff_smul, smul_eq_mul, map_mul,
    mul_comm (v a), hprod, ← hcard, ← prod_const]
  exact mul_le_mul_of_nonneg_right
    (abv_coeff_prod_le_of_isNonarchimedean (fun q ↦ f q.1) hv
      (fun q hq ↦ hB q.1 (mem_sigma.1 hq).1) t) (v.nonneg a)

/-- Each coefficient of `linearSubst M (monomial s a)` is bounded under `v` by
`(card σ * B) ^ s.degree * v a` when the entries of `M` are bounded by `B`. -/
theorem abv_coeff_linearSubst_monomial_le [Fintype σ] [CommSemiring S] [PartialOrder S]
    [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S} {M : Matrix σ σ R} {B : S}
    (hM : ∀ i j, v (M i j) ≤ B) (s : σ →₀ ℕ) (a : R) (t : σ →₀ ℕ) :
    v ((linearSubst M (monomial s a)).coeff t) ≤ (Fintype.card σ * B) ^ s.degree * v a := by
  rw [linearSubst_eq_aeval]
  exact abv_coeff_aeval_monomial_le
    (fun i _ ↦ card_support_sum_C_mul_X_le (M i) id)
    (fun i _ ↦ abv_coeff_sum_C_mul_X_le Function.injective_id ((v.nonneg _).trans (hM i i)) (hM i))
    a t

/-- Nonarchimedean companion to `abv_coeff_linearSubst_monomial_le`. -/
theorem abv_coeff_linearSubst_monomial_le_of_isNonarchimedean [Fintype σ] [CommSemiring S]
    [LinearOrder S] [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S}
    (hv : IsNonarchimedean v) {M : Matrix σ σ R} {B : S} (hM : ∀ i j, v (M i j) ≤ B)
    (s : σ →₀ ℕ) (a : R) (t : σ →₀ ℕ) :
    v ((linearSubst M (monomial s a)).coeff t) ≤ B ^ s.degree * v a := by
  rw [linearSubst_eq_aeval]
  exact abv_coeff_aeval_monomial_le_of_isNonarchimedean hv
    (fun i _ ↦ abv_coeff_sum_C_mul_X_le Function.injective_id ((v.nonneg _).trans (hM i i)) (hM i))
    a t

/-- For a homogeneous polynomial `p` of degree `n`, if the entries of `M` are bounded by `B` and
the coefficients of `p` are bounded by `C` under `v`, then every coefficient of `linearSubst M p` is
bounded by `(card σ ^ 2 * B) ^ n * C`. -/
theorem abv_coeff_linearSubst_le_of_isHomogeneous [Fintype σ] [CommSemiring S] [PartialOrder S]
    [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S} {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) {M : Matrix σ σ R} {B C : S} (hM : ∀ i j, v (M i j) ≤ B)
    (hpC : ∀ a, v (p.coeff a) ≤ C) (t : σ →₀ ℕ) :
    v ((linearSubst M p).coeff t) ≤ (Fintype.card σ ^ 2 * B) ^ n * C := by
  classical
  have hC0 : 0 ≤ C := (v.nonneg _).trans (hpC 0)
  have hB0 : 0 ≤ Fintype.card σ * B := by
    by_cases hσ : Nonempty σ
    · obtain ⟨i₀⟩ := hσ
      exact mul_nonneg (Nat.cast_nonneg _) ((v.nonneg _).trans (hM i₀ i₀))
    · rw [not_nonempty_iff] at hσ
      simp
  have hsum : linearSubst M p = ∑ s ∈ p.support, linearSubst M (monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    exact map_sum _ _ _
  calc v ((linearSubst M p).coeff t)
      ≤ ∑ s ∈ p.support, v ((linearSubst M (monomial s (p.coeff s))).coeff t) := by
        rw [hsum, coeff_sum]
        exact v.sum_le _ _
    _ ≤ ∑ _s ∈ p.support, (Fintype.card σ * B) ^ n * C := sum_le_sum fun s hs ↦ by
        have hdeg : s.degree = n := by
          rw [Finsupp.degree_eq_weight_one (R := ℕ)]
          exact hp (mem_support_iff.1 hs)
        rw [← hdeg]
        exact (abv_coeff_linearSubst_monomial_le hM s (p.coeff s) t).trans
          (mul_le_mul_of_nonneg_left (hpC s) (pow_nonneg hB0 _))
    _ = #p.support * ((Fintype.card σ * B) ^ n * C) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card σ : S) ^ n * ((Fintype.card σ * B) ^ n * C) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg hB0 _) hC0)
        simpa only [Nat.cast_pow] using (Nat.mono_cast (card_support_le_pow_of_isHomogeneous hp) :
          (#p.support : S) ≤ ((Fintype.card σ ^ n : ℕ) : S))
    _ = (Fintype.card σ ^ 2 * B) ^ n * C := by
        rw [← mul_assoc, ← mul_pow, sq, mul_assoc]

/-- Nonarchimedean companion to `abv_coeff_linearSubst_le_of_isHomogeneous`. -/
theorem abv_coeff_linearSubst_le_of_isHomogeneous_of_isNonarchimedean [Fintype σ] [CommSemiring S]
    [LinearOrder S] [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S}
    (hv : IsNonarchimedean v) {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    {M : Matrix σ σ R} {B C : S} (hB0 : 0 ≤ B) (hM : ∀ i j, v (M i j) ≤ B)
    (hpC : ∀ a, v (p.coeff a) ≤ C) (t : σ →₀ ℕ) :
    v ((linearSubst M p).coeff t) ≤ B ^ n * C := by
  classical
  have hC0 : 0 ≤ C := (v.nonneg _).trans (hpC 0)
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using mul_nonneg (pow_nonneg hB0 n) hC0
  have hne : p.support.Nonempty := support_nonempty.2 hp0
  have hsum : linearSubst M p = ∑ s ∈ p.support, linearSubst M (monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    exact map_sum _ _ _
  rw [hsum, coeff_sum]
  refine (hv.apply_sum_le_sup hne).trans (sup'_le hne _ fun s hs ↦ ?_)
  have hdeg : s.degree = n := by
    rw [Finsupp.degree_eq_weight_one (R := ℕ)]
    exact hp (mem_support_iff.1 hs)
  rw [← hdeg]
  exact (abv_coeff_linearSubst_monomial_le_of_isNonarchimedean hv hM s (p.coeff s) t).trans
    (mul_le_mul_of_nonneg_left (hpC s) (pow_nonneg hB0 _))

/-- Each coefficient of `blockSubst A (monomial s a)` is bounded under `v` by
`(card ι * B) ^ s.degree * v a` when the entries of `A` are bounded by `B`. The bound depends on
`card ι` rather than on the block index type `κ`. -/
theorem abv_coeff_blockSubst_monomial_le [Fintype ι] [CommSemiring S] [PartialOrder S]
    [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S} {A : Matrix ι ι R} {B : S}
    (hA : ∀ i j, v (A i j) ≤ B) (s : κ × ι →₀ ℕ) (a : R) (t : κ × ι →₀ ℕ) :
    v ((blockSubst A (monomial s a)).coeff t) ≤ (Fintype.card ι * B) ^ s.degree * v a := by
  rw [blockSubst_eq_aeval]
  exact abv_coeff_aeval_monomial_le
    (fun p _ ↦ by
      simpa only [blockLinearForm_apply] using
        card_support_sum_C_mul_X_le (A p.2) (Prod.mk p.1))
    (fun p _ m ↦ by
      simpa only [blockLinearForm_apply] using
        abv_coeff_sum_C_mul_X_le (Prod.mk_right_injective p.1) ((v.nonneg _).trans (hA p.2 p.2))
          (hA p.2) m)
    a t

/-- Nonarchimedean companion to `abv_coeff_blockSubst_monomial_le`. -/
theorem abv_coeff_blockSubst_monomial_le_of_isNonarchimedean [Fintype ι] [CommSemiring S]
    [LinearOrder S] [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S}
    (hv : IsNonarchimedean v) {A : Matrix ι ι R} {B : S} (hA : ∀ i j, v (A i j) ≤ B)
    (s : κ × ι →₀ ℕ) (a : R) (t : κ × ι →₀ ℕ) :
    v ((blockSubst A (monomial s a)).coeff t) ≤ B ^ s.degree * v a := by
  rw [blockSubst_eq_aeval]
  exact abv_coeff_aeval_monomial_le_of_isNonarchimedean hv
    (fun p _ m ↦ by
      simpa only [blockLinearForm_apply] using
        abv_coeff_sum_C_mul_X_le (Prod.mk_right_injective p.1) ((v.nonneg _).trans (hA p.2 p.2))
          (hA p.2) m)
    a t

/-- For a multihomogeneous polynomial `P` of multidegree `d`, if the entries of `A` are bounded by
`B` and the coefficients of `P` are bounded by `C` under `v`, then every coefficient of
`blockSubst A P` is bounded by `(card ι ^ 2 * B) ^ (∑ h, d h) * C`. -/
theorem abv_coeff_blockSubst_le_of_isMultiHomogeneous [Fintype κ] [DecidableEq κ] [Fintype ι]
    [CommSemiring S] [PartialOrder S] [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S}
    {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} (hP : IsMultiHomogeneous d P) {A : Matrix ι ι R}
    {B C : S} (hA : ∀ i j, v (A i j) ≤ B) (hPC : ∀ a, v (P.coeff a) ≤ C) (t : κ × ι →₀ ℕ) :
    v ((blockSubst A P).coeff t) ≤ (Fintype.card ι ^ 2 * B) ^ (∑ h, d h) * C := by
  classical
  have hC0 : 0 ≤ C := (v.nonneg _).trans (hPC 0)
  have hB0 : 0 ≤ Fintype.card ι * B := by
    by_cases hι : Nonempty ι
    · obtain ⟨i₀⟩ := hι
      exact mul_nonneg (Nat.cast_nonneg _) ((v.nonneg _).trans (hA i₀ i₀))
    · rw [not_nonempty_iff] at hι
      simp
  have hsum : blockSubst A P = ∑ s ∈ P.support, blockSubst A (monomial s (P.coeff s)) := by
    conv_lhs => rw [P.as_sum]
    exact map_sum _ _ _
  calc v ((blockSubst A P).coeff t)
      ≤ ∑ s ∈ P.support, v ((blockSubst A (monomial s (P.coeff s))).coeff t) := by
        rw [hsum, coeff_sum]
        exact v.sum_le _ _
    _ ≤ ∑ _s ∈ P.support, (Fintype.card ι * B) ^ (∑ h, d h) * C := sum_le_sum fun s hs ↦ by
        have hdeg : s.degree = ∑ h, d h := by
          rw [Finsupp.degree_eq_weight_one (R := ℕ)]
          exact hP.isHomogeneous (mem_support_iff.1 hs)
        rw [← hdeg]
        exact (abv_coeff_blockSubst_monomial_le hA s (P.coeff s) t).trans
          (mul_le_mul_of_nonneg_left (hPC s) (pow_nonneg hB0 _))
    _ = #P.support * ((Fintype.card ι * B) ^ (∑ h, d h) * C) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card ι : S) ^ (∑ h, d h) * ((Fintype.card ι * B) ^ (∑ h, d h) * C) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg hB0 _) hC0)
        simpa only [Nat.cast_pow] using
          (Nat.mono_cast (card_support_le_pow_of_isMultiHomogeneous hP) :
            (#P.support : S) ≤ ((Fintype.card ι ^ ∑ h, d h : ℕ) : S))
    _ = (Fintype.card ι ^ 2 * B) ^ (∑ h, d h) * C := by
        rw [← mul_assoc, ← mul_pow, sq, mul_assoc]

/-- Nonarchimedean companion to `abv_coeff_blockSubst_le_of_isMultiHomogeneous`. -/
theorem abv_coeff_blockSubst_le_of_isMultiHomogeneous_of_isNonarchimedean [Fintype κ]
    [DecidableEq κ] [Fintype ι] [CommSemiring S] [LinearOrder S] [IsOrderedRing S] [IsDomain S]
    {v : AbsoluteValue R S} (hv : IsNonarchimedean v) {P : MvPolynomial (κ × ι) R} {d : κ → ℕ}
    (hP : IsMultiHomogeneous d P) {A : Matrix ι ι R} {B C : S} (hB0 : 0 ≤ B)
    (hA : ∀ i j, v (A i j) ≤ B) (hPC : ∀ a, v (P.coeff a) ≤ C) (t : κ × ι →₀ ℕ) :
    v ((blockSubst A P).coeff t) ≤ B ^ (∑ h, d h) * C := by
  classical
  have hC0 : 0 ≤ C := (v.nonneg _).trans (hPC 0)
  rcases eq_or_ne P 0 with rfl | hP0
  · simpa using mul_nonneg (pow_nonneg hB0 _) hC0
  have hne : P.support.Nonempty := support_nonempty.2 hP0
  have hsum : blockSubst A P = ∑ s ∈ P.support, blockSubst A (monomial s (P.coeff s)) := by
    conv_lhs => rw [P.as_sum]
    exact map_sum _ _ _
  rw [hsum, coeff_sum]
  refine (hv.apply_sum_le_sup hne).trans (sup'_le hne _ fun s hs ↦ ?_)
  have hdeg : s.degree = ∑ h, d h := by
    rw [Finsupp.degree_eq_weight_one (R := ℕ)]
    exact hP.isHomogeneous (mem_support_iff.1 hs)
  rw [← hdeg]
  exact (abv_coeff_blockSubst_monomial_le_of_isNonarchimedean hv hA s (P.coeff s) t).trans
    (mul_le_mul_of_nonneg_left (hPC s) (pow_nonneg hB0 _))

end AbsoluteValue

/-- `0 ≤ B` cannot be dropped in `abv_coeff_linearSubst_le_of_isHomogeneous_of_isNonarchimedean`:
over `σ = Empty`, the entry bound `∀ i j, v (M i j) ≤ B` is vacuous, so taking `p = 0`, `n = 1`,
`B = -1`, and `C = 1` gives `0 = v 0 > (-1) ^ 1 * 1`. -/
example :
    let v : AbsoluteValue ℤ ℤ := AbsoluteValue.trivial
    IsNonarchimedean v ∧ (0 : MvPolynomial Empty ℤ).IsHomogeneous 1 ∧
      (∀ i j : Empty, v ((0 : Matrix Empty Empty ℤ) i j) ≤ -1) ∧
      (∀ a, v ((0 : MvPolynomial Empty ℤ).coeff a) ≤ 1) ∧
      ¬ v ((linearSubst (0 : Matrix Empty Empty ℤ) 0).coeff 0) ≤ (-1 : ℤ) ^ 1 * 1 := by
  refine ⟨fun x y ↦ ?_, isHomogeneous_zero Empty ℤ 1, fun i ↦ i.elim, ?_, by simp⟩
  · by_cases hxy : x + y = 0 <;> by_cases hx : x = 0 <;>
      simp [AbsoluteValue.trivial_apply, hxy, hx]
  · intro a
    simp [Subsingleton.elim a 0]

end MvPolynomial
