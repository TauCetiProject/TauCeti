/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.BigWitt.Ghost.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Data.Nat.PadicValNat

import TauCeti.Data.Nat.Factorization.MulDvd
import TauCeti.RingTheory.Coprime.Lemmas
import Mathlib.NumberTheory.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# The image of the big Witt ghost map

Dwork's criterion describes integral ghost sequences using prime Frobenius lifts, without
requiring the lifts to commute or the coefficient ring to be torsion-free. Ghost coordinates
are unique when multiplication by each truncation index is injective. If those indices are
units, every ghost sequence has unique coordinates on the truncation set.

The image criterion follows Hesselholt, *The big de Rham–Witt complex*, Lemma 1.1.
-/

public section

namespace TauCeti.BigWitt

variable {R : Type*} [CommRing R]

private theorem dvd_sub_ghostSummand (p d m : ℕ) (hp : p.Prime) (hm : m ≠ 0)
    (hd : d ∣ m) (φ : R →+* R) (hφ : ∀ a : R, (p : R) ∣ φ a - a ^ p)
    (a : R) : (p : R) ^ (p * m).factorization p ∣
      (d : R) * a ^ (p * m / d) - φ ((d : R) * a ^ (m / d)) := by
  have hd0 := ne_zero_of_dvd_ne_zero hm hd
  have hv : (p * m).factorization p =
      d.factorization p + ((m / d).factorization p + 1) := by
    have hle := (Nat.factorization_le_iff_dvd hd0 hm).mpr hd p
    simp only [Nat.factorization_mul hp.ne_zero hm, Finsupp.add_apply,
      hp.factorization_self, Nat.factorization_div hd, Finsupp.tsub_apply]
    omega
  -- The power congruence supplies the factors of `p` missing from the coefficient `d`.
  have hpower : (p : R) ^ ((m / d).factorization p + 1) ∣
      (a ^ p) ^ (m / d) - (φ a) ^ (m / d) := by
    obtain ⟨k, hk⟩ := Nat.ordProj_dvd (m / d) p
    have h := dvd_trans (dvd_sub_pow_of_dvd_sub
      (by simpa only [neg_sub] using dvd_neg.mpr (hφ a)) ((m / d).factorization p))
      (sub_dvd_pow_sub_pow ((a ^ p) ^ p ^ (m / d).factorization p)
        ((φ a) ^ p ^ (m / d).factorization p) k)
    simpa only [← pow_mul, mul_assoc, ← hk] using h
  have hcoeff : (p : R) ^ d.factorization p ∣ (d : R) := by
    simpa using (Nat.castRingHom R).map_dvd (Nat.ordProj_dvd d p)
  have hsummand : (d : R) * a ^ (p * m / d) - φ ((d : R) * a ^ (m / d)) =
      (d : R) * ((a ^ p) ^ (m / d) - (φ a) ^ (m / d)) := by
    simp only [map_mul, map_natCast, map_pow, Nat.mul_div_assoc p hd, pow_mul, mul_sub]
  calc
    (p : R) ^ (p * m).factorization p =
        (p : R) ^ d.factorization p * (p : R) ^ ((m / d).factorization p + 1) := by
      rw [hv, pow_add]
    _ ∣ (d : R) * ((a ^ p) ^ (m / d) - (φ a) ^ (m / d)) :=
      mul_dvd_mul hcoeff hpower
    _ = (d : R) * a ^ (p * m / d) - φ ((d : R) * a ^ (m / d)) := hsummand.symm

private theorem dvd_ghostPolynomial_sub_frobenius (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0)
    (φ : R →+* R) (hφ : ∀ a : R, (p : R) ∣ φ a - a ^ p)
    (x : ℕ → R) : (p : R) ^ (p * m).factorization p ∣
      ghostPolynomial (p * m) x - φ (ghostPolynomial m x) := by
  classical
  have hn : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
  have hs : (p * m).divisors.filter (· ∣ m) = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨fun h => ⟨h.2, hm⟩, fun h => ⟨⟨h.1.trans (dvd_mul_left m p), hn⟩, h.1⟩⟩
  rw [ghostPolynomial_eq_sum, ghostPolynomial_eq_sum, map_sum, ← hs,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro d hd
  by_cases hdm : d ∣ m
  · simpa [hdm] using dvd_sub_ghostSummand p d m hp hm hdm φ hφ (x d)
  · simp only [hdm, ↓reduceIte, sub_zero]
    -- A divisor of `p * m` that does not divide `m` contains the full `p`-part.
    have hd' := Nat.dvd_of_mem_divisors hd
    have hpd : ¬ p * d ∣ p * m := by
      simpa only [Nat.mul_dvd_mul_iff_left hp.pos] using hdm
    have h := (Nat.mul_dvd_iff_forall_not_pow_dvd hn (dvd_mul_right p m) hd').not.mp hpd
    have hv := hp.factorization_pos_of_dvd hn (dvd_mul_right p m)
    have hpow : p ^ (p * m).factorization p ∣ d := by
      simpa [hp.primeFactors, hp.factorization_self, Nat.sub_add_cancel hv] using h
    apply dvd_mul_of_dvd_left
    simpa using (Nat.castRingHom R).map_dvd hpow

private noncomputable def ghostCoordinates (b : ℕ → R) : ℕ → R := by
  classical
  exact Nat.strongRec fun n rec =>
    let prev := fun d => if hd : d < n then rec d hd else 0
    let c := b n - ∑ d ∈ n.properDivisors, (d : R) * prev d ^ (n / d)
    if h : (n : R) ∣ c then Classical.choose h else 0

private theorem ghostCoordinates_spec (b : ℕ → R) (n : ℕ)
    (h : (n : R) ∣ b n -
      ∑ d ∈ n.properDivisors, (d : R) * ghostCoordinates b d ^ (n / d)) :
    (n : R) * ghostCoordinates b n = b n -
      ∑ d ∈ n.properDivisors, (d : R) * ghostCoordinates b d ^ (n / d) := by
  classical
  have he : (∑ d ∈ n.properDivisors, (d : R) *
      (if d < n then ghostCoordinates b d else 0) ^ (n / d)) =
      ∑ d ∈ n.properDivisors, (d : R) * ghostCoordinates b d ^ (n / d) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [ite_eq_left (Nat.mem_properDivisors.mp hd).2]
  unfold ghostCoordinates at h he ⊢
  conv_lhs =>
    arg 2
    rw [Nat.strongRec_eq]
  simp only [dite_eq_ite, he, dite_eq_left h]
  exact (Classical.choose_spec h).symm

private theorem ghost_numerator_dvd (S : TruncationSet) (φ : ℕ → R →+* R)
    (hφ : ∀ p, p.Prime → p ∈ S → ∀ a : R, (p : R) ∣ φ p a - a ^ p)
    (b x : ℕ → R)
    (hb : ∀ p, p.Prime → ∀ n ∈ S, p ∣ n →
      (p : R) ^ n.factorization p ∣ b n - φ p (b (n / p)))
    {n : ℕ} (hn : n ∈ S)
    (hprev : ∀ m ∈ S, m < n → ghostPolynomial m x = b m) :
    (n : R) ∣ b n - ∑ d ∈ n.properDivisors, (d : R) * x d ^ (n / d) := by
  classical
  let y := Function.update x n 0
  have hny : ghostPolynomial n y =
      ∑ d ∈ n.properDivisors, (d : R) * x d ^ (n / d) := by
    rw [ghostPolynomial_eq_sum_properDivisors_add n y (S.pos hn).ne']
    simp only [y, Function.update_self, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Function.update_of_ne (Nat.mem_properDivisors.mp hd).2.ne]
  have hprime : ∀ p ∈ n.primeFactors, (p : R) ^ n.factorization p ∣
      b n - ghostPolynomial n y := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have hm := Nat.div_pos (Nat.le_of_dvd (S.pos hn) hpn) hpp.pos
    have hmn := Nat.div_lt_self (S.pos hn) hpp.one_lt
    have hmy : ghostPolynomial (n / p) y = b (n / p) := by
      refine (ghostPolynomial_congr (y := x) ?_).trans
        (hprev _ (S.mem_of_dvd hn (Nat.div_dvd_of_dvd hpn)) hmn)
      intro d hd
      exact Function.update_of_ne ((Nat.divisor_le hd).trans_lt hmn).ne 0 x
    have hy := dvd_ghostPolynomial_sub_frobenius p (n / p) hpp hm.ne' (φ p)
      (hφ p hpp (S.mem_of_dvd hn hpn)) y
    rw [Nat.mul_div_cancel' hpn, hmy] at hy
    simpa only [sub_sub_sub_cancel_right] using dvd_sub (hb p hpp n hn hpn) hy
  have hprod := Finset.prod_primes_pow_dvd
    (fun p hp => Nat.prime_of_mem_primeFactors hp) n.factorization hprime
  have hnprod := congrArg (fun k : ℕ => (k : R))
    (Nat.prod_primeFactors_pow_factorization (S.pos hn).ne')
  simp only [Nat.cast_prod, Nat.cast_pow] at hnprod
  rwa [← hnprod, hny] at hprod

/-- Dwork's ghost-image criterion with independent prime Frobenius lifts.
The modulus at a prime `p` dividing `n` is its full power `p ^ padicValNat p n`.
The lifts can be chosen independently over any commutative ring.
See Hesselholt, *The big de Rham–Witt complex*, Lemma 1.1. -/
theorem ghost_image (S : TruncationSet) (φ : ℕ → R →+* R)
    (hφ : ∀ p, p.Prime → p ∈ S → ∀ a : R,
      φ p a - a ^ p ∈ Ideal.span ({(p : R)} : Set R)) (b : ℕ → R) :
    (∃ x : ℕ → R, ∀ n ∈ S, ghostPolynomial n x = b n) ↔
      ∀ p, p.Prime → ∀ n ∈ S, p ∣ n →
        b n - φ p (b (n / p)) ∈
          Ideal.span ({(p : R) ^ padicValNat p n} : Set R) := by
  have hφ' : ∀ p, p.Prime → p ∈ S → ∀ a : R, (p : R) ∣ φ p a - a ^ p := by
    intro p hp hps a
    exact Ideal.mem_span_singleton.mp (hφ p hp hps a)
  constructor
  · rintro ⟨x, hx⟩ p hp n hn hpn
    have hm := Nat.div_pos (Nat.le_of_dvd (S.pos hn) hpn) hp.pos
    apply Ideal.mem_span_singleton.mpr
    rw [← hx n hn, ← hx (n / p) (S.mem_of_dvd hn (Nat.div_dvd_of_dvd hpn))]
    have h := dvd_ghostPolynomial_sub_frobenius p (n / p) hp hm.ne' (φ p)
      (hφ' p hp (S.mem_of_dvd hn hpn)) x
    simpa only [Nat.mul_div_cancel' hpn, Nat.factorization_def n hp, Nat.padicValNat_def] using h
  · intro hb
    refine ⟨ghostCoordinates b, ?_⟩
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      have hnum := ghost_numerator_dvd S φ hφ' b (ghostCoordinates b)
        (fun p hp n hn hpn => by
          simpa only [Nat.factorization_def n hp, Nat.padicValNat_def] using
            Ideal.mem_span_singleton.mp (hb p hp n hn hpn)) hn
        (fun m hm hmn => ih m hmn hm)
      rw [ghostPolynomial_eq_sum_properDivisors_add n _ (S.pos hn).ne',
        ghostCoordinates_spec b n hnum]
      rw [add_comm, sub_add_cancel]

/-- If every truncation index is a unit, each ghost sequence has coordinates, uniquely
on the truncation set. Values outside the truncation set impose no uniqueness condition. -/
theorem ghost_exists_eqOn_unique_of_isUnit (S : TruncationSet)
    (hS : ∀ n ∈ S, IsUnit (n : R)) (b : ℕ → R) :
    ∃ x : ℕ → R, (∀ n ∈ S, ghostPolynomial n x = b n) ∧
      ∀ y : ℕ → R, (∀ n ∈ S, ghostPolynomial n y = b n) → Set.EqOn y x S := by
  have hφ : ∀ p : ℕ, p.Prime → p ∈ S → ∀ a : R,
      RingHom.id R a - a ^ p ∈ Ideal.span ({(p : R)} : Set R) := by
    intro p _ hp a
    exact Ideal.mem_span_singleton.mpr (hS p hp).dvd
  obtain ⟨x, hx⟩ := (ghost_image S (fun _ => RingHom.id R) hφ b).mpr (by
    intro p _ n hn hpn
    exact Ideal.mem_span_singleton.mpr ((hS p (S.mem_of_dvd hn hpn)).pow _).dvd)
  refine ⟨x, hx, fun y hy => ghost_injective S ?_ (fun n hn => (hy n hn).trans (hx n hn).symm)⟩
  intro n hn a c hac
  apply (hS n hn).mul_right_injective
  simpa only [nsmul_eq_mul] using hac

end TauCeti.BigWitt
