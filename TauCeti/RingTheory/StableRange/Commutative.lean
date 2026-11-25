/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.RingHom
public import TauCeti.RingTheory.StableRange
public import Mathlib.RingTheory.HopkinsLevitzki

import TauCeti.RingTheory.Ideal.PrimeAvoidance
import TauCeti.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Bass stable range of commutative semilocal and noetherian rings

This file bounds the Bass stable range `TauCeti.HasStableRangeLE` of two classes of commutative
rings, the bounds used for elementary reduction of invertible matrices in algebraic `K₁`.

* A commutative **semilocal** ring, one with finitely many maximal ideals, has stable range at
  most `1`. If `a` and `b` are coprime, then `a` is a unit modulo `b`; units lift along the
  quotient map `R → R ⧸ (b)` of a semilocal ring, so some `a + b * c` is a unit.
* **Bass's reduction step.** If every unimodular row `(a₀, …, aₛ₊₁)` has an element
  `x ∈ a₀ + (a₁, …, aₛ₊₁)` with `R ⧸ (x)` of stable range at most `s`, then `R` has stable range
  at most `s + 1`: the row `(a₁, …, aₛ₊₁)` is unimodular modulo `x`, and a shortening of it
  modulo `x` lifts to a shortening of `(a₀, …, aₛ₊₁)`. Two choices of `x` are useful: any nonzero
  element of the row, and, by prime avoidance for the coset `a₀ + (a₁, …, aₛ₊₁)`, an element
  outside every minimal prime when there are finitely many of those.
* **Bass's bound.** A commutative noetherian ring of Krull dimension at most `d` has stable range
  at most `d + 1`. Dividing by an element outside every minimal prime lowers the Krull dimension,
  so the reduction step gives the bound by induction on `d`, starting from the artinian, hence
  semilocal, rings of dimension zero. For instance a Dedekind domain such as `ℤ`, or a ring of
  `S`-integers, has stable range at most `2`.

## Main results

* `IsCoprime.exists_isUnit_add_mul`: in a semilocal ring, coprime `a`, `b` have a unit
  of the form `a + b * c`.
* `TauCeti.hasStableRangeLE_one_of_finite_maximalSpectrum`: commutative semilocal rings have
  stable range at most `1`.
* `TauCeti.hasStableRangeLE_succ_of_forall_exists`: Bass's reduction step.
* `TauCeti.hasStableRangeLE_succ_of_forall_ne_zero` and
  `TauCeti.hasStableRangeLE_succ_of_forall_notMem_minimalPrimes`: the reduction step through
  nonzero elements and through elements outside every minimal prime.
* `TauCeti.hasStableRangeLE_of_ringKrullDim_le`: Bass's bound `sr(R) ≤ dim R + 1` for commutative
  noetherian rings.

## References

* H. Bass, *K-theory and stable algebra*, Publ. Math. IHÉS 22 (1964), §4 and §6.
* H. Bass, *Algebraic K-Theory*, W. A. Benjamin (1968), Chapter V, §3, Theorem 3.5.
* I. Kaplansky, *Commutative Rings*, revised edition, University of Chicago Press (1974),
  Theorem 124.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, Exercise 1.5, and Chapter III, Lemma 1.4.
-/

public section

open Function

namespace TauCeti

/-! ## Semilocal rings -/

section Semilocal

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]

/-- In a commutative semilocal ring, if `a` and `b` are coprime then `a + b * c` is a unit for some
`c`. -/
theorem _root_.IsCoprime.exists_isUnit_add_mul {a b : R} (hab : IsCoprime a b) :
    ∃ c, IsUnit (a + b * c) := by
  -- Lift the unit `a` of `R ⧸ (b)` to a unit `w` of `R`; then `w - a` is a multiple of `b`.
  let f := Ideal.Quotient.mk (Ideal.span {b})
  obtain ⟨u, v, huv⟩ := hab
  have hfb : f b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b)
  have hfa : IsUnit (f a) :=
    .of_mul_eq_one_right (f u) (by simpa [hfb] using congrArg f huv)
  obtain ⟨w, hw⟩ := f.surjective_units_map_of_surjective Ideal.Quotient.mk_surjective hfa.unit
  have hmem : (w : R) - a ∈ Ideal.span {b} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    simpa [Units.coe_map, IsUnit.unit_spec] using congrArg Units.val hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨c, by rw [mul_comm, hc, add_sub_cancel]; exact w.isUnit⟩

/-- **Semilocal rings have stable range one.** A commutative ring with finitely many maximal ideals
(in particular a commutative local ring, or a commutative artinian ring) has Bass stable range at
most `1`. -/
theorem hasStableRangeLE_one_of_finite_maximalSpectrum (R : Type*) [CommRing R]
    [Finite (MaximalSpectrum R)] : HasStableRangeLE R 1 := by
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_
  have hcop : IsCoprime (a 0) (a 1) :=
    ⟨b 0, b 1, by simpa [Fin.sum_univ_two, mul_comm] using hab⟩
  obtain ⟨c, u, hu⟩ := hcop.exists_isUnit_add_mul
  exact ⟨fun _ ↦ c, fun _ ↦ ↑u⁻¹, by simp [Fin.last, ← hu]⟩

end Semilocal

/-! ## Bass's reduction step and the Krull-dimension bound -/

section Reduction

variable {R : Type*} [CommRing R]

/-- **Bass's reduction step.** Suppose every unimodular row `(a₀, …, aₛ₊₁)` over a commutative
ring `R` has an element `x ∈ a₀ + (a₁, …, aₛ₊₁)` whose quotient `R ⧸ (x)` has stable range at
most `s`. Then `R` has stable range at most `s + 1`: the row `(a₁, …, aₛ₊₁)` is unimodular modulo
`x`, its shortening modulo `x` lifts, and `x` itself restores unimodularity in `R`. -/
theorem hasStableRangeLE_succ_of_forall_exists {s : ℕ}
    (h : ∀ a : Fin (s + 2) → R, Module.IsUnimodular R a → ∃ x,
      x - a 0 ∈ Ideal.span (Set.range fun i : Fin (s + 1) ↦ a i.succ) ∧
        HasStableRangeLE (R ⧸ Ideal.span {x}) s) :
    HasStableRangeLE R (s + 1) := by
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_
  obtain ⟨x, hx, hxs⟩ := h a (TauCeti.Module.isUnimodular_pi_iff.mpr ⟨b, hab⟩)
  -- Write `x = a₀ + ∑ tₖ aₖ₊₁`.
  obtain ⟨t, ht⟩ := Submodule.mem_span_range_iff_exists_fun R |>.mp hx
  simp only [smul_eq_mul] at ht
  set L := a (Fin.last (s + 1))
  let π := Ideal.Quotient.mk (Ideal.span {x})
  -- Modulo `x`, the row `(a₁, …, aₛ₊₁)` is unimodular, since `a₀ ≡ -∑ tₖ aₖ₊₁`.
  have hsum : ∑ k : Fin (s + 1), π (a k.succ) * π (b k.succ - t k * b 0) = 1 := by
    have hπx : π x = 0 := Ideal.Quotient.mk_singleton_self x
    have h1 := congrArg π hab
    have h2 := congrArg π ht
    rw [map_sum, Fin.sum_univ_succ] at h1
    simp only [map_sum, map_mul, map_sub, map_one] at h1 h2 ⊢
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hπx] at h2
    have h3 : ∑ k : Fin (s + 1), π (a k.succ) * (π (t k) * π (b 0)) =
        (∑ k : Fin (s + 1), π (t k) * π (a k.succ)) * π (b 0) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [h3, h2]
    linear_combination h1
  obtain ⟨c', d', hcd'⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp hxs _ _ hsum
  choose c hc using fun j ↦ Ideal.Quotient.mk_surjective (c' j)
  choose d hd using fun j ↦ Ideal.Quotient.mk_surjective (d' j)
  -- Lift the shortened row and correct the defect, a multiple `r * x` of `x`.
  have hmem : ∑ j : Fin s, (a j.castSucc.succ + L * c j) * d j - 1 ∈ Ideal.span {x} := by
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    simpa [π, hc, hd, sub_eq_zero] using hcd'
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  -- With `c₀ = tₛ - ∑ tⱼ cⱼ`, the new leading entry is `x - ∑ tⱼ (aⱼ₊₁ + L cⱼ)`.
  refine ⟨Fin.cons (t (Fin.last s) - ∑ j : Fin s, t j.castSucc * c j) c,
    Fin.cons (-r) fun j ↦ d j - r * t j.castSucc, ?_⟩
  rw [Fin.sum_univ_castSucc] at ht
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, ← Fin.succ_castSucc, mul_sub,
    Finset.sum_sub_distrib, Fin.succ_last] at ht ⊢
  have e1 : ∑ j : Fin s, (a j.castSucc.succ + L * c j) * (r * t j.castSucc) =
      r * ∑ j : Fin s, t j.castSucc * a j.castSucc.succ +
        r * L * ∑ j : Fin s, t j.castSucc * c j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [e1]
  linear_combination -r * ht - hr

/-- **Bass's reduction step for nonzero elements.** If the quotient of a commutative ring `R` by
every nonzero principal ideal has stable range at most `s`, then `R` has stable range at most
`s + 1`. -/
theorem hasStableRangeLE_succ_of_forall_ne_zero {s : ℕ}
    (h : ∀ x : R, x ≠ 0 → HasStableRangeLE (R ⧸ Ideal.span {x}) s) :
    HasStableRangeLE R (s + 1) := by
  cases subsingleton_or_nontrivial R
  · exact HasStableRangeLE.of_subsingleton R _
  refine hasStableRangeLE_succ_of_forall_exists fun a ha ↦ ?_
  -- Some entry `aᵢ` of the unimodular row is nonzero; use `a₀` if it is, and `a₀ + aᵢ = aᵢ`
  -- otherwise.
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h0
    obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
    simp [h0] at hb
  by_cases h0 : a 0 = 0
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (show i ≠ 0 by rintro rfl; exact hi h0)
    have hj : a j.succ ∈ Ideal.span (Set.range fun i : Fin (s + 1) ↦ a i.succ) :=
      Ideal.subset_span ⟨j, rfl⟩
    exact ⟨a j.succ, by simpa [h0] using hj, h _ hi⟩
  · exact ⟨a 0, by simp, h _ h0⟩

/-- **Bass's reduction step through minimal primes.** Let `R` be a commutative ring with finitely
many minimal primes. If `R ⧸ (x)` has stable range at most `s` for every `x` outside all minimal
primes of `R`, then `R` has stable range at most `s + 1`. Coset prime avoidance moves the leading
entry of a unimodular row outside every minimal prime. -/
theorem hasStableRangeLE_succ_of_forall_notMem_minimalPrimes {s : ℕ}
    (hfin : (minimalPrimes R).Finite)
    (h : ∀ x : R, (∀ p ∈ minimalPrimes R, x ∉ p) → HasStableRangeLE (R ⧸ Ideal.span {x}) s) :
    HasStableRangeLE R (s + 1) := by
  refine hasStableRangeLE_succ_of_forall_exists fun a ha ↦ ?_
  -- No prime contains every entry of the unimodular row `a`.
  have hp : ∀ p ∈ minimalPrimes R, a 0 ∈ p →
      ¬Ideal.span (Set.range fun i : Fin (s + 1) ↦ a i.succ) ≤ p := by
    intro p hp ha0 hle
    obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp ha
    refine hp.1.1.ne_top (p.eq_top_iff_one.mpr (hb ▸ p.sum_mem fun i _ ↦ p.mul_mem_right _ ?_))
    cases i using Fin.cases with
    | zero => exact ha0
    | succ j => exact hle (Ideal.subset_span ⟨j, rfl⟩)
  obtain ⟨y, hy, hay⟩ := Ideal.exists_mem_forall_add_notMem hfin (fun p hp ↦ hp.1.1) hp
  exact ⟨a 0 + y, by simpa using hy, h _ hay⟩

/-- **Bass's bound** (Bass, Theorem V.3.5). A commutative noetherian ring of Krull dimension at
most `d` has stable range at most `d + 1`. For instance a Dedekind domain such as `ℤ`, or a ring
of `S`-integers, has stable range at most `2`. -/
theorem hasStableRangeLE_of_ringKrullDim_le (A : Type*) [CommRing A] [IsNoetherianRing A]
    (d : ℕ) (h : ringKrullDim A ≤ d) : HasStableRangeLE A (d + 1) := by
  induction d generalizing A with
  | zero =>
    -- A zero-dimensional noetherian ring is artinian, hence semilocal.
    have : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr (by simpa using h)
    have := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := A)
    exact hasStableRangeLE_one_of_finite_maximalSpectrum A
  | succ d ih =>
    refine hasStableRangeLE_succ_of_forall_notMem_minimalPrimes
      (minimalPrimes.finite_of_isNoetherianRing A) fun x hx ↦ ih _ ?_
    -- Dividing by `x` outside every minimal prime lowers the dimension.
    have := (ringKrullDim_quotient_span_singleton_succ_le_of_notMem_minimalPrimes hx).trans h
    rwa [Nat.cast_add_one, ENat.WithBot.add_le_add_one_right_iff] at this

end Reduction

end TauCeti
