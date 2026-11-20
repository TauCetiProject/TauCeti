/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StableRange
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Bass stable range of semilocal rings and of one-dimensional domains

This file bounds the Bass stable range `TauCeti.HasStableRangeLE` of two classes of commutative
rings, the bounds used for elementary reduction of invertible matrices in algebraic `K₁`.

* A commutative **semilocal** ring, one with finitely many maximal ideals, has stable range at
  most `1`. If `a` and `b` are coprime, the Chinese remainder theorem gives `c` which is `1`
  modulo the maximal ideals containing `a` and `0` modulo the others; then `a + b * c` lies in
  no maximal ideal, so it is a unit.
* **Bass's reduction step.** If every quotient `R ⧸ (x)` by a nonzero element has stable range at
  most `s`, then `R` has stable range at most `s + 1`. One first moves a nonzero entry into the
  leading coordinate of a unimodular row and then shortens the remaining coordinates modulo it.
* A commutative noetherian domain of Krull dimension at most one, for instance a Dedekind domain
  such as `ℤ` or a ring of `S`-integers, or a field, has stable range at most `2`: its quotients by
  nonzero elements are artinian, hence semilocal.

## Main results

* `TauCeti.exists_isUnit_add_mul_of_isCoprime`: in a semilocal ring, coprime `a`, `b` have a unit
  of the form `a + b * c`.
* `TauCeti.hasStableRangeLE_one_of_finite_maximalSpectrum`: commutative semilocal rings have
  stable range at most `1`.
* `TauCeti.hasStableRangeLE_succ_of_forall_ne_zero`: Bass's reduction step.
* `TauCeti.hasStableRangeLE_two_of_krullDimLE_one`: noetherian domains of Krull dimension at most
  one have stable range at most `2`.

## References

* H. Bass, *K-theory and stable algebra*, Publ. Math. IHÉS 22 (1964), §4 and §6.
* H. Bass, *Algebraic K-Theory*, W. A. Benjamin (1968), Chapter V, §3.
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
theorem exists_isUnit_add_mul_of_isCoprime {a b : R} (hab : IsCoprime a b) :
    ∃ c, IsUnit (a + b * c) := by
  classical
  -- By the Chinese remainder theorem choose `c` congruent to `1` modulo the maximal ideals
  -- containing `a` and to `0` modulo the others; then `a + b * c` lies in no maximal ideal.
  let I : MaximalSpectrum R → Ideal R := fun m ↦ m.asIdeal
  have hI : Pairwise (IsCoprime on I) := fun m n hmn ↦
    Ideal.isCoprime_of_isMaximal fun h ↦ hmn (MaximalSpectrum.ext h)
  obtain ⟨c', hc'⟩ := Ideal.quotientInfToPiQuotient_surj hI
    fun m ↦ Ideal.Quotient.mk (I m) (if a ∈ I m then 1 else 0)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  refine ⟨c, by_contra fun hu ↦ ?_⟩
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  have hc : Ideal.Quotient.mk m c = Ideal.Quotient.mk m (if a ∈ m then 1 else 0) :=
    congrFun hc' ⟨m, hm⟩
  obtain ⟨u, v, huv⟩ := hab
  have hmk : Ideal.Quotient.mk m (u * a + v * b) = 1 := by rw [huv, map_one]
  have hmem' : Ideal.Quotient.mk m (a + b * c) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_add, map_mul, hc] at hmem'
  by_cases ha : a ∈ m
  · have ha' : Ideal.Quotient.mk m a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    simp only [ha, ite_true, map_one, ha', mul_one, zero_add] at hmem'
    simp [ha', hmem'] at hmk
  · simp only [ha, ite_false, map_zero, mul_zero, add_zero] at hmem'
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mp hmem')

/-- **Semilocal rings have stable range one.** A commutative ring with finitely many maximal ideals
(in particular a commutative local ring, or a commutative artinian ring) has Bass stable range at
most `1`. -/
theorem hasStableRangeLE_one_of_finite_maximalSpectrum (R : Type*) [CommRing R]
    [Finite (MaximalSpectrum R)] : HasStableRangeLE R 1 := by
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_
  have hcop : IsCoprime (a 0) (a 1) :=
    ⟨b 0, b 1, by simpa [Fin.sum_univ_two, mul_comm] using hab⟩
  obtain ⟨c, u, hu⟩ := exists_isUnit_add_mul_of_isCoprime hcop
  exact ⟨fun _ ↦ c, fun _ ↦ ↑u⁻¹, by simp [Fin.last, ← hu]⟩

end Semilocal

/-! ## Bass's reduction step and one-dimensional domains -/

section Reduction

variable {R : Type*} [CommRing R]

/-- **Bass's reduction step.** If the quotient of a commutative ring `R` by every nonzero
principal ideal has stable range at most `s`, then `R` has stable range at most `s + 1`. -/
theorem hasStableRangeLE_succ_of_forall_ne_zero {s : ℕ}
    (h : ∀ x : R, x ≠ 0 → HasStableRangeLE (R ⧸ Ideal.span {x}) s) :
    HasStableRangeLE R (s + 1) := by
  classical
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_
  -- If the last entry vanishes, the remaining row is already unimodular.
  by_cases hL : a (Fin.last (s + 1)) = 0
  · refine ⟨0, fun i ↦ b i.castSucc, ?_⟩
    simpa [Fin.sum_univ_castSucc, hL] using hab
  set L := a (Fin.last (s + 1))
  -- Otherwise make the leading entry `x = a₀ + aₛ₊₁ * c₀` nonzero, shorten `(a₁, …, aₛ₊₁)`
  -- modulo `x`, and use `x` itself to restore unimodularity in `R`.
  set c₀ : R := if a 0 = 0 then 1 else 0
  set x : R := a 0 + L * c₀
  have hx : x ≠ 0 := by
    by_cases h0 : a 0 = 0 <;> simp [x, c₀, h0, hL]
  set π := Ideal.Quotient.mk (Ideal.span {x}) with hπ
  have hπx : π x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  -- Modulo `x`, the row `(a₁, …, aₛ₊₁)` is unimodular.
  have hsum : ∑ k : Fin (s + 1), π (a k.succ) *
      (π (b k.succ) - if k = Fin.last s then π (c₀ * b 0) else 0) = 1 := by
    have hπa0 : π (a 0) = -(π L * π c₀) := by
      rw [eq_neg_iff_add_eq_zero, ← map_mul, ← map_add]
      exact hπx
    have := congrArg π hab
    rw [map_one, map_sum, Fin.sum_univ_succ, map_mul, hπa0] at this
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Fin.succ_last, map_mul]
    rw [← this]
    simp only [L, map_mul]
    ring
  obtain ⟨c', d', hcd'⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp (h x hx) _ _ hsum
  choose c hc using fun j ↦ Ideal.Quotient.mk_surjective (c' j)
  choose d hd using fun j ↦ Ideal.Quotient.mk_surjective (d' j)
  -- Lift the shortened row and correct the defect, a multiple of `x`.
  have hmem : ∑ j : Fin s, (a j.castSucc.succ + L * c j) * d j - 1 ∈ Ideal.span {x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hπ, map_sub, map_one, sub_eq_zero, ← hcd', map_sum]
    simp only [map_mul, map_add, hπ, hc, hd, L, Fin.succ_last, Nat.succ_eq_add_one]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨Fin.cons c₀ c, Fin.cons (-r) d, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]
  rw [← eq_sub_iff_add_eq.mp hr]
  ring

/-- **One-dimensional noetherian domains have stable range at most two.** A commutative noetherian
domain of Krull dimension at most one, such as a Dedekind domain or a field, has Bass stable range
at most `2`: its quotient by a nonzero element is artinian, hence semilocal, and so has stable range
at most `1`. -/
theorem hasStableRangeLE_two_of_krullDimLE_one (R : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] : HasStableRangeLE R 2 := by
  refine hasStableRangeLE_succ_of_forall_ne_zero fun x hx ↦ ?_
  have : IsArtinianRing (R ⧸ Ideal.span {x}) := by
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff,
      ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
    exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hx)).trans Order.KrullDimLE.krullDim_le
  exact hasStableRangeLE_one_of_finite_maximalSpectrum _

end Reduction

end TauCeti
