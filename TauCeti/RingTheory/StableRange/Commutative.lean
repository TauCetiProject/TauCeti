/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.RingHom
public import TauCeti.RingTheory.StableRange
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Bass stable range of semilocal rings and of one-dimensional domains

This file bounds the Bass stable range `TauCeti.HasStableRangeLE` of two classes of commutative
rings, the bounds used for elementary reduction of invertible matrices in algebraic `K₁`.

* A commutative **semilocal** ring, one with finitely many maximal ideals, has stable range at
  most `1`. If `a` and `b` are coprime, then `a` is a unit modulo `b`; units lift along the
  quotient map `R → R ⧸ (b)` of a semilocal ring, so some `a + b * c` is a unit.
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
  -- `R ⧸ (x)` has finite length as an `R`-module, so it is an artinian ring.
  have : IsArtinianRing (R ⧸ Ideal.span {x}) :=
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero hx))).2
    isArtinian_of_tower R this
  exact hasStableRangeLE_one_of_finite_maximalSpectrum _

end Reduction

end TauCeti
