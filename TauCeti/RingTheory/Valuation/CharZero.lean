/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import TauCeti.RingTheory.Valuation.Center
import TauCeti.RingTheory.Valuation.LocalizationAtCenter
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Valuation subrings of fields of characteristic zero, over `ℚ`

A valuation subring `A` of a field `L` contains the image of `ℤ`, so it has a prime centre on `ℤ`
(Tau Ceti's `Valuation.centerIdeal`). This file records two consequences used to compare valuation
subrings of algebraic extensions of `ℚ` with places.

* If `L` is algebraic over `ℚ` and `A ≠ L`, the centre is nonzero, so some prime number `p` is a
  nonunit of `A` (`ValuationSubring.exists_prime_natCast_mem_nonunits`): if every nonzero integer
  were a unit of `A`, then `A` would contain every element of `L`, since a nonzero integer multiple
  of an algebraic element is integral over `ℤ`.
* Two valuation subrings of `L` having the same prime number `p` among their nonunits meet `ℚ` in
  the same valuation subring, the localization of `ℤ` at `p`
  (`ValuationSubring.comap_algebraMap_rat_eq_of_natCast_mem_nonunits`).

## Main results

* `ValuationSubring.exists_prime_natCast_mem_nonunits`: a proper valuation subring of a field
  algebraic over `ℚ` has a prime number among its nonunits.
* `ValuationSubring.comap_algebraMap_rat_eq_of_natCast_mem_nonunits`: valuation subrings with a
  common prime nonunit have the same restriction to `ℚ`.
-/

public section

namespace ValuationSubring

variable {L : Type*} [Field L]

private theorem valuation_intCast_le_one (A : ValuationSubring L) (n : ℤ) :
    A.valuation (algebraMap ℤ L n) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (by simp)

/-- The prime ideal of `ℤ` at which a valuation subring of `L` is centred. -/
private noncomputable abbrev intCenter (A : ValuationSubring L) : Ideal ℤ :=
  A.valuation.centerIdeal ℤ (valuation_intCast_le_one A)

private theorem isPrime_intCenter (A : ValuationSubring L) : (intCenter A).IsPrime :=
  Valuation.isPrime_centerIdeal _

private theorem natCast_mem_intCenter_iff (A : ValuationSubring L) (p : ℕ) :
    (p : ℤ) ∈ intCenter A ↔ (p : L) ∈ A.nonunits := by
  rw [Valuation.mem_centerIdeal, ← mem_nonunits_iff, map_natCast]

/-- Two prime ideals of `ℤ` containing the same prime number are equal. -/
private theorem intCenter_eq_of_mem {A A' : ValuationSubring L} {p : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∈ intCenter A) (h' : (p : ℤ) ∈ intCenter A') : intCenter A = intCenter A' := by
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible
    (Nat.prime_iff_prime_int.mp hp).irreducible
  rw [← hmax.eq_of_le (isPrime_intCenter A).ne_top ((Ideal.span_singleton_le_iff_mem _).mpr h),
    hmax.eq_of_le (isPrime_intCenter A').ne_top ((Ideal.span_singleton_le_iff_mem _).mpr h')]

variable [CharZero L]

/-- A valuation subring of a field algebraic over `ℚ` other than the whole field has a prime
number among its nonunits. -/
theorem exists_prime_natCast_mem_nonunits [Algebra.IsAlgebraic ℚ L] {A : ValuationSubring L}
    (hA : A ≠ ⊤) : ∃ p : ℕ, p.Prime ∧ (p : L) ∈ A.nonunits := by
  have hne : intCenter A ≠ ⊥ := by
    intro hbot
    refine hA (_root_.eq_top_iff.mpr fun x _ ↦ ?_)
    have : Algebra.IsAlgebraic ℤ L :=
      (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).mpr inferInstance
    obtain ⟨y, hy0, hy⟩ :=
      IsAlgebraic.exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x)
    -- `y • x` is integral over `ℤ`, so it lies in `A`, and `y` is a unit of `A`
    have hyA : y • x ∈ A :=
      Subring.isIntegrallyClosed_iff.mp inferInstance (hy.tower_top (A := A))
    have hy1 : A.valuation (algebraMap ℤ L y) = 1 := by
      refine le_antisymm (valuation_intCast_le_one A y) (not_lt.mp fun hlt ↦ hy0 ?_)
      have : y ∈ intCenter A := Valuation.mem_centerIdeal.mpr hlt
      rwa [hbot, Ideal.mem_bot] at this
    have hyinv : (algebraMap ℤ L y)⁻¹ ∈ A :=
      (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hy1, inv_one])
    have hy0' : (algebraMap ℤ L y) ≠ 0 := by simpa using hy0
    have := A.mul_mem _ _ hyinv hyA
    rwa [zsmul_eq_mul, ← eq_intCast (algebraMap ℤ L), inv_mul_cancel_left₀ hy0'] at this
  obtain ⟨x, hx, hxp⟩ := (isPrime_intCenter A).exists_mem_prime_of_ne_bot hne
  refine ⟨x.natAbs, Int.prime_iff_natAbs_prime.mp hxp, (natCast_mem_intCenter_iff A _).mp ?_⟩
  rw [Int.natCast_natAbs]
  rcases abs_choice x with h | h <;> rw [h]
  · exact hx
  · exact (intCenter A).neg_mem hx

/-- Two valuation subrings of `L` with the same centre on `ℤ` meet `ℚ` in the same valuation
subring. -/
private theorem comap_eq_of_intCenter_eq {A A' : ValuationSubring L}
    (h : intCenter A = intCenter A') :
    A.comap (algebraMap ℚ L) = A'.comap (algebraMap ℚ L) := by
  have hc (B : ValuationSubring L) : (B.comap (algebraMap ℚ L)).IsCenteredAt (intCenter B) :=
    ⟨fun n ↦ by
      rw [mem_comap, ← IsScalarTower.algebraMap_apply]
      exact (B.valuation_le_one_iff _).mp (valuation_intCast_le_one B n),
    fun n ↦ by
      rw [mem_nonunits_comap, ← IsScalarTower.algebraMap_apply, Valuation.mem_centerIdeal,
        mem_nonunits_iff]⟩
  have := isPrime_intCenter A
  exact (hc A).eq (h ▸ hc A')

/-- **Valuation subrings with a common prime nonunit agree on `ℚ`.** Two valuation subrings of a
field of characteristic zero having the same prime number `p` among their nonunits meet `ℚ` in the
same valuation subring. -/
theorem comap_algebraMap_rat_eq_of_natCast_mem_nonunits {A A' : ValuationSubring L} {p : ℕ}
    (hp : p.Prime) (h : (p : L) ∈ A.nonunits) (h' : (p : L) ∈ A'.nonunits) :
    A.comap (algebraMap ℚ L) = A'.comap (algebraMap ℚ L) :=
  comap_eq_of_intCenter_eq <| intCenter_eq_of_mem hp
    ((natCast_mem_intCenter_iff A p).mpr h) ((natCast_mem_intCenter_iff A' p).mpr h')

end ValuationSubring
