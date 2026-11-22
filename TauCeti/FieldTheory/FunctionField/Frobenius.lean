/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.FieldTheory.RatFunc.PowerTower
public import TauCeti.RingTheory.Valuation.Discrete.Frobenius
import TauCeti.FieldTheory.Frobenius.Range
import TauCeti.FieldTheory.IntermediateField.Adjoin.Transcendental
import TauCeti.RingTheory.Kaehler.PBasis

/-!
# Frobenius and separating elements of a function field

This file proves the fixed-parameter part of Stichtenoth's separable-generation criterion.  For a
one-variable function field `F / k` over a perfect field of exponential characteristic `p`, an
element outside the subfield `F^p` of Frobenius powers is separating.  Consequently, a place at
which the order of `x` is not divisible by `p` certifies that `x` is separating.

A separating parameter exists over a perfect field, which makes the Kähler differentials `Ω[F⁄k]`
one-dimensional; in positive characteristic, the degree–dimension formula
`TauCeti.finrank_fieldRange_frobenius_eq_pow_finrank_kaehlerDifferential` then gives
`[F : F^p] = p`. Combined with `TauCeti.D_eq_zero_iff_mem_fieldRange_frobenius` for the kernel
identification `ker (D k F) = F^p` and the differential separability criterion, this characterizes
separating elements as the elements outside `F^p`.

## Main results

* `TauCeti.IsFunctionField.finrank_fieldRange_frobenius`: `[F : F^p] = p`.
* `TauCeti.IsFunctionField.isSeparable_adjoin_iff_notMem_fieldRange_frobenius`: `x` is separating
  exactly when it lies outside `F^p`.
* `TauCeti.IsFunctionField.transcendental_and_isSeparable_adjoin_of_notMem_fieldRange_frobenius`:
  an element outside `F^p` is transcendental and separating.
* `TauCeti.IsFunctionField.exists_pow_eq_and_adjoin_eq_top_of_finrank_prime_of_not_isSeparable`:
  an inseparable subextension `F / k(x)` of prime degree has `x = y ^ p` with `F = k(y)`.
* `TauCeti.IsFunctionField.transcendental_and_isSeparable_adjoin_of_not_dvd_ord`: the
  valuation-order criterion.
* `TauCeti.Place.transcendental_and_isSeparable_adjoin_of_not_dvd_ord`: its form for places, in
  every characteristic: an element whose order at a place is not divisible by the characteristic
  is separating, and `TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`: in
  particular every prime element of a place is separating.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

public section

noncomputable section

open Module KaehlerDifferential

open scoped IntermediateField WithZero

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace IsFunctionField

/-- The degree of a one-variable function field over its subfield of `p`-th powers is `p`.
This is the degree computation underlying the fixed-parameter separability criterion. -/
theorem finrank_fieldRange_frobenius [PerfectField k] (hF : TauCeti.IsFunctionField k F)
    (p : ℕ) [ExpChar F p] :
    Module.finrank (frobenius F p).fieldRange F = p := by
  cases (inferInstance : ExpChar F p) with
  | zero =>
    have htop : (frobenius F 1).fieldRange = ⊤ :=
      eq_top_iff.mpr fun x _ ↦ ⟨x, by rw [frobenius_def, pow_one]⟩
    rw [htop, ← Subfield.relfinrank_top_right, Subfield.relfinrank_top_left]
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    have : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
    have : PerfectRing k p := PerfectField.toPerfectRing p
    obtain ⟨_, hy, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    have hdim : Module.finrank F Ω[F⁄k] = 1 :=
      finrank_kaehlerDifferential_eq_one_of_separating hy
    have : FiniteDimensional F Ω[F⁄k] := Module.finite_of_finrank_pos (by simp [hdim])
    have : FiniteDimensional (frobenius F p).fieldRange F :=
      (finiteDimensional_kaehlerDifferential_iff p k F
        (fun c ↦ algebraMap_mem_fieldRange_frobenius_of_perfectRing p c)).mp ‹_›
    rw [finrank_fieldRange_frobenius_eq_pow_finrank_kaehlerDifferential p k F
      (fun c ↦ algebraMap_mem_fieldRange_frobenius_of_perfectRing p c), hdim, pow_one]

/-- **Separating elements are the elements outside `F^p`** (Stichtenoth, Proposition 3.10.2(a)):
in a one-variable function field over a perfect field of characteristic `p`, `F / k(x)` is
separable exactly when `x` is not a `p`-th power in `F`. -/
theorem isSeparable_adjoin_iff_notMem_fieldRange_frobenius [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact p.Prime] (x : F) :
    Algebra.IsSeparable k⟮x⟯ F ↔ x ∉ (frobenius F p).fieldRange := by
  have : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  have : PerfectRing k p := PerfectField.toPerfectRing p
  rw [hF.isSeparable_adjoin_iff_D_ne_zero, ne_eq,
    TauCeti.D_eq_zero_iff_mem_fieldRange_frobenius
      (fun c ↦ algebraMap_mem_fieldRange_frobenius_of_perfectRing p c) x]

/-- **An element outside `F^p` is separating** (Stichtenoth, Proposition 3.10.2(a)): in a
one-variable function field over a perfect field of exponential characteristic `p`, an element
that is not a `p`-th power in `F` is transcendental over `k`, and `F / k(x)` is separable. In
characteristic zero (`p = 1`) the hypothesis `x ∉ F^p` is contradictory. -/
theorem transcendental_and_isSeparable_adjoin_of_notMem_fieldRange_frobenius [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] {x : F}
    (hx : x ∉ (frobenius F p).fieldRange) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hx ⟨x, by rw [frobenius_def, pow_one]⟩).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    have : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
    have : PerfectRing k p := PerfectField.toPerfectRing p
    have hDx : D k F x ≠ 0 := fun h ↦ hx ((TauCeti.D_eq_zero_iff_mem_fieldRange_frobenius
      (fun c ↦ algebraMap_mem_fieldRange_frobenius_of_perfectRing p c) x).mp h)
    exact ⟨transcendental_of_D_ne_zero hDx, hF.isSeparable_adjoin_iff_D_ne_zero.mpr hDx⟩

/-- **An inseparable subextension of prime degree comes from a `p`-th root.** Over a perfect
field of exponential characteristic `p`, if `[F : k(x)]` is prime and
`F / k(x)` is not separable, then `x = y ^ p` for an element `y` that generates `F` over `k`. So
`F` is then a rational function field, and `[F : k(x)] = p`. In characteristic zero the
hypotheses are contradictory. -/
theorem exists_pow_eq_and_adjoin_eq_top_of_finrank_prime_of_not_isSeparable [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] {x : F}
    (hprime : (Module.finrank k⟮x⟯ F).Prime) (hsep : ¬ Algebra.IsSeparable k⟮x⟯ F) :
    ∃ y : F, y ^ p = x ∧ k⟮y⟯ = ⊤ := by
  have : FiniteDimensional k⟮x⟯ F := Module.finite_of_finrank_pos hprime.pos
  have : Algebra.Transcendental k F := Algebra.transcendental_def.mpr hF.exists_transcendental
  have hx : Transcendental k x := transcendental_of_isAlgebraic_adjoin
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hsep inferInstance).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    -- `x` is a `p`-th power `y ^ p`, and `[k(y) : k(y ^ p)] = p` is a factor of the prime
    -- `[F : k(x)]`, so the complementary factor `[F : k(y)]` is one.
    obtain ⟨y, rfl⟩ : x ∈ (frobenius F p).fieldRange :=
      not_not.mp ((hF.isSeparable_adjoin_iff_notMem_fieldRange_frobenius p x).not.mp hsep)
    rw [frobenius_def] at hx hprime ⊢
    have hy : Transcendental k y := fun h ↦ hx (h.isIntegral.pow p).isAlgebraic
    have hle : k⟮y ^ p⟯ ≤ k⟮y⟯ := IntermediateField.adjoin_simple_le_iff.mpr
      (pow_mem (IntermediateField.mem_adjoin_simple_self k y) p)
    rw [← IntermediateField.relfinrank_mul_finrank_top hle, hy.relfinrank_adjoin_pow_adjoin p,
      Nat.prime_mul_iff] at hprime
    refine ⟨y, rfl, IntermediateField.finrank_eq_one_iff_eq_top.mp ?_⟩
    rcases hprime with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact (hp.ne_one h).elim

/-- **The valuation-order criterion for a separating element** (Stichtenoth, Proposition
3.10.2): if the order of `x` at a discrete valuation is not divisible by the exponential
characteristic `p`, then `x` is transcendental and `F / k(x)` is separable. -/
theorem transcendental_and_isSeparable_adjoin_of_not_dvd_ord [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (v : Valuation F ℤᵐ⁰) (p : ℕ)
    [ExpChar F p] {x : F} (hx : ¬ (p : ℤ) ∣ v.ord x) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hx (one_dvd _)).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    have hnotmem : x ∉ (frobenius F p).fieldRange := by
      rw [← iterateFrobenius_one (R := F) p]
      apply v.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord p 1
      simpa using hx
    exact hF.transcendental_and_isSeparable_adjoin_of_notMem_fieldRange_frobenius p hnotmem

end IsFunctionField

namespace Place

/-- **The valuation-order criterion for a separating element, at a place** (Stichtenoth,
Proposition 3.10.2): over a perfect field, if the order of `x` at a place is not divisible by the
characteristic of `F`, then `x` is transcendental and `F / k(x)` is separable. In characteristic
zero the hypothesis says that the order of `x` is nonzero. In particular every prime element of a
place, an element of order one, is separating. -/
theorem transcendental_and_isSeparable_adjoin_of_not_dvd_ord [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) {x : F}
    (hx : ¬ (ringChar F : ℤ) ∣ P.ord x) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  by_cases h0 : ringChar F = 0
  · -- In characteristic zero every algebraic extension is separable.
    have : CharP F 0 := ringChar.of_eq h0
    have : CharZero F := CharP.charP_to_charZero F
    have htr : Transcendental k x := P.transcendental_of_ord_ne_zero fun h ↦ hx (by simp [h])
    have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin htr
    exact ⟨htr, inferInstance⟩
  · have : CharP F (ringChar F) := ringChar.charP F
    have : ExpChar F (ringChar F) := .prime (CharP.char_prime_of_ne_zero F h0)
    exact hF.transcendental_and_isSeparable_adjoin_of_not_dvd_ord P.valuation (ringChar F)
      (by rwa [Valuation.ord_def, ← P.ord_def])

/-- **Every prime element of a place is separating** over a perfect field: an element of order one
at a place is transcendental, and `F` is separable over the subfield it generates. -/
theorem transcendental_and_isSeparable_adjoin_of_ord_eq_one [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) {t : F} (ht : P.ord t = 1) :
    Transcendental k t ∧ Algebra.IsSeparable k⟮t⟯ F :=
  P.transcendental_and_isSeparable_adjoin_of_not_dvd_ord hF <| by
    rw [ht, ← Nat.cast_one, Int.natCast_dvd_natCast, Nat.dvd_one]
    exact CharP.ringChar_ne_one

end Place

end TauCeti
