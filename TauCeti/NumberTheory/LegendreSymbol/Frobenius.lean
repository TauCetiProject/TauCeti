/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.Frobenius

/-!
# The Frobenius acts on square roots by the Legendre symbol

Let `S` be a commutative domain, `Q` a prime of `S` lying over the rational prime `p ≠ 2`, and
`φ` an arithmetic Frobenius at `Q` (`AlgHom.IsArithFrobAt`, so `φ y ≡ y ^ p (mod Q)` for all
`y`). If `x ∈ S` is a square root of an integer `d` with `p ∤ d`, then

`φ x = legendreSym p d • x`.

Indeed `φ x ≡ x ^ p = (x²)^((p-1)/2) · x = d^((p-1)/2) · x ≡ (d/p) · x (mod Q)` by Euler's
criterion, while `(φ x)² = x²` forces `φ x = ± x` on the nose; the two signs are separated
modulo `Q` because `2x ∈ Q` would force `p ∣ 4d`. This is the local input for the Frobenius
form of the multiquadratic splitting law (Layer 1 of the multiquadratic roadmap): the Frobenius
of `ℚ(√d₁, …, √dₙ)` at `p` acts on each generator by the sign `(dᵢ/p)`.
`TauCeti.NumberTheory.NumberField.Frobenius` transports this computation to the Galois group of
a number field, and `TauCeti.NumberTheory.Multiquadratic.Frobenius` applies it to the
multiquadratic generators.

## Main results

* `TauCeti.AlgHom.IsArithFrobAt.apply_sqrt`: `φ x = legendreSym p d • x` for an arithmetic
  Frobenius `φ : S →ₐ[ℤ] S` at `Q` and `x² = d`.
* `TauCeti.IsArithFrobAt.smul_sqrt`: the same for a Frobenius element `σ` of a group acting
  on `S`.
-/

public section

open Ideal

namespace TauCeti

/-- An ideal of a `ℤ`-algebra lying over the integer ideal `(a)` meets `ℤ` exactly in the
multiples of `a`: `algebraMap ℤ S m ∈ Q ↔ a ∣ m`. -/
theorem algebraMap_int_mem_iff_dvd_of_liesOver {S : Type*} [CommRing S] {a : ℤ}
    (Q : Ideal S) [Q.LiesOver (span {a})] (m : ℤ) :
    algebraMap ℤ S m ∈ Q ↔ a ∣ m :=
  (Ideal.mem_of_liesOver Q (span {a}) m).symm.trans Ideal.mem_span_singleton

variable {S : Type*} [CommRing S] [IsDomain S] {Q : Ideal S}
  {p : ℕ} [Fact p.Prime] {d : ℤ} {x : S}

omit [IsDomain S] [Fact p.Prime] in
/-- The residue cardinality entering `AlgHom.IsArithFrobAt` over the rational prime `p` is `p`
itself. -/
private theorem natCard_quotient_under (Q : Ideal S) [Q.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := Q) (p := span {(p : ℤ)}),
    Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv]
  simp

/-- **An arithmetic Frobenius acts on square roots by the Legendre symbol.** Let `S` be a
domain, `Q` a prime of `S` over the odd rational prime `p`, and `φ : S →ₐ[ℤ] S` an arithmetic
Frobenius at `Q`. If `x² = d` for an integer `d` not divisible by `p`, then
`φ x = legendreSym p d • x`: the Frobenius fixes `√d` when `d` is a quadratic residue mod `p`
and negates it otherwise. -/
theorem AlgHom.IsArithFrobAt.apply_sqrt {φ : S →ₐ[ℤ] S} (H : φ.IsArithFrobAt Q)
    [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (hodd : p ≠ 2) (hd : ¬ (p : ℤ) ∣ d)
    (hx : x ^ 2 = algebraMap ℤ S d) :
    φ x = legendreSym p d • x := by
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hodd)
  -- The Frobenius congruence at `Q`, with the residue cardinality identified as `p`.
  have hcong : φ x - x ^ p ∈ Q := by
    have h := H x
    rwa [natCard_quotient_under (p := p) Q] at h
  -- `x ^ p = d ^ (p / 2) · x` exactly, since `x² = d` and `p = 2·(p/2) + 1`.
  have hxp : x ^ p = algebraMap ℤ S (d ^ (p / 2)) * x := by
    conv_lhs => rw [show p = 2 * (p / 2) + 1 by omega]
    rw [pow_succ, pow_mul, hx, ← map_pow]
  -- Euler's criterion: `p ∣ d ^ (p / 2) - legendreSym p d`.
  have heuler : (p : ℤ) ∣ d ^ (p / 2) - legendreSym p d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr (legendreSym.eq_pow p d).symm
  -- Combining: `φ x ≡ legendreSym p d • x (mod Q)`.
  have hkey : φ x - legendreSym p d • x ∈ Q := by
    have hstep : algebraMap ℤ S (d ^ (p / 2)) * x - legendreSym p d • x ∈ Q := by
      have hfactor : algebraMap ℤ S (d ^ (p / 2)) * x - legendreSym p d • x =
          algebraMap ℤ S (d ^ (p / 2) - legendreSym p d) * x := by
        simp only [map_sub, sub_mul, zsmul_eq_mul, eq_intCast]
      rw [hfactor]
      exact Q.mul_mem_right x ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mpr heuler)
    have hsum := Q.add_mem hcong hstep
    rw [hxp] at hsum
    rwa [sub_add_sub_cancel] at hsum
  -- `(φ x)² = x²`, so `φ x = ± x` on the nose.
  have hsq : (φ x - x) * (φ x + x) = 0 := by
    have hexp : (φ x - x) * (φ x + x) = φ (x ^ 2) - x ^ 2 := by rw [map_pow]; ring
    rw [hexp, hx, AlgHom.commutes, sub_self]
  -- The Legendre symbol is `±1` since `p ∤ d`.
  have hleg : legendreSym p d = 1 ∨ legendreSym p d = -1 :=
    legendreSym.eq_one_or_neg_one p (by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd)
  -- If the global sign disagreed with the symbol, `2x ∈ Q` would give `p ∣ 4d`.
  have hsep : x + x ∉ Q := by
    intro hmem
    have h4d : algebraMap ℤ S (4 * d) ∈ Q := by
      have hsq4 : algebraMap ℤ S (4 * d) = (x + x) * (x + x) := by
        rw [map_mul, ← hx, eq_intCast]
        push_cast
        ring
      rw [hsq4]
      exact Q.mul_mem_right _ hmem
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    rcases hpint.dvd_mul.mp ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp h4d) with h4 | hdd
    · -- `p ∣ 4` forces `p = 2`, excluded.
      have hp4 : p ∣ 4 := by exact_mod_cast h4
      have h22 : p ∣ 2 ^ 2 := by simpa using hp4
      have hp2' : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow h22
      exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp2')
    · exact hd hdd
  rcases mul_eq_zero.mp hsq with h | h
  · -- `φ x = x`: the congruence forces the symbol to be `1`.
    have hfix : φ x = x := sub_eq_zero.mp h
    rcases hleg with h1 | h1
    · rw [hfix, h1, one_smul]
    · exfalso
      apply hsep
      have hmem := hkey
      rw [hfix, h1, neg_smul, one_smul, sub_neg_eq_add] at hmem
      exact hmem
  · -- `φ x = -x`: the congruence forces the symbol to be `-1`.
    have hflip : φ x = -x := eq_neg_of_add_eq_zero_left h
    rcases hleg with h1 | h1
    · exfalso
      apply hsep
      have hmem := hkey
      rw [hflip, h1, one_smul] at hmem
      have hneg := Q.neg_mem hmem
      rwa [neg_sub, sub_neg_eq_add] at hneg
    · rw [hflip, h1, neg_smul, one_smul]

/-- **A Frobenius element acts on square roots by the Legendre symbol**, group-action form: if
`σ : G` is an arithmetic Frobenius at a prime `Q` over the odd prime `p` and `x² = d` with
`p ∤ d`, then `σ • x = legendreSym p d • x`. -/
theorem IsArithFrobAt.smul_sqrt {G : Type*} [Group G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] {σ : G} (H : _root_.IsArithFrobAt ℤ σ Q)
    [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (hodd : p ≠ 2) (hd : ¬ (p : ℤ) ∣ d)
    (hx : x ^ 2 = algebraMap ℤ S d) :
    σ • x = legendreSym p d • x :=
  TauCeti.AlgHom.IsArithFrobAt.apply_sqrt H hodd hd hx

end TauCeti
