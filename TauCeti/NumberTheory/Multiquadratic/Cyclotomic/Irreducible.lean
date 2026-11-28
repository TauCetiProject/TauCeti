/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.FundamentalDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Cyclotomic.QuadraticBaseChange
import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.Conductor
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants

/-!
# Cyclotomic polynomials over quadratic number fields

The conductor of `ℚ(√D)` for a fundamental discriminant `D ≠ 1` decides whether a cyclotomic
polynomial remains irreducible over that field: `Φₙ` stays irreducible exactly when `|D| ∤ n`.
In particular, adjoining a primitive root of unity of order coprime to an odd prime `p ≡ 3 mod 4`
to `ℚ(√−p)` gives a cyclotomic extension of the full degree `φ(n)`.

The conductor input is `TauCeti.Multiquadratic.mem_adjoin_simple_iff_natAbs_dvd`, which uses
quadratic Gauss sums; see also Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section

open IntermediateField Polynomial TauCeti.Multiquadratic

/-- For a fundamental discriminant `D ≠ 1`, the `n`-th cyclotomic polynomial is irreducible over
`ℚ(√D)` if and only if `|D|` does not divide `n`. -/
theorem Int.IsFundamentalDiscr.irreducible_cyclotomic_adjoin_sqrt_iff_not_dvd
    {L : Type*} [Field L] [CharZero L] {n : ℕ} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hD₁ : D ≠ 1) {x : L} (hx : x ^ 2 = (D : L)) :
    Irreducible (cyclotomic n ℚ⟮x⟯) ↔ ¬ D.natAbs ∣ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  let : NeZero n := ⟨hn.ne'⟩
  -- Put both roots in a common field without assuming `L` contains roots of unity.
  let f := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure L) n
  have hx' : f x ^ 2 = (D : AlgebraicClosure L) := by rw [← map_pow, hx, map_intCast]
  have hmap : ℚ⟮x⟯.map f = ℚ⟮f x⟯ := by rw [adjoin_map, Set.image_singleton]
  let e := (equivMap ℚ⟮x⟯ f).trans (equivOfEq hmap)
  have he : Irreducible (cyclotomic n ℚ⟮f x⟯) ↔ Irreducible (cyclotomic n ℚ⟮x⟯) := by
    simpa only [coe_mapAlgEquiv, map_cyclotomic] using
      (MulEquiv.irreducible_iff (Polynomial.mapAlgEquiv e) (x := cyclotomic n ℚ⟮x⟯))
  have hx'' : f x ^ 2 = algebraMap ℚ (AlgebraicClosure L) (D : ℚ) := by
    simpa only [map_intCast] using hx'
  rw [← he, hζ.irreducible_cyclotomic_adjoin_sq_iff_notMem (cyclotomic.irreducible_rat hn) hx''
    (hD.not_isSquare_rat hD₁), mem_adjoin_simple_iff_natAbs_dvd hn hζ hD hx']

/-- For a prime `p ≡ 3 mod 4`, `Φₙ` is irreducible over `ℚ(√−p)` exactly when `p ∤ n`. -/
theorem Nat.Prime.irreducible_cyclotomic_adjoin_sqrt_neg_prime_iff
    {L : Type*} [Field L] [CharZero L] {n p : ℕ} (hp : p.Prime) (hp₄ : p % 4 = 3)
    {x : L} (hx : x ^ 2 = -(p : L)) :
    Irreducible (cyclotomic n ℚ⟮x⟯) ↔ ¬ p ∣ n := by
  have hD : Int.IsFundamentalDiscr (-(p : ℤ)) := by
    rw [← oddPrimeDiscriminant_of_mod_four_eq_three hp₄]
    have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
    exact (isPrimeDiscriminant_oddPrimeDiscriminant hp hpodd).isFundamentalDiscr
  have hD₁ : -(p : ℤ) ≠ 1 := by omega
  have hx' : x ^ 2 = Int.cast (R := L) (-(p : ℤ)) := by
    simpa only [Int.cast_neg, Int.cast_natCast] using hx
  simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
    hD.irreducible_cyclotomic_adjoin_sqrt_iff_not_dvd hD₁ hx'
