/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Basic

import TauCeti.FieldTheory.IntermediateField.Quadratic
import TauCeti.NumberTheory.Cyclotomic.CoprimeCompositum
import TauCeti.NumberTheory.Cyclotomic.RootsOfUnity
import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant

/-!
# Roots of unity in quadratic composita with even cyclotomic fields

Adjoining the square root of an odd prime discriminant of absolute value `p > 3` to an even
cyclotomic field does not enlarge its group of roots of unity. This identifies the possible
torsion elements when testing whether a character of a norm-one torus is trivial on global
integral points.

The degree argument follows `New.Parameters.exists_zeta_pow_eq` in
`New/Reduction/Data/FieldsAndPlaces.lean` of lsernau/grh-lean at `72fead1`. The cyclotomic field
facts are those of Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section

open IntermediateField Module
open TauCeti.Cyclotomic TauCeti.Multiquadratic

namespace IsPrimitiveRoot

/-- For an even positive `n` and a prime `p > 3`, the roots of unity in the compositum
`ℚ(ζ, √D)` are exactly the powers of `ζ`, where `ζ` is primitive of order `n` and `D` is the
odd prime discriminant of `p`. In particular, `D = -p` when `p ≡ 3 (mod 4)`. -/
theorem eq_pow_of_mem_sup_adjoin_of_sq_eq_oddPrimeDiscriminant {n p : ℕ} [NeZero n]
    {ζ x z : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : Even n) (hp : p.Prime) (hp3 : 3 < p)
    (hx : x ^ 2 = (oddPrimeDiscriminant p : ℂ)) (hz : IsOfFinOrder z)
    (hmem : z ∈ ℚ⟮ζ⟯ ⊔ ℚ⟮x⟯) : ∃ k < n, ζ ^ k = z := by
  have hζfield : ℚ⟮ζ⟯ = complexField n := by
    have : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ :=
      (isCyclotomicExtension_singleton_iff_eq_adjoin n ℚ ℂ _ hζ).mpr rfl
    exact isCyclotomicExtension_eq (S := {n}) (K := ℚ) (L := ℂ) _ _
  have : NeZero p := ⟨hp.ne_zero⟩
  have hD := isPrimeDiscriminant_oddPrimeDiscriminant hp (hp.odd_of_ne_two (by omega))
  have hxfield {j : ℕ} [NeZero j] (hj : p ∣ j) : ℚ⟮x⟯ ≤ complexField j := by
    rw [adjoin_simple_le_iff]
    exact mem_of_sq_eq_of_isFundamentalDiscr (NeZero.pos j) isPrimitiveRoot_complexRoot
      (complexRoot_mem_complexField j) hD.isFundamentalDiscr (by simpa using hj) hx
  refine hζ.eq_pow_of_pow_eq_one (orderOf_dvd_iff_pow_eq_one.mp ?_)
  by_cases hpn : p ∣ n
  · have hmem' : z ∈ complexField n := sup_le hζfield.le (hxfield hpn) hmem
    let z' : complexField n := ⟨z, hmem'⟩
    have hz' : IsPrimitiveRoot z' (orderOf z) :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (IsPrimitiveRoot.orderOf z)
    exact hz'.dvd_of_isCyclotomicExtension_even hz.orderOf_pos.ne' hn
  · have hnp := (hp.coprime_iff_not_dvd.mpr hpn).symm
    let E : IntermediateField ℚ ℂ := ℚ⟮ζ⟯ ⊔ ℚ⟮x⟯
    have he : E ≤ complexField (n * p) := by
      rw [← complexField_sup_eq hnp]
      exact sup_le_sup hζfield.le (hxfield dvd_rfl)
    let z' : E := ⟨z, hmem⟩
    let ζ' : E := ⟨ζ, (le_sup_left : ℚ⟮ζ⟯ ≤ E) (mem_adjoin_simple_self ℚ ζ)⟩
    have hz' : IsPrimitiveRoot z' (orderOf z) :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (IsPrimitiveRoot.orderOf z)
    have hζ' : IsPrimitiveRoot ζ' n := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
    refine hz'.dvd_of_finrank_lt_totient_mul_prime hz.orderOf_pos.ne' hζ' (inclusion he)
      (hn.mul_right p) hp ?_
    -- The quadratic compositum has degree at most `2φ(n)`, strictly smaller than `φ(np)`.
    have hx2 : x ^ 2 ∈ ℚ⟮ζ⟯ := by rw [hx]; exact intCast_mem _ _
    calc
      finrank ℚ E ≤ finrank ℚ ℚ⟮ζ⟯ * 2 := finrank_sup_adjoin_simple_le_mul_two _ hx2
      _ = n.totient * 2 := by rw [hζfield, IsCyclotomicExtension.Rat.finrank n]
      _ < (n * p).totient := by
        rw [Nat.totient_mul hnp, Nat.totient_prime hp]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.totient_pos.mpr (NeZero.pos n))

end IsPrimitiveRoot
