/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.IntegralNormOne
public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.RootsOfUnity
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Integral norm-one points in quadratic cyclotomic composita

In a CM field obtained by adjoining a square root of an odd prime discriminant of absolute
value greater than three to an even cyclotomic field, the integral points of the norm-one
torus are precisely the powers of the cyclotomic generator. In particular, triviality of a
character on the integral principal points can be tested on one root of unity.

This is the integral-point calculation of `New.Data.exists_zeta_pow_eq_of_isIntegral` in
`grh/src/New/Derivatives/Field/ChosenPlaces.lean` of lsernau/grh-lean at `72fead1`. It uses
Kronecker's theorem and the cyclotomic compositum calculation of
`IsPrimitiveRoot.eq_pow_of_mem_sup_adjoin_of_sq_eq_oddPrimeDiscriminant`.
-/

public section

open IntermediateField NumberField NumberField.IsCMField TauCeti.Multiquadratic

namespace IsPrimitiveRoot

/-- Let `E = ℚ(ζ, √D)` be a CM number field, where `ζ` is primitive of positive even order `n`
and `D` is the discriminant of absolute value `p` for a prime `p > 3`. Its integral elements
of norm one to the maximal real subfield are exactly the powers `ζ ^ k` with `k < n`. -/
theorem exists_pow_eq_iff_isIntegral_and_mul_complexConj_eq_one
    {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]
    {n p : ℕ} [NeZero n]
    {ζ x z : E} (hζ : IsPrimitiveRoot ζ n) (hn : Even n) (hp : p.Prime) (hp3 : 3 < p)
    (hx : x ^ 2 = (oddPrimeDiscriminant p : E)) (hgen : ℚ⟮ζ⟯ ⊔ ℚ⟮x⟯ = ⊤) :
    (∃ k < n, ζ ^ k = z) ↔ IsIntegral ℤ z ∧ z * complexConj E z = 1 := by
  have hpair : adjoin ℚ ({ζ, x} : Set E) = ⊤ := by
    rw [← Set.singleton_union, adjoin_union, hgen]
  have : FiniteDimensional ℚ (⊤ : IntermediateField ℚ E) := hpair ▸
    finiteDimensional_adjoin_pair (Algebra.IsIntegral.isIntegral ζ)
      (Algebra.IsIntegral.isIntegral x)
  have : FiniteDimensional ℚ E := IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have : NumberField E := { }
  rw [← isOfFinOrder_iff_isIntegral_and_mul_complexConj_eq_one]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact (hζ.isOfFinOrder (NeZero.ne n)).pow (n := k)
  · intro hz
    let f : E →ₐ[ℚ] ℂ := IsAlgClosed.lift
    have hx' : (f x) ^ 2 = (oddPrimeDiscriminant p : ℂ) := by
      simp [← map_pow, hx]
    have hmap : f z ∈ (ℚ⟮ζ⟯ ⊔ ℚ⟮x⟯).map f := ⟨z, hgen ▸ mem_top, rfl⟩
    have hmem : f z ∈ ℚ⟮f ζ⟯ ⊔ ℚ⟮f x⟯ := by
      simpa only [IntermediateField.map_sup, adjoin_map, Set.image_singleton] using hmap
    obtain ⟨k, hk, heq⟩ := eq_pow_of_mem_sup_adjoin_of_sq_eq_oddPrimeDiscriminant
      (hζ.map_of_injective f.injective) hn hp hp3 hx' (f.toMonoidHom.isOfFinOrder hz) hmem
    exact ⟨k, hk, f.injective ((map_pow f ζ k).trans heq)⟩

end IsPrimitiveRoot
