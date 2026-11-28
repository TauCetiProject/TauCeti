/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.PlaceOfInt
import TauCeti.Algebra.GroupWithZero.Basic

/-!
# The Galois action of signed cyclotomic place labels

The cyclotomic automorphism attached to an invertible integer label acts on roots of unity
by the integer power itself, not just by its nonnegative residue. This lets the action of a
negative label be computed using inversion. Nonunit labels give the identity action.

The integer-label formula is `New.Parameters.galOfPlace_placeOfInt_zeta` in
`grh/src/New/Reduction/Data/FieldsAndPlaces.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
(revision `72fead1`).
-/

public section

open IsCyclotomicExtension Polynomial

namespace TauCeti.OneSidedBound.Parameters

/-- The automorphism at an integer label acts on all roots of unity of the tower order.
For a unit residue the exponent is the original signed integer; for a nonunit the
place label is the identity. -/
theorem autEquivPow_symm_placeOfInt_apply (P : Parameters) (s : ℕ)
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {P.q₁ s} K L]
    (hirr : Irreducible (cyclotomic (P.q₁ s) K)) {a : ℤ} {x : L} (hx : x ^ P.q₁ s = 1) :
    (autEquivPow L hirr).symm (P.placeOfInt s a) x =
      if IsUnit (a : ZMod P.q₀) then x ^ a else x := by
  classical
  by_cases ha : IsUnit (a : ZMod P.q₀)
  · simp only [ite_eq_left ha, autEquivPow_apply_of_pow_eq_one L hirr _ hx,
      MulEquiv.apply_symm_apply]
    rw [← zpow_natCast]
    apply zpow_eq_zpow_of_modEq hx
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    rw [Int.cast_natCast, ZMod.natCast_zmod_val, P.val_placeOfInt_of_isUnit s ha]
  · simp [ha]

end TauCeti.OneSidedBound.Parameters
