/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Char.Two
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Char.Three

/-!
# The height-two bound for elliptic Weierstrass curves at 2 and 3

For an elliptic Weierstrass curve over any commutative ring, the third height ideal
of its formal group is the unit ideal at the primes 2 and 3. Equivalently, Landweber's
`v₂` is a unit modulo `(p, v₁)`. All subsequent height quotients therefore vanish.
The statements concern families, including rings with nilpotents and the zero ring;
they impose no characteristic assumption on the coefficient ring.

The field-height classifications in characteristics 2 and 3, together with detection
of a proper height ideal on a maximal-ideal quotient, give the family-level result.
This supplies the height-two unit condition for Landweber exactness at these primes.
It does not assert the separate regularity of `p` and `v₁` for an arbitrary family.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7 and V.3.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    {p n : ℕ}

/-- At 2 and 3, every height ideal from `I₃` onward of the formal group of an elliptic
Weierstrass curve is the unit ideal. This holds over arbitrary commutative coefficient rings. -/
theorem heightIdeal_formalGroup_eq_top_of_two_or_three (hp : p = 2 ∨ p = 3)
    (hn : 3 ≤ n) : (formalGroup W).heightIdeal p n = ⊤ := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  apply ((formalGroup W).heightIdeal_eq_top_iff_forall_height_lt hprime (by omega)).mpr
  intro K _ _ f
  rw [← map_formalGroup]
  have hheight : (formalGroup (W.map f)).height p = 1 ∨
      (formalGroup (W.map f)).height p = 2 := by
    rcases hp with rfl | rfl
    · exact (W.map f).height_formalGroup_eq_one_or_eq_two_of_char_two
    · exact (W.map f).height_formalGroup_eq_one_or_eq_two_of_char_three
  rcases hheight with h | h <;> rw [h] <;> exact_mod_cast (by omega : _ < n)

/-- At 2 and 3, Landweber's `v₂` of the formal group of an elliptic Weierstrass curve is
a unit modulo `(p, v₁)`. This is the height-two unit condition, with no regularity assumption
on the coefficient ring. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_of_two_or_three (hp : p = 2 ∨ p = 3) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  exact ((formalGroup W).isUnit_mk_coeff_nsmulSeries_iff hprime 2).mpr
    (W.heightIdeal_formalGroup_eq_top_of_two_or_three hp le_rfl)

end WeierstrassCurve
