/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Synonym

/-!
# Ring structure on the colexicographic type synonym

Transfer the additive-with-one and ring instances from `R` to `Colex R`, as Mathlib does for
`Rᵒᵈ` and `Lex R`, together with the `toColex`/`ofColex` lemmas for numerals and casts.
-/

public section

variable {R : Type*}

namespace Colex

instance distrib [Distrib R] : Distrib (Colex R) := inferInstanceAs <| Distrib R

instance leftDistribClass [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass (Colex R) :=
  inferInstanceAs <| LeftDistribClass R

instance rightDistribClass [Mul R] [Add R] [RightDistribClass R] : RightDistribClass (Colex R) :=
  inferInstanceAs <| RightDistribClass R

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (Colex R) :=
  inferInstanceAs <| NonUnitalNonAssocSemiring R

instance nonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (Colex R) :=
  inferInstanceAs <| NonUnitalSemiring R

instance natCast [NatCast R] : NatCast (Colex R) := inferInstanceAs <| NatCast R

instance intCast [IntCast R] : IntCast (Colex R) := inferInstanceAs <| IntCast R

instance addMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (Colex R) :=
  inferInstanceAs <| AddMonoidWithOne R

instance addCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne (Colex R) :=
  inferInstanceAs <| AddCommMonoidWithOne R

instance addGroupWithOne [AddGroupWithOne R] : AddGroupWithOne (Colex R) :=
  inferInstanceAs <| AddGroupWithOne R

instance addCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne (Colex R) :=
  inferInstanceAs <| AddCommGroupWithOne R

instance nonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (Colex R) :=
  inferInstanceAs <| NonAssocSemiring R

instance semiring [Semiring R] : Semiring (Colex R) := inferInstanceAs <| Semiring R

instance nonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring (Colex R) :=
  inferInstanceAs <| NonUnitalCommSemiring R

instance commSemiring [CommSemiring R] : CommSemiring (Colex R) := inferInstanceAs <| CommSemiring R

instance hasDistribNeg [Mul R] [HasDistribNeg R] : HasDistribNeg (Colex R) :=
  inferInstanceAs <| HasDistribNeg R

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (Colex R) :=
  inferInstanceAs <| NonUnitalNonAssocRing R

instance nonUnitalRing [NonUnitalRing R] : NonUnitalRing (Colex R) :=
  inferInstanceAs <| NonUnitalRing R

instance nonAssocRing [NonAssocRing R] : NonAssocRing (Colex R) := inferInstanceAs <| NonAssocRing R

instance ring [Ring R] : Ring (Colex R) := inferInstanceAs <| Ring R

instance nonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (Colex R) :=
  inferInstanceAs <| NonUnitalCommRing R

instance commRing [CommRing R] : CommRing (Colex R) := inferInstanceAs <| CommRing R

instance isDomain [Ring R] [IsDomain R] : IsDomain (Colex R) := inferInstanceAs <| IsDomain R

end Colex

@[simp]
theorem toColex_natCast [NatCast R] (n : ℕ) : toColex (n : R) = n :=
  rfl

@[simp]
theorem toColex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    toColex (ofNat(n) : R) = OfNat.ofNat n :=
  rfl

@[simp]
theorem ofColex_natCast [NatCast R] (n : ℕ) : (ofColex n : R) = n :=
  rfl

@[simp]
theorem ofColex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    ofColex (ofNat(n) : Colex R) = OfNat.ofNat n :=
  rfl

@[simp]
theorem toColex_intCast [IntCast R] (n : ℤ) : toColex (n : R) = n :=
  rfl

@[simp]
theorem ofColex_intCast [IntCast R] (n : ℤ) : (ofColex n : R) = n :=
  rfl
