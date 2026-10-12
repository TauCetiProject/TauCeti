/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.CompletelyReducible
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful

/-!
# The unipotent radical obstruction for the type-D spin carrier

Let `H` be the coordinate Hopf algebra of the specialized full-weight type-`Dₙ` spin carrier.
Over an algebraically closed field, if `H` is reduced, then every normal smooth unipotent closed
subgroup of the carrier is trivial. Consequently its unipotent radical is trivial.

The mathematical input is the carrier's spin representation, its standard comodule of dimension
`2^n`. It is completely reducible and faithful. The generic normal-unipotent
elimination theorem
`TauCeti.HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful` then applies:
normality makes the fixed vectors of a smooth unipotent closed subgroup an ambient subcomodule,
Kolchin's fixed-vector theorem forces the subgroup to act trivially, and faithfulness identifies
its defining ideal with the augmentation ideal.

Reducedness is stated explicitly. No smoothness or connectedness of the carrier is asserted here,
so the result is the normal-unipotent obstruction needed for reductivity rather than a proof that
the carrier is reductive.

## Main declarations

* `TauCeti.TypeDSpinCarrier.eq_augmentation_of_isNormal_of_smoothUnipotent`: every normal smooth
  unipotent closed subgroup of a reduced specialized carrier is trivial.
* `TauCeti.TypeDSpinCarrier.unipotentRadicalDefiningIdeal_eq_augmentation`: the unipotent radical
  of a reduced specialized carrier is trivial.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The argument follows the type-`B` spin carrier in
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.UnipotentRadical` and the doubled minuscule
carrier in `TauCeti.Algebra.Lie.E6.DoubledMinuscule.UnipotentRadical`.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier

universe u

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) (k : Type u) [Field k] [IsAlgClosed k]

attribute [local instance] standardComodule

/-- **Every normal smooth unipotent closed subgroup of a reduced specialized type-`Dₙ` spin
carrier is trivial.**

The conclusion is stated contravariantly: the subgroup's defining Hopf ideal is the augmentation
ideal of the carrier's coordinate algebra. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    [IsReduced (coordinateHopfAlgebra n hn k)]
    (I : HopfIdeal k (coordinateHopfAlgebra n hn k)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra n hn k) I)) :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra n hn k) :=
  HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful k
    (finiteTypeCoordinateHopfAlgebra n hn k) (Fin (dimension n) → k)
    (isCompletelyReducible_standardComodule n hn k) (isFaithful_standardComodule n hn k) I hI hU

/-- **The unipotent radical of a reduced specialized type-`Dₙ` spin carrier over an
algebraically closed field is trivial.** -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation
    [IsReduced (coordinateHopfAlgebra n hn k)] :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (finiteTypeCoordinateHopfAlgebra n hn k) =
      HopfIdeal.augmentation k (coordinateHopfAlgebra n hn k) :=
  FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_of_isFaithful k
    (finiteTypeCoordinateHopfAlgebra n hn k) (Fin (dimension n) → k)
    (isCompletelyReducible_standardComodule n hn k) (isFaithful_standardComodule n hn k)

end

end TauCeti.TypeDSpinCarrier
