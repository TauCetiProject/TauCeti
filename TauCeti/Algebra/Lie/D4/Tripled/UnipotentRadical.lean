/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful

/-!
# The unipotent radical obstruction for the tripled type-D4 carrier

Let `H` be the coordinate Hopf algebra of the specialized tripled type-`D₄` carrier. Over an
algebraically closed field, if `H` is reduced, then every normal smooth unipotent closed subgroup
of the carrier is trivial. Consequently its unipotent radical is trivial.

The mathematical input is the carrier's standard 24-dimensional comodule
`V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)`. It is faithful and, by
`TauCeti.D4Tripled.isCompletelyReducible_standardComodule`, completely reducible although not
simple. The generic normal-unipotent elimination theorem
`TauCeti.HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful` then applies:
normality makes the fixed vectors of a smooth unipotent closed subgroup an ambient subcomodule,
Kolchin's fixed-vector theorem and complete reducibility force the subgroup to act trivially, and
faithfulness identifies its defining ideal with the augmentation ideal.

Reducedness is stated explicitly. No smoothness or connectedness of the carrier is asserted here,
so the result is the normal-unipotent obstruction needed for reductivity rather than a proof that
the carrier is reductive.

## Main declarations

* `TauCeti.D4Tripled.eq_augmentation_of_isNormal_of_smoothUnipotent`: every normal smooth
  unipotent closed subgroup of a reduced specialized carrier is trivial.
* `TauCeti.D4Tripled.unipotentRadicalDefiningIdeal_eq_augmentation`: the unipotent radical of
  a reduced specialized carrier is trivial.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The statements follow `TauCeti.Algebra.Lie.E7.Minuscule.UnipotentRadical`.
-/

public section

open CategoryTheory

namespace TauCeti.D4Tripled

universe u

noncomputable section

variable (k : Type u) [Field k] [IsAlgClosed k]

attribute [local instance] standardComodule

/-- **Every normal smooth unipotent closed subgroup of a reduced specialized tripled type-`D₄`
carrier is trivial.**

The conclusion is stated contravariantly: the subgroup's defining Hopf ideal is the augmentation
ideal of the carrier's coordinate algebra. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    [IsReduced (coordinateHopfAlgebra k)]
    (I : HopfIdeal k (coordinateHopfAlgebra k)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k) I)) :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k) :=
  HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful k
    (finiteTypeCoordinateHopfAlgebra k) (Fin 24 → k)
    (isCompletelyReducible_standardComodule k) (isFaithful_standardComodule k) I hI hU

/-- **The unipotent radical of a reduced specialized tripled type-`D₄` carrier over an
algebraically closed field is trivial.** -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation
    [IsReduced (coordinateHopfAlgebra k)] :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (finiteTypeCoordinateHopfAlgebra k) =
      HopfIdeal.augmentation k (coordinateHopfAlgebra k) :=
  FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_of_isFaithful k
    (finiteTypeCoordinateHopfAlgebra k) (Fin 24 → k)
    (isCompletelyReducible_standardComodule k) (isFaithful_standardComodule k)

end

end TauCeti.D4Tripled
