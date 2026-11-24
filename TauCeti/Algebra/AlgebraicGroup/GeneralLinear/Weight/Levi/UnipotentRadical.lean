/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful

/-!
# Normal smooth unipotent subgroups of a weight Levi are trivial

Over an algebraically closed field, every normal smooth unipotent closed subgroup of a
general-linear weight Levi is trivial.
The statement allows repeated weights, arbitrary characteristic, and rank zero. It provides
the normal-subgroup input for reductivity of block-diagonal Levi subgroups and for identifying
the unipotent radical of their parabolics.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 19.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.
* Formal source: `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Basic`.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (k : Type u) [Field k] [IsAlgClosed k] {N : ℕ} (w : Fin N → ℤ)

/-- Every normal smooth unipotent closed subgroup of a weight Levi over an algebraically
closed field is trivial, including when distinct coordinates have the same weight. -/
theorem eq_augmentation_weightLevi_of_isNormal_of_smoothUnipotent
    (I : HopfIdeal k (weightLeviFiniteTypeCoordinateHopfAlgebra k w)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (weightLeviFiniteTypeCoordinateHopfAlgebra k w) I)) :
    I = HopfIdeal.augmentation k (weightLeviFiniteTypeCoordinateHopfAlgebra k w) := by
  let _ : Comodule k (weightLeviCoordinateHopfAlgebra k w) (Fin N → k) :=
    weightLeviStandardComodule k w
  exact HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful
    k (weightLeviFiniteTypeCoordinateHopfAlgebra k w) (Fin N → k)
    (isCompletelyReducible_weightLeviStandardComodule w k)
    (isFaithful_weightLeviStandardComodule k w) I hI hU

end

end TauCeti.GeneralLinear
