/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful

/-!
# Triviality of the unipotent radical of a weight Levi

Over an algebraically closed field, every normal smooth unipotent closed subgroup of a
general-linear weight Levi is trivial. In particular, the unipotent radical is trivial.
The statements allow repeated weights, arbitrary characteristic, and rank zero. They provide
the normal-subgroup input for reductivity of block-diagonal Levi subgroups and for identifying
the unipotent radical of their parabolics.

The standard representation is faithful and completely reducible: each weight block is simple,
and invariant subspaces are sums of blocks. The general normal-invariants criterion therefore
forces a normal smooth unipotent subgroup to act trivially. Faithfulness identifies its defining
Hopf ideal with the augmentation ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 19.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.

The assembly follows `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive` and uses
`HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful_of_iso` for the
normal-invariants argument and transport to the finite-type coordinate package.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (k : Type u) [Field k] [IsAlgClosed k] {N : ℕ} (w : Fin N → ℤ)

/-- Every normal smooth unipotent closed subgroup of a weight Levi over an algebraically
closed field is trivial, including when distinct coordinates have the same weight. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent_weightLevi
    (I : HopfIdeal k (weightLeviFiniteTypeCoordinateHopfAlgebra k w)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (weightLeviFiniteTypeCoordinateHopfAlgebra k w) I)) :
    I = HopfIdeal.augmentation k (weightLeviFiniteTypeCoordinateHopfAlgebra k w) := by
  let H : FiniteTypeCommHopfAlgCat k :=
    ⟨weightLeviCoordinateHopfAlgebra k w,
      inferInstanceAs (Algebra.FiniteType k (weightLeviCoordinateHopfAlgebra k w))⟩
  let _ : IsReduced H :=
    inferInstanceAs (IsReduced (weightLeviCoordinateHopfAlgebra k w))
  let _ : Comodule k (weightLeviCoordinateHopfAlgebra k w) (Fin N → k) :=
    weightLeviStandardComodule k w
  exact HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful_of_iso
    k H (Fin N → k) (weightLeviFiniteTypeCoordinateHopfAlgebra k w)
    (eqToIso (weightLeviFiniteTypeCoordinateHopfAlgebra_obj k w).symm)
    (isCompletelyReducible_weightLeviStandardComodule w k)
    (isFaithful_weightLeviStandardComodule k w) I hI hU

/-- The unipotent radical of every weight Levi over an algebraically closed field is trivial.
Contravariantly, its defining ideal is the augmentation ideal. -/
@[simp]
theorem unipotentRadicalDefiningIdeal_weightLeviFiniteTypeCoordinateHopfAlgebra :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (weightLeviFiniteTypeCoordinateHopfAlgebra k w) =
      HopfIdeal.augmentation k (weightLeviFiniteTypeCoordinateHopfAlgebra k w) := by
  rw [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  exact eq_augmentation_of_isNormal_of_smoothUnipotent_weightLevi k w I
    hI.isNormal hI.smoothUnipotent

end

end TauCeti.GeneralLinear
