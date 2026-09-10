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

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 19.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.
* Formal source: `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive`.
-/

public section

open CategoryTheory

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
  -- The named finite-type package has an unexposed body. This local presentation has
  -- the coordinate algebra as its carrier, so its reducedness and comodule instances
  -- are those of that algebra. The object lemma below supplies the explicit transport.
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
  exact eq_augmentation_weightLevi_of_isNormal_of_smoothUnipotent k w I
    hI.isNormal hI.smoothUnipotent

end

end TauCeti.GeneralLinear
