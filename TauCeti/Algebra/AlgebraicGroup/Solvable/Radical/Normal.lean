/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.RationalPoint
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Solvable radicals of normal closed subgroups

Over an algebraically closed field, the solvable radical of a normal closed subgroup of a
reduced finite-type affine group is normal in the ambient group. Conjugation restricts to an
automorphism of the normal subgroup and preserves its solvable radical. Since the radical is
smooth, rational-point stability proves scheme-theoretic normality.

Consequently this radical is contained in the ambient solvable radical. In particular, a normal
closed subgroup of a group with trivial solvable radical again has trivial solvable radical.
The normal subgroup itself need not be smooth or connected; those hypotheses are needed only
when recognizing it as semisimple.

The automorphism-invariance input is
`FiniteTypeCommHopfAlgCat.comapOfSurjective_solvableRadicalDefiningIdeal`.

## References

* A. Borel, *Linear Algebraic Groups*, §11.21.
* J. S. Milne, *Algebraic Groups* (2017), §§6.45–6.46 and 21.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
variable {I : HopfIdeal k H}

/-- The solvable radical of a normal closed subgroup is a connected normal smooth solvable
closed subgroup of the ambient reduced affine group. The subgroup itself may be nonsmooth
or disconnected. -/
theorem isSolvableRadicalCandidate_comap_solvableRadicalDefiningIdeal_quotient
    (hI : I.IsNormal) :
    HopfIdeal.IsSolvableRadicalCandidate H
      ((solvableRadicalDefiningIdeal (quotient H I)).comapOfSurjective
        (CommHopfAlgCat.mkQuotient H.obj I).hom
        (CommHopfAlgCat.mkQuotient_surjective H.obj I)) := by
  let Q := quotient H I
  let J := solvableRadicalDefiningIdeal Q
  let P := J.comapOfSurjective (CommHopfAlgCat.mkQuotient H.obj I).hom
    (CommHopfAlgCat.mkQuotient_surjective H.obj I)
  let e : (quotient H P).obj ≅ (solvableRadical Q).obj :=
    CommHopfAlgCat.quotientIsoOfSurjective (CommHopfAlgCat.mkQuotient H.obj I)
      (CommHopfAlgCat.mkQuotient_surjective H.obj I) J
  have hsm : Algebra.Smooth k (quotient H P) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e.symm
        ((smoothCommHopfAlgProperty_iff _).mpr (smooth_solvableRadical Q))
  let _ := hsm
  let _ : IsReduced (H ⧸ P.toIdeal) := isReduced_of_smooth k (quotient H P)
  refine .mk (hI.comapOfSurjective_of_forall_iso J ?_) ?_ hsm ?_
  · intro a
    exact comapOfSurjective_solvableRadicalDefiningIdeal
      (ObjectProperty.isoMk _ a : Q ≅ Q)
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallyConnected_solvableRadical Q)
  · exact (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm
      (geometricallySolvable_solvableRadical Q)

/-- The solvable radical of a normal closed subgroup is contained in the ambient solvable
radical. The inclusion of represented subgroups reverses the inequality of Hopf ideals. -/
theorem solvableRadicalDefiningIdeal_le_comap_solvableRadicalDefiningIdeal_quotient
    (hI : I.IsNormal) :
    solvableRadicalDefiningIdeal H ≤
      (solvableRadicalDefiningIdeal (quotient H I)).comapOfSurjective
        (CommHopfAlgCat.mkQuotient H.obj I).hom
        (CommHopfAlgCat.mkQuotient_surjective H.obj I) :=
  solvableRadicalDefiningIdeal_le H _
    (isSolvableRadicalCandidate_comap_solvableRadicalDefiningIdeal_quotient H hI)

/-- If the ambient solvable radical is trivial, then so is the solvable radical of every
normal closed subgroup, without a smoothness or connectedness assumption on that subgroup. -/
theorem solvableRadicalDefiningIdeal_quotient_eq_augmentation_of_isNormal
    (hI : I.IsNormal)
    (hH : solvableRadicalDefiningIdeal H = HopfIdeal.augmentation k H) :
    solvableRadicalDefiningIdeal (quotient H I) =
      HopfIdeal.augmentation k (quotient H I) := by
  apply (HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff
    (CommHopfAlgCat.mkQuotient H.obj I).hom
    (CommHopfAlgCat.mkQuotient_surjective H.obj I)).mp
  rw [HopfIdeal.comapOfSurjective_augmentation]
  apply le_antisymm (HopfIdeal.le_augmentation k H _)
  rw [← hH]
  exact solvableRadicalDefiningIdeal_le_comap_solvableRadicalDefiningIdeal_quotient H hI

end

end TauCeti.FiniteTypeCommHopfAlgCat
