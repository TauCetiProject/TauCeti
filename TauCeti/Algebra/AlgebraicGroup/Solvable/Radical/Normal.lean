/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.RationalPoint
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Connected.Finite

/-!
# Solvable radicals of normal closed subgroups

Over an algebraically closed field, the solvable radical of a normal closed subgroup of a
reduced finite-type affine group is normal in the ambient group.

Consequently this radical is contained in the ambient solvable radical. In particular, a normal
closed subgroup of a group with trivial solvable radical again has trivial solvable radical.
The normal subgroup itself need not be smooth or connected; those hypotheses are needed only
when recognizing it as semisimple.

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
    CommHopfAlgCat.Hom.quotientIsoOfSurjective (CommHopfAlgCat.mkQuotient H.obj I)
      (CommHopfAlgCat.mkQuotient_surjective H.obj I) J
  have hsm : Algebra.Smooth k (quotient H P) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e.symm
        ((smoothCommHopfAlgProperty_iff _).mpr (smooth_solvableRadical Q))
  let _ := hsm
  let _ : IsReduced (H ⧸ P.toIdeal) := isReduced_of_smooth k (quotient H P)
  -- Restricted conjugation preserves the radical by
  -- comapOfSurjective_solvableRadicalDefiningIdeal; rational-point stability gives normality.
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

/-- If the ambient solvable radical meets a normal closed subgroup in a finite subgroup scheme,
then that normal subgroup has trivial solvable radical. In coordinates, finiteness of the
intersection is finite-dimensionality of `H ⧸ (R(H) ⊔ I)`. The radical of the normal subgroup
lies in this intersection, and a finite connected smooth group is trivial. -/
theorem solvableRadicalDefiningIdeal_quotient_eq_augmentation_of_moduleFinite
    (hI : I.IsNormal) [Module.Finite k (H ⧸ (solvableRadicalDefiningIdeal H ⊔ I).toIdeal)] :
    solvableRadicalDefiningIdeal (quotient H I) =
      HopfIdeal.augmentation k (quotient H I) := by
  let q := CommHopfAlgCat.mkQuotient H.obj I
  have hq := CommHopfAlgCat.mkQuotient_surjective H.obj I
  let P := (solvableRadicalDefiningIdeal (quotient H I)).comapOfSurjective q.hom hq
  have hP := isSolvableRadicalCandidate_comap_solvableRadicalDefiningIdeal_quotient H hI
  -- The radical of the normal subgroup lies in the intersection of `R(H)` with that subgroup.
  have hle : solvableRadicalDefiningIdeal H ⊔ I ≤ P := by
    refine sup_le (solvableRadicalDefiningIdeal_le_comap_solvableRadicalDefiningIdeal_quotient
      H hI) fun x hx ↦ HopfIdeal.mem_comapOfSurjective.mpr ?_
    rw [(CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I x).mpr hx]
    exact zero_mem _
  let _ : Module.Finite k (quotient H P) := Module.Finite.of_surjective
    (CommHopfAlgCat.quotientMapOfLe H.obj hle).hom.toLinearMap
    (CommHopfAlgCat.quotientMapOfLe_surjective H.obj hle)
  let _ : Algebra.Smooth k (quotient H P) := hP.smooth
  let _ : IsReduced (quotient H P) := isReduced_of_smooth k _
  let _ : ConnectedSpace (PrimeSpectrum (quotient H P)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hP.geometricallyConnected
  -- A finite connected reduced group is trivial, so `P` is the augmentation ideal.
  have hbot := HopfIdeal.augmentation_eq_bot_of_moduleFinite (k := k) (H := quotient H P)
  have hPaug : P = HopfIdeal.augmentation k H := by
    apply le_antisymm (HopfIdeal.le_augmentation k H P)
    intro x hx
    have hx' : (CommHopfAlgCat.mkQuotient H.obj P).hom x ∈
        HopfIdeal.augmentation k (quotient H P) := by
      rw [HopfIdeal.mem_augmentation, CoalgHomClass.counit_comp_apply]
      exact (HopfIdeal.mem_augmentation k H).mp hx
    rw [hbot, HopfIdeal.mem_bot] at hx'
    exact (CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj P x).mp hx'
  rw [← HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff q.hom hq,
    HopfIdeal.comapOfSurjective_augmentation]
  exact hPaug

end

end TauCeti.FiniteTypeCommHopfAlgCat
