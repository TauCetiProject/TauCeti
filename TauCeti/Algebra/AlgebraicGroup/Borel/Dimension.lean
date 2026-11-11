/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugacy.Containment
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import Mathlib.RingTheory.KrullDimension.Basic
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.RingTheory.KrullDimension.Quotient

/-!
# The dimension bound for solvable closed subgroups

Over an algebraically closed field, a closed subgroup whose rational points form a solvable
group has dimension at most that of any prescribed Borel subgroup. Neither the ambient group
nor the solvable subgroup needs to be reduced or connected.

Reduction preserves Krull dimension. The reduced subgroup is smooth, and its identity
component has the same dimension and is a Borel candidate. Borel containment conjugates this
candidate into the prescribed Borel, and conjugation preserves dimension through its quotient
Hopf-algebra isomorphism.

## Main declarations

* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.ringKrullDim_quotient_le`: the dimension bound for
  arbitrary closed subgroups with solvable rational points.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §21.3.
* J. S. Milne, *Algebraic Groups* (2017), §17.a.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Every closed subgroup with solvable rational points has dimension at most that of a
Borel subgroup. The closed subgroup may be nonreduced and disconnected. -/
theorem IsBorelOverAlgClosed.ringKrullDim_quotient_le {B : HopfIdeal k H}
    (hB : IsBorelOverAlgClosed k H B) (D : HopfIdeal k H)
    [Group.IsSolvable (WithConv ((H ⧸ D.toIdeal) →ₐ[k] k))] :
    ringKrullDim (H ⧸ D.toIdeal) ≤ ringKrullDim (H ⧸ B.toIdeal) := by
  let Q := FiniteTypeCommHopfAlgCat.quotient H D
  have hQ : geometricallySolvablePointsCommHopfAlgProperty k Q.obj :=
    geometricallySolvablePointsCommHopfAlgProperty_of_isAlgClosed Q.obj
  let R := reduction k Q
  let _ : Algebra.Smooth k (Q ⧸ R.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k
        (FiniteTypeCommHopfAlgCat.quotient Q R).obj)
  let _ := R.smooth_identityComponent
  have hC : IsBorelCandidate k Q R.identityComponent :=
    IsBorelCandidate.mk ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
      R.geometricallyConnected_identityComponent
      (geometricallySolvablePointsCommHopfAlgProperty_quotient k Q.obj
        R.identityComponent hQ)
  let f := FiniteTypeCommHopfAlgCat.mkQuotient H D
  have hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f) :=
    CommHopfAlgCat.mkQuotient_surjective H.obj D
  let P := R.identityComponent.comapOfSurjective
    (FiniteTypeCommHopfAlgCat.toBialgHom f) hf
  have hP : IsBorelCandidate k H P :=
    (isBorelCandidate_comapOfSurjective_iff f hf R.identityComponent).mpr hC
  have hdim : ringKrullDim (H ⧸ P.toIdeal) = ringKrullDim (H ⧸ D.toIdeal) := by
    let e := CommHopfAlgCat.ofIso (f.hom.quotientIsoOfSurjective hf R.identityComponent)
    calc
      ringKrullDim (H ⧸ P.toIdeal) = ringKrullDim (Q ⧸ R.identityComponent.toIdeal) :=
        ringKrullDim_eq_of_ringEquiv e.toAlgEquiv.toRingEquiv
      _ = ringKrullDim (Q ⧸ R.toIdeal) :=
        R.ringKrullDim_quotient_identityComponent_of_smooth
      _ = ringKrullDim Q := by rw [reduction_toIdeal, ringKrullDim_quotient_nilradical]
  obtain ⟨g, hg⟩ := hB.exists_le_conjugate_of_isBorelCandidate hP
  calc
    ringKrullDim (H ⧸ D.toIdeal) = ringKrullDim (H ⧸ P.toIdeal) := hdim.symm
    _ = ringKrullDim (H ⧸ (P.conjugate g).toIdeal) :=
      (ringKrullDim_eq_of_ringEquiv
        (P.quotientConjugationEquiv _ g rfl).toAlgEquiv.toRingEquiv).symm
    _ ≤ ringKrullDim (H ⧸ B.toIdeal) :=
      ringKrullDim_le_of_surjective
        (CommHopfAlgCat.quotientMapOfLe H.obj hg).hom.toAlgHom.toRingHom
        (CommHopfAlgCat.quotientMapOfLe_surjective H.obj hg)

end TauCeti.HopfIdeal
