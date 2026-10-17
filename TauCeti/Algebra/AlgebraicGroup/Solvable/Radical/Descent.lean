/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Solvable.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent
import Mathlib.RingTheory.Etale.Descent

/-!
# Descent of solvable-radical candidates

The conditions defining a solvable-radical candidate are reflected by field extension.
Consequently, the solvable radical commutes with extension along a surjective map of
fields. In particular, passing from an algebraically closed field to its algebraic closure
introduces no new radical candidates. This is the comparison needed to recognize
semisimplicity over an algebraically closed ground field.

The proof reuses `Module.Basis.coefficientHopfIdeal`, geometric connectedness and
solvability descent, and `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 2 and 19.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace HopfIdeal.IsSolvableRadicalCandidate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The solvable-radical candidate conditions descend under field extension. -/
theorem of_baseChange
    (hI : IsSolvableRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I)) :
    IsSolvableRadicalCandidate H I := by
  let e := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  let Q := (FiniteTypeCommHopfAlgCat.quotient H I).obj
  have hconn := (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso e
    hI.geometricallyConnected
  have hsolv := (geometricallySolvablePointsCommHopfAlgProperty K).prop_of_iso e
    hI.geometricallySolvable
  have hsmooth := (smoothCommHopfAlgProperty K).prop_of_iso e
    ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth)
  refine .mk (CommHopfAlgCat.isNormal_of_baseChangeHopfIdeal hI.isNormal)
    (geometricallyConnectedCommHopfAlgProperty.of_baseChange k K Q hconn) ?_
    (geometricallySolvablePointsCommHopfAlgProperty.of_baseChange Q hsolv)
  let _ : Algebra.Smooth K (CommHopfAlgCat.baseChange (K := K) Q) :=
    (smoothCommHopfAlgProperty_iff _).mp hsmooth
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K

/-- Being a solvable-radical candidate is invariant under field extension. -/
@[simp]
theorem baseChange_iff :
    IsSolvableRadicalCandidate
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) ↔
      IsSolvableRadicalCandidate H I :=
  ⟨of_baseChange, baseChange⟩

end HopfIdeal.IsSolvableRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The solvable radical commutes with scalar extension along a surjective map of fields.
This applies, in particular, to algebraic extensions of algebraically closed fields. -/
theorem baseChangeHopfIdeal_solvableRadicalDefiningIdeal_of_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : Function.Surjective (algebraMap k K)) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (solvableRadicalDefiningIdeal H) =
      solvableRadicalDefiningIdeal (baseChange (K := K) H) := by
  apply le_antisymm _ (solvableRadicalDefiningIdeal_baseChange_le H)
  obtain ⟨I, hI⟩ := CommHopfAlgCat.baseChangeHopfIdeal_surjective (H := H.obj) h
    (solvableRadicalDefiningIdeal (baseChange (K := K) H))
  rw [← hI]
  apply CommHopfAlgCat.baseChangeHopfIdeal_mono
  exact solvableRadicalDefiningIdeal_le H I <|
    HopfIdeal.IsSolvableRadicalCandidate.of_baseChange <|
      hI.symm ▸ isSolvableRadicalCandidate_solvableRadicalDefiningIdeal
        (baseChange (K := K) H)

end FiniteTypeCommHopfAlgCat

end TauCeti
