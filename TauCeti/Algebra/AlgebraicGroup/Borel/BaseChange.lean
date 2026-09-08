/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Solvable.BaseChange

/-!
# Borel subgroups over an arbitrary field are Borel candidates

Over an arbitrary field `k`, a Borel subgroup is defined by a condition on its base change to an
algebraic closure: the base-changed ideal is a maximal Borel candidate there. The three geometric
conditions defining a Borel candidate — smoothness, geometric connectedness and geometric
solvability of the coordinate quotient — are therefore only visible after base change. This file
descends them back to the ground field, so that a Borel subgroup over `k` is in particular a Borel
candidate over `k`.

Each of the three conditions descends by its own mechanism. Smoothness descends along the
faithfully flat extension `k → AlgebraicClosure k`, using Mathlib's
`Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`. Geometric connectedness and geometric
solvability are stated in terms of geometric points, and are reflected by an arbitrary field
extension. In all three cases the coordinate quotient of the base-changed ideal is identified with
the base change of the coordinate quotient by `CommHopfAlgCat.quotientBaseChangeIso`.

## Main declarations

* `TauCeti.HopfIdeal.IsBorel.isBorelCandidate`: a Borel subgroup over an arbitrary field is a
  Borel candidate over that field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§17.a and 1.h.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.21.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsBorel

variable {k : Type u} [Field k] {H : CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
variable {I : HopfIdeal k H}

/-- A Borel subgroup over an arbitrary field is a Borel candidate over that field: its quotient
is smooth, geometrically connected, and geometrically solvable. -/
theorem isBorelCandidate (hI : IsBorel k H I) :
    IsBorelCandidate k ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I := by
  let H' : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := AlgebraicClosure k) I
  have hIK : IsBorelCandidate (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H')
      (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I) :=
    ((isBorelOverAlgClosed_iff _ _ _).mp
      ((isBorel_iff_isBorelOverAlgClosed_baseChange k H I).mp hI)).2.1
  refine IsBorelCandidate.mk ?_ ?_ ?_
  · rw [smoothCommHopfAlgProperty_iff]
    -- Unwrap the finite-type quotient for Mathlib's faithfully-flat smoothness descent lemma.
    change Algebra.Smooth k (CommHopfAlgCat.quotient H I)
    have hsmooth :=
      (smoothCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso qIso hIK.smooth
    let _ : Algebra.Smooth (AlgebraicClosure k)
        (CommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          (CommHopfAlgCat.quotient H I)) :=
      (smoothCommHopfAlgProperty_iff _).mp hsmooth
    exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (AlgebraicClosure k)
  · apply geometricallyConnectedCommHopfAlgProperty.of_baseChange k (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient H' I).obj
    exact (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      qIso hIK.geometricallyConnected
  · apply geometricallySolvablePointsCommHopfAlgProperty.of_baseChange
      (K := AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient H' I).obj
    exact (geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      qIso hIK.geometricallySolvable

end HopfIdeal.IsBorel

end

end TauCeti
