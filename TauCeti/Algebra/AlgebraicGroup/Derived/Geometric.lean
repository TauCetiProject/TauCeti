/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Connected
public import TauCeti.Algebra.AlgebraicGroup.Derived.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Derived.FreeBaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange
import Mathlib.Algebra.Field.ULift

/-!
# Geometric properties of the derived subgroup

The derived closed subgroup of a smooth finite-type affine group over any field is smooth.
The derived subgroup of a geometrically connected finite-type affine group is geometrically
connected, without a smoothness or reducedness assumption. In particular the derived subgroup
of a smooth geometrically connected group is again smooth and geometrically connected, even
over an imperfect field.

These results supply the geometric hypotheses needed to apply normal-subgroup theorems to the
derived subgroup. Formation of the derived subgroup commutes with field extension by
`TauCeti.CommHopfAlgCat.baseChangeHopfIdeal_derivedDefiningIdeal`. Thus the algebraically closed
results of `Derived.Connected` and `Derived.Smooth` descend to the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
* A. Borel, *Linear Algebraic Groups*, §2, derived subgroups.
-/

public section

namespace TauCeti

universe u v

open CategoryTheory

variable {k : Type u} [Field k] {H : CommHopfAlgCat.{v} k} [Algebra.FiniteType k H]

/-- The derived subgroup of a geometrically connected finite-type affine group is geometrically
connected. The group need not be smooth or reduced, and the field need not be perfect. -/
theorem geometricallyConnectedCommHopfAlgProperty.derived
    (hH : geometricallyConnectedCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H)) := by
  let K := AlgebraicClosure k
  let G := CommHopfAlgCat.baseChange (K := K) H
  let e := CommHopfAlgCat.quotientBaseChangeIso (K := K)
    (CommHopfAlgCat.derivedDefiningIdeal H)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_derivedDefiningIdeal] at e
  have hG := geometricallyConnectedCommHopfAlgProperty.baseChange k K H hH
  let _ : ConnectedSpace (PrimeSpectrum G) := hG.connectedSpace K G
  apply geometricallyConnectedCommHopfAlgProperty.of_baseChange k K
  exact (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso e
    (CommHopfAlgCat.geometricallyConnectedCommHopfAlgProperty_derived G)

/-- The derived subgroup of a smooth finite-type affine group is smooth over the ground field.
Connectedness, perfectness, and restrictions on the characteristic are unnecessary. -/
theorem smoothCommHopfAlgProperty.derived (hH : smoothCommHopfAlgProperty k H) :
    smoothCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H)) := by
  -- The geometric-reducedness descent API tests extensions in the joint universe.
  let K := AlgebraicClosure (ULift.{v} k)
  let _ : Algebra k K := Algebra.compHom K (algebraMap k (ULift.{v} k))
  let G := CommHopfAlgCat.baseChange (K := K) H
  let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff H).mp hH
  let _ : Algebra.Smooth K G := inferInstance
  let _ : IsReduced G := isReduced_of_smooth K G
  let e := CommHopfAlgCat.quotientBaseChangeIso (K := K)
    (CommHopfAlgCat.derivedDefiningIdeal H)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_derivedDefiningIdeal] at e
  have hderived :=
    CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_derivedDefiningIdeal (k := K) G
  have hD := (smoothCommHopfAlgProperty K).prop_of_iso e hderived
  apply smoothCommHopfAlgProperty_of_geometricallyReduced
  apply geometricallyReducedCommHopfAlgProperty.of_baseChange K
  exact (smoothCommHopfAlgProperty_iff_geometricallyReduced K _).mp hD

end TauCeti
