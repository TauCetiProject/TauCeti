/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# Base change of tori

Tori remain tori under arbitrary field extensions: embed an algebraic closure of the smaller
field into one of the larger field, extend the splitting along that embedding with
`TauCeti.splitTorusCommHopfAlgProperty.baseChange`, and transport it through the two
base-change towers.

This is the scalar-extension step used to descend maximality of tori along an arbitrary field
extension in `TauCeti.Algebra.AlgebraicGroup.Torus.Maximal`.

## Main declarations

* `TauCeti.torusCommHopfAlgProperty.baseChange`: field extension preserves tori.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- A torus remains a torus after an arbitrary field extension. -/
theorem torusCommHopfAlgProperty.baseChange
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} (hH : torusCommHopfAlgProperty k H) :
    torusCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  let f : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := f.toAlgebra
  have : IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  -- The torus predicate supplies a splitting over the algebraic closure of the base field.
  rw [torusCommHopfAlgProperty_iff, ← splitTorusCommHopfAlgProperty_iff] at hH ⊢
  exact (splitTorusCommHopfAlgProperty (AlgebraicClosure K)).prop_of_iso
    (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := AlgebraicClosure k) k
        (AlgebraicClosure K) H ≪≫
      (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := K) k (AlgebraicClosure K) H).symm)
    (hH.baseChange (AlgebraicClosure K))

end TauCeti
