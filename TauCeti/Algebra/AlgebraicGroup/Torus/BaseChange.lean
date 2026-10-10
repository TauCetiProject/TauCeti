/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange

/-!
# Base change of tori

Split tori remain split after extending scalars between commutative rings. Tori remain tori
under arbitrary field extensions: embed an algebraic closure of the smaller field into one
of the larger field and transport the splitting through the two base-change towers.

This provides the scalar-extension step for descent of maximal tori in Layer 7, "Borel
subgroups, maximal tori", of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.splitTorusCommHopfAlgProperty.baseChange`: scalar extension preserves split tori.
* `TauCeti.torusCommHopfAlgProperty.baseChange`: field extension preserves tori.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- A split torus remains split after extending scalars. -/
theorem splitTorusCommHopfAlgProperty.baseChange
    {k : Type u} [CommRing k] (K : Type u) [CommRing K] [Algebra k K]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} (hH : splitTorusCommHopfAlgProperty k H) :
    splitTorusCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  rw [splitTorusCommHopfAlgProperty_iff] at hH ⊢
  obtain ⟨n, ⟨i⟩⟩ := hH
  exact ⟨n, ⟨(DiagonalizableGroup.baseChangeCoordinateRingIso k K
    (SplitTorus.characterGroup (ULift.{u} (Fin n)))).symm ≪≫
      (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := K)).mapIso i⟩⟩

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
    (ObjectProperty.isoMk _
      ((CommHopfAlgCat.baseChangeTowerIso k (AlgebraicClosure K)
        (E := AlgebraicClosure k) H.obj) ≪≫
        (CommHopfAlgCat.baseChangeTowerIso k (AlgebraicClosure K) (E := K) H.obj).symm))
    (hH.baseChange (AlgebraicClosure K))

end TauCeti
