/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Rational trivializations of line bundles

A line bundle on an integral scheme is trivial on a dense open subset.  Equivalently, it has a
basis near the generic point.  This is the first step in associating a divisor to an arbitrary
line bundle: after fixing such a rational basis, its transition functions at codimension-one
points give the coefficients of the divisor.

## Main declaration

* `SheafOfModules.IsInvertible.exists_dense_open_trivialization` produces a dense open subset
  containing the generic point on which an invertible sheaf is free of rank one.

No formalization is vendored.  The proof selects the member containing the generic point from the
local trivialization cover supplied by
`SheafOfModules.LocalTrivializations.ofIsInvertible`.
-/

public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

namespace LocalTrivializations

variable {X : Scheme.{u}} {M : X.Modules}

/-- A member of a local trivialization atlas, expressed as an isomorphism of module sheaves on
the corresponding open subscheme. -/
def schemeIso (t : TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} M) (i : t.I) :
    _root_.SheafOfModules.unit (t.X i : Scheme).ringCatSheaf ≅
      M.restrict (AlgebraicGeometry.Scheme.Opens.ι (t.X i)) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv (t.X i)).functor.mapIso
      ((TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over (t.X i))).symm ≪≫
        t.iso i) ≪≫
    (AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (t.X i)).app M

end LocalTrivializations

/-- An invertible sheaf on an irreducible scheme is free of rank one on a dense open subset
containing the generic point.

This is the rational trivialization used to associate a divisor to a line bundle: a local basis
on an open neighbourhood of the generic point is a basis of the generic fibre. -/
theorem exists_dense_open_trivialization {X : Scheme.{u}} [IrreducibleSpace X]
    (M : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ Dense (U : Set X) ∧
      Nonempty
        (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) := by
  let t := SheafOfModules.LocalTrivializations.ofIsInvertible M
  have hcover : ⨆ i, t.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop
  have hgeneric : genericPoint X ∈ ⨆ i, t.X i := by
    rw [hcover]
    exact Opens.mem_top _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hgeneric
  refine ⟨t.X i, hi, (t.X i).isOpen.dense ⟨genericPoint X, hi⟩, ⟨t.iso i⟩⟩

/-- An invertible sheaf on an irreducible scheme becomes the structure sheaf on a dense open
subscheme containing the generic point. -/
theorem exists_dense_open_restrict_iso_unit {X : Scheme.{u}} [IrreducibleSpace X]
    (M : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ Dense (U : Set X) ∧
      Nonempty (M.restrict (AlgebraicGeometry.Scheme.Opens.ι U) ≅
        _root_.SheafOfModules.unit (U : Scheme).ringCatSheaf) := by
  let t := SheafOfModules.LocalTrivializations.ofIsInvertible M
  have hcover : ⨆ i, t.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop
  have hgeneric : genericPoint X ∈ ⨆ i, t.X i := by
    rw [hcover]
    exact Opens.mem_top _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hgeneric
  exact ⟨t.X i, hi, (t.X i).isOpen.dense ⟨genericPoint X, hi⟩, ⟨(t.schemeIso i).symm⟩⟩

end SheafOfModules

end

end TauCeti
