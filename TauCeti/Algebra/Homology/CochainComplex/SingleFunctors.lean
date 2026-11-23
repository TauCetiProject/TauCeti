/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Additive functors and the single functors of cochain complexes

For an additive functor `F : C ⥤ D`, Mathlib's `HomologicalComplex.singleMapHomologicalComplex`
identifies the termwise image of the complex `X[a]` concentrated in degree `a` with `(F X)[a]`.
This file shows that this comparison is compatible with the identifications
`(CochainComplex.singleFunctors C).shiftIso n a a' : X[a'][n] ≅ X[a]` for `n + a = a'`, and with
the commutation of `F` with the shift.

## Main results

* `CochainComplex.singleMapHomologicalComplex_inv_app_comp_shiftIso`: the comparison of single
  complexes commutes with the shift identifications.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CochainComplex

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]

/-- **The comparison of single complexes commutes with shifts**: for `n + a = a'`, comparing
`F (X[a'])` with `(F X)[a']` and shifting by `n` agrees with identifying `X[a'][n] ≅ X[a]`,
comparing `F (X[a])` with `(F X)[a]`, and commuting `F` with the shift. -/
@[reassoc]
theorem singleMapHomologicalComplex_inv_app_comp_shiftIso (n a a' : ℤ) (h : n + a = a')
    (X : C) :
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) a).inv.app X ≫
        (F.mapHomologicalComplex (.up ℤ)).map
          (((singleFunctors C).shiftIso n a a' h).inv.app X) ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app _ =
      ((singleFunctors D).shiftIso n a a' h).inv.app (F.obj X) ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) a').inv.app X)⟦n⟧' := by
  apply HomologicalComplex.from_single_hom_ext
  have h' : a + n = a' := by omega
  simp [singleFunctors, HomologicalComplex.singleMapHomologicalComplex, eqToHom_map, h']

end CochainComplex
