/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Transporting subcomplexes of complexes of modules

A subcomplex `S` of a homological complex `D` of modules is recorded degreewise by the range of
the components of `S.arrow`.  When `D` is only propositionally equal to another complex `C`, for
instance because `C` is a definition whose body is not exposed and `D` is its unfolding, `S` is
transported to a subcomplex of `C` by `Subobject.mapIsoToOrderIso (eqToIso _)`.  This file
records that the transported subcomplex has the same degreewise range, up to the transport of
elements along `eqToHom`.

## Main results

* `HomologicalComplex.mem_range_mapIsoToOrderIso_eqToIso_arrow_f_iff`: degreewise
  membership in a subcomplex transported along an equality of complexes.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}

/-- Transporting a subcomplex along `eqToIso` does not change its degreewise range, up to the
transport of elements. -/
theorem mem_range_mapIsoToOrderIso_eqToIso_arrow_f_iff.{v}
    {C D : HomologicalComplex (ModuleCat.{v} R) c} (e : C = D) (S : Subobject D) (n : ι)
    (x : C.X n) :
    x ∈ LinearMap.range ((Subobject.mapIsoToOrderIso (eqToIso e.symm) S).arrow.f n).hom ↔
      ((eqToHom e).f n).hom x ∈ LinearMap.range (S.arrow.f n).hom := by
  subst e
  rw [eqToIso_refl, show Subobject.mapIsoToOrderIso (Iso.refl C) S = S from Subobject.map_id S,
    eqToHom_refl, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

end HomologicalComplex
