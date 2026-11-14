/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Monoidal.Grp.Subobject

/-!
# Descent of subgroup structures

A subobject of a group object over `S` is a subgroup if its base change along a universally
strong epimorphism `S' ⟶ S` is a subgroup. Factorization through the subobject descends,
so the identity, multiplication and inverse restrict to it. Their axioms follow by cancellation
of the inclusion, using `TauCeti.grpObjOfMono`.

For group schemes this applies to an fpqc cover and to closed subschemes which have already
been descended. No compatibility conditions on the local group law have to be assumed:
the inclusion in the ambient group scheme determines it uniquely.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
* The Stacks Project, Tag 02W0 (fpqc descent of morphisms of schemes).
-/

public section

open CategoryTheory Limits MonoidalCategory
open scoped MonObj Obj

namespace TauCeti

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)
  [∀ {Z : C} (g : Z ⟶ S), StrongEpi (pullback.fst g p)]
  {H G : Over S} [GrpObj G]

/-- A subobject of a group object over `S` admits a compatible group structure if and only if
its base change along a universally strong epimorphism does. -/
theorem exists_grpObj_isMonHom_pullback_iff (i : H ⟶ G) [Mono i] :
    (∃ h : GrpObj ((Over.pullback p).obj H),
      letI := h; IsMonHom ((Over.pullback p).map i)) ↔
      ∃ h : GrpObj H, letI := h; IsMonHom i := by
  let F := Over.pullback p
  constructor
  · rintro ⟨h, hi⟩
    let := h
    let := hi
    obtain ⟨e, he⟩ := (Over.exists_factor_thru_pullback_iff p i η[G]).1
      ⟨Functor.OplaxMonoidal.η F ≫ η[F.obj H], by simp [F]⟩
    obtain ⟨m, hm⟩ := (Over.exists_factor_thru_pullback_iff p i ((i ⊗ₘ i) ≫ μ[G])).1
      ⟨Functor.OplaxMonoidal.δ F H H ≫ μ[F.obj H], by simp [F]⟩
    obtain ⟨j, hj⟩ := (Over.exists_factor_thru_pullback_iff p i (i ≫ ι[G])).1
      ⟨ι[F.obj H], by simp⟩
    exact ⟨grpObjOfMono i e m j he hm hj, isMonHom_grpObjOfMono i e m j he hm hj⟩
  · rintro ⟨h, hi⟩
    let := h
    let := hi
    exact ⟨F.grpObjObj, inferInstance⟩

end TauCeti
