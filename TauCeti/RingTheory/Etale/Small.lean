/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.RingTheory.Etale.Finite

/-!
# Essential smallness of finite étale algebras

Finite étale algebras over a ring `R : Type u` are of finite type, so they form a `u`-essentially
small category, as a full subcategory of the finitely generated `R`-algebras
(`TauCeti.essentiallySmall_commAlgCatFiniteEtale`).
-/

public section

open CategoryTheory

universe v u

namespace TauCeti

/-- Finite étale algebras over a ring `R : Type u` form a `u`-essentially small category: they
are of finite type, and finitely generated `R`-algebras form one. -/
instance essentiallySmall_commAlgCatFiniteEtale (R : Type u) [CommRing R] :
    EssentiallySmall.{u} (CommAlgCat.FiniteEtale.{v} R) :=
  essentiallySmall_of_fully_faithful
    (ObjectProperty.ιOfLE (P' := fun A : CommAlgCat.{v} R ↦ Algebra.FiniteType R A)
      fun A (hA : CommAlgCat.finiteEtale R A) ↦ by
        have := hA.1
        infer_instance)

end TauCeti
