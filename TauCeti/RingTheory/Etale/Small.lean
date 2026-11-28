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

Concretely, `TauCeti.FiniteEtaleSkeleton R` is the small type of quotients `R[X_1, …, X_n] ⧸ I` of
polynomial rings in finitely many variables that are finite étale over `R`, the finite étale
members of Mathlib's small family `FGAlgCatSkeleton R` of finitely generated `R`-algebras. Every
finite étale `R`-algebra, in any universe, is isomorphic to one of them
(`TauCeti.FiniteEtaleSkeleton.exists_algEquiv`).
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

/-- The quotients `R[X_1, …, X_n] ⧸ I` of polynomial rings in finitely many variables that are
finite étale over `R`: the members of Mathlib's small family `FGAlgCatSkeleton R` of finitely
generated `R`-algebras whose realisation is finite étale. Different presentations of isomorphic
algebras are different elements, so the family may contain repetitions up to isomorphism. -/
structure FiniteEtaleSkeleton (R : Type u) [CommRing R] : Type u where
  /-- The presentation `R[X_1, …, X_n] ⧸ I`. -/
  toFGAlgCatSkeleton : FGAlgCatSkeleton R
  /-- The presented algebra is étale. -/
  etale : Algebra.Etale R toFGAlgCatSkeleton.eval.obj
  /-- The presented algebra is finite. -/
  finite : Module.Finite R toFGAlgCatSkeleton.eval.obj

namespace FiniteEtaleSkeleton

attribute [instance] etale finite

/-- Every finite étale `R`-algebra is isomorphic to one presented by
`TauCeti.FiniteEtaleSkeleton R`: it is of finite type, hence a quotient of a polynomial ring in
finitely many variables. -/
theorem exists_algEquiv (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] :
    ∃ P : FiniteEtaleSkeleton R, Nonempty (S ≃ₐ[R] P.toFGAlgCatSkeleton.eval.obj) := by
  obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R S
  exact ⟨⟨P, .of_equiv e, .equiv e.toLinearEquiv⟩, ⟨e⟩⟩

end FiniteEtaleSkeleton

end TauCeti
