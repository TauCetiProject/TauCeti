/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.CommMon
public import TauCeti.CategoryTheory.Monoidal.Internal.Module
public import TauCeti.RingTheory.Almost.Monoidal

/-!
# Almost algebras over a basic setup

Let `S = (V, m)` be a basic setup. An *almost `V`-algebra* is a commutative unital monoid object
in the symmetric monoidal category `TauCeti.Almost.Module S` of almost `V`-modules, with monoid
morphisms (Gabber–Ramero §2.2). Almost commutative algebra, such as almost finite
étale algebras and the almost purity theorem for perfectoid rings, takes place in this category.

Almostification `M ↦ M^a` is braided monoidal, so it sends commutative monoid objects of
`ModuleCat V`, that is commutative `V`-algebras, to almost algebras. This gives the functor
`R ↦ R^a` from commutative `V`-algebras to almost `V`-algebras, whose underlying almost module is
the almostification of the underlying `V`-module of `R`. It inverts exactly the algebra maps that
are almost isomorphisms, and `R^a` is zero exactly when `m` maps to zero in `R`; in particular
`(V ⧸ m)^a = 0`. For the classical setup `(V, V)` it is full and faithful.

## Main definitions

* `TauCeti.Almost.Algebra`: the category `CommMon (Almost.Module S)` of almost `V`-algebras.
* `TauCeti.Almost.Algebra.toAlmost`: the almostification functor `R ↦ R^a` from commutative
  `V`-algebras to almost `V`-algebras.

## Main results

* `TauCeti.Almost.Algebra.toAlmost_obj_X`: the underlying almost module of `R^a` is the
  almostification of the underlying `V`-module of `R`.
* `TauCeti.Almost.Algebra.isIso_toAlmost_map_iff`: `f^a` is an isomorphism of almost algebras
  iff `f` is an almost isomorphism of `V`-modules.
* `TauCeti.Almost.Algebra.isZero_toAlmost_obj_X_iff`: `R^a` is zero iff `m` is contained in the
  kernel of `V → R`.
* `TauCeti.Almost.Algebra.full_toAlmost_classical`,
  `TauCeti.Almost.Algebra.faithful_toAlmost_classical`: for the classical setup, almostification
  of algebras is full and faithful.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4.
-/

public section

universe u

open CategoryTheory Limits
open scoped MonObj

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- The category of **almost `V`-algebras** for a basic setup `S = (V, m)`: commutative monoid
objects in the symmetric monoidal category of almost `V`-modules (Gabber–Ramero §2.2; Scholze,
*Perfectoid spaces*, §4). -/
abbrev Algebra : Type (u + 1) :=
  CommMon (Module S)

namespace Algebra

/-- The **almostification** functor `R ↦ R^a` from commutative `V`-algebras to almost
`V`-algebras: a commutative `V`-algebra is a commutative monoid object in `ModuleCat V`, and the
braided monoidal functor `Almost.Module.toAlmost S` sends it to a commutative monoid object in
almost modules. -/
@[expose]
noncomputable def toAlmost : CommAlgCat.{u} V ⥤ Algebra S :=
  ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙ (Module.toAlmost S).mapCommMon

/-- The underlying almost module of `R^a` is the almostification of the underlying `V`-module of
`R`. -/
@[simp]
theorem toAlmost_obj_X (R : CommAlgCat.{u} V) :
    ((toAlmost S).obj R).X = (Module.toAlmost S).obj (ModuleCat.of V R) :=
  (rfl)

/-- The underlying morphism of almost modules of `f^a` is the almostification of the underlying
linear map of `f`. -/
@[simp]
theorem toAlmost_map_hom_hom {R R' : CommAlgCat.{u} V} (f : R ⟶ R') :
    ((toAlmost S).map f).hom.hom = (Module.toAlmost S).map (ModuleCat.ofHom f.hom.toLinearMap) :=
  (rfl)

/-- The unit of `R^a` is the almostification of the unit `V → R` of `R`. -/
@[simp]
theorem toAlmost_obj_one (R : CommAlgCat.{u} V) :
    η[((toAlmost S).obj R).X] = Functor.LaxMonoidal.ε (Module.toAlmost S) ≫
      (Module.toAlmost S).map (ModuleCat.ofHom (Algebra.linearMap V R)) :=
  rfl

/-- The multiplication of `R^a` is the almostification of the multiplication `R ⊗[V] R → R`
of `R`. -/
@[simp]
theorem toAlmost_obj_mul (R : CommAlgCat.{u} V) :
    μ[((toAlmost S).obj R).X] =
      Functor.LaxMonoidal.μ (Module.toAlmost S) (ModuleCat.of V R) (ModuleCat.of V R) ≫
        (Module.toAlmost S).map (ModuleCat.ofHom (LinearMap.mul' V R)) :=
  rfl

/-- **`f^a` is an isomorphism iff `f` is an almost isomorphism.** An algebra map becomes invertible
after almostification exactly when its kernel and cokernel are killed by `m`. -/
@[simp]
theorem isIso_toAlmost_map_iff {R R' : CommAlgCat.{u} V} (f : R ⟶ R') :
    IsIso ((toAlmost S).map f) ↔ S.IsAlmostIso f.hom.toLinearMap := by
  rw [← ModuleCat.hom_ofHom f.hom.toLinearMap, ← Module.isIso_toAlmost_map_iff,
    ← toAlmost_map_hom_hom]
  -- The underlying morphism `g.hom.hom` of a homomorphism `g` of commutative monoid objects is
  -- `(CommMon.forget _).map g` by definition.
  exact (isIso_iff_of_reflects_iso _ (CommMon.forget (Module S))).symm

/-- **`R^a` is zero iff `m` maps to zero in `R`.** -/
theorem isZero_toAlmost_obj_X_iff (R : CommAlgCat.{u} V) :
    IsZero ((toAlmost S).obj R).X ↔ S.ideal ≤ RingHom.ker (algebraMap V R) := by
  rw [toAlmost_obj_X, Module.isZero_toAlmost_obj_iff, BasicSetup.isAlmostZero_iff]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε x ↦ ?_⟩
  · simpa [Algebra.smul_def] using h ε hε 1
  · simp [Algebra.smul_def, RingHom.mem_ker.mp (h hε)]

/-- For the classical setup `(V, V)`, almostification of algebras is full. -/
instance full_toAlmost_classical : (toAlmost (BasicSetup.classical V)).Full :=
  inferInstanceAs (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
    (Module.toAlmost (BasicSetup.classical V)).mapCommMon).Full

/-- For the classical setup `(V, V)`, almostification of algebras is faithful. -/
instance faithful_toAlmost_classical : (toAlmost (BasicSetup.classical V)).Faithful :=
  inferInstanceAs (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
    (Module.toAlmost (BasicSetup.classical V)).mapCommMon).Faithful

end Algebra

end TauCeti.Almost
