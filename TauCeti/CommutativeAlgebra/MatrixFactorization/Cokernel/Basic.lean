/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Linear.FullSubcategory

/-!
# Cokernels of matrix factorizations

Taking the cokernel of the even-to-odd differential gives an additive functor to finitely
generated modules over the coefficient ring. The projection and its universal property retain
the ordinary categorical cokernel API. The functor uses Mathlib's
`CategoryTheory.Limits.coker` on the arrows supplied by the differential.

Composing scalar extension with this functor gives cokernels over a target ring with arbitrary
image potential. In particular, reduction modulo the potential gives the finite module used in
hypersurface comparisons; no vanishing condition is required for the cokernel construction.

This construction requires only commutative rings; it does not assert that its values are maximal
Cohen–Macaulay, which requires additional hypotheses. After reduction modulo the potential, the
cokernel descends to a functor from the homotopy category to a stable module category; that
descent is in `TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Stable`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Section 3.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S : Type u} [CommRing S] {w : S}

private theorem finite_cokernel (X : MatrixFactorization S w) :
    Module.Finite S (cokernel X.obj.d₀.hom : ModuleCat.{u} S) := by
  exact Module.Finite.of_surjective (cokernel.π X.obj.d₀.hom).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Take the cokernel of the even-to-odd differential. Its finite generation follows from
that of the odd component, without any condition on the potential. -/
def cokernelFunctor : MatrixFactorization S w ⥤ FGModuleCat.{u} S := by
  let G : MatrixFactorization S w ⥤ Arrow (ModuleCat.{u} S) :=
    { obj X := Arrow.mk X.obj.d₀.hom
      map g := Arrow.homMk g.hom.f₀.hom g.hom.f₁.hom
        (congrArg (fun k => k.hom) g.hom.comm₀)
      map_id X := by ext <;> simp
      map_comp g h := by ext <;> simp }
  exact (ModuleCat.isFG S).lift (G ⋙ coker (ModuleCat.{u} S)) finite_cokernel

/-- The underlying module of the finite cokernel functor is the categorical cokernel of the
even differential. This isomorphism permits use of Mathlib's cokernel API without
unfolding the functor. -/
def cokernelFunctorObjIso (X : MatrixFactorization S w) :
    (cokernelFunctor.obj X).obj ≅
      cokernel X.obj.d₀.hom := Iso.refl _

/-- The projection from the odd component onto the finite cokernel, as a map of modules. -/
def cokernelπ (X : MatrixFactorization S w) :
    X.obj.X₁.obj ⟶ (cokernelFunctor.obj X).obj :=
  cokernel.π _

/-- The object comparison carries the projection to the categorical cokernel projection. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_objIso_hom (X : MatrixFactorization S w) :
    cokernelπ X ≫ (cokernelFunctorObjIso X).hom =
      cokernel.π X.obj.d₀.hom := by
  exact Category.comp_id _

/-- The even differential vanishes after projection to the cokernel. -/
@[reassoc (attr := simp)]
theorem d₀_cokernelπ (X : MatrixFactorization S w) :
    X.obj.d₀.hom ≫ cokernelπ X = 0 :=
  cokernel.condition _

/-- The cokernel projection is natural with respect to closed even maps. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_naturality {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    cokernelπ X ≫ (cokernelFunctor.map g).hom =
      g.hom.f₁.hom ≫ cokernelπ Y := by
  exact cokernel.π_desc _ _ _

/-- The projection exhibits the underlying finite module as the categorical cokernel.
This supplies the full existence and uniqueness API for maps killing the even differential. -/
def isColimitCokernelπ (X : MatrixFactorization S w) :
    IsColimit (CokernelCofork.ofπ (cokernelπ X) (d₀_cokernelπ X)) :=
  cokernelIsCokernel _

instance cokernelπ_epi (X : MatrixFactorization S w) :
    Epi (cokernelπ X) :=
  epi_of_isColimit_cofork
    (c := CokernelCofork.ofπ (cokernelπ X) (d₀_cokernelπ X))
    (isColimitCokernelπ X)

/-- Under the object comparisons, a closed even map acts by the map induced on categorical
cokernels by its components. -/
theorem cokernelFunctor_map_objIso_hom {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (cokernelFunctor.map g).hom ≫ (cokernelFunctorObjIso Y).hom =
      (cokernelFunctorObjIso X).hom ≫
        cokernel.map _ _ g.hom.f₀.hom
          g.hom.f₁.hom
          (congrArg (fun k => k.hom) g.hom.comm₀).symm := by
  apply (cancel_epi (cokernelπ X)).mp
  rw [← Category.assoc, cokernelπ_naturality, Category.assoc,
    cokernelπ_objIso_hom, cokernelπ_objIso_hom_assoc]
  exact (cokernel.π_desc _ _ _).symm

/-- The cokernel functor preserves addition of closed even maps. -/
instance cokernelFunctor_additive :
    (cokernelFunctor (S := S) (w := w)).Additive where
  map_add := by
    intro X Y g h
    apply ObjectProperty.hom_ext
    apply (cancel_epi (cokernelπ X)).mp
    simp only [ObjectProperty.add_hom, Preadditive.comp_add, cokernelπ_naturality,
      CurvedDuplex.add_f₁, Preadditive.add_comp]

end TauCeti.MatrixFactorization
