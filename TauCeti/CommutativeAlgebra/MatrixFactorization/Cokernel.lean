/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Cokernels of scalar-extended matrix factorizations

Taking the cokernel of the even-to-odd differential after extension along any ring map gives
an additive functor to finitely generated modules over the target ring. No vanishing condition
on the image potential is needed. In particular, reduction modulo the potential gives the finite
module used in hypersurface comparisons. The projection and its universal property retain the
ordinary categorical cokernel API. The functor uses Mathlib's
`CategoryTheory.Limits.coker` on the arrows supplied by the scalar-extended differential.

This construction requires only commutative rings; it does not assert that its values are maximal
Cohen–Macaulay, or that it descends to a stable category. Such assertions require additional
hypotheses and comparisons.

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

variable {S T : Type u} [CommRing S] [CommRing T] {w : S}

private theorem finite_baseChange_cokernel (f : S →+* T) (X : MatrixFactorization S w) :
    Module.Finite T
      (cokernel ((baseChangeFunctor f).obj X).obj.d₀.hom : ModuleCat.{u} T) := by
  exact Module.Finite.of_surjective
    (cokernel.π ((baseChangeFunctor f).obj X).obj.d₀.hom).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Take the cokernel of the even-to-odd differential after scalar extension along a map
with arbitrary image potential. Its finite generation follows from that of the odd component. -/
def cokernelFunctor (f : S →+* T) :
    MatrixFactorization S w ⥤ FGModuleCat.{u} T := by
  let F := baseChangeFunctor (w := w) f
  let G : MatrixFactorization S w ⥤ Arrow (ModuleCat.{u} T) :=
    { obj X := Arrow.mk (F.obj X).obj.d₀.hom
      map g := Arrow.homMk (F.map g).hom.f₀.hom (F.map g).hom.f₁.hom
        (congrArg (fun k => k.hom) (F.map g).hom.comm₀)
      map_id X := by ext <;> simp
      map_comp g h := by ext <;> simp }
  exact (ModuleCat.isFG T).lift (G ⋙ coker (ModuleCat.{u} T)) (finite_baseChange_cokernel f)

/-- The underlying module of the finite cokernel functor is the categorical cokernel of the
scalar-extended even differential. This isomorphism permits use of Mathlib's cokernel API without
unfolding the functor. -/
def cokernelFunctorObjIso (f : S →+* T) (X : MatrixFactorization S w) :
    ((cokernelFunctor f).obj X).obj ≅
      cokernel ((baseChangeFunctor f).obj X).obj.d₀.hom := Iso.refl _

/-- The projection from the odd component onto the finite cokernel, as a map of modules. -/
def cokernelπ (f : S →+* T) (X : MatrixFactorization S w) :
    ((baseChangeFunctor f).obj X).obj.X₁.obj ⟶ ((cokernelFunctor f).obj X).obj :=
  cokernel.π _

/-- The object comparison carries the projection to the categorical cokernel projection. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_objIso_hom (f : S →+* T)
    (X : MatrixFactorization S w) :
    cokernelπ f X ≫ (cokernelFunctorObjIso f X).hom =
      cokernel.π ((baseChangeFunctor f).obj X).obj.d₀.hom := by
  exact Category.comp_id _

/-- The even differential vanishes after projection to the cokernel. -/
@[reassoc (attr := simp)]
theorem d₀_cokernelπ (f : S →+* T) (X : MatrixFactorization S w) :
    ((baseChangeFunctor f).obj X).obj.d₀.hom ≫ cokernelπ f X = 0 :=
  cokernel.condition _

/-- The cokernel projection is natural with respect to closed even maps. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_naturality (f : S →+* T)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    cokernelπ f X ≫ ((cokernelFunctor f).map g).hom =
      ((baseChangeFunctor f).map g).hom.f₁.hom ≫ cokernelπ f Y := by
  exact cokernel.π_desc _ _ _

/-- The projection exhibits the underlying finite module as the categorical cokernel.
This supplies the full existence and uniqueness API for maps killing the even differential. -/
def isColimitCokernelπ (f : S →+* T) (X : MatrixFactorization S w) :
    IsColimit (CokernelCofork.ofπ (cokernelπ f X) (d₀_cokernelπ f X)) :=
  cokernelIsCokernel _

instance cokernelπ_epi (f : S →+* T) (X : MatrixFactorization S w) :
    Epi (cokernelπ f X) :=
  epi_of_isColimit_cofork
    (c := CokernelCofork.ofπ (cokernelπ f X) (d₀_cokernelπ f X))
    (isColimitCokernelπ f X)

/-- Under the object comparisons, a closed even map acts by the map induced on categorical
cokernels by its scalar-extended components. -/
theorem cokernelFunctor_map_objIso_hom (f : S →+* T)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    ((cokernelFunctor f).map g).hom ≫ (cokernelFunctorObjIso f Y).hom =
      (cokernelFunctorObjIso f X).hom ≫
        cokernel.map _ _ ((baseChangeFunctor f).map g).hom.f₀.hom
          ((baseChangeFunctor f).map g).hom.f₁.hom
          (congrArg (fun k => k.hom) ((baseChangeFunctor f).map g).hom.comm₀).symm := by
  apply (cancel_epi (cokernelπ f X)).mp
  rw [← Category.assoc, cokernelπ_naturality, Category.assoc,
    cokernelπ_objIso_hom, cokernelπ_objIso_hom_assoc]
  exact (cokernel.π_desc _ _ _).symm

/-- The cokernel functor preserves addition of closed even maps. -/
instance cokernelFunctor_additive (f : S →+* T) :
    (cokernelFunctor (w := w) f).Additive where
  map_add := by
    intro X Y g h
    apply ObjectProperty.hom_ext
    apply (cancel_epi (cokernelπ f X)).mp
    simp only [ObjectProperty.add_hom, Preadditive.comp_add, cokernelπ_naturality,
      Functor.map_add, CurvedDuplex.add_f₁, Preadditive.add_comp]

end TauCeti.MatrixFactorization
