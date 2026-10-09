/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Cokernels of reduced matrix factorizations

A ring map killing the potential turns a matrix factorization into a square-zero duplex.
Taking the cokernel of its even-to-odd differential gives an additive functor to finitely
generated modules over the target ring. In particular, reduction modulo the potential gives
the finite module used in hypersurface comparisons. The projection and its universal property
retain the ordinary categorical cokernel API. The functor uses Mathlib's
`CategoryTheory.Limits.coker` on the arrows supplied by the reduced differential.

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

private theorem finite_reduced_cokernel (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    Module.Finite T (cokernel ((baseChangeToCurvedDuplex f hw).obj X).d₀ : ModuleCat.{u} T) := by
  let _ : Algebra S T := f.toAlgebra
  have : Module.Finite T ((baseChangeToCurvedDuplex f hw).obj X).X₁ := by
    -- Scalar extension uses this tensor-product carrier; the component formula is an equality
    -- of bundled modules and does not rewrite a dependent typeclass goal.
    change Module.Finite T (TensorProduct S T X.obj.X₁)
    infer_instance
  exact Module.Finite.of_surjective (cokernel.π ((baseChangeToCurvedDuplex f hw).obj X).d₀).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Take the cokernel of the even-to-odd differential after scalar extension along a map
killing the potential. Its finite generation follows from that of the odd component. -/
def cokernelFunctor (f : S →+* T) (hw : f w = 0) :
    MatrixFactorization S w ⥤ FGModuleCat.{u} T := by
  let F := baseChangeToCurvedDuplex f hw
  let G : MatrixFactorization S w ⥤ Arrow (ModuleCat.{u} T) :=
    { obj X := Arrow.mk (F.obj X).d₀
      map g := Arrow.homMk (F.map g).f₀ (F.map g).f₁ (F.map g).comm₀
      map_id X := by ext <;> simp
      map_comp g h := by ext <;> simp }
  exact (ModuleCat.isFG T).lift (G ⋙ coker (ModuleCat.{u} T)) (finite_reduced_cokernel f hw)

/-- The underlying module of the finite cokernel functor is the categorical cokernel of the
reduced even differential. This isomorphism permits use of Mathlib's cokernel API without
unfolding the functor. -/
def cokernelFunctorObjIso (f : S →+* T) (hw : f w = 0) (X : MatrixFactorization S w) :
    ((cokernelFunctor f hw).obj X).obj ≅
      cokernel ((baseChangeToCurvedDuplex f hw).obj X).d₀ := Iso.refl _

/-- The projection from the odd component onto the finite cokernel, as a map of modules. -/
def cokernelπ (f : S →+* T) (hw : f w = 0) (X : MatrixFactorization S w) :
    ((baseChangeToCurvedDuplex f hw).obj X).X₁ ⟶ ((cokernelFunctor f hw).obj X).obj :=
  cokernel.π _

/-- The object comparison carries the projection to the categorical cokernel projection. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_objIso_hom (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    cokernelπ f hw X ≫ (cokernelFunctorObjIso f hw X).hom =
      cokernel.π ((baseChangeToCurvedDuplex f hw).obj X).d₀ := by
  exact Category.comp_id _

/-- The even differential vanishes after projection to the cokernel. -/
@[reassoc]
theorem d₀_cokernelπ (f : S →+* T) (hw : f w = 0) (X : MatrixFactorization S w) :
    ((baseChangeToCurvedDuplex f hw).obj X).d₀ ≫ cokernelπ f hw X = 0 :=
  cokernel.condition _

/-- The cokernel projection is natural with respect to closed even maps. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_naturality (f : S →+* T) (hw : f w = 0)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    cokernelπ f hw X ≫ ((cokernelFunctor f hw).map g).hom =
      ((baseChangeToCurvedDuplex f hw).map g).f₁ ≫ cokernelπ f hw Y := by
  exact cokernel.π_desc _ _ _

/-- The projection exhibits the underlying finite module as the categorical cokernel.
This supplies the full existence and uniqueness API for maps killing the even differential. -/
def isColimitCokernelπ (f : S →+* T) (hw : f w = 0) (X : MatrixFactorization S w) :
    IsColimit (CokernelCofork.ofπ (cokernelπ f hw X) (d₀_cokernelπ f hw X)) :=
  cokernelIsCokernel _

instance cokernelπ_epi (f : S →+* T) (hw : f w = 0) (X : MatrixFactorization S w) :
    Epi (cokernelπ f hw X) :=
  epi_of_isColimit_cofork
    (c := CokernelCofork.ofπ (cokernelπ f hw X) (d₀_cokernelπ f hw X))
    (isColimitCokernelπ f hw X)

/-- Under the object comparisons, a closed even map acts by the map induced on categorical
cokernels by its reduced components. -/
theorem cokernelFunctor_map_objIso_hom (f : S →+* T) (hw : f w = 0)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    ((cokernelFunctor f hw).map g).hom ≫ (cokernelFunctorObjIso f hw Y).hom =
      (cokernelFunctorObjIso f hw X).hom ≫
        cokernel.map _ _ ((baseChangeToCurvedDuplex f hw).map g).f₀
          ((baseChangeToCurvedDuplex f hw).map g).f₁
          ((baseChangeToCurvedDuplex f hw).map g).comm₀.symm := by
  rfl

/-- The cokernel functor preserves addition of closed even maps. -/
instance cokernelFunctor_additive (f : S →+* T) (hw : f w = 0) :
    (cokernelFunctor f hw).Additive where
  map_add := by
    intro X Y g h
    apply ObjectProperty.hom_ext
    apply (cancel_epi (cokernelπ f hw X)).mp
    simp only [ObjectProperty.add_hom, Preadditive.comp_add, cokernelπ_naturality,
      Functor.map_add, CurvedDuplex.add_f₁, Preadditive.add_comp]

end TauCeti.MatrixFactorization
