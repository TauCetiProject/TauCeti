/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

/-!
# Ordered multiplication of Chevalley root morphisms

For any Chevalley datum and any ordered list of roots, multiply the integral root morphisms
with one additive-group coordinate for each root occurring in the list. The construction
applies to positive, negative, or mixed root lists. Its ring-valued points are the ordered
products of `ChevalleyDatum.rootSubgroupPoints`, by
`ChevalleyDatum.schemePointsMulEquiv_rootSubgroup`.

`ChevalleyDatum.mono_rootProduct_of_injective` turns uniqueness of those point coordinates
over arbitrary commutative rings into a scheme monomorphism. This provides the uniqueness
step for scheme-theoretic root coordinates; it asserts neither a closed immersion nor an
identification of the product image.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

noncomputable section

/-- The parameter scheme for an ordered root product. Only roots occurring in the list
carry parameters. It is a finite product of copies of the additive group scheme. -/
abbrev rootProductParameters (t : DynkinType) (l : List (Fin t.numRoots)) :
    Over (Spec (CommRingCat.of ℤ)) :=
  ∏ᶜ fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X

namespace ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Ordered multiplication of the integral root morphisms. This is a morphism of schemes
over `ℤ`, not a homomorphism of group schemes. Repeated roots reuse the same coordinate. -/
def rootProduct (l : List (Fin t.numRoots)) : t.rootProductParameters l ⟶ D.groupScheme.X :=
  (l.attach.map fun γ =>
    Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ ≫
      (D.rootSubgroup γ.val).hom.hom).prod

/-- Ordered root multiplication is the product of the projected root morphisms. -/
theorem rootProduct_def (l : List (Fin t.numRoots)) :
    D.rootProduct l = (l.attach.map fun γ =>
      Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ ≫
        (D.rootSubgroup γ.val).hom.hom).prod :=
  (rfl)

/-- The empty root product is the constant unit morphism. -/
@[simp]
theorem rootProduct_nil : D.rootProduct [] = 1 := by
  simp [rootProduct_def]

/-- Postcomposing ordered root multiplication with a monoid-object homomorphism
postcomposes each root factor. -/
@[reassoc]
theorem rootProduct_comp (l : List (Fin t.numRoots))
    {M : Over (Spec (CommRingCat.of ℤ))} [MonObj M]
    (g : D.groupScheme.X ⟶ M) [IsMonHom g] :
    D.rootProduct l ≫ g = (l.attach.map fun γ =>
      Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ ≫
        (D.rootSubgroup γ.val).hom.hom ≫ g).prod := by
  rw [D.rootProduct_def, ← IsMonHom.monoidHom_apply g _, map_list_prod]
  simp only [List.map_map, Function.comp_def, IsMonHom.monoidHom_apply, Category.assoc]

/-- Precomposing ordered root multiplication evaluates each root factor at the corresponding
additive-group coordinate of the test point. -/
@[reassoc]
theorem comp_rootProduct (l : List (Fin t.numRoots))
    {S : Over (Spec (CommRingCat.of ℤ))} (p : S ⟶ t.rootProductParameters l) :
    p ≫ D.rootProduct l = (l.attach.map fun γ =>
      p ≫ Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ ≫
        (D.rootSubgroup γ.val).hom.hom).prod := by
  let precomp : (t.rootProductParameters l ⟶ D.groupScheme.X) →* (S ⟶ D.groupScheme.X) :=
    ((yonedaMonObj D.groupScheme.X).map p.op).hom
  -- Mathlib's yonedaMonObj map is definitionally precomposition, with no application lemma.
  -- Isolate that projection equation instead of unfolding the functor inside simplification.
  have precomp_apply (f : t.rootProductParameters l ⟶ D.groupScheme.X) :
      precomp f = p ≫ f := (rfl)
  simpa only [rootProduct_def, precomp_apply, List.map_map, Function.comp_def, Category.assoc] using
    precomp.map_list_prod (l.attach.map fun γ =>
      Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ ≫
        (D.rootSubgroup γ.val).hom.hom)

/-- Ordered root multiplication on ring-valued points is the ordered product of the root
homomorphisms with the same additive coordinates. -/
@[simp]
theorem schemePointsMulEquiv_rootProduct (l : List (Fin t.numRoots))
    (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      t.rootProductParameters l) :
    GeneralLinear.schemePointsMulEquiv D.dim A
        (p ≫ D.rootProduct l ≫ D.groupSchemeι.hom.hom) =
      (l.attach.map fun γ => (D.rootSubgroupPoints γ.val A
        (AdditiveGroup.schemePointsMulEquiv A
          (p ≫ Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ)) :
            Matrix.GeneralLinearGroup (Fin D.dim) A)).prod := by
  rw [← Category.assoc, D.comp_rootProduct,
    ← IsMonHom.monoidHom_apply D.groupSchemeι.hom.hom _, map_list_prod, map_list_prod]
  simp only [List.map_map, Function.comp_def, IsMonHom.monoidHom_apply, Category.assoc]
  congr 1
  apply List.map_congr_left
  intro γ _
  rw [← Category.assoc p (Pi.π _ γ), D.schemePointsMulEquiv_rootSubgroup,
    AdditiveGroup.schemePointsMulEquiv_apply]

private theorem rootProduct_spec_injective
    (l : List (Fin t.numRoots))
    (hinj : ∀ (A : Type) [CommRing A] {u v : Fin t.numRoots → A},
      (l.map fun γ => D.rootSubgroupPoints γ A (ofAdd (u γ))).prod =
        (l.map fun γ => D.rootSubgroupPoints γ A (ofAdd (v γ))).prod → ∀ γ ∈ l, u γ = v γ)
    (A : Type) [CommRing A] :
    Function.Injective (fun p : (Spec (CommRingCat.of A)).asOver
      (Spec (CommRingCat.of ℤ)) ⟶ t.rootProductParameters l =>
        p ≫ D.rootProduct l) := by
  classical
  -- Extend by zero only inside this proof to use the native all-root parameter API.
  let coord := fun (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      t.rootProductParameters l) (γ : Fin t.numRoots) =>
    if hγ : γ ∈ l then toAdd (AdditiveGroup.schemePointsMulEquiv A
      (p ≫ Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) ⟨γ, hγ⟩))
    else 0
  have eval (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      t.rootProductParameters l) :
      GeneralLinear.schemePointsMulEquiv D.dim A (p ≫ D.rootProduct l ≫ D.groupSchemeι.hom.hom) =
        ((l.map fun γ => D.rootSubgroupPoints γ A (ofAdd (coord p γ))).prod :
          Matrix.GeneralLinearGroup (Fin D.dim) A) := by
    rw [D.schemePointsMulEquiv_rootProduct]
    simp only [SubmonoidClass.coe_list_prod, List.map_map, Function.comp_def]
    rw [← List.attach_map_val (l := l)]
    apply congrArg List.prod
    apply List.map_congr_left
    intro γ _
    simp only [coord, dite_eq_left γ.property, ofAdd_toAdd]
  intro p q hpq
  have hmat := congrArg (fun z => GeneralLinear.schemePointsMulEquiv D.dim A
    (z ≫ D.groupSchemeι.hom.hom)) hpq
  simp only [Category.assoc] at hmat
  rw [eval p, eval q] at hmat
  have hprod : (l.map fun γ => D.rootSubgroupPoints γ A (ofAdd (coord p γ))).prod =
      (l.map fun γ => D.rootSubgroupPoints γ A (ofAdd (coord q γ))).prod :=
    Subtype.ext hmat
  have hcoord := hinj A hprod
  apply Pi.hom_ext
  intro γ
  apply (AdditiveGroup.schemePointsMulEquiv A).injective
  simpa only [coord, dite_eq_left γ.property, ofAdd_toAdd] using
    congrArg ofAdd (hcoord γ.val γ.property)

/-- If ordered root products determine their parameters over every commutative ring,
then ordered root multiplication is a monomorphism on arbitrary test schemes. -/
theorem mono_rootProduct_of_injective (l : List (Fin t.numRoots))
    (hinj : ∀ (A : Type) [CommRing A] {u v : Fin t.numRoots → A},
      (l.map fun γ => D.rootSubgroupPoints γ A (ofAdd (u γ))).prod =
        (l.map fun γ => D.rootSubgroupPoints γ A (ofAdd (v γ))).prod → ∀ γ ∈ l, u γ = v γ) :
    Mono (D.rootProduct l) := by
  constructor
  intro S p q hpq
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall_spec fun A a => ?_
  let u : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶ S :=
    Over.homMk a (specZIsTerminal.hom_ext _ _)
  have h : u ≫ p = u ≫ q := D.rootProduct_spec_injective l hinj A
    (by simpa only [Category.assoc] using congrArg (u ≫ ·) hpq)
  have hu : u.left = a := Over.homMk_left
    (U := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ))) (V := S) a _
  simpa only [Over.comp_left, hu] using! congrArg (fun z => z.left) h

end ChevalleyDatum

end

end TauCeti.DynkinType
