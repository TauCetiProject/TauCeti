/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Coherent
public import TauCeti.CategoryTheory.ObjectProperty.Presented
public import TauCeti.CategoryTheory.Preadditive.Progenerator
public import TauCeti.CategoryTheory.Preadditive.Projectivization

/-!
# The progenerator equivalence for abelian categories

Let `C` be an abelian category with a progenerator `P` (`TauCeti.IsProgenerator P`), and write
`Γ = End P`. Because `C` is idempotent complete (`CategoryTheory.isIdempotentComplete_of_abelian`)
and `proj C = add P` (`TauCeti.IsProgenerator.isProjective_eq_additiveClosure`), projectivization
(`TauCeti.projectivizationFunctor P`) already identifies `proj C` and `add P` with the category
`proj Γᵐᵒᵖ` of finitely generated projective right `Γ`-modules
(`TauCeti.IsProgenerator.projectiveEquivalence`).

Passing to cokernels extends `Hom(P, -)` to an equivalence on all of `C`:

* every object of `C` is a cokernel of a morphism in `add P`
  (`TauCeti.IsProgenerator.presented_additiveClosure_eq_top`);
* since `P` is projective, `Hom(P, -)` (`CategoryTheory.preadditiveCoyonedaObj P`) is exact and
  preserves finite colimits, so it sends every object of `C` to a cokernel of a morphism in
  `proj Γᵐᵒᵖ`, that is to a finitely presented `Γᵐᵒᵖ`-module
  (`TauCeti.IsProgenerator.finitePresentationModules_preadditiveCoyonedaObj_obj`);
* `Hom(P, -)` is fully faithful on all of `C`
  (`TauCeti.IsProgenerator.preadditiveCoyonedaObj_map_bijective`), by lifting morphisms along
  presentations in `add P` and using projectivization there;
* every finitely presented `Γᵐᵒᵖ`-module is the cokernel of a morphism in `proj Γᵐᵒᵖ`, which lifts
  across projectivization to a morphism in `add P` whose cokernel realizes the module
  (`TauCeti.IsProgenerator.finitePresentationModules_le_essImage`).

Thus `Hom(P, -)` restricts to an additive equivalence
`TauCeti.IsProgenerator.progeneratorEquivalence` between `C` and
`(TauCeti.finitePresentationModules (End P)ᵐᵒᵖ).FullSubcategory`, extending
`TauCeti.projectivizationFunctor P` on `add P`. Because `C` has kernels, the equivalent category of
finitely presented `Γᵐᵒᵖ`-modules also has kernels, so `(End P)ᵐᵒᵖ` is automatically left coherent
(`TauCeti.IsProgenerator.isCoherentRing_end_mulOpposite`).

## Main definitions

* `TauCeti.IsProgenerator.progeneratorFunctor`: `Hom(P, -)` from `C` to the finitely presented
  `(End P)ᵐᵒᵖ`-modules; it is an additive equivalence of categories.
* `TauCeti.IsProgenerator.progeneratorEquivalence`: the bundled equivalence between `C` and the
  finitely presented `(End P)ᵐᵒᵖ`-modules.
* `TauCeti.IsProgenerator.additiveClosureCompProgeneratorFunctorIso`: compatibility of
  `progeneratorFunctor` with `TauCeti.projectivizationFunctor P` on `add P`.

## Main results

* `TauCeti.IsProgenerator.presented_additiveClosure_eq_top`: every object of `C` has a presentation
  in `add P`.
* `TauCeti.IsProgenerator.finitePresentationModules_preadditiveCoyonedaObj_obj`,
  `TauCeti.IsProgenerator.preadditiveCoyonedaObj_map_bijective`, and
  `TauCeti.IsProgenerator.finitePresentationModules_le_essImage`: well-definedness, full
  faithfulness, and essential surjectivity of `Hom(P, -)` onto finitely presented right
  `End P`-modules.
* `TauCeti.IsProgenerator.isCoherentRing_end_mulOpposite`: for any progenerator `P` of an abelian
  category, `(End P)ᵐᵒᵖ` is left coherent.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Proposition 2.3 and Proposition 3.10.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section II.2.
-/

public section

namespace TauCeti.IsProgenerator

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

variable {P : C}

/-! ### Presentations by `add P` -/

/-- In an abelian category with a progenerator `P`, every object is the cokernel of a morphism in
`add P`. -/
theorem presented_additiveClosure_eq_top (hP : IsProgenerator P) :
    (additiveClosure P).presented = ⊤ :=
  ObjectProperty.presented_eq_top hP.exists_epi_additiveClosure

/-! ### Well-definedness, full faithfulness, and essential image of `Hom(P, -)` -/

/-- For a progenerator `P` of an abelian category `C` and any object `X` of `C`, `Hom(P, X)` is a
finitely presented `(End P)ᵐᵒᵖ`-module. -/
theorem finitePresentationModules_preadditiveCoyonedaObj_obj (hP : IsProgenerator P) (X : C) :
    finitePresentationModules (End P)ᵐᵒᵖ ((preadditiveCoyonedaObj P).obj X) := by
  have := hP.projective
  rw [← presented_finiteProjectiveModules (End P)ᵐᵒᵖ]
  have hX : (additiveClosure P).presented X := by
    rw [hP.presented_additiveClosure_eq_top]
    trivial
  obtain @⟨Q₀, Q₁, u, c, hc, hQ₀, hQ₁⟩ := hX
  let hc' : IsColimit (CokernelCofork.ofπ c.π c.condition) :=
    IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))
  exact MorphismProperty.cokernels.of_isColimit ((preadditiveCoyonedaObj P).map u) _
    (isColimitCoforkMapOfIsColimit' (preadditiveCoyonedaObj P) c.condition hc')
    ⟨finiteProjectiveModules_preadditiveCoyonedaObj_obj hQ₀,
      finiteProjectiveModules_preadditiveCoyonedaObj_obj hQ₁⟩

/-- For a progenerator `P` of an abelian category `C`, `Hom(P, -)` is bijective on morphisms
between arbitrary objects of `C`. -/
theorem preadditiveCoyonedaObj_map_bijective (hP : IsProgenerator P) (X Y : C) :
    Function.Bijective ((preadditiveCoyonedaObj P).map : (X ⟶ Y) → _) := by
  have := hP.projective
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨Q, π, hQ, hπ⟩ := hP.exists_epi_additiveClosure X
    refine (cancel_epi π).mp ((TauCeti.preadditiveCoyonedaObj_map_bijective hQ Y).1 ?_)
    rw [Functor.map_comp, Functor.map_comp, hf]
  · have hX : (additiveClosure P).presented X := by
      rw [hP.presented_additiveClosure_eq_top]
      trivial
    obtain @⟨Q₀, Q₁, u, c, hc, hQ₀, hQ₁⟩ := hX
    obtain ⟨h, hh⟩ := (TauCeti.preadditiveCoyonedaObj_map_bijective hQ₁ Y).2
      ((preadditiveCoyonedaObj P).map c.π ≫ φ)
    have huh : u ≫ h = 0 := (TauCeti.preadditiveCoyonedaObj_map_bijective hQ₀ Y).1 <| by
      rw [Functor.map_comp, hh, ← Category.assoc, ← Functor.map_comp, CokernelCofork.condition,
        Functor.map_zero, Limits.zero_comp, Functor.map_zero]
    obtain ⟨f, hf⟩ := CokernelCofork.IsColimit.desc' hc h huh
    have : Epi c.π := Cofork.IsColimit.epi hc
    refine ⟨f, (cancel_epi ((preadditiveCoyonedaObj P).map c.π)).mp ?_⟩
    rw [← Functor.map_comp, hf, hh]

/-- For a progenerator `P` of an abelian category `C`, every finitely presented `(End P)ᵐᵒᵖ`-module
is isomorphic to `Hom(P, X)` for some `X : C`. -/
theorem finitePresentationModules_le_essImage (hP : IsProgenerator P) :
    finitePresentationModules (End P)ᵐᵒᵖ ≤ (preadditiveCoyonedaObj P).essImage := by
  have := hP.projective
  intro M hM
  rw [← presented_finiteProjectiveModules (End P)ᵐᵒᵖ] at hM
  obtain @⟨A₀, A₁, α, c, hc, hA₀, hA₁⟩ := hM
  let F := projectivizationFunctor P
  let Q₀ := F.objPreimage ⟨A₀, hA₀⟩
  let Q₁ := F.objPreimage ⟨A₁, hA₁⟩
  let e₀ : (preadditiveCoyonedaObj P).obj Q₀.obj ≅ A₀ :=
    (finiteProjectiveModules (End P)ᵐᵒᵖ).ι.mapIso (F.objObjPreimageIso ⟨A₀, hA₀⟩)
  let e₁ : (preadditiveCoyonedaObj P).obj Q₁.obj ≅ A₁ :=
    (finiteProjectiveModules (End P)ᵐᵒᵖ).ι.mapIso (F.objObjPreimageIso ⟨A₁, hA₁⟩)
  obtain ⟨u, hu⟩ := (TauCeti.preadditiveCoyonedaObj_map_bijective Q₀.property Q₁.obj).2
    (e₀.hom ≫ α ≫ e₁.inv)
  have hu' : (preadditiveCoyonedaObj P).map u ≫ e₁.hom = e₀.hom ≫ α := by
    rw [hu, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨cokernel u, ⟨?_⟩⟩
  exact PreservesCokernel.iso (preadditiveCoyonedaObj P) u ≪≫
    cokernel.mapIso _ α e₀ e₁ hu' ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hc

/-! ### The progenerator equivalence and coherence of `(End P)ᵐᵒᵖ` -/

/-- For a progenerator `P` of an abelian category `C`, `Hom(P, -)` as a functor from `C` to the
finitely presented `(End P)ᵐᵒᵖ`-modules. -/
noncomputable def progeneratorFunctor (hP : IsProgenerator P) :
    C ⥤ (finitePresentationModules (End P)ᵐᵒᵖ).FullSubcategory :=
  (finitePresentationModules (End P)ᵐᵒᵖ).lift (preadditiveCoyonedaObj P)
    hP.finitePresentationModules_preadditiveCoyonedaObj_obj

/-- `hP.progeneratorFunctor` followed by the inclusion into `ModuleCat (End P)ᵐᵒᵖ` is
`Hom(P, -)`. -/
noncomputable def progeneratorFunctorCompιIso (hP : IsProgenerator P) :
    hP.progeneratorFunctor ⋙ (finitePresentationModules (End P)ᵐᵒᵖ).ι ≅ preadditiveCoyonedaObj P :=
  ObjectProperty.liftCompιIso _ _ _

@[simp]
theorem progeneratorFunctor_obj_obj (hP : IsProgenerator P) (X : C) :
    (hP.progeneratorFunctor.obj X).obj = (preadditiveCoyonedaObj P).obj X :=
  (rfl)

@[simp]
theorem progeneratorFunctorCompιIso_hom_app (hP : IsProgenerator P) (X : C) :
    hP.progeneratorFunctorCompιIso.hom.app X = eqToHom (hP.progeneratorFunctor_obj_obj X) :=
  (rfl)

@[simp]
theorem progeneratorFunctorCompιIso_inv_app (hP : IsProgenerator P) (X : C) :
    hP.progeneratorFunctorCompιIso.inv.app X = eqToHom (hP.progeneratorFunctor_obj_obj X).symm :=
  (rfl)

/-- The action of `hP.progeneratorFunctor` on morphisms agrees with `Hom(P, -)` modulo the
comparison isomorphism `hP.progeneratorFunctorCompιIso`. -/
theorem progeneratorFunctor_map_hom (hP : IsProgenerator P) {X Y : C} (f : X ⟶ Y) :
    (hP.progeneratorFunctor.map f).hom =
      hP.progeneratorFunctorCompιIso.hom.app X ≫ (preadditiveCoyonedaObj P).map f ≫
        hP.progeneratorFunctorCompιIso.inv.app Y :=
  (NatIso.naturality_2 hP.progeneratorFunctorCompιIso f).symm

instance additive_progeneratorFunctor (hP : IsProgenerator P) :
    hP.progeneratorFunctor.Additive where
  map_add {_ _ _ _} := ObjectProperty.hom_ext _ (preadditiveCoyonedaObj P).map_add

instance full_progeneratorFunctor (hP : IsProgenerator P) : hP.progeneratorFunctor.Full where
  map_surjective {X Y} φ :=
    have ⟨f, hf⟩ := (hP.preadditiveCoyonedaObj_map_bijective X Y).2 φ.hom
    ⟨f, ObjectProperty.hom_ext _ hf⟩

instance faithful_progeneratorFunctor (hP : IsProgenerator P) :
    hP.progeneratorFunctor.Faithful where
  map_injective {X Y} _ _ h :=
    (hP.preadditiveCoyonedaObj_map_bijective X Y).1 (congrArg (fun g ↦ g.hom) h)

/-- **The progenerator equivalence.** For a progenerator `P` of an abelian category `C`, `Hom(P, -)`
is an equivalence between `C` and the finitely presented right `End P`-modules. -/
instance isEquivalence_progeneratorFunctor (hP : IsProgenerator P) :
    hP.progeneratorFunctor.IsEquivalence :=
  have : hP.progeneratorFunctor.EssSurj :=
    (ObjectProperty.essSurj_lift_iff _ _ _).mpr hP.finitePresentationModules_le_essImage
  { }

/-- **The progenerator equivalence**, bundled as an equivalence of categories
`C ≌ (finitePresentationModules (End P)ᵐᵒᵖ).FullSubcategory`. -/
noncomputable def progeneratorEquivalence (hP : IsProgenerator P) :
    C ≌ (finitePresentationModules (End P)ᵐᵒᵖ).FullSubcategory :=
  hP.progeneratorFunctor.asEquivalence

@[simp]
theorem progeneratorEquivalence_functor (hP : IsProgenerator P) :
    hP.progeneratorEquivalence.functor = hP.progeneratorFunctor :=
  (rfl)

/-- On `add P`, `hP.progeneratorFunctor` restricts to `TauCeti.projectivizationFunctor P` followed
by the inclusion of finitely generated projective modules into finitely presented modules. -/
noncomputable def additiveClosureCompProgeneratorFunctorIso (hP : IsProgenerator P) :
    (additiveClosure P).ι ⋙ hP.progeneratorFunctor ≅
      projectivizationFunctor P ⋙
        ObjectProperty.ιOfLE (finiteProjectiveModules_le_finitePresentationModules (End P)ᵐᵒᵖ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

@[simp]
theorem additiveClosureCompProgeneratorFunctorIso_hom_app (hP : IsProgenerator P)
    (X : (additiveClosure P).FullSubcategory) :
    (hP.additiveClosureCompProgeneratorFunctorIso.hom.app X).hom =
      eqToHom (hP.progeneratorFunctor_obj_obj X.obj) :=
  (rfl)

@[simp]
theorem additiveClosureCompProgeneratorFunctorIso_inv_app (hP : IsProgenerator P)
    (X : (additiveClosure P).FullSubcategory) :
    (hP.additiveClosureCompProgeneratorFunctorIso.inv.app X).hom =
      eqToHom (hP.progeneratorFunctor_obj_obj X.obj).symm :=
  (rfl)

/-- **Coherence of the endomorphism ring of a progenerator.** If `P` is a progenerator of an abelian
category `C`, then `(End P)ᵐᵒᵖ` is left coherent: the full subcategory of finitely presented
`(End P)ᵐᵒᵖ`-modules is equivalent to `C` and therefore has kernels. -/
theorem isCoherentRing_end_mulOpposite (hP : IsProgenerator P) : IsCoherentRing (End P)ᵐᵒᵖ := by
  have : HasEqualizers (finitePresentationModules (End P)ᵐᵒᵖ).FullSubcategory :=
    Adjunction.hasLimitsOfShape_of_equivalence hP.progeneratorEquivalence.inverse
  exact hasKernels_finitePresentationModules_iff_isCoherentRing.mp inferInstance

end TauCeti.IsProgenerator
