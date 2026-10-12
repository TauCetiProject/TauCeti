/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.StableMorphism
public import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation
public import TauCeti.Algebra.Module.Projective.FinitePresentation

/-!
# The stable transpose functor

The Auslander–Bridger transpose is an additive contravariant functor on finitely presented
modules modulo maps factoring through projectives. Choosing a finite projective presentation
at each module constructs this functor; changing the presentations gives a natural isomorphism.
The comparison maps are the stable transposes of the identity maps of the presented modules.

The objects and morphisms here form a full subcategory of the existing projective stable
quotient of `ModuleCat`. In particular, the quotient kills maps factoring through arbitrary
projectives. No Noetherian, commutativity, or minimality hypothesis is needed.

## Main definitions

* `TauCeti.FinitelyPresentedStableModule`: finitely presented modules in the projective stable
  quotient.
* `TauCeti.stableTransposeFunctor`: the functor attached to a family of presentations.
* `TauCeti.stableTransposeFunctorIso`: natural independence of that family.
* `TauCeti.stableTranspose`: the functor obtained by choosing finite projective presentations.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Section 2.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable (A : Type u) [Ring A]

/-- Finitely presented modules, with morphisms taken modulo maps through projective modules.
This is a full subcategory of the projective stable quotient of `ModuleCat`. -/
abbrev FinitelyPresentedStableModule :=
  ObjectProperty.FullSubcategory
    (fun M : (ExactStructure.abelian (ModuleCat.{v} A)).ProjectiveStableCategory ↦
      Module.FinitePresentation A M.as)

variable {A}

local notation "S" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))
local notation "T" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))

namespace FiniteProjectivePresentation

variable {M N L : ModuleCat.{max u v} A}

/-- The transpose of a finite projective presentation, as a finitely presented stable module
over the opposite ring. -/
noncomputable abbrev stableTransposeObj (P : FiniteProjectivePresentation M) :
    FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ :=
  ⟨(T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p)),
    inferInstanceAs (Module.FinitePresentation Aᵐᵒᵖ (AuslanderReitenTranspose P.p))⟩

/-- The underlying stable object of a transposed presentation. -/
@[simp]
theorem stableTransposeObj_obj (P : FiniteProjectivePresentation M) :
    P.stableTransposeObj.obj =
      (T).obj (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p)) := (rfl)

/-- Two presentations of the same module give canonically isomorphic stable transposes.
Both directions are computed by transposing the identity of the presented module. -/
noncomputable def stableTransposeIso (P Q : FiniteProjectivePresentation M) :
    P.stableTransposeObj ≅ Q.stableTransposeObj where
  hom := ObjectProperty.homMk
    (AuslanderReitenTranspose.stableMap Q.exact.linearMap_comp_eq_zero P.exact P.surjective
      (𝟙 ((S).obj M)))
  inv := ObjectProperty.homMk
    (AuslanderReitenTranspose.stableMap P.exact.linearMap_comp_eq_zero Q.exact Q.surjective
      (𝟙 ((S).obj M)))
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.FullSubcategory.id_hom]
    rw [← AuslanderReitenTranspose.stableMap_comp]
    simpa only [Category.id_comp] using
      AuslanderReitenTranspose.stableMap_id P.exact P.surjective
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.FullSubcategory.id_hom]
    rw [← AuslanderReitenTranspose.stableMap_comp]
    simpa only [Category.id_comp] using
      AuslanderReitenTranspose.stableMap_id Q.exact Q.surjective

/-- The comparison of two stable transposes is induced by the identity of the module. -/
@[simp]
theorem stableTransposeIso_hom (P Q : FiniteProjectivePresentation M) :
    (P.stableTransposeIso Q).hom.hom =
      AuslanderReitenTranspose.stableMap Q.exact.linearMap_comp_eq_zero P.exact P.surjective
        (𝟙 ((S).obj M)) := (rfl)

/-- The inverse comparison is induced by the same identity with the presentations exchanged. -/
@[simp]
theorem stableTransposeIso_inv (P Q : FiniteProjectivePresentation M) :
    (P.stableTransposeIso Q).inv.hom =
      AuslanderReitenTranspose.stableMap P.exact.linearMap_comp_eq_zero Q.exact Q.surjective
        (𝟙 ((S).obj M)) := (rfl)

/-- Comparing a presentation with itself gives the identity isomorphism. -/
@[simp]
theorem stableTransposeIso_refl (P : FiniteProjectivePresentation M) :
    P.stableTransposeIso P = Iso.refl P.stableTransposeObj := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact AuslanderReitenTranspose.stableMap_id P.exact P.surjective

/-- Presentation comparisons compose coherently. -/
@[simp]
theorem stableTransposeIso_trans (P Q R : FiniteProjectivePresentation M) :
    P.stableTransposeIso Q ≪≫ Q.stableTransposeIso R = P.stableTransposeIso R := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  simp only [Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom, stableTransposeIso_hom]
  rw [← AuslanderReitenTranspose.stableMap_comp, Category.id_comp]

end FiniteProjectivePresentation

variable (P Q : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
  FiniteProjectivePresentation M.obj.as)

/-- The additive contravariant transpose functor determined by finite projective presentations.
Contravariance is expressed by taking values in the opposite stable category. -/
noncomputable def stableTransposeFunctor :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ where
  obj M := Opposite.op (P M).stableTransposeObj
  map {M N} f := (ObjectProperty.homMk
    (AuslanderReitenTranspose.stableMap (P M).exact.linearMap_comp_eq_zero
      (P N).exact (P N).surjective f.hom)).op
  map_id M := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact AuslanderReitenTranspose.stableMap_id (P M).exact (P M).surjective
  map_comp {M N L} f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact AuslanderReitenTranspose.stableMap_comp (P M).exact.linearMap_comp_eq_zero
      (P N).exact (P N).surjective (P L).exact (P L).surjective f.hom g.hom

/-- The object assigned by the transpose functor is the transpose of its chosen presentation. -/
@[simp]
theorem stableTransposeFunctor_obj (M : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTransposeFunctor P).obj M = Opposite.op (P M).stableTransposeObj := (rfl)

/-- The map assigned by the transpose functor is the stable transpose of the underlying map,
after identifying its objects with the transposed presentations. -/
@[simp]
theorem stableTransposeFunctor_map {M N : FinitelyPresentedStableModule.{u, max u v} A}
    (f : M ⟶ N) :
    (stableTransposeFunctor P).map f =
      eqToHom (stableTransposeFunctor_obj P M) ≫
        (ObjectProperty.homMk
          (AuslanderReitenTranspose.stableMap (P M).exact.linearMap_comp_eq_zero
            (P N).exact (P N).surjective f.hom)).op ≫
        eqToHom (stableTransposeFunctor_obj P N).symm := by
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The stable transpose functor preserves sums of morphisms. -/
instance : (stableTransposeFunctor P).Additive where
  map_add := by
    intro M N f g
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact map_add _ f.hom g.hom

/-- Changing finite projective presentations gives a natural isomorphism of transpose functors. -/
noncomputable def stableTransposeFunctorIso : stableTransposeFunctor P ≅ stableTransposeFunctor Q :=
  NatIso.ofComponents (fun M ↦ ((Q M).stableTransposeIso (P M)).op) fun {M N} f ↦ by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    simp only [stableTransposeFunctor, Iso.op_hom, unop_comp, Quiver.Hom.unop_op,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      FiniteProjectivePresentation.stableTransposeIso_hom]
    rw [← AuslanderReitenTranspose.stableMap_comp,
      ← AuslanderReitenTranspose.stableMap_comp, Category.id_comp, Category.comp_id]

/-- The component of the natural comparison is the identity-induced presentation comparison. -/
@[simp]
theorem stableTransposeFunctorIso_app (M : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTransposeFunctorIso P Q).app M =
      eqToIso (stableTransposeFunctor_obj P M) ≪≫
        ((Q M).stableTransposeIso (P M)).op ≪≫
        (eqToIso (stableTransposeFunctor_obj Q M)).symm := by
  exact ((Iso.refl_trans _).trans (Iso.trans_refl _)).symm

variable (A)

/-- The Auslander–Bridger transpose on finitely presented stable modules, using chosen finite
projective presentations. The result is independent of the choices by
`TauCeti.stableTransposeFunctorIso`. -/
noncomputable def stableTranspose :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ :=
  stableTransposeFunctor fun M ↦
    letI := M.property
    FiniteProjectivePresentation.ofFinitePresentation (M := M.obj.as)

/-- The transpose is the functor constructed from the chosen finite projective presentations. -/
theorem stableTranspose_def :
    stableTranspose.{u, v} A = stableTransposeFunctor (fun M ↦
      letI := M.property
      FiniteProjectivePresentation.ofFinitePresentation (M := M.obj.as)) := (rfl)

/-- The transpose using chosen presentations is additive. -/
instance : (stableTranspose.{u, v} A).Additive := inferInstanceAs
  (stableTransposeFunctor (fun M ↦
    letI := M.property
    FiniteProjectivePresentation.ofFinitePresentation (M := M.obj.as))).Additive

end TauCeti
