/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Binary biproduct squares

This file records generic categorical properties of binary biproducts. A biproduct map factors
through the maps obtained by changing one summand at a time, and the squares obtained by adjoining
an identity summand are pushouts or pullbacks. The biproduct of two cokernels is the cokernel of
the biproduct of the two morphisms (`CategoryTheory.Limits.CokernelCofork.isColimitBiprod`); this
is the biproduct analogue of Mathlib's `CategoryTheory.Limits.CokernelCofork.isColimitTensor`.
For functors preserving zero morphisms, biproduct preservation is stable under composition
and follows from preservation of products and coproducts of the same shape. The short complex
of a mapped commutative square agrees with the mapped short complex through the canonical
biproduct comparison.

In a category with zero morphisms, a zero object and binary biproducts give all finite biproducts
(`TauCeti.hasFiniteBiproducts_of_hasBinaryBiproducts`), and a biproduct indexed by
`Option J` splits off its `none` summand (`TauCeti.biproductOptionIso`); the latter is the
inductive step for computing additive invariants of finite biproducts. An additive functor which
kills one summand of a binary biproduct inverts the projection onto the other
(`CategoryTheory.Functor.isIso_map_biprod_fst_of_isZero`). For a functor out of `Cᵒᵖ`, the
comparison `F.obj (op (X ⊞ Y)) ≅ F.obj (op X) ⊞ F.obj (op Y)` through `biprod.opIso` has inverse
given by the images of the projections
(`CategoryTheory.Functor.mapIso_biprod_opIso_trans_mapBiprod_inv`).
-/

public section

namespace CategoryTheory.CommSq

open Limits

universe v w u u'

/-- Mapping the short complex of a commutative square agrees, up to the canonical biproduct
comparison, with the short complex of the mapped square. -/
noncomputable def shortComplexMapIso
    {C₁ : Type u} {D : Type u'} [Category.{v} C₁] [Preadditive C₁]
    [Category.{w} D] [Preadditive D]
    {F : C₁ ⥤ D} [F.Additive]
    {W X Y Z : C₁} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    [HasBinaryBiproduct X Y] [HasBinaryBiproduct (F.obj X) (F.obj Y)]
    (sq : CommSq f g h i) :
    sq.shortComplex.map F ≅ (F.map_commSq sq).shortComplex := by
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact ShortComplex.isoMk (Iso.refl _) (F.mapBiprod X Y) (Iso.refl _)
    (by
      dsimp only [ShortComplex.map, CommSq.shortComplex, Functor.map_commSq]
      simpa only [Iso.refl_hom, Category.id_comp, Functor.map_neg] using
        (biprod.map_lift_mapBiprod F X Y f (-g)).symm)
    (by
      dsimp only [ShortComplex.map, CommSq.shortComplex, Functor.map_commSq]
      simpa only [Iso.refl_hom, Category.comp_id] using
        (biprod.mapBiprod_hom_desc F X Y h i))

end CategoryTheory.CommSq

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w w' u u'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A binary biproduct map factors by changing its first and second summands in succession. -/
theorem biprod_map_factor {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ X₂]
    [HasBinaryBiproduct Y₁ Y₂] :
    biprod.map f g = biprod.map f (𝟙 X₂) ≫ biprod.map (𝟙 Y₁) g := by
  ext <;> simp

/-- The square formed by a morphism and the corresponding biproduct inclusions is a pushout. -/
theorem isPushout_biprod_inl_map {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryBiproduct X Z] [HasBinaryBiproduct Y Z] :
    IsPushout (biprod.inl : X ⟶ X ⊞ Z) f (biprod.map f (𝟙 Z))
      (biprod.inl : Y ⟶ Y ⊞ Z) :=
  (IsPushout.of_coprod_inl_with_id f Z).of_iso
    (Iso.refl X) (biprod.isoCoprod X Z).symm
    (Iso.refl Y) (biprod.isoCoprod Y Z).symm
    (by simp) (by simp) (by ext <;> simp) (by simp)

/-- The square formed by a morphism and the corresponding biproduct projections is a pullback. -/
theorem isPullback_biprod_map_fst {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryBiproduct X Z] [HasBinaryBiproduct Y Z] :
    IsPullback (biprod.fst : X ⊞ Z ⟶ X) (biprod.map f (𝟙 Z)) f
      (biprod.fst : Y ⊞ Z ⟶ Y) :=
  (IsPullback.of_prod_fst_with_id f Z).of_iso
    (biprod.isoProd X Z).symm (Iso.refl X)
    (biprod.isoProd Y Z).symm (Iso.refl Y)
    (by simp) (by ext <;> simp) (by simp) (by simp)

open ZeroObject in
/-- A category with zero morphisms, a zero object and binary biproducts has finite biproducts.
Like Mathlib's `CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts`, this is a theorem
rather than an instance, so that a concrete category may keep finite biproducts with better
definitional properties. -/
theorem hasFiniteBiproducts_of_hasBinaryBiproducts [HasZeroObject C] [HasBinaryBiproducts C] :
    HasFiniteBiproducts C where
  out n := by
    classical
    refine Fintype.induction_empty_option
      (P := fun J _ => HasBiproductsOfShape J C) ?_ ?_ ?_ (Fin n)
    · intro α β _ e hα
      let : Fintype α := Fintype.ofEquiv β e.symm
      let : HasBiproductsOfShape α C := hα
      exact hasBiproductsOfShape_of_equiv C e.symm
    · refine ⟨fun f => HasBiproduct.mk ?_⟩
      let b : Bicone f := { pt := 0, π := fun j => j.elim, ι := fun j => j.elim }
      exact ⟨b, ⟨Fan.IsLimit.mk _ (fun _ => 0) (fun _ j => j.elim)
        (fun _ _ _ => (isZero_zero C).eq_of_tgt _ _),
        Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => j.elim)
        (fun _ _ _ => (isZero_zero C).eq_of_src _ _)⟩⟩
    · intro α _ hα
      let : HasBiproductsOfShape α C := hα
      refine ⟨fun f => HasBiproduct.mk ?_⟩
      let b : Bicone f :=
        { pt := f none ⊞ ⨁ fun j => f (some j)
          π := fun j => match j with
            | none => biprod.fst
            | some j => biprod.snd ≫ biproduct.π _ j
          ι := fun j => match j with
            | none => biprod.inl
            | some j => biproduct.ι (fun j => f (some j)) j ≫ biprod.inr
          ι_π := by
            rintro (_ | j) (_ | k) <;> simp [biproduct.ι_π] }
      refine ⟨b, ⟨Fan.IsLimit.mk _ (fun s =>
        biprod.lift (s.proj none) (biproduct.lift fun j => s.proj (some j))) ?_ ?_,
        Cofan.IsColimit.mk _ (fun s =>
        biprod.desc (s.inj none) (biproduct.desc fun j => s.inj (some j))) ?_ ?_⟩⟩
      · rintro s (_ | j) <;> simp [b]
      · intro s m hm
        apply biprod.hom_ext
        · simpa [b] using hm none
        · apply biproduct.hom_ext
          intro j
          simpa [b] using hm (some j)
      · rintro s (_ | j) <;> simp [b]
      · intro s m hm
        apply biprod.hom_ext'
        · simpa [b] using hm none
        · apply biproduct.hom_ext'
          intro j
          simpa [b] using hm (some j)

variable {J : Type w} (f : Option J → C) [HasBiproduct f]
  [HasBiproduct fun j => f (some j)] [HasBinaryBiproduct (f none) (⨁ fun j => f (some j))]

/-- A biproduct indexed by `Option J` is the binary biproduct of its `none` summand and the
biproduct of the remaining summands. -/
noncomputable def biproductOptionIso : ⨁ f ≅ f none ⊞ ⨁ fun j => f (some j) where
  hom := biprod.lift (biproduct.π f none) (biproduct.lift fun j => biproduct.π f (some j))
  inv := biproduct.lift fun j => match j with
    | none => biprod.fst
    | some j => biprod.snd ≫ biproduct.π _ j
  hom_inv_id := by
    apply biproduct.hom_ext
    rintro (_ | j) <;> simp
  inv_hom_id := by
    apply biprod.hom_ext
    · simp
    · apply biproduct.hom_ext
      intro j
      simp

@[simp]
theorem biproductOptionIso_hom_fst :
    (biproductOptionIso f).hom ≫ biprod.fst = biproduct.π f none := by
  simp [biproductOptionIso]

@[simp]
theorem biproductOptionIso_hom_snd_π (j : J) :
    (biproductOptionIso f).hom ≫ biprod.snd ≫ biproduct.π _ j = biproduct.π f (some j) := by
  simp [biproductOptionIso]

@[simp]
theorem biprod_inl_biproductOptionIso_inv :
    biprod.inl ≫ (biproductOptionIso f).inv = biproduct.ι f none := by
  classical
  apply biproduct.hom_ext
  rintro (_ | j) <;> simp [biproductOptionIso]

@[simp]
theorem biproduct_ι_biprod_inr_biproductOptionIso_inv (j : J) :
    biproduct.ι (fun j => f (some j)) j ≫ biprod.inr ≫ (biproductOptionIso f).inv =
      biproduct.ι f (some j) := by
  classical
  apply biproduct.hom_ext
  rintro (_ | k) <;> simp [biproductOptionIso, biproduct.ι_π]

end TauCeti

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {D : Type u'} [Category.{w'} D] [HasZeroMorphisms D]
  {E : Type*} [Category* E] [HasZeroMorphisms E]

/-- The composite of functors preserving biproducts of shape `J` preserves them. -/
instance (priority := 100) preservesBiproductsOfShape_comp (J : Type w) (F : C ⥤ D)
    (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [PreservesBiproductsOfShape J F] [PreservesBiproductsOfShape J G] :
    PreservesBiproductsOfShape J (F ⋙ G) where
  preserves := { preserves := fun hb =>
    ⟨isBilimitOfPreserves G (isBilimitOfPreserves F hb)⟩ }

/-- A functor preserving zero morphisms, products and coproducts of shape `J` preserves
biproducts of that shape. -/
instance (priority := 100) preservesBiproductsOfShape_of_preservesLimits_and_colimits
    (J : Type w) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesLimitsOfShape (Discrete J) F] [PreservesColimitsOfShape (Discrete J) F] :
    PreservesBiproductsOfShape J F where
  preserves := fun {f} => { preserves := fun {b} hb => ⟨{
    isLimit := IsLimit.ofIsoLimit
      ((IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
        (isLimitOfPreserves F hb.isLimit))
      (Cone.ext (Iso.refl (F.obj b.pt)) (by
        rintro ⟨j⟩
        -- Unfold `Cone.postcompose`, `Functor.mapCone`, `Bicone.toCone` and
        -- `Functor.mapBicone`, including their composite discrete endpoints.
        -- `Discrete.compNatIsoDiscrete` contributes identities. Projection rewrites alone
        -- leave these endpoint types opaque, so the identity laws need this conversion.
        change F.map (b.π j) ≫ 𝟙 (F.obj (f j)) = 𝟙 (F.obj b.pt) ≫ F.map (b.π j)
        simp))
    isColimit := IsColimit.ofIsoColimit
      ((IsColimit.precomposeInvEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
        (isColimitOfPreserves F hb.isColimit))
      (Cocone.ext (Iso.refl (F.obj b.pt)) (by
        rintro ⟨j⟩
        -- Unfold `Cocone.precompose`, `Functor.mapCocone`, `Bicone.toCocone` and
        -- `Functor.mapBicone`, including their composite discrete endpoints.
        -- `Discrete.compNatIsoDiscrete` contributes identities. Projection rewrites alone
        -- leave these endpoint types opaque, so the identity laws need this conversion.
        change (𝟙 (F.obj (f j)) ≫ F.map (b.ι j)) ≫ 𝟙 (F.obj b.pt) = F.map (b.ι j)
        simp)) }⟩ }

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open Limits

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w'} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D) [F.Additive]

/-- An additive functor which sends the second summand of a binary biproduct to a zero object
sends the first projection to an isomorphism, with inverse the image of the first inclusion. -/
theorem isIso_map_biprod_fst_of_isZero (X Y : C) [HasBinaryBiproduct X Y]
    (hY : IsZero (F.obj Y)) : IsIso (F.map (biprod.fst : X ⊞ Y ⟶ X)) := by
  refine ⟨F.map biprod.inl, ?_, ?_⟩
  · rw [← F.map_comp, eq_sub_of_add_eq biprod.total]
    simp [hY.eq_zero_of_tgt (F.map biprod.snd)]
  · rw [← F.map_comp, biprod.inl_fst, F.map_id]

section Op

open Opposite

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w'} D] [HasZeroMorphisms C]
  [HasZeroMorphisms D] (F : Cᵒᵖ ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]
  [F.PreservesZeroMorphisms] [PreservesBinaryBiproduct (op X) (op Y) F]

/-- For a functor `F` out of `Cᵒᵖ`, the inverse of the comparison
`F.obj (op (X ⊞ Y)) ≅ F.obj (op X) ⊞ F.obj (op Y)` through `biprod.opIso` is given by the images
of the opposites of the projections. -/
theorem mapIso_biprod_opIso_trans_mapBiprod_inv :
    (F.mapIso (biprod.opIso X Y) ≪≫ F.mapBiprod (op X) (op Y)).inv =
      biprod.desc (F.map (biprod.fst : X ⊞ Y ⟶ X).op) (F.map (biprod.snd : X ⊞ Y ⟶ Y).op) := by
  rw [Iso.trans_inv, Functor.mapIso_inv, Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, ← F.map_comp, biprod.inl_opIso_inv, biprod.inl_desc]
  · rw [biprod.inr_desc_assoc, ← F.map_comp, biprod.inr_opIso_inv, biprod.inr_desc]

end Op

end CategoryTheory.Functor

namespace CategoryTheory.Limits.CokernelCofork

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {X₁ Y₁ : C} {f₁ : X₁ ⟶ Y₁} {c₁ : CokernelCofork f₁}
  {X₂ Y₂ : C} {f₂ : X₂ ⟶ Y₂} {c₂ : CokernelCofork f₂}
  [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂] [HasBinaryBiproduct c₁.pt c₂.pt]

variable (c₁ c₂) in
/-- Given cokernel coforks `c₁` and `c₂` for `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂`, this is the
cokernel cofork for `biprod.map f₁ f₂ : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with point `c₁.pt ⊞ c₂.pt`. -/
noncomputable abbrev biprod : CokernelCofork (biprod.map f₁ f₂) :=
  CokernelCofork.ofπ (biprod.map c₁.π c₂.π) (by ext <;> simp)

/-- The biproduct of two colimit cokernel coforks is a colimit: `c₁.pt ⊞ c₂.pt` is the cokernel
of `biprod.map f₁ f₂`. -/
noncomputable def isColimitBiprod (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (c₁.biprod c₂) :=
  IsColimit.ofπ _ _
    (fun k hk ↦ biprod.desc
      (Cofork.IsColimit.desc hc₁ (biprod.inl ≫ k) (by simpa using biprod.inl ≫= hk))
      (Cofork.IsColimit.desc hc₂ (biprod.inr ≫ k) (by simpa using biprod.inr ≫= hk)))
    (fun k hk ↦ by ext <;> simp)
    (fun k hk m hm ↦ by
      subst hm
      ext
      · exact Cofork.IsColimit.hom_ext hc₁ (by simp)
      · exact Cofork.IsColimit.hom_ext hc₂ (by simp))

end CategoryTheory.Limits.CokernelCofork
