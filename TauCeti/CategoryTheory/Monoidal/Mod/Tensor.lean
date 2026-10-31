/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Mod.Bimodule
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Bicategory.End

/-!
# The balanced tensor product of modules over a commutative monoid

Let `A` be a commutative monoid object in a braided monoidal category `C` with coequalizers,
preserved by tensoring on either side. The balanced tensor product `M ⊗_A N` of two left
`A`-modules is the coequalizer of the two actions of `A` on `M ⊗ A ⊗ N`: the right action
`m ⊗ a ↦ a • m` of `A` on `M`, obtained through the braiding, and the left action on `N`. The
scalars act on `M ⊗_A N` through `M`. With unit the regular module `A`, this makes `Mod C A` a
monoidal category.

For the commutative sphere monoid in symmetric sequences this is the smash product `X ∧ Y` of
symmetric spectra, the coequalizer of `X ⊗ S ⊗ Y ⇉ X ⊗ Y`.

The construction reuses Mathlib's tensor product of bimodules `Bimod.tensorBimod`, with the
associator and unitors of Mathlib's bicategory `Bimod.monBicategory` of monoids and bimodules.
A module over a commutative monoid is a bimodule through `Mod.toBimod`. The bimodule tensor
product of two such bimodules is again of this form (`Bimod.tensorBimod_actRight_eq`), so the
monoidal structure of the endomorphism category `Bimod R R` is transported to `Mod C A` along the
fully faithful functor `Mod.toBimod` by Mathlib's `Monoidal.induced`.

## Main definitions

* `Bimod.monoidalCategory`: the monoidal category of `R`-`R`-bimodules under the tensor product of
  bimodules.
* `Mod.monoidalCategory`: the monoidal category of modules over a commutative monoid object, under
  the balanced tensor product.
* `Mod.tensorπ M N : M.X ⊗ N.X ⟶ (M ⊗ N).X`: the quotient map onto the balanced tensor product, and
  `Mod.tensorDesc`, its universal property.

## Main statements

* `Bimod.tensorBimod_actRight_eq`: the tensor product of bimodules whose right actions are their
  left actions moved through the braiding again has this property.
* `Mod.tensorπ_whiskerLeft_hom`, `Mod.tensorπ_whiskerRight_hom`, `Mod.tensorπ_associator_hom_hom`,
  `Mod.tensorπ_leftUnitor_hom_hom` and `Mod.tensorπ_rightUnitor_hom_hom`: the monoidal structure
  on representatives in `M.X ⊗ N.X`.
* The instance `(Mod.toBimod (A := A)).Monoidal`: `Mod.toBimod` is a monoidal functor.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonoidalLeftAction MonObj BraidedCategory Limits

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {R : Mon C}

/-- Bimodules over a monoid object `R` form a monoidal category under the tensor product of
bimodules, with unit the regular bimodule: the category of endomorphisms of `R` in Mathlib's
bicategory `Bimod.monBicategory`. -/
noncomputable instance _root_.Bimod.monoidalCategory (R : Mon C) :
    MonoidalCategory (Bimod R R) :=
  @instMonoidalCategoryHom _ Bimod.monBicategory R

/-- The associator of bimodules on representatives in `P.X ⊗ Q.X ⊗ L.X`. -/
@[reassoc]
theorem _root_.Bimod.π_associator_hom_hom (P Q L : Bimod R R) :
    coequalizer.π (P.actRight ▷ Q.X) ((α_ P.X R.X Q.X).hom ≫ P.X ◁ Q.actLeft) ▷ L.X ≫
        coequalizer.π ((P ⊗ Q).actRight ▷ L.X)
          ((α_ (P ⊗ Q).X R.X L.X).hom ≫ (P ⊗ Q).X ◁ L.actLeft) ≫ (α_ P Q L).hom.hom =
      (α_ P.X Q.X L.X).hom ≫
        P.X ◁ coequalizer.π (Q.actRight ▷ L.X) ((α_ Q.X R.X L.X).hom ≫ Q.X ◁ L.actLeft) ≫
          coequalizer.π (P.actRight ▷ (Q ⊗ L).X)
            ((α_ P.X R.X (Q ⊗ L).X).hom ≫ P.X ◁ (Q ⊗ L).actLeft) := by
  -- The associator is defined by descending twice along these coequalizers.
  erw [coequalizer.π_desc]
  apply π_tensor_id_preserves_coequalizer_inv_desc

/-- The left unitor of bimodules is induced by the left action. -/
@[reassoc]
theorem _root_.Bimod.π_leftUnitor_hom_hom (P : Bimod R R) :
    coequalizer.π ((Bimod.regular R).actRight ▷ P.X)
        ((α_ R.X R.X P.X).hom ≫ R.X ◁ P.actLeft) ≫ (λ_ P).hom.hom = P.actLeft :=
  coequalizer.π_desc _ _

/-- The right unitor of bimodules is induced by the right action. -/
@[reassoc]
theorem _root_.Bimod.π_rightUnitor_hom_hom (P : Bimod R R) :
    coequalizer.π (P.actRight ▷ R.X)
        ((α_ P.X R.X R.X).hom ≫ P.X ◁ (Bimod.regular R).actLeft) ≫ (ρ_ P).hom.hom = P.actRight :=
  coequalizer.π_desc _ _

variable [BraidedCategory C] in
/-- If the right actions of two `R`-`R`-bimodules are their left actions precomposed with the
inverse braiding, then so is the right action of their tensor product. -/
theorem _root_.Bimod.tensorBimod_actRight_eq (P Q : Bimod R R)
    (hP : P.actRight = (β_ R.X P.X).inv ≫ P.actLeft)
    (hQ : Q.actRight = (β_ R.X Q.X).inv ≫ Q.actLeft) :
    (P.tensorBimod Q).actRight = (β_ R.X _).inv ≫ (P.tensorBimod Q).actLeft := by
  refine (cancel_epi ((tensorRight R.X).map (coequalizer.π _ _))).1 ?_
  dsimp
  rw [Bimod.TensorBimod.π_tensor_id_actRight]
  dsimp only [Bimod.TensorBimod.X]
  rw [braiding_inv_naturality_left_assoc,
    Bimod.TensorBimod.whiskerLeft_π_actLeft, hQ, braiding_tensor_right_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, ← hP]
  rw [coequalizer.condition]
  simp

end

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A]

/-- The balanced tensor product `M ⊗_A N` of modules over a commutative monoid object: the
tensor product of the associated bimodules, with its left action. -/
-- Exposed so that its carrier is definitionally that of the bimodule tensor product, which the
-- comparison `toBimodTensorObjIso` uses on underlying morphisms.
@[expose] noncomputable def tensorObj (M N : Mod C A) : Mod C A :=
  (Bimod.toLeftMod _ _).obj (toBimod.obj M ⊗ toBimod.obj N)

/-- The bimodule associated with `M ⊗_A N` is the tensor product of the bimodules associated with
`M` and `N`. The comparison is the identity on the common carrier. -/
noncomputable def toBimodTensorObjIso (M N : Mod C A) :
    toBimod.obj M ⊗ toBimod.obj N ≅ toBimod.obj (tensorObj M N) :=
  (Bimod.toLeftModToBimodIsoOfActRightEq _
    (Bimod.tensorBimod_actRight_eq (toBimod.obj M) (toBimod.obj N) rfl rfl)).symm

@[simp]
theorem toBimodTensorObjIso_hom_hom (M N : Mod C A) :
    (toBimodTensorObjIso M N).hom.hom = 𝟙 _ := by
  simp [toBimodTensorObjIso]
  rfl

@[simp]
theorem toBimodTensorObjIso_inv_hom (M N : Mod C A) :
    (toBimodTensorObjIso M N).inv.hom = 𝟙 _ := by
  simp [toBimodTensorObjIso]
  rfl

/-- The balanced tensor product, with the monoidal data of bimodules conjugated by
`toBimodTensorObjIso`. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct (Mod C A) where
  tensorObj := tensorObj
  whiskerLeft M _ _ g := fullyFaithfulToBimod.preimage
    ((toBimodTensorObjIso M _).inv ≫ (toBimod.obj M ◁ toBimod.map g) ≫
      (toBimodTensorObjIso M _).hom)
  whiskerRight f N := fullyFaithfulToBimod.preimage
    ((toBimodTensorObjIso _ N).inv ≫ (toBimod.map f ▷ toBimod.obj N) ≫
      (toBimodTensorObjIso _ N).hom)
  tensorHom f g := fullyFaithfulToBimod.preimage
    ((toBimodTensorObjIso _ _).inv ≫ (toBimod.map f ⊗ₘ toBimod.map g) ≫
      (toBimodTensorObjIso _ _).hom)
  tensorUnit := regular A
  associator M N P := fullyFaithfulToBimod.preimageIso
    (((toBimodTensorObjIso _ _).symm ≪≫ ((toBimodTensorObjIso _ _).symm ⊗ᵢ .refl _))
      ≪≫ α_ (toBimod.obj M) (toBimod.obj N) (toBimod.obj P)
      ≪≫ ((.refl _ ⊗ᵢ toBimodTensorObjIso _ _) ≪≫ toBimodTensorObjIso _ _))
  leftUnitor M := fullyFaithfulToBimod.preimageIso
    (((toBimodTensorObjIso _ _).symm ≪≫ (toBimodRegularIso ⊗ᵢ .refl _)) ≪≫
      λ_ (toBimod.obj M))
  rightUnitor M := fullyFaithfulToBimod.preimageIso
    (((toBimodTensorObjIso _ _).symm ≪≫ (.refl _ ⊗ᵢ toBimodRegularIso)) ≪≫
      ρ_ (toBimod.obj M))

/-- The data inducing the monoidal structure of `Mod C A` from that of bimodules along `toBimod`. -/
noncomputable def inducingFunctorData : Monoidal.InducingFunctorData (toBimod (A := A)) where
  μIso := toBimodTensorObjIso
  whiskerLeft_eq _ _ _ _ := fullyFaithfulToBimod.map_preimage _
  whiskerRight_eq _ _ := fullyFaithfulToBimod.map_preimage _
  tensorHom_eq _ _ := fullyFaithfulToBimod.map_preimage _
  εIso := toBimodRegularIso.symm
  associator_eq _ _ _ := fullyFaithfulToBimod.map_preimage _
  leftUnitor_eq _ := fullyFaithfulToBimod.map_preimage _
  rightUnitor_eq _ := fullyFaithfulToBimod.map_preimage _

/-- Modules over a commutative monoid object form a monoidal category under the balanced tensor
product, with unit the regular module. -/
noncomputable instance monoidalCategory : MonoidalCategory (Mod C A) :=
  Monoidal.induced toBimod inducingFunctorData

/-- Regarding modules over a commutative monoid object as bimodules is a monoidal functor. -/
noncomputable instance : (toBimod (A := A)).Monoidal :=
  Monoidal.fromInducedMonoidal toBimod inducingFunctorData

/-- The quotient map `M ⊗ N ⟶ M ⊗_A N` onto the balanced tensor product. -/
noncomputable def tensorπ (M N : Mod C A) : M.X ⊗ N.X ⟶ (M ⊗ N).X :=
  coequalizer.π _ _

/-- The quotient map onto `M ⊗_A N` identifies the action of `A` on `M` with that on `N`. -/
@[reassoc]
theorem tensorπ_condition (M N : Mod C A) :
    ((β_ A M.X).inv ≫ γ[A, M.X]) ▷ N.X ≫ tensorπ M N =
      (α_ M.X A N.X).hom ≫ M.X ◁ γ[A, N.X] ≫ tensorπ M N :=
  (coequalizer.condition _ _).trans (Category.assoc _ _ _)

instance (M N : Mod C A) : Epi (tensorπ M N) :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- Morphisms out of `M ⊗_A N` are determined by their composites with the quotient map. -/
@[ext]
theorem tensor_hom_ext {M N : Mod C A} {Z : C} {f g : (M ⊗ N).X ⟶ Z}
    (h : tensorπ M N ≫ f = tensorπ M N ≫ g) : f = g :=
  (cancel_epi _).1 h

/-- A morphism out of `M ⊗ N` identifying the actions of `A` on `M` and on `N` factors through
the balanced tensor product. -/
noncomputable def tensorDesc {M N : Mod C A} {Z : C} (f : M.X ⊗ N.X ⟶ Z)
    (hf : ((β_ A M.X).inv ≫ γ[A,M.X]) ▷ N.X ≫ f = (α_ M.X A N.X).hom ≫ M.X ◁ γ[A,N.X] ≫ f) :
    (M ⊗ N).X ⟶ Z :=
  coequalizer.desc f (by simpa using hf)

/-- The factorization through the balanced tensor product restricts to the given morphism. -/
@[reassoc (attr := simp)]
theorem tensorπ_tensorDesc {M N : Mod C A} {Z : C} (f : M.X ⊗ N.X ⟶ Z)
    (hf : ((β_ A M.X).inv ≫ γ[A,M.X]) ▷ N.X ≫ f = (α_ M.X A N.X).hom ≫ M.X ◁ γ[A,N.X] ≫ f) :
    tensorπ M N ≫ tensorDesc f hf = f :=
  coequalizer.π_desc _ _

/-- The scalars act on `M ⊗_A N` through `M`. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_tensorπ_smul (M N : Mod C A) :
    A ◁ tensorπ M N ≫ γ[A, (M ⊗ N).X] = (α_ A M.X N.X).inv ≫ γ[A, M.X] ▷ N.X ≫ tensorπ M N :=
  Bimod.TensorBimod.whiskerLeft_π_actLeft (toBimod.obj M) (toBimod.obj N)

/- The comparison `toBimodTensorObjIso` is the identity between carriers which agree only after
unfolding `tensorObj`, so cancelling it uses `erw`. -/
private lemma hom_eq_of_toBimod_map_eq {M₁ N₁ M₂ N₂ : Mod C A} {f : M₁ ⊗ N₁ ⟶ M₂ ⊗ N₂}
    {φ : toBimod.obj M₁ ⊗ toBimod.obj N₁ ⟶ toBimod.obj M₂ ⊗ toBimod.obj N₂}
    (h : toBimod.map f = (toBimodTensorObjIso M₁ N₁).inv ≫ φ ≫ (toBimodTensorObjIso M₂ N₂).hom) :
    f.hom = φ.hom := by
  have := congrArg Bimod.Hom.hom h
  simp only [Bimod.comp_hom', toBimodTensorObjIso_inv_hom,
    toBimodTensorObjIso_hom_hom] at this
  erw [Category.id_comp, Category.comp_id] at this
  exact this

@[reassoc (attr := simp)]
theorem tensorπ_whiskerLeft_hom (M : Mod C A) {N N' : Mod C A} (g : N ⟶ N') :
    tensorπ M N ≫ (M ◁ g).hom = M.X ◁ g.hom ≫ tensorπ M N' := by
  rw [hom_eq_of_toBimod_map_eq (inducingFunctorData.whiskerLeft_eq M g)]
  exact ι_colimMap _ _

@[reassoc (attr := simp)]
theorem tensorπ_whiskerRight_hom {M M' : Mod C A} (f : M ⟶ M') (N : Mod C A) :
    tensorπ M N ≫ (f ▷ N).hom = f.hom ▷ N.X ≫ tensorπ M' N := by
  rw [hom_eq_of_toBimod_map_eq (inducingFunctorData.whiskerRight_eq f N)]
  exact ι_colimMap _ _

@[reassoc (attr := simp)]
theorem tensorπ_tensorHom_hom {M M' N N' : Mod C A} (f : M ⟶ M') (g : N ⟶ N') :
    tensorπ M N ≫ (f ⊗ₘ g).hom = (f.hom ⊗ₘ g.hom) ≫ tensorπ M' N' := by
  simp [MonoidalCategory.tensorHom_def]

@[reassoc]
theorem tensorπ_associator_hom_hom (M N P : Mod C A) :
    tensorπ M N ▷ P.X ≫ tensorπ (M ⊗ N) P ≫ (α_ M N P).hom.hom =
      (α_ M.X N.X P.X).hom ≫ M.X ◁ tensorπ N P ≫ tensorπ M (N ⊗ P) := by
  have h : toBimod.map (α_ M N P).hom = (toBimodTensorObjIso (M ⊗ N) P).inv ≫
      ((toBimodTensorObjIso M N).inv ▷ toBimod.obj P ≫
        (α_ (toBimod.obj M) (toBimod.obj N) (toBimod.obj P)).hom ≫
          toBimod.obj M ◁ (toBimodTensorObjIso N P).hom) ≫
      (toBimodTensorObjIso M (N ⊗ P)).hom := by
    rw [inducingFunctorData.associator_eq]
    simp [inducingFunctorData]
  rw [hom_eq_of_toBimod_map_eq h]
  simp only [Bimod.comp_hom', tensorπ]
  -- The conjugating comparisons are identities between coequalizers of equal, but not
  -- syntactically equal, pairs of morphisms; `erw` rewrites through their carriers.
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one, toBimodTensorObjIso_inv_hom]
  erw [id_whiskerRight, Category.id_comp,
    Bimod.π_associator_hom_hom_assoc (toBimod.obj M) (toBimod.obj N) (toBimod.obj P)]
  erw [ι_colimMap]
  simp only [parallelPairHom_app_one, toBimodTensorObjIso_hom_hom]
  erw [whiskerLeft_id, Category.id_comp]
  rfl

@[reassoc (attr := simp)]
theorem tensorπ_leftUnitor_hom_hom (M : Mod C A) :
    tensorπ (𝟙_ (Mod C A)) M ≫ (λ_ M).hom.hom = γ[A, M.X] := by
  have h : toBimod.map (λ_ M).hom = (toBimodTensorObjIso (𝟙_ (Mod C A)) M).inv ≫
      (toBimodRegularIso.hom ▷ toBimod.obj M) ≫ (λ_ (toBimod.obj M)).hom := by
    rw [inducingFunctorData.leftUnitor_eq]
    simp [inducingFunctorData]
  -- As for the associator, the comparisons are identities on carriers agreeing up to unfolding.
  have h' := congrArg Bimod.Hom.hom h
  simp only [Bimod.comp_hom', toBimodTensorObjIso_inv_hom] at h'
  erw [Category.id_comp] at h'
  rw [h', tensorπ]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one, toBimodRegularIso_hom_hom]
  erw [eqToHom_refl, id_whiskerRight, Category.id_comp]
  exact Bimod.π_leftUnitor_hom_hom (toBimod.obj M)

@[reassoc (attr := simp)]
theorem tensorπ_rightUnitor_hom_hom (M : Mod C A) :
    tensorπ M (𝟙_ (Mod C A)) ≫ (ρ_ M).hom.hom = (β_ A M.X).inv ≫ γ[A, M.X] := by
  have h : toBimod.map (ρ_ M).hom = (toBimodTensorObjIso M (𝟙_ (Mod C A))).inv ≫
      (toBimod.obj M ◁ toBimodRegularIso.hom) ≫ (ρ_ (toBimod.obj M)).hom := by
    rw [inducingFunctorData.rightUnitor_eq]
    simp [inducingFunctorData]
  -- As for the associator, the comparisons are identities on carriers agreeing up to unfolding.
  have h' := congrArg Bimod.Hom.hom h
  simp only [Bimod.comp_hom', toBimodTensorObjIso_inv_hom] at h'
  erw [Category.id_comp] at h'
  rw [h', tensorπ]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one, toBimodRegularIso_hom_hom]
  erw [eqToHom_refl, whiskerLeft_id, Category.id_comp]
  exact Bimod.π_rightUnitor_hom_hom (toBimod.obj M)

end Mod

end CategoryTheory
