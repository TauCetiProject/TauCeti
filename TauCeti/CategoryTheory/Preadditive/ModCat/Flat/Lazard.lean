/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Factorization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import TauCeti.CategoryTheory.Preadditive.ModCat.Evaluation

/-!
# The Lazard–Govorov presentation of flat modules

For a module `F` over a preadditive category, the category of maps from finite sums
of representables to `F` is filtered precisely when `F` is flat. If `F` is flat and
the source category is essentially small in the morphism universe, this category
admits a small model and its tautological diagram presents `F` as a filtered colimit.
The empty sum provides an object of the diagram even if the source category is empty.

The finite-free factorization argument is the categorical analogue of Lazard's
*Autour de la platitude*, Chapter I, Theorem 1.2. The category of maps to a module is
the finite-sum version of Crawley-Boevey's category of elements in *Locally finitely
presented additive categories*, §1.2, Lemma 1 and §1.3, Theorem. The pointwise colimit
argument follows the method of `TauCeti.flatModuleFilteredFree` for ring modules.
-/

public section

noncomputable section

universe v u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {F : ModCat.{v} C}

/-- Maps from finite free modules to `F`, with morphisms the commuting triangles over `F`. -/
abbrev FiniteFreeOver (F : ModCat.{v} C) :=
  CostructuredArrow (isFiniteFree C).ι F

namespace FiniteFreeOver

/-- A map from a finite free module defines an object over `F`. -/
abbrev mk (W : ModCat.{v} C) (hW : isFiniteFree C W) (f : W ⟶ F) : FiniteFreeOver F :=
  CostructuredArrow.mk (Y := ObjectProperty.FullSubcategory.mk W hW) f

/-- A map between finite free modules that commutes with their maps to `F` defines a morphism
over `F`. -/
def homMk {i j : FiniteFreeOver F} (a : i.left.obj ⟶ j.left.obj)
    (h : a ≫ j.hom = i.hom) : i ⟶ j :=
  CostructuredArrow.homMk (ObjectProperty.homMk a) h

/-- The underlying module map of `homMk a h` is `a`. -/
@[simp]
theorem homMk_left_hom {i j : FiniteFreeOver F} (a : i.left.obj ⟶ j.left.obj)
    (h : a ≫ j.hom = i.hom) : (homMk a h).left.hom = a :=
  (rfl)

@[simp]
private theorem comp_left_hom {i j k : FiniteFreeOver F} (f : i ⟶ j) (g : j ⟶ k) :
    (f ≫ g).left.hom = f.left.hom ≫ g.left.hom := by
  rw [CostructuredArrow.comp_left, ObjectProperty.FullSubcategory.comp_hom]

end FiniteFreeOver

/-- The arrow from the empty sum of representables gives an object over every module. -/
instance (F : ModCat.{v} C) : Nonempty (FiniteFreeOver F) :=
  ⟨FiniteFreeOver.mk _ (isFiniteFree_biproduct_yoneda (Fin.elim0 : Fin 0 → C)) 0⟩

/-- Biproducts provide common targets, and flatness coequalizes parallel arrows. -/
instance (F : ModCat.{v} C) [F.Flat] : IsFiltered (FiniteFreeOver F) where
  cocone_objs i j := by
    let k := FiniteFreeOver.mk _ (isFiniteFree_biprod i.left.property j.left.property)
      (biprod.desc i.hom j.hom)
    refine ⟨k, FiniteFreeOver.homMk biprod.inl ?_, FiniteFreeOver.homMk biprod.inr ?_, trivial⟩
    · simp only [k, CostructuredArrow.mk_hom_eq_self, biprod.inl_desc]
    · simp only [k, CostructuredArrow.mk_hom_eq_self, biprod.inr_desc]
  cocone_maps {i j} f g := by
    have h : (f.left.hom - g.left.hom) ≫ j.hom = 0 := by
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact (CostructuredArrow.w f).trans (CostructuredArrow.w g).symm
    obtain ⟨W, hW, a, b, hab, ha⟩ :=
      Flat.exists_factorization_of_comp_eq_zero i.left.property j.left.property _ j.hom h
    let k : FiniteFreeOver F := FiniteFreeOver.mk W hW b
    refine ⟨k, FiniteFreeOver.homMk a hab, ?_⟩
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    simpa only [FiniteFreeOver.comp_left_hom, FiniteFreeOver.homMk_left_hom,
      Preadditive.sub_comp, sub_eq_zero] using ha

/-- Equational flatness is equivalent to filteredness of the maps from finite free modules. -/
theorem flat_iff_isFiltered_finiteFreeOver : F.Flat ↔ IsFiltered (FiniteFreeOver F) := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ flat_iff_forall_exists_factorization.mpr ?_⟩
  intro P hP f
  obtain ⟨U, V, hU, hV, d, p, hp, ⟨hc⟩⟩ :=
    isFinitelyPresentedFunctor_iff_exists_finiteFree_presentation.mp hP
  let i : FiniteFreeOver F := FiniteFreeOver.mk U hU 0
  let j : FiniteFreeOver F := FiniteFreeOver.mk V hV (p ≫ f)
  let a : i ⟶ j := FiniteFreeOver.homMk d (by simp [i, j, ← Category.assoc, hp])
  let b : i ⟶ j := FiniteFreeOver.homMk 0 (by simp [i])
  obtain ⟨k, g, hg⟩ := IsFilteredOrEmpty.cocone_maps a b
  have hz : d ≫ g.left.hom = 0 := by
    simpa only [FiniteFreeOver.comp_left_hom, a, b, FiniteFreeOver.homMk_left_hom, zero_comp]
      using congrArg (fun t : i ⟶ k ↦ t.left.hom) hg
  obtain ⟨q, hq⟩ := CokernelCofork.IsColimit.desc' hc g.left.hom hz
  refine ⟨k.left.obj, k.left.property, q, k.hom, Cofork.IsColimit.hom_ext hc ?_⟩
  have hq' : p ≫ q = g.left.hom := by simpa only [CokernelCofork.π_ofπ] using hq
  have hw : g.left.hom ≫ k.hom = p ≫ f := CostructuredArrow.w g
  simpa only [CokernelCofork.π_ofπ, reassoc_of% hq'] using hw

/-- The category of finite free modules over a module is essentially small in the morphism
universe whenever the source category is. -/
instance essentiallySmall_finiteFreeOver (F : ModCat.{v} C) [EssentiallySmall.{v} C] :
    EssentiallySmall.{v} (FiniteFreeOver F) := by
  let e := (equivSmallModel.{v} Cᵒᵖ).congrLeft (E := AddCommGrpCat.{v})
  have : LocallySmall.{v} (Cᵒᵖ ⥤ AddCommGrpCat.{v}) := locallySmall_of_faithful e.functor
  exact inferInstanceAs (EssentiallySmall (CostructuredArrow (isFiniteFree C).ι F))

private def isColimit_forgetEval_finiteFreeOver [F.Flat] (X : C) :
    IsColimit ((forgetEval X).mapCocone
      ((Functor.LeftExtension.mk (𝟭 _) (isFiniteFree C).ι.rightUnitor.inv).coconeAt F)) := by
  let E := forgetEval X
  let c := (Functor.LeftExtension.mk (𝟭 _) (isFiniteFree C).ι.rightUnitor.inv).coconeAt F
  let generator : E.obj ((yoneda C).obj X) := 𝟙 X
  have leg (i : FiniteFreeOver F) (x : E.obj i.left.obj) :
      (E.mapCocone c).ι.app i x = E.map i.hom x := by
    have h : c.ι.app i = i.hom := by
      simp only [c, Functor.LeftExtension.coconeAt_ι_app, Functor.LeftExtension.mk_hom,
        Functor.LeftExtension.mk_right, Functor.rightUnitor_inv_app, Functor.id_map]
      exact Category.id_comp _
    rw [Functor.mapCocone_ι_app, h]
  have transition {i j : FiniteFreeOver F} (f : i ⟶ j) :
      ((CostructuredArrow.proj (isFiniteFree C).ι F ⋙ (isFiniteFree C).ι) ⋙ E).map f =
        E.map f.left.hom := by
    simp only [Functor.comp_map, CostructuredArrow.proj_map, ObjectProperty.ι_map]
  have lift (G : ModCat.{v} C) (x : E.obj G) :
      ∃ p : (yoneda C).obj X ⟶ G, E.map p generator = x := by
    obtain ⟨p, hp⟩ := exists_biproduct_desc_app_id (Y := fun _ : Fin 1 ↦ X) fun _ ↦ x
    let a := biproduct.ι ((yoneda C).obj ∘ fun _ : Fin 1 ↦ X) 0 ≫ p
    exact ⟨a, (forgetEval_map_apply X a generator).trans (hp 0)⟩
  have hY := isFiniteFree_yoneda_obj X
  refine Types.FilteredColimit.isColimitOf' _ (E.mapCocone c) ?_ ?_
  · -- Every element comes from the identity generator of a representable.
    intro x
    obtain ⟨p, hp⟩ := lift F x
    let i : FiniteFreeOver F := FiniteFreeOver.mk _ hY p
    exact ⟨i, generator, ((leg i _).trans hp).symm⟩
  · -- Equality in `F` gives two parallel arrows over `F` from that representable.
    intro i x y h
    rw [leg, leg] at h
    obtain ⟨p, hp⟩ := lift i.left.obj x
    obtain ⟨q, hq⟩ := lift i.left.obj y
    have w : p ≫ i.hom = q ≫ i.hom := by
      suffices E.map (p ≫ i.hom) generator = E.map (q ≫ i.hom) generator from
        yoneda_hom_ext_of_forgetEval this
      simpa only [E.map_comp_apply, hp, hq] using h
    let k : FiniteFreeOver F := FiniteFreeOver.mk _ hY (p ≫ i.hom)
    let a : k ⟶ i := FiniteFreeOver.homMk p rfl
    let b : k ⟶ i := FiniteFreeOver.homMk q w.symm
    obtain ⟨l, f, hf⟩ := IsFilteredOrEmpty.cocone_maps a b
    refine ⟨l, f, ?_⟩
    have he : p ≫ f.left.hom = q ≫ f.left.hom := by
      simpa only [FiniteFreeOver.comp_left_hom, a, b, FiniteFreeOver.homMk_left_hom]
        using congrArg (fun t : k ⟶ l ↦ t.left.hom) hf
    rw [transition]
    simpa only [E.map_comp_apply, hp, hq] using
      congrArg (fun t : (yoneda C).obj X ⟶ l.left.obj ↦ E.map t generator) he

/-- For a flat module, the given arrows from its finite free modules form a colimit cocone. -/
def Flat.denseAtIsFiniteFreeι [EssentiallySmall.{v} C] [F.Flat] :
    (isFiniteFree C).ι.DenseAt F := by
  -- Use the small model to obtain reflection by the forgetful functor.
  let e := (equivSmallModel.{v} (FiniteFreeOver F)).symm
  have := IsFiltered.of_equivalence e.symm
  let U := forget AddCommGrpCat.{v}
  have : HasColimitsOfShape (FiniteFreeOver F) AddCommGrpCat.{v} :=
    hasColimitsOfShape_of_equivalence e
  have : PreservesColimitsOfShape (FiniteFreeOver F) U := preservesColimitsOfShape_of_equiv e U
  have : ReflectsColimitsOfShape (FiniteFreeOver F) U :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine (Functor.denseAtEquiv (isFiniteFree C).ι F).symm ?_
  apply isColimitOfReflects (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι
  apply evaluationJointlyReflectsColimits
  intro X
  apply isColimitOfReflects U
  exact isColimit_forgetEval_finiteFreeOver X.unop

/-- A flat module over an essentially small preadditive category is a small filtered colimit of
finite free modules. -/
theorem Flat.ind_isFiniteFree [EssentiallySmall.{v} C] [F.Flat] :
    (isFiniteFree C).ind.{v} F :=
  ObjectProperty.of_essentiallySmall_index
    (J := FiniteFreeOver F) ⟨_, _, Flat.denseAtIsFiniteFreeι⟩ fun i ↦ i.left.property

end TauCeti.ModCat
