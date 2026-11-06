/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.CategoryTheory.Preadditive.Yoneda

/-!
# Finitely presented functors

Let `C` be a preadditive category. A functor `F : Cᵒᵖ ⥤ AddCommGrpCat` is *finitely generated*
if it is a quotient of a representable functor `(-, Y) = preadditiveYoneda.obj Y`, and *finitely
presented* if there is an exact sequence `(-, X) ⟶ (-, Y) ⟶ F ⟶ 0` coming from a morphism
`f : X ⟶ Y` of `C`. Following Auslander (*Coherent functors*, 1966), the finitely presented
functors form the category `mod C`, the natural home of the functorial approach to
Auslander-Reiten theory: almost-split sequences become minimal projective resolutions of simple
functors.

This file sets up `mod C` as a property of objects of the abelian category of functors
`Cᵒᵖ ⥤ AddCommGrpCat`. A finitely presented functor is the cokernel of the image of a morphism of
`C`, and conversely (`isFinitelyPresentedFunctor_iff_exists_isColimit`). Finitely generated
functors, hence finitely presented ones, are additive. Representable functors are finitely
presented. When `C` has binary biproducts, the cokernel of a morphism from a finitely generated
functor to a finitely presented one is finitely presented: if `p : (-, Y) ⟶ F` is onto and
`G` is presented by `g : X' ⟶ Y'`, lift `p ≫ φ` to `(-, u)` for some `u : Y ⟶ Y'`; then the
cokernel of `φ` is presented by `g` and `u` together, as a morphism `X' ⊞ Y ⟶ Y'`. Finitely
presented functors are also closed under binary biproducts. So when `C` is additive, `mod C`
contains zero and is closed under isomorphisms, cokernels and finite products and coproducts in the
functor category.

## Main declarations

* `TauCeti.IsFinitelyGeneratedFunctor`, `TauCeti.IsFinitelyPresentedFunctor`: the two finiteness
  conditions, and `TauCeti.isFinitelyPresentedFunctor C`, the property of objects defining
  `mod C`.
* `TauCeti.isFinitelyPresentedFunctor_iff_exists_isColimit`: finitely presented functors are
  the cokernels of the images of morphisms of `C`.
* `TauCeti.IsFinitelyGeneratedFunctor.additive`: finitely generated functors are additive.
* `TauCeti.isFinitelyPresentedFunctor_preadditiveYoneda_obj`: representable functors are
  finitely presented.
* `TauCeti.IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork`: closure under cokernels of
  morphisms out of finitely generated functors.
* `TauCeti.IsFinitelyPresentedFunctor.biprod`: closure under binary biproducts.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A functor `F : Cᵒᵖ ⥤ AddCommGrpCat` is *finitely generated* if it is a quotient of a
representable functor `(-, Y)`. -/
def IsFinitelyGeneratedFunctor (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∃ (Y : C) (p : preadditiveYoneda.obj Y ⟶ F), Epi p

/-- A functor `F : Cᵒᵖ ⥤ AddCommGrpCat` is *finitely presented* if there is a morphism
`f : X ⟶ Y` of `C` and an exact sequence `(-, X) ⟶ (-, Y) ⟶ F ⟶ 0` whose first map is
`(-, f)`. -/
def IsFinitelyPresentedFunctor (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∃ (X Y : C) (f : X ⟶ Y) (p : preadditiveYoneda.obj Y ⟶ F)
    (h : preadditiveYoneda.map f ≫ p = 0), Epi p ∧ (ShortComplex.mk _ _ h).Exact

variable (C) in
/-- The finitely presented functors `Cᵒᵖ ⥤ AddCommGrpCat`, as a property of objects of the functor
category; its full subcategory is `mod C`. -/
abbrev isFinitelyPresentedFunctor : ObjectProperty (Cᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  IsFinitelyPresentedFunctor

variable {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}}

/-- A functor is finitely presented exactly when it is the cokernel of `(-, f)` for a morphism
`f` of `C`. -/
theorem isFinitelyPresentedFunctor_iff_exists_isColimit :
    IsFinitelyPresentedFunctor F ↔ ∃ (X Y : C) (f : X ⟶ Y) (p : preadditiveYoneda.obj Y ⟶ F)
      (h : preadditiveYoneda.map f ≫ p = 0), Nonempty (IsColimit (CokernelCofork.ofπ p h)) := by
  constructor
  · rintro ⟨X, Y, f, p, h, hp, hS⟩
    exact ⟨X, Y, f, p, h, ⟨hS.gIsCokernel⟩⟩
  · rintro ⟨X, Y, f, p, h, ⟨hc⟩⟩
    exact ⟨X, Y, f, p, h, Cofork.IsColimit.epi hc, ShortComplex.exact_of_g_is_cokernel _ hc⟩

/-- A finitely presented functor is finitely generated. -/
theorem IsFinitelyPresentedFunctor.isFinitelyGeneratedFunctor (hF : IsFinitelyPresentedFunctor F) :
    IsFinitelyGeneratedFunctor F := by
  obtain ⟨_, Y, _, p, _, hp, _⟩ := hF
  exact ⟨Y, p, hp⟩

/-- A quotient of a finitely generated functor is finitely generated. -/
theorem IsFinitelyGeneratedFunctor.of_epi (hF : IsFinitelyGeneratedFunctor F) (q : F ⟶ G)
    [Epi q] : IsFinitelyGeneratedFunctor G := by
  obtain ⟨Y, p, hp⟩ := hF
  exact ⟨Y, p ≫ q, epi_comp p q⟩

/-- A finitely generated functor is additive: it is a quotient of the additive functor `(-, Y)`.
-/
theorem IsFinitelyGeneratedFunctor.additive (hF : IsFinitelyGeneratedFunctor F) : F.Additive := by
  obtain ⟨Y, p, hp⟩ := hF
  refine ⟨fun {Z W a b} ↦ ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (p.app Z)).1 inferInstance x
  simp only [AddCommGrpCat.hom_add_apply, ← NatTrans.naturality_apply, Functor.map_add, map_add]

/-- A finitely presented functor is additive. -/
theorem IsFinitelyPresentedFunctor.additive (hF : IsFinitelyPresentedFunctor F) : F.Additive :=
  hF.isFinitelyGeneratedFunctor.additive

/-- Being finitely presented is invariant under isomorphism. -/
theorem IsFinitelyPresentedFunctor.of_iso (e : F ≅ G) (hF : IsFinitelyPresentedFunctor F) :
    IsFinitelyPresentedFunctor G := by
  obtain ⟨X, Y, f, p, h, ⟨hc⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hF
  exact isFinitelyPresentedFunctor_iff_exists_isColimit.2 ⟨X, Y, f, p ≫ e.hom,
    by rw [reassoc_of% h, zero_comp], ⟨IsColimit.ofIsoColimit hc (Cofork.ext e (by simp))⟩⟩

instance : (isFinitelyPresentedFunctor C).IsClosedUnderIsomorphisms where
  of_iso e hF := hF.of_iso e

/-- A representable functor `(-, Y)` is finitely presented, as the cokernel of `(-, 0)` for the
zero endomorphism of `Y`. -/
theorem isFinitelyPresentedFunctor_preadditiveYoneda_obj (Y : C) :
    IsFinitelyPresentedFunctor (preadditiveYoneda.obj Y) :=
  isFinitelyPresentedFunctor_iff_exists_isColimit.2 ⟨Y, Y, 0, 𝟙 _, by simp,
    ⟨CokernelCofork.IsColimit.ofId _ (Functor.map_zero _ _ _)⟩⟩

/-- A representable functor `(-, Y)` is finitely generated. -/
theorem isFinitelyGeneratedFunctor_preadditiveYoneda_obj (Y : C) :
    IsFinitelyGeneratedFunctor (preadditiveYoneda.obj Y) :=
  (isFinitelyPresentedFunctor_preadditiveYoneda_obj Y).isFinitelyGeneratedFunctor

open ZeroObject in
instance [HasZeroObject C] : (isFinitelyPresentedFunctor C).ContainsZero where
  exists_zero := ⟨_, preadditiveYoneda.map_isZero (isZero_zero C),
    isFinitelyPresentedFunctor_preadditiveYoneda_obj 0⟩

section Biproducts

variable [HasBinaryBiproducts C]

/-- The cokernel of a morphism from a finitely generated functor to a finitely presented functor
is finitely presented. -/
theorem IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork {φ : F ⟶ G}
    {c : CokernelCofork φ} (hc : IsColimit c) (hF : IsFinitelyGeneratedFunctor F)
    (hG : IsFinitelyPresentedFunctor G) : IsFinitelyPresentedFunctor c.pt := by
  obtain ⟨Y, p, hp⟩ := hF
  obtain ⟨X', Y', g, q, hgq, ⟨hq⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hG
  have : Epi q := Cofork.IsColimit.epi hq
  -- Lift `p ≫ φ` along the epimorphism `q` to `(-, u)`, for some `u : Y ⟶ Y'`.
  obtain ⟨u, hu⟩ := exists_preadditiveYoneda_map_comp_eq q (p ≫ φ)
  have hg : preadditiveYoneda.map g = preadditiveYoneda.map biprod.inl ≫
      preadditiveYoneda.map (biprod.desc g u) := by
    rw [← Functor.map_comp, biprod.inl_desc]
  have hu' : preadditiveYoneda.map u = preadditiveYoneda.map biprod.inr ≫
      preadditiveYoneda.map (biprod.desc g u) := by
    rw [← Functor.map_comp, biprod.inr_desc]
  have : Epi c.π := Cofork.IsColimit.epi hc
  -- `c.pt` is the cokernel of `(-, g ⊔ u) : (-, X' ⊞ Y) ⟶ (-, Y')`.
  refine isFinitelyPresentedFunctor_iff_exists_isColimit.2
    ⟨X' ⊞ Y, Y', biprod.desc g u, q ≫ c.π, ?_,
      ⟨CokernelCofork.IsColimit.ofπ' _ _ fun t ht ↦ ?_⟩⟩
  · simp [biprod.desc_eq, reassoc_of% hgq, reassoc_of% hu]
  · obtain ⟨t', ht'⟩ := CokernelCofork.IsColimit.desc' hq t (by rw [hg, Category.assoc, ht,
      comp_zero])
    rw [Cofork.π_ofπ] at ht'
    obtain ⟨t'', ht''⟩ := CokernelCofork.IsColimit.desc' hc t' (by
      rw [← cancel_epi p, ← reassoc_of% hu, ht', hu', Category.assoc, ht, comp_zero, comp_zero])
    exact ⟨t'', by rw [Category.assoc, ht'', ht']⟩

/-- A binary biproduct of finitely presented functors is finitely presented. -/
theorem IsFinitelyPresentedFunctor.biprod (hF : IsFinitelyPresentedFunctor F)
    (hG : IsFinitelyPresentedFunctor G) : IsFinitelyPresentedFunctor (F ⊞ G) := by
  obtain ⟨X₁, Y₁, f₁, p₁, h₁, ⟨hc₁⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hF
  obtain ⟨X₂, Y₂, f₂, p₂, h₂, ⟨hc₂⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hG
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v})
  have hnat := Functor.biprodComparison_natural preadditiveYoneda f₁ f₂
  simp only [Functor.biprodComparison, ← Functor.mapBiprod_hom] at hnat
  exact isFinitelyPresentedFunctor_iff_exists_isColimit.2 ⟨X₁ ⊞ X₂, Y₁ ⊞ Y₂, biprod.map f₁ f₂,
    _, _, ⟨CokernelCofork.isColimitOfIsColimitOfIff (CokernelCofork.isColimitBiprod hc₁ hc₂)
      (preadditiveYoneda.map (biprod.map f₁ f₂)) (preadditiveYoneda.mapBiprod Y₁ Y₂)
      (fun W ψ ↦ by
        rw [reassoc_of% hnat]
        exact (Preadditive.IsIso.comp_left_eq_zero _ _).symm)⟩⟩

instance : (isFinitelyPresentedFunctor C).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨_, k, hk, hF, hG⟩
    exact IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork hk hF.isFinitelyGeneratedFunctor hG

instance : (isFinitelyPresentedFunctor C).IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    refine (isFinitelyPresentedFunctor C).prop_of_iso ?_
      ((p.prop_diag_obj (.mk .left)).biprod (p.prop_diag_obj (.mk .right)))
    exact IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit _ _)
      ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm _).2 p.isColimit)

instance : (isFinitelyPresentedFunctor C).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (isFinitelyPresentedFunctor C).prop_of_iso ?_
      ((p.prop_diag_obj (.mk .left)).biprod (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

end Biproducts

instance [HasFiniteBiproducts C] :
    (isFinitelyPresentedFunctor C).IsClosedUnderFiniteCoproducts :=
  have := hasBinaryBiproducts_of_finite_biproducts C
  .mk'

instance [HasFiniteBiproducts C] : (isFinitelyPresentedFunctor C).IsClosedUnderFiniteProducts :=
  have := hasBinaryBiproducts_of_finite_biproducts C
  .mk'

end TauCeti
