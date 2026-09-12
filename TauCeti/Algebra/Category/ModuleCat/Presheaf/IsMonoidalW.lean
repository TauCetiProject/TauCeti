/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Local isomorphisms of presheaves of modules are stable under tensor products

Let `R` be a presheaf of commutative rings on a small site `(C, J)`. A morphism `f` of presheaves
of `R`-modules is a *local isomorphism* when its underlying morphism of presheaves of abelian
groups lies in `J.W`, i.e. becomes an isomorphism after sheafification. This file proves that the
sectionwise tensor product of presheaves of modules preserves local isomorphisms in each variable:
the morphism property `J.W.inverseImage (PresheafOfModules.toPresheaf _)` is monoidal.

This is the input needed to compare iterated sheafified tensor products of sheaves of modules:
sheafifying `M ⊗ N` before tensoring with `P` does not change the sheafification of the result.

## Main declarations

* `PresheafOfModules.isLocallySurjective_whiskerLeft`: tensoring with any presheaf of modules
  preserves local surjectivity;
* `PresheafOfModules.isLocallyInjective_free_whiskerLeft`: tensoring with a free presheaf of
  modules preserves local injectivity;
* `PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft` and
  `PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight`: tensoring with any presheaf of
  modules preserves local isomorphisms;
* `PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`: the resulting `IsMonoidal` instance.

## Proof

For free presheaves of modules the statement is checked on sections: a section of
`free F ⊗ N` over `U` is a finite sum `∑ z ⊗ n_z` indexed by distinct elements `z` of `F(U)`, and
it is killed by `free F ◁ f` exactly when every coefficient `n_z` is killed by `f`. Local
injectivity of `f` then makes all the coefficients vanish on a common covering sieve.
A general presheaf of modules is a cokernel of a morphism between coproducts of free presheaves
of modules (`PresheafOfModules.isColimitFreeYonedaCoproductsCokernelCofork`). Tensoring preserves
colimits, and local isomorphisms are stable under colimits because sheafification preserves them,
so the statement passes from free presheaves to all presheaves of modules. No formalization is
vendored.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite TensorProduct

namespace TauCeti

universe u

section Algebra

variable {S : Type*} [CommRing S] {ι : Type*} {B B' : Type*} [AddCommGroup B] [Module S B]
  [AddCommGroup B'] [Module S B']

/-- The coefficients of `(1 ⊗ g) t` in the free module `(ι →₀ S) ⊗ B'` are the images under `g`
of the coefficients of `t`. -/
private lemma finsuppScalarLeft_lTensor_apply [DecidableEq ι] (g : B →ₗ[S] B')
    (t : (ι →₀ S) ⊗[S] B) (z : ι) :
    finsuppScalarLeft S B' ι (g.lTensor _ t) z = g (finsuppScalarLeft S B ι t z) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p n => simp
  | add a b ha hb => simp [ha, hb]

/-- An element of `(ι →₀ S) ⊗ B` is the sum of its coefficients against the basis vectors. -/
private lemma eq_sum_single_tmul [DecidableEq ι] (t : (ι →₀ S) ⊗[S] B) :
    t = ∑ z ∈ (finsuppScalarLeft S B ι t).support,
      Finsupp.single z (1 : S) ⊗ₜ finsuppScalarLeft S B ι t z := by
  conv_lhs => rw [← (finsuppScalarLeft S B ι).symm_apply_apply t,
    ← Finsupp.sum_single (finsuppScalarLeft S B ι t)]
  simp [Finsupp.sum, finsuppScalarLeft_symm_apply_single]

end Algebra

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Tensoring with a presheaf of modules `P` preserves local surjectivity: a section of
`P ⊗ N'` is locally a sum of elementary tensors whose second factors lift along `f`. -/
theorem _root_.PresheafOfModules.isLocallySurjective_whiskerLeft
    (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (f : N ⟶ N') [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map (P ◁ f)) where
  imageSieve_mem {U} t := by
    change (P.obj (op U) ⊗ N'.obj (op U) : ModuleCat _) at t
    induction t using TensorProduct.induction_on with
    | zero =>
      refine J.superset_covering ?_ (J.top_mem U)
      rintro V g -
      exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
    | tmul p n' =>
      refine J.superset_covering ?_
        (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) n')
      rintro V g ⟨n, hn⟩
      refine ⟨P.map g.op p ⊗ₜ n, ?_⟩
      change P.map g.op p ⊗ₜ f.app (op V) n = (P ⊗ N').map g.op (p ⊗ₜ n')
      change f.app (op V) n = N'.map g.op n' at hn
      rw [hn]
      rfl
    | add a b ha hb =>
      refine J.superset_covering ?_ (J.intersection_covering ha hb)
      rintro V g ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
      exact ⟨a' + b', (map_add _ a' b').trans
        ((congrArg₂ (· + ·) ha' hb').trans (map_add _ a b).symm)⟩

/-- Tensoring with the free presheaf of modules on a presheaf of types `F` preserves local
injectivity. A section of `free F ⊗ N` killed by `free F ◁ f` has all its coefficients killed by
`f`, and these finitely many coefficients vanish together on a covering sieve. -/
theorem _root_.PresheafOfModules.isLocallyInjective_free_whiskerLeft (F : Cᵒᵖ ⥤ Type u)
    {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : N ⟶ N')
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map ((PresheafOfModules.free _).obj F ◁ f)) where
  equalizerSieve_mem {U} x y hxy := by
    classical
    let e := finsuppScalarLeft ((R ⋙ forget₂ _ RingCat).obj U) (N.obj U) (F.obj U)
    let t : (F.obj U →₀ (R ⋙ forget₂ _ RingCat).obj U) ⊗[(R ⋙ forget₂ _ RingCat).obj U]
      N.obj U := x - y
    have ht : (f.app U).hom.lTensor _ t = 0 := (map_sub _ x y).trans (sub_eq_zero.2 hxy)
    have hz : ∀ z ∈ (e t).support, Presheaf.equalizerSieve
        (F := (PresheafOfModules.toPresheaf _).obj N) (e t z) 0 ∈ J U.unop := fun z _ ↦
      Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map f) _ _ <| by
        have := congrArg (fun s ↦ finsuppScalarLeft ((R ⋙ forget₂ _ RingCat).obj U) (N'.obj U)
          (F.obj U) s z) ht
        simp only [finsuppScalarLeft_lTensor_apply, map_zero, Finsupp.coe_zero,
          Pi.zero_apply] at this
        exact this.trans (map_zero _).symm
    refine J.superset_covering ?_ (Finset.inf_induction (J.top_mem _)
      (fun _ h₁ _ h₂ ↦ J.intersection_covering h₁ h₂) hz)
    intro V g hg
    have hg' : ∀ z ∈ (e t).support, N.map g.op (e t z) = 0 := fun z hz ↦
      (Finset.inf_le (f := fun z ↦ Presheaf.equalizerSieve
        (F := (PresheafOfModules.toPresheaf _).obj N) (e t z) 0) hz g hg).trans (map_zero _)
    have key : ((PresheafOfModules.free _).obj F ⊗ N).map g.op t = 0 := by
      refine (congrArg _ (eq_sum_single_tmul t)).trans
        ((map_sum _ _ _).trans (Finset.sum_eq_zero fun z hz ↦ ?_))
      change _ ⊗ₜ N.map g.op (e t z) = 0
      exact (congrArg _ (hg' z hz)).trans (tmul_zero _ _)
    exact sub_eq_zero.1 ((map_sub _ x y).symm.trans key)

variable [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Local isomorphisms of presheaves of modules are stable under every shape of colimits which
the forgetful functor to presheaves of abelian groups and sheafification preserve. -/
private lemma isStableUnderColimitsOfShape_inverseImage_W_toPresheaf (K : Type*) [Category K]
    [PreservesColimitsOfShape K (PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ _ _))]
    [PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{u})] :
    MorphismProperty.IsStableUnderColimitsOfShape ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (R ⋙ forget₂ _ _))) K where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    let G := PresheafOfModules.toPresheaf (R ⋙ forget₂ _ _) ⋙
      presheafToSheaf J AddCommGrpCat.{u}
    have : PreservesColimitsOfShape K G := comp_preservesColimitsOfShape _ _
    have hW : ∀ {M M' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ M'),
        (J.W (A := AddCommGrpCat.{u})).inverseImage
          (PresheafOfModules.toPresheaf (R ⋙ forget₂ _ _)) g ↔ IsIso (G.map g) := fun g ↦ by
      rw [MorphismProperty.inverseImage_iff, J.W_eq_inverseImage_isomorphisms]
      rfl
    rw [hW]
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition (W := .isomorphisms _)
      (X₁ ⋙ G) (X₂ ⋙ G) (G.mapCocone c₁) (G.mapCocone c₂) (isColimitOfPreserves G h₁)
      (isColimitOfPreserves G h₂) (Functor.whiskerRight f G) (fun k ↦ (hW _).1 (hf k))
      (G.map φ) (fun k ↦ by simp [G, ← Functor.map_comp, hφ])

/-- If tensoring with each term of a diagram preserves a local isomorphism `f`, then so does
tensoring with the colimit of the diagram. -/
private lemma inverseImage_W_toPresheaf_whiskerLeft_of_isColimit {K : Type*} [Category K]
    [PreservesColimitsOfShape K (PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ _ _))]
    [∀ N : PresheafOfModules.{u} (R ⋙ forget₂ _ _), PreservesColimitsOfShape K (tensorRight N)]
    {D : K ⥤ PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {c : Cocone D} (hc : IsColimit c)
    {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : N ⟶ N')
    (hD : ∀ k, (J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf _) (D.obj k ◁ f)) :
    (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) (c.pt ◁ f) :=
  (isStableUnderColimitsOfShape_inverseImage_W_toPresheaf J K).condition
    (D ⋙ tensorRight N) (D ⋙ tensorRight N')
    ((tensorRight N).mapCocone c) ((tensorRight N').mapCocone c) (isColimitOfPreserves _ hc)
    (isColimitOfPreserves _ hc) (Functor.whiskerLeft D ((tensoringRight _).map f)) hD
    (c.pt ◁ f) (fun _ ↦ (whisker_exchange _ _).symm)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Tensoring with a presheaf of modules on the left preserves local isomorphisms. -/
theorem _root_.PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft
    (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    {f : N ⟶ N'}
    (hf : (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) f) :
    (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) (P ◁ f) := by
  rw [MorphismProperty.inverseImage_iff, J.W_iff_isLocallyBijective] at hf
  obtain ⟨_, _⟩ := hf
  have hfree (F : Cᵒᵖ ⥤ Type u) : (J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf _) ((PresheafOfModules.free _).obj F ◁ f) := by
    have := PresheafOfModules.isLocallySurjective_whiskerLeft J
      ((PresheafOfModules.free _).obj F) f
    have := PresheafOfModules.isLocallyInjective_free_whiskerLeft J F f
    exact J.W_of_isLocallyBijective _
  have hcoprod (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
      (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _)
        (M.freeYonedaCoproduct ◁ f) :=
    inverseImage_W_toPresheaf_whiskerLeft_of_isColimit J (colimit.isColimit _) f
      fun _ ↦ hfree _
  exact inverseImage_W_toPresheaf_whiskerLeft_of_isColimit J
    P.isColimitFreeYonedaCoproductsCokernelCofork f (by rintro (_ | _) <;> exact hcoprod _)

/-- Tensoring with a presheaf of modules on the right preserves local isomorphisms. -/
theorem _root_.PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight
    {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {f : N ⟶ N'}
    (hf : (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) f)
    (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) (f ▷ P) :=
  (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (β_ N P) (β_ N' P))).2
    (PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft J P hf)

/-- Local isomorphisms of presheaves of modules form a monoidal morphism property. -/
instance _root_.PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf :
    MorphismProperty.IsMonoidal ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ _ _))) where
  whiskerLeft P _ _ _ hg := PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft J P hg
  whiskerRight _ hf P := PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight J hf P

end TauCeti
