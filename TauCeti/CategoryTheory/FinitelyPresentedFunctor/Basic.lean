/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic
public import TauCeti.CategoryTheory.Preadditive.AdditiveFunctor
public import TauCeti.CategoryTheory.Preadditive.Yoneda

/-!
# Finitely presented functors

Let `C` be a preadditive category. A functor `F : Cᵒᵖ ⥤ AddCommGrpCat` is *finitely generated*
if it is a quotient of a finite sum `(-, Y₁) ⊕ ⋯ ⊕ (-, Yₙ)` of representable functors
`(-, Y) = preadditiveYoneda.obj Y`, and *finitely presented* if it is the cokernel of a morphism
between two such finite sums. Following Auslander (*Coherent functors*, 1966), the finitely
presented functors form the category `mod C`, the natural home of the functorial approach to
Auslander-Reiten theory: almost-split sequences become minimal projective resolutions of simple
functors.

When `C` has finite biproducts, a finite sum `(-, Y₁) ⊕ ⋯ ⊕ (-, Yₙ)` is the representable
functor `(-, Y₁ ⊕ ⋯ ⊕ Yₙ)`, and by the Yoneda lemma a morphism between two finite sums comes from
a morphism of `C`. So `F` is finitely generated exactly when it is a quotient of a single
representable functor, and finitely presented exactly when there is an exact sequence
`(-, X) ⟶ (-, Y) ⟶ F ⟶ 0` whose first map is `(-, f)` for a morphism `f : X ⟶ Y` of `C`
(`TauCeti.isFinitelyGeneratedFunctor_iff_exists_single`,
`TauCeti.isFinitelyPresentedFunctor_iff_exists_single`). Without finite biproducts the two forms
differ: over the ring `ℤ`, seen as a preadditive category with one object, the free module `ℤ²` is
a finite sum of representable functors but not a quotient of a single one. Finite sums make `mod C`
well behaved for every preadditive `C`.

This file sets up `mod C` as a property of objects of the abelian category of functors
`Cᵒᵖ ⥤ AddCommGrpCat`. Finitely generated functors, hence finitely presented ones, are additive.
Representable functors are finitely presented, so the Yoneda embedding factors through `mod C`
(`TauCeti.modYoneda`), and with finite biproducts every object of `mod C` is a quotient of a
representable functor. The zero functor is the empty sum. The cokernel of a morphism `φ : F ⟶ G`
from a finitely generated functor to a finitely presented one is finitely presented: if `F` is a
quotient of `U` and `G` is presented by `V₁ ⟶ V₀`, lift `U ⟶ F ⟶ G` to `V₀`; then the cokernel of
`φ` is presented by `V₁ ⊕ U ⟶ V₀`, adding the lifted generators of `F` to the relations of `G`.
Finitely presented functors are also closed under binary biproducts, combining presentations
by block matrices, and under retracts, as the cokernel of `𝟙 - e` for an idempotent `e`. So `mod C`
contains zero and is closed under isomorphisms, cokernels, retracts and finite products and
coproducts in the functor category.

For a property `P` of objects of `C`, the restriction `(-, X)|_P` of a representable functor to the
full subcategory of `P` is a quotient of a single representable functor exactly when `X` has a
right `P`-approximation: a morphism `u : Y ⟶ X` from an object of `P` through which every morphism
from an object of `P` to `X` factors. By the Yoneda lemma, an epimorphism `(-, Y) ⟶ (-, X)|_P` is
postcomposition with such a `u`.

## Main declarations

* `TauCeti.IsFinitelyGeneratedFunctor`, `TauCeti.IsFinitelyPresentedFunctor`: the two finiteness
  conditions, and `TauCeti.isFinitelyPresentedFunctor C`, the property of objects defining
  `mod C`.
* `TauCeti.isFinitelyGeneratedFunctor_iff_exists_single`,
  `TauCeti.isFinitelyPresentedFunctor_iff_exists_single`: with finite biproducts, single
  representable functors suffice.
* `TauCeti.isFinitelyPresentedFunctor_iff_exists_isColimit`: finitely presented functors are
  the cokernels of morphisms between finite sums of representable functors.
* `TauCeti.IsFinitelyGeneratedFunctor.additive`: finitely generated functors are additive.
* `TauCeti.isFinitelyPresentedFunctor_preadditiveYoneda_obj`: representable functors are
  finitely presented.
* `TauCeti.modYoneda`: the Yoneda embedding of `C` into `mod C`, which preserves small limits.
* `TauCeti.exists_epi_modYoneda_obj`: with finite biproducts, every object of `mod C` is a quotient
  of a representable functor.
* `TauCeti.IsFinitelyPresentedFunctor.cokernel` and
  `TauCeti.IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork`: closure under cokernels of
  morphisms out of finitely generated functors.
* `TauCeti.IsFinitelyPresentedFunctor.biprod`: closure under binary biproducts.
* `CategoryTheory.ObjectProperty.isFinitelyGeneratedFunctor_restrictedPreadditiveYoneda_obj_iff`:
  the restriction `(-, X)|_P` is finitely generated exactly when `X` has a right
  `P`-approximation, when the full subcategory of `P` has finite biproducts.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §§3 and 11.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A functor `F : Cᵒᵖ ⥤ AddCommGrpCat` is *finitely generated* if it is a quotient of a finite
sum `(-, Y₁) ⊕ ⋯ ⊕ (-, Yₙ)` of representable functors. -/
def IsFinitelyGeneratedFunctor (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∃ (n : ℕ) (Y : Fin n → C) (p : (∐ fun i ↦ preadditiveYoneda.obj (Y i)) ⟶ F), Epi p

/-- A functor `F : Cᵒᵖ ⥤ AddCommGrpCat` is *finitely presented* if it is the cokernel of a
morphism between finite sums of representable functors: there is an exact sequence
`(-, X₁) ⊕ ⋯ ⊕ (-, Xₘ) ⟶ (-, Y₁) ⊕ ⋯ ⊕ (-, Yₙ) ⟶ F ⟶ 0`. -/
def IsFinitelyPresentedFunctor (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∃ (m n : ℕ) (X : Fin m → C) (Y : Fin n → C)
    (f : (∐ fun j ↦ preadditiveYoneda.obj (X j)) ⟶ ∐ fun i ↦ preadditiveYoneda.obj (Y i))
    (p : (∐ fun i ↦ preadditiveYoneda.obj (Y i)) ⟶ F) (h : f ≫ p = 0),
    Epi p ∧ (ShortComplex.mk _ _ h).Exact

variable (C) in
/-- The finitely presented functors `Cᵒᵖ ⥤ AddCommGrpCat`, as a property of objects of the functor
category; its full subcategory is `mod C`. -/
abbrev isFinitelyPresentedFunctor : ObjectProperty (Cᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  IsFinitelyPresentedFunctor

variable {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}}

/-- A functor is finitely generated exactly when it admits an epimorphism from a finite sum of
representable functors. -/
theorem isFinitelyGeneratedFunctor_def :
    IsFinitelyGeneratedFunctor F ↔ ∃ (n : ℕ) (Y : Fin n → C)
      (p : (∐ fun i ↦ preadditiveYoneda.obj (Y i)) ⟶ F), Epi p :=
  Iff.rfl

/-- A functor is finitely presented exactly when there is an exact sequence
`(-, X₁) ⊕ ⋯ ⊕ (-, Xₘ) ⟶ (-, Y₁) ⊕ ⋯ ⊕ (-, Yₙ) ⟶ F ⟶ 0`. -/
theorem isFinitelyPresentedFunctor_def :
    IsFinitelyPresentedFunctor F ↔ ∃ (m n : ℕ) (X : Fin m → C) (Y : Fin n → C)
      (f : (∐ fun j ↦ preadditiveYoneda.obj (X j)) ⟶ ∐ fun i ↦ preadditiveYoneda.obj (Y i))
      (p : (∐ fun i ↦ preadditiveYoneda.obj (Y i)) ⟶ F) (h : f ≫ p = 0),
      Epi p ∧ (ShortComplex.mk _ _ h).Exact :=
  Iff.rfl

/-- A functor is finitely presented exactly when it is the cokernel of a morphism between finite
sums of representable functors. -/
theorem isFinitelyPresentedFunctor_iff_exists_isColimit :
    IsFinitelyPresentedFunctor F ↔ ∃ (m n : ℕ) (X : Fin m → C) (Y : Fin n → C)
      (f : (∐ fun j ↦ preadditiveYoneda.obj (X j)) ⟶ ∐ fun i ↦ preadditiveYoneda.obj (Y i))
      (p : (∐ fun i ↦ preadditiveYoneda.obj (Y i)) ⟶ F) (h : f ≫ p = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ p h)) := by
  constructor
  · rintro ⟨m, n, X, Y, f, p, h, hp, hS⟩
    exact ⟨m, n, X, Y, f, p, h, ⟨hS.gIsCokernel⟩⟩
  · rintro ⟨m, n, X, Y, f, p, h, ⟨hc⟩⟩
    exact ⟨m, n, X, Y, f, p, h, Cofork.IsColimit.epi hc, ShortComplex.exact_of_g_is_cokernel _ hc⟩

/-- A finitely presented functor is finitely generated. -/
theorem IsFinitelyPresentedFunctor.isFinitelyGeneratedFunctor (hF : IsFinitelyPresentedFunctor F) :
    IsFinitelyGeneratedFunctor F := by
  obtain ⟨_, n, _, Y, _, p, _, hp, _⟩ := hF
  exact ⟨n, Y, p, hp⟩

/-- A quotient of a finitely generated functor is finitely generated. -/
theorem IsFinitelyGeneratedFunctor.of_epi (hF : IsFinitelyGeneratedFunctor F) (q : F ⟶ G)
    [Epi q] : IsFinitelyGeneratedFunctor G := by
  obtain ⟨n, Y, p, hp⟩ := hF
  exact ⟨n, Y, p ≫ q, epi_comp p q⟩

/-! ### Additivity -/

/-- A finitely generated functor is additive: it is a quotient of an additive finite sum of
representable functors. -/
theorem IsFinitelyGeneratedFunctor.additive (hF : IsFinitelyGeneratedFunctor F) : F.Additive := by
  obtain ⟨n, Y, p, hp⟩ := hF
  exact Functor.additive_of_epi p

/-- A finitely presented functor is additive. -/
theorem IsFinitelyPresentedFunctor.additive (hF : IsFinitelyPresentedFunctor F) : F.Additive :=
  hF.isFinitelyGeneratedFunctor.additive

/-! ### Finite sums of representable functors -/

/-- A functor is isomorphic to a finite sum of representable functors. -/
private def IsFiniteSum (A : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∃ (n : ℕ) (Y : Fin n → C), Nonempty (A ≅ ∐ fun i ↦ preadditiveYoneda.obj (Y i))

private theorem IsFiniteSum.of_iso {A B : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (hA : IsFiniteSum A)
    (e : A ≅ B) : IsFiniteSum B := by
  obtain ⟨n, Y, ⟨e'⟩⟩ := hA
  exact ⟨n, Y, ⟨e.symm ≪≫ e'⟩⟩

private theorem isFiniteSum_sigma {J : Type} [Finite J] (Y : J → C) :
    IsFiniteSum (∐ fun j ↦ preadditiveYoneda.obj (Y j)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  exact ⟨n, Y ∘ e.symm, ⟨(Sigma.reindex e.symm (fun j ↦ preadditiveYoneda.obj (Y j))).symm⟩⟩

private theorem isFiniteSum_preadditiveYoneda_obj (Y : C) :
    IsFiniteSum (preadditiveYoneda.obj Y) :=
  ⟨1, fun _ ↦ Y, ⟨(coproductUniqueIso fun _ : Fin 1 ↦ preadditiveYoneda.obj Y).symm⟩⟩

/-- The binary biproduct of two finite sums of representable functors is the finite sum indexed
by the disjoint union. -/
private noncomputable def biprodSigmaIso {J K : Type} (X : J → C) (Y : K → C) :
    (∐ fun j ↦ preadditiveYoneda.obj (X j)) ⊞ (∐ fun k ↦ preadditiveYoneda.obj (Y k)) ≅
      ∐ fun l ↦ preadditiveYoneda.obj (Sum.elim X Y l) :=
  IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit _ _)
    (MonoCoprod.isColimitBinaryCofanSum _ _ _
      (coproductIsCoproduct fun l ↦ preadditiveYoneda.obj (Sum.elim X Y l))
      (coproductIsCoproduct fun j ↦ preadditiveYoneda.obj (X j))
      (coproductIsCoproduct fun k ↦ preadditiveYoneda.obj (Y k)))

private theorem IsFiniteSum.biprod {A B : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (hA : IsFiniteSum A)
    (hB : IsFiniteSum B) : IsFiniteSum (A ⊞ B) := by
  obtain ⟨m, X, ⟨eA⟩⟩ := hA
  obtain ⟨n, Y, ⟨eB⟩⟩ := hB
  exact (isFiniteSum_sigma (Sum.elim X Y)).of_iso
    ((biprodSigmaIso X Y).symm ≪≫ biprod.mapIso eA.symm eB.symm)

/-- A functor presented, up to isomorphism, by a morphism between finite sums of representable
functors is finitely presented. -/
private theorem isFinitelyPresentedFunctor_of_isFiniteSum {A B : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (f : A ⟶ B) (p : B ⟶ F) (h : f ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p h))
    (hA : IsFiniteSum A) (hB : IsFiniteSum B) : IsFinitelyPresentedFunctor F := by
  obtain ⟨m, X, ⟨eA⟩⟩ := hA
  obtain ⟨n, Y, ⟨eB⟩⟩ := hB
  have : Epi p := Cofork.IsColimit.epi hc
  refine ⟨m, n, X, Y, eA.inv ≫ f ≫ eB.hom, eB.inv ≫ p, by simp [h], epi_comp _ _,
    (ShortComplex.exact_iff_of_iso ?_).2 (ShortComplex.exact_of_g_is_cokernel (.mk f p h) hc)⟩
  exact ShortComplex.isoMk eA.symm eB.symm (Iso.refl _) (by simp) (by simp)

/-! ### Representable functors and the Yoneda embedding -/

/-- Being finitely presented is invariant under isomorphism. -/
theorem IsFinitelyPresentedFunctor.of_iso (e : F ≅ G) (hF : IsFinitelyPresentedFunctor F) :
    IsFinitelyPresentedFunctor G := by
  obtain ⟨m, n, X, Y, f, p, h, ⟨hc⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hF
  exact isFinitelyPresentedFunctor_iff_exists_isColimit.2 ⟨m, n, X, Y, f, p ≫ e.hom,
    by rw [reassoc_of% h, zero_comp], ⟨IsColimit.ofIsoColimit hc (Cofork.ext e (by simp))⟩⟩

instance : (isFinitelyPresentedFunctor C).IsClosedUnderIsomorphisms where
  of_iso e hF := hF.of_iso e

/-- A representable functor `(-, Y)` is finitely presented, as the cokernel of `(-, 0)` for the
zero endomorphism of `Y`. -/
theorem isFinitelyPresentedFunctor_preadditiveYoneda_obj (Y : C) :
    IsFinitelyPresentedFunctor (preadditiveYoneda.obj Y) :=
  isFinitelyPresentedFunctor_of_isFiniteSum (preadditiveYoneda.map (0 : Y ⟶ Y)) (𝟙 _) (by simp)
    (CokernelCofork.IsColimit.ofId _ (Functor.map_zero _ _ _))
    (isFiniteSum_preadditiveYoneda_obj Y) (isFiniteSum_preadditiveYoneda_obj Y)

/-- A representable functor `(-, Y)` is finitely generated. -/
theorem isFinitelyGeneratedFunctor_preadditiveYoneda_obj (Y : C) :
    IsFinitelyGeneratedFunctor (preadditiveYoneda.obj Y) :=
  (isFinitelyPresentedFunctor_preadditiveYoneda_obj Y).isFinitelyGeneratedFunctor

/-- The Yoneda embedding of `C` into `mod C`, sending `X` to the representable functor `(-, X)`. -/
abbrev modYoneda : C ⥤ (isFinitelyPresentedFunctor C).FullSubcategory :=
  (isFinitelyPresentedFunctor C).lift preadditiveYoneda
    isFinitelyPresentedFunctor_preadditiveYoneda_obj

/-- The Yoneda embedding of `C` into `mod C` preserves small limits, since `preadditiveYoneda`
does and the inclusion of `mod C` into the functor category reflects them. -/
instance (J : Type*) [Category* J] [Small.{v} J] :
    PreservesLimitsOfShape J (modYoneda : C ⥤ (isFinitelyPresentedFunctor C).FullSubcategory) :=
  have : PreservesLimitsOfShape J ((modYoneda : C ⥤ _) ⋙ (isFinitelyPresentedFunctor C).ι) :=
    inferInstanceAs (PreservesLimitsOfShape J (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ (isFinitelyPresentedFunctor C).ι

/-- The zero functor is finitely presented, as the empty sum of representable functors. -/
instance : (isFinitelyPresentedFunctor C).ContainsZero where
  exists_zero := by
    have hZ : IsZero (∐ fun i : Fin 0 ↦ preadditiveYoneda.obj (Fin.elim0 i : C)) :=
      (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i ↦ Fin.elim0 i)
    exact ⟨_, hZ, 0, 0, Fin.elim0, Fin.elim0, 0, 𝟙 _, zero_comp, inferInstance,
      ShortComplex.exact_of_isZero_X₂ _ hZ⟩

/-! ### Single representable functors -/

/-- With finite biproducts, the finite sum `(-, Y₁) ⊕ ⋯ ⊕ (-, Yₙ)` is the representable functor
`(-, Y₁ ⊕ ⋯ ⊕ Yₙ)`. -/
private noncomputable def preadditiveYonedaBiproductIso [HasFiniteBiproducts C] {n : ℕ}
    (Y : Fin n → C) : preadditiveYoneda.obj (⨁ Y) ≅ ∐ fun i ↦ preadditiveYoneda.obj (Y i) :=
  preadditiveYoneda.mapBiproduct Y ≪≫ biproduct.isoCoproduct _

/-- With finite biproducts, a functor is finitely generated exactly when it is a quotient of a
single representable functor `(-, Y)`. -/
theorem isFinitelyGeneratedFunctor_iff_exists_single [HasFiniteBiproducts C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    IsFinitelyGeneratedFunctor F ↔ ∃ (Y : C) (p : preadditiveYoneda.obj Y ⟶ F), Epi p :=
  ⟨fun ⟨_, Y, p, _⟩ ↦ ⟨⨁ Y, (preadditiveYonedaBiproductIso Y).hom ≫ p, epi_comp _ _⟩,
    fun ⟨Y, p, _⟩ ↦ (isFinitelyGeneratedFunctor_preadditiveYoneda_obj Y).of_epi p⟩

/-- With finite biproducts, finite presentation by finite sums of representable functors agrees
with presentation by single ones: `F` is finitely presented exactly when there is an exact sequence
`(-, X) ⟶ (-, Y) ⟶ F ⟶ 0` whose first map is `(-, f)` for a morphism `f : X ⟶ Y` of `C`. -/
theorem isFinitelyPresentedFunctor_iff_exists_single [HasFiniteBiproducts C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    IsFinitelyPresentedFunctor F ↔
      ∃ (X Y : C) (f : X ⟶ Y) (p : preadditiveYoneda.obj Y ⟶ F)
        (h : preadditiveYoneda.map f ≫ p = 0), Epi p ∧ (ShortComplex.mk _ _ h).Exact := by
  constructor
  · rintro ⟨m, n, X, Y, f, p, h, hp, hS⟩
    -- Transport the presentation along `(-, ⨁ X) ≅ ∐ (-, X j)` and `(-, ⨁ Y) ≅ ∐ (-, Y i)`; the
    -- transported morphism `(-, ⨁ X) ⟶ (-, ⨁ Y)` is `(-, g)` by the Yoneda lemma.
    let eX := preadditiveYonedaBiproductIso X
    let eY := preadditiveYonedaBiproductIso Y
    obtain ⟨g, hg⟩ := preadditiveYoneda.map_surjective (eX.hom ≫ f ≫ eY.inv)
    have h' : preadditiveYoneda.map g ≫ eY.hom ≫ p = 0 := by simp [hg, h]
    refine ⟨⨁ X, ⨁ Y, g, eY.hom ≫ p, h', epi_comp _ _, (ShortComplex.exact_iff_of_iso ?_).2 hS⟩
    exact ShortComplex.isoMk eX eY (Iso.refl _) (by simp [hg]) (by simp)
  · rintro ⟨X, Y, f, p, h, hp, hS⟩
    exact isFinitelyPresentedFunctor_of_isFiniteSum _ p h hS.gIsCokernel
      (isFiniteSum_preadditiveYoneda_obj X) (isFiniteSum_preadditiveYoneda_obj Y)

/-- With finite biproducts, every object of `mod C` is a quotient of a representable functor. -/
theorem exists_epi_modYoneda_obj [HasFiniteBiproducts C]
    (F : (isFinitelyPresentedFunctor C).FullSubcategory) :
    ∃ (Y : C) (p : modYoneda.obj Y ⟶ F), Epi p := by
  obtain ⟨Y, p, hp⟩ :=
    (isFinitelyGeneratedFunctor_iff_exists_single _).1 F.property.isFinitelyGeneratedFunctor
  exact ⟨Y, ObjectProperty.homMk p, (isFinitelyPresentedFunctor C).ι.epi_of_epi_map hp⟩

/-! ### Closure properties -/

/-- The cokernel of a morphism from a finitely generated functor to a finitely presented functor
is finitely presented: if `F` is a quotient of `U` and `G` is presented by `g : V₁ ⟶ V₀`, lift
`U ⟶ F ⟶ G` to `ℓ : U ⟶ V₀`; then the cokernel is presented by `[g, ℓ] : V₁ ⊞ U ⟶ V₀`. -/
theorem IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork {φ : F ⟶ G}
    {c : CokernelCofork φ} (hc : IsColimit c) (hF : IsFinitelyGeneratedFunctor F)
    (hG : IsFinitelyPresentedFunctor G) : IsFinitelyPresentedFunctor c.pt := by
  obtain ⟨k, Z, p, hp⟩ := hF
  obtain ⟨m, n, X, Y, g, q, hgq, hq, hS⟩ := hG
  obtain ⟨ℓ, hℓ⟩ := exists_comp_eq_sigma_preadditiveYoneda_obj_of_epi q (p ≫ φ)
  have : Epi c.π := Cofork.IsColimit.epi hc
  have hgc : biprod.desc g ℓ ≫ q ≫ c.π = 0 := by
    apply biprod.hom_ext'
    · simp [reassoc_of% hgq]
    · simp [reassoc_of% hℓ]
  refine isFinitelyPresentedFunctor_of_isFiniteSum _ _ hgc
    (CokernelCofork.IsColimit.ofπ' _ _ fun t ht ↦ ?_)
    ((isFiniteSum_sigma X).biprod (isFiniteSum_sigma Z)) (isFiniteSum_sigma Y)
  -- A morphism `t` killing `[g, ℓ]` factors through `q` as `t'`, and `t'` kills `φ`.
  obtain ⟨t', ht'⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel t
    (by simpa using biprod.inl ≫= ht)
  have ht' : q ≫ t' = t := ht'
  obtain ⟨t'', ht''⟩ := CokernelCofork.IsColimit.desc' hc t' (by
    rw [← cancel_epi p, comp_zero, ← Category.assoc, ← hℓ, Category.assoc, ht']
    simpa using biprod.inr ≫= ht)
  exact ⟨t'', by rw [Category.assoc, ht'', ht']⟩

/-- If `F` is finitely generated and `G` is finitely presented, the cokernel of `φ : F ⟶ G` is
finitely presented. -/
theorem IsFinitelyPresentedFunctor.cokernel {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : F ⟶ G)
    (hF : IsFinitelyGeneratedFunctor F) (hG : IsFinitelyPresentedFunctor G) :
    IsFinitelyPresentedFunctor (Limits.cokernel φ) :=
  of_isColimit_cokernelCofork (colimit.isColimit _) hF hG

/-- A binary biproduct of finitely presented functors is finitely presented. -/
theorem IsFinitelyPresentedFunctor.biprod (hF : IsFinitelyPresentedFunctor F)
    (hG : IsFinitelyPresentedFunctor G) : IsFinitelyPresentedFunctor (F ⊞ G) := by
  obtain ⟨_, _, X₁, Y₁, f₁, p₁, h₁, _, hS₁⟩ := hF
  obtain ⟨_, _, X₂, Y₂, f₂, p₂, h₂, _, hS₂⟩ := hG
  exact isFinitelyPresentedFunctor_of_isFiniteSum (biprod.map f₁ f₂) (biprod.map p₁ p₂) _
    (CokernelCofork.isColimitBiprod hS₁.gIsCokernel hS₂.gIsCokernel)
    ((isFiniteSum_sigma X₁).biprod (isFiniteSum_sigma X₂))
    ((isFiniteSum_sigma Y₁).biprod (isFiniteSum_sigma Y₂))

instance : (isFinitelyPresentedFunctor C).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨_, k, hk, hF, hG⟩
    exact IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork hk hF.isFinitelyGeneratedFunctor hG

/-- A retract `F` of a finitely presented functor `G` is finitely presented, as the cokernel of
`𝟙 - e` for the idempotent `e : G ⟶ F ⟶ G`. -/
instance : (isFinitelyPresentedFunctor C).IsStableUnderRetracts where
  of_retract {F G} h hG := by
    have hr : (𝟙 G - h.r ≫ h.i) ≫ h.r = 0 := by simp
    refine IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork
      (c := CokernelCofork.ofπ h.r hr) ?_ hG.isFinitelyGeneratedFunctor hG
    refine CokernelCofork.IsColimit.ofπ _ _ (fun t _ ↦ h.i ≫ t) (fun t ht ↦ ?_)
      (fun t _ m hm ↦ by rw [← hm, h.retract_assoc])
    rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero, Category.assoc] at ht
    exact ht.symm

instance : (isFinitelyPresentedFunctor C).IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    refine (isFinitelyPresentedFunctor C).prop_of_iso ?_
      ((p.prop_diag_obj (.mk .left)).biprod (p.prop_diag_obj (.mk .right)))
    exact IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit _ _)
      ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm _).invFun p.isColimit)

instance : (isFinitelyPresentedFunctor C).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (isFinitelyPresentedFunctor C).prop_of_iso ?_
      ((p.prop_diag_obj (.mk .left)).biprod (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).invFun p.isLimit)

instance : (isFinitelyPresentedFunctor C).IsClosedUnderFiniteCoproducts := .mk'

instance : (isFinitelyPresentedFunctor C).IsClosedUnderFiniteProducts := .mk'

end TauCeti

namespace CategoryTheory.ObjectProperty

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] (P : ObjectProperty C)

/-- The restriction `(-, X)|_P` of a representable functor to the full subcategory of `P` is
finitely generated when `X` itself satisfies `P`, as it is then representable. -/
theorem isFinitelyGeneratedFunctor_restrictedPreadditiveYoneda_obj {X : C} (hX : P X) :
    IsFinitelyGeneratedFunctor (P.restrictedPreadditiveYoneda.obj X) :=
  (isFinitelyGeneratedFunctor_preadditiveYoneda_obj (⟨X, hX⟩ : P.FullSubcategory)).of_epi
    (P.preadditiveYonedaIsoRestricted.hom.app ⟨X, hX⟩)

/-- **Finite generation of a restricted representable functor.** For a property `P` of objects
of `C` whose full subcategory has finite biproducts, the restriction `(-, X)|_P` of `(-, X)` to the
full subcategory of `P` is finitely generated exactly when some morphism `u : Y ⟶ X` out of an
object of `P` is a right `P`-approximation of `X`: every morphism to `X` from an object of `P`
factors through `u`. -/
theorem isFinitelyGeneratedFunctor_restrictedPreadditiveYoneda_obj_iff
    [HasFiniteBiproducts P.FullSubcategory] (X : C) :
    IsFinitelyGeneratedFunctor (P.restrictedPreadditiveYoneda.obj X) ↔
      ∃ (Y : C) (_ : P Y) (u : Y ⟶ X), ∀ Z, P Z → ∀ g : Z ⟶ X, ∃ h : Z ⟶ Y, h ≫ u = g := by
  rw [isFinitelyGeneratedFunctor_iff_exists_single]
  constructor
  · rintro ⟨Y, p, hp⟩
    refine ⟨Y.obj, Y.property, p.app (op Y) (𝟙 Y), fun Z hZ g ↦ ?_⟩
    rw [NatTrans.epi_iff_epi_app] at hp
    obtain ⟨(h : (⟨Z, hZ⟩ : P.FullSubcategory) ⟶ Y), rfl⟩ :=
      (AddCommGrpCat.epi_iff_surjective _).1 (hp (op ⟨Z, hZ⟩)) g
    refine ⟨h.hom, ?_⟩
    have := NatTrans.naturality_apply p h.op (𝟙 Y)
    simp only [preadditiveYoneda_obj_map_apply, Category.comp_id] at this
    exact (this.trans (P.restrictedPreadditiveYoneda_obj_map_apply X h.op _)).symm
  · rintro ⟨Y, hY, u, hu⟩
    have : Epi (P.restrictedPreadditiveYoneda.map u) := by
      rw [NatTrans.epi_iff_epi_app]
      intro Q
      rw [AddCommGrpCat.epi_iff_surjective]
      intro (g : Q.unop.obj ⟶ X)
      obtain ⟨h, rfl⟩ := hu _ Q.unop.property g
      exact ⟨h, P.restrictedPreadditiveYoneda_map_app_apply u Q h⟩
    exact ⟨⟨Y, hY⟩, P.preadditiveYonedaIsoRestricted.hom.app ⟨Y, hY⟩ ≫
      P.restrictedPreadditiveYoneda.map u, inferInstance⟩

end CategoryTheory.ObjectProperty
