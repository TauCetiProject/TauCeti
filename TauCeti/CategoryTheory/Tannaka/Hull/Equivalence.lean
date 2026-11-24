/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact
public import TauCeti.Algebra.Category.ModuleCat.NatEnd
public import TauCeti.CategoryTheory.Tannaka.Hull.Algebra
public import TauCeti.CategoryTheory.Tannaka.RepresentingObject

/-!
# The hull of an object is equivalent to finite modules over the fibre-endomorphism algebra

Let `ω : C ⥤ ModuleCat K` be an exact faithful `K`-linear functor from a `K`-linear abelian
category to vector spaces, and let `X : C` have finite-dimensional fibre. Write `⟨X⟩` for the
full subcategory `TauCeti.subquotientHull X` of subquotients of finite direct sums of copies of
`X`, and `A_X = End (⟨X⟩.ι ⋙ ω)` for the algebra of natural endomorphisms of the restricted fibre
functor; it is finite-dimensional, and evaluation at `X` identifies it with
`CategoryTheory.Functor.hullAlgebra` (`CategoryTheory.Functor.hullEndAlgEquiv`).

Every fibre `ω Y` with `Y ∈ ⟨X⟩` is a module over `A_X`, and every `ω f` is `A_X`-linear. This
file proves that the resulting functor `CategoryTheory.Functor.hullModuleFunctor` from `⟨X⟩` to
finitely generated `A_X`-modules is an equivalence of categories
(`CategoryTheory.Functor.hullEquivalence`). This is the finite case of the reconstruction of a
category with an exact faithful fibre functor as the finite comodules over a coalgebra. The
underlying type of the module attached to `Y` is `ω Y`, and the map attached to a morphism `g` is
`ω g` (`CategoryTheory.Functor.hullModuleFunctor_obj_obj`,
`CategoryTheory.Functor.hullModuleFunctor_map_hom_hom_apply`); the coalgebra is assembled
from the duals of the algebras `A_X` as `X` varies.

The proof uses the representing object `P = CategoryTheory.Functor.hullRepresenting ω X` of `ω`
on `⟨X⟩`, with its point `p ∈ ω P`: evaluation at `p` identifies `P ⟶ Y` with `ω Y` for every
`Y ∈ ⟨X⟩` (`CategoryTheory.Functor.hullEvalEquiv`). Each `q ∈ ω P` defines a natural
endomorphism of `ω` on `⟨X⟩`, sending `ω f p` to `ω f q`; this identifies `A_X` with the
regular module `ω P`. Consequently the `A_X`-submodules of `ω Y` are the images of morphisms from
finite direct sums of copies of `P`. Fullness then follows by factoring through an epimorphism
from such a direct sum, and every finitely generated `A_X`-module is the fibre of a cokernel of a
morphism between such direct sums.

## Main definitions and results

* `CategoryTheory.Functor.hullModuleFunctor`: the functor `⟨X⟩ ⥤ FGModuleCat A_X`, defined for
  a fibre functor to modules over a Noetherian ring that preserves monomorphisms and
  epimorphisms.
* `CategoryTheory.Functor.hullModuleFunctor_obj_obj`,
  `CategoryTheory.Functor.hullModuleFunctor_map_hom_hom_apply`: it acts on objects and morphisms
  as `ω`.
* `CategoryTheory.Functor.hullModuleFunctorCompRestrictScalarsIso`: restricting scalars back to
  the base ring, `hullModuleFunctor` recovers the restricted fibre functor `⟨X⟩.ι ⋙ ω`.
* `CategoryTheory.Functor.hullEquivalence`: for an exact faithful linear functor to vector
  spaces, `hullModuleFunctor` is an equivalence `⟨X⟩ ≌ FGModuleCat A_X`.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, Lemma 2.13 and its proof.
* A. Huber, S. Müller-Stach, *Periods and Nori motives*, §7.3 and Proposition 7.4.1.
-/

public section

namespace CategoryTheory.Functor

open Limits TauCeti

universe w v u u'

variable {C : Type u} [Category.{v} C]

attribute [local instance] natEndModule

section Functor

variable {R : Type u'} [CommRing R] [IsNoetherianRing R] [Preadditive C] [HasFiniteBiproducts C]
  (ω : C ⥤ ModuleCat.{w} R) [ω.Additive] [ω.PreservesMonomorphisms] [ω.PreservesEpimorphisms]
  {X : C} [Module.Finite R (ω.obj X)]

variable (X)

/-- The fibre functor on the hull of `X`, with each fibre `ω Y` regarded as a finitely generated
module over the algebra `End (⟨X⟩.ι ⋙ ω)` of natural endomorphisms of the restricted fibre
functor, acting through components. -/
@[expose] noncomputable def hullModuleFunctor :
    (subquotientHull X).FullSubcategory ⥤ FGModuleCat.{w} (End ((subquotientHull X).ι ⋙ ω)) :=
  ObjectProperty.lift _ ((subquotientHull X).ι ⋙ ω).toNatEndModule fun Y ↦
    have : Module.Finite R (((subquotientHull X).ι ⋙ ω).obj Y) :=
      ω.finite_obj_of_subquotientHull Y.property
    Module.Finite.of_restrictScalars_finite R (End ((subquotientHull X).ι ⋙ ω))
      (((subquotientHull X).ι ⋙ ω).obj Y)

variable {X}

/-- The module attached by `hullModuleFunctor` to `Y` is the fibre `ω Y`, with the action of
`End (⟨X⟩.ι ⋙ ω)` through components. -/
@[simp]
theorem hullModuleFunctor_obj_obj (Y : (subquotientHull X).FullSubcategory) :
    ((ω.hullModuleFunctor X).obj Y).obj = ((subquotientHull X).ι ⋙ ω).toNatEndModule.obj Y :=
  (rfl)

/-- `hullModuleFunctor` acts on morphisms as `ω`. -/
@[simp]
theorem hullModuleFunctor_map_hom_hom_apply {Y Y' : (subquotientHull X).FullSubcategory}
    (g : Y ⟶ Y') (y : ω.obj Y.obj) :
    ((ω.hullModuleFunctor X).map g).hom.hom y = (ω.map g.hom).hom y :=
  (rfl)

variable (X) in
/-- Restricting scalars back to `R`, `hullModuleFunctor` recovers the fibre functor `ω` on the
hull of `X`; the components are identities. -/
noncomputable def hullModuleFunctorCompRestrictScalarsIso :
    ω.hullModuleFunctor X ⋙ (ModuleCat.isFG _).ι ⋙
        ModuleCat.restrictScalars (algebraMap R (End ((subquotientHull X).ι ⋙ ω))) ≅
      (subquotientHull X).ι ⋙ ω :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ((ModuleCat.isFG _).liftCompιIso _ _) _ ≪≫
    ((subquotientHull X).ι ⋙ ω).toNatEndModuleCompRestrictScalarsIso

/-- The components of `hullModuleFunctorCompRestrictScalarsIso` are identities. -/
theorem hullModuleFunctorCompRestrictScalarsIso_hom_app_hom_apply
    (Y : (subquotientHull X).FullSubcategory) (y : ω.obj Y.obj) :
    ((ω.hullModuleFunctorCompRestrictScalarsIso X).hom.app Y).hom y = y :=
  ((subquotientHull X).ι ⋙ ω).toNatEndModuleCompRestrictScalarsIso_hom_app_hom_apply Y y

/-- The inverse components of `hullModuleFunctorCompRestrictScalarsIso` are identities. -/
theorem hullModuleFunctorCompRestrictScalarsIso_inv_app_hom_apply
    (Y : (subquotientHull X).FullSubcategory) (y : ω.obj Y.obj) :
    ((ω.hullModuleFunctorCompRestrictScalarsIso X).inv.app Y).hom y = y :=
  ((subquotientHull X).ι ⋙ ω).toNatEndModuleCompRestrictScalarsIso_inv_app_hom_apply Y y

end Functor

section Equivalence

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] {K : Type w} [Field K] [CategoryTheory.Linear K C]
  (ω : C ⥤ ModuleCat.{w} K) [ω.Additive] [ω.Linear K] [ω.Faithful] [PreservesFiniteLimits ω]
  [ω.PreservesEpimorphisms] {X : C} [FiniteDimensional K (ω.obj X)]

/-- The natural endomorphism of `ω` on the hull of `X` attached to `q ∈ ω P_X`: it sends `ω f p`
to `ω f q` for every `f : P_X ⟶ Y`, where `p` is the point of `P_X`. -/
private noncomputable def hullEndOfPoint :
    ω.obj (ω.hullRepresenting X : C) →+ End ((subquotientHull X).ι ⋙ ω) :=
  AddMonoidHom.mk' (fun q ↦ .of
    { app Y := ModuleCat.ofHom
        { toFun y := (ω.map ((ω.hullEvalEquiv Y.property).symm y)).hom q
          map_add' y y' := by simp [ω.map_add]
          map_smul' c y := by simp [ω.map_smul] }
      naturality Y Y' g := by
        ext y
        simp [hullEvalEquiv_symm_naturality ω Y.property Y'.property] })
    fun q q' ↦ by
      refine End.ext (NatTrans.ext (funext fun Y ↦ ?_))
      ext y
      simp

private lemma hullEndOfPoint_smul (q : ω.obj (ω.hullRepresenting X : C))
    {Y : (subquotientHull X).FullSubcategory} (y : ((subquotientHull X).ι ⋙ ω).obj Y) :
    hullEndOfPoint ω q • y = (ω.map ((ω.hullEvalEquiv Y.property).symm y)).hom q :=
  (rfl)

/-- The natural endomorphism attached to the point of `P_X` is the identity. -/
private lemma hullEndOfPoint_point :
    hullEndOfPoint (X := X) ω (ω.fiberSpanPoint (ω.hullBasisPoint X)) = 1 := by
  refine End.ext (NatTrans.ext (funext fun Y ↦ ?_))
  ext y
  rw [← natEndModule_smul, hullEndOfPoint_smul]
  simp

/-- `hullEndOfPoint` is `End (⟨X⟩.ι ⋙ ω)`-linear: it identifies the algebra with the regular
module `ω P_X`. -/
private lemma hullEndOfPoint_app (η : End ((subquotientHull X).ι ⋙ ω))
    (q : ω.obj (ω.hullRepresenting X : C)) :
    hullEndOfPoint ω ((η.asHom.app ⟨_, ω.subquotientHull_hullRepresenting X⟩).hom q) =
      η * hullEndOfPoint ω q := by
  refine End.ext (NatTrans.ext (funext fun Y ↦ ?_))
  ext y
  simp only [← natEndModule_smul, mul_smul, hullEndOfPoint_smul]
  exact ω.map_hom_app_hom_apply η (Y := ⟨_, ω.subquotientHull_hullRepresenting X⟩) _ q

/-- The value of a morphism out of a finite direct sum of copies of `P_X`, assembled from
morphisms with prescribed values `y j` at the point of `P_X`. -/
private lemma map_biproductDesc_apply {ι : Type} [Fintype ι]
    {Y : (subquotientHull X).FullSubcategory} (y : ι → ((subquotientHull X).ι ⋙ ω).obj Y)
    (v : ω.obj (⨁ fun _ : ι ↦ (ω.hullRepresenting X : C))) :
    (ω.map (biproduct.desc fun j ↦ (ω.hullEvalEquiv Y.property).symm (y j))).hom v =
      ∑ j, hullEndOfPoint ω ((ω.map (biproduct.π _ j)).hom v) • y j := by
  conv_lhs => rw [← ω.sum_map_ι_map_π_apply _ v]
  rw [_root_.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hullEndOfPoint_smul, map_biproductDesc_map_ι_apply]

/-- A linear map is surjective once every member of a spanning family lies in its range. -/
private lemma surjective_of_span_range_eq_top {S M N ι : Type*} [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Module S M] [Module S N] {s : ι → N}
    (hs : Submodule.span S (Set.range s) = ⊤) (f : M →ₗ[S] N) (h : ∀ j, s j ∈ LinearMap.range f) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact h j

/-- Every `End (⟨X⟩.ι ⋙ ω)`-linear map between fibres of objects of the hull of `X` is `ω g` for
some morphism `g`. -/
private lemma exists_map_eq {Y Y' : (subquotientHull X).FullSubcategory}
    (φ : ((subquotientHull X).ι ⋙ ω).obj Y →ₗ[End ((subquotientHull X).ι ⋙ ω)]
      ((subquotientHull X).ι ⋙ ω).obj Y') :
    ∃ g : Y.obj ⟶ Y'.obj, ∀ y, (ω.map g).hom y = φ y := by
  have : Module.Finite K (((subquotientHull X).ι ⋙ ω).obj Y) :=
    ω.finite_obj_of_subquotientHull Y.property
  let b := Module.finBasis K (((subquotientHull X).ι ⋙ ω).obj Y)
  let f₁ := biproduct.desc fun j ↦ (ω.hullEvalEquiv Y.property).symm (b j)
  let f₂ := biproduct.desc fun j ↦ (ω.hullEvalEquiv Y'.property).symm (φ (b j))
  have h₂ (v) : (ω.map f₂).hom v = φ ((ω.map f₁).hom v) := by
    simp only [f₁, f₂, map_biproductDesc_apply, _root_.map_sum, LinearMap.map_smul]
  have hsurj : Function.Surjective (ω.map f₁).hom :=
    surjective_of_span_range_eq_top b.span_eq _ fun j ↦
      ⟨(ω.map (biproduct.ι _ j)).hom (ω.fiberSpanPoint (ω.hullBasisPoint X)), by simp [f₁]⟩
  have : Epi f₁ := ω.epi_of_epi_map ((ModuleCat.epi_iff_surjective _).2 hsurj)
  have hker : kernel.ι f₁ ≫ f₂ = 0 := ω.map_injective <| by
    ext z
    rw [ω.map_comp, ModuleCat.comp_apply, h₂, map_map_apply_eq_zero ω (kernel.condition f₁),
      map_zero φ]
    simp
  refine ⟨Abelian.epiDesc f₁ f₂ hker, fun y ↦ ?_⟩
  obtain ⟨v, rfl⟩ := hsurj y
  rw [← ModuleCat.comp_apply, ← ω.map_comp, Abelian.comp_epiDesc, h₂]

/-- Every `End (⟨X⟩.ι ⋙ ω)`-submodule of a fibre `ω Y`, for `Y` in the hull of `X`, is the image
of `ω f` for a morphism `f` from a finite direct sum of copies of `P_X`. -/
private lemma exists_range_eq {Y : (subquotientHull X).FullSubcategory}
    (N : Submodule (End ((subquotientHull X).ι ⋙ ω)) (((subquotientHull X).ι ⋙ ω).obj Y)) :
    ∃ (n : ℕ) (f : (⨁ fun _ : Fin n ↦ (ω.hullRepresenting X : C)) ⟶ Y.obj),
      ∀ y, y ∈ N ↔ ∃ v, (ω.map f).hom v = y := by
  have : Module.Finite K (((subquotientHull X).ι ⋙ ω).obj Y) :=
    ω.finite_obj_of_subquotientHull Y.property
  let b := Module.finBasis K (N.restrictScalars K)
  refine ⟨_, biproduct.desc fun j ↦ (ω.hullEvalEquiv Y.property).symm (b j).val, fun y ↦
    ⟨fun hy ↦ ?_, ?_⟩⟩
  · have hsum := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, SetLike.val_smul] at hsum
    refine ⟨∑ j, b.repr ⟨y, hy⟩ j •
      (ω.map (biproduct.ι _ j)).hom (ω.fiberSpanPoint (ω.hullBasisPoint X)), ?_⟩
    simpa using hsum
  · rintro ⟨v, rfl⟩
    rw [map_biproductDesc_apply]
    exact N.sum_mem fun j _ ↦ N.smul_mem _ (b j).property

/-- The `End (⟨X⟩.ι ⋙ ω)`-linear map from the fibre of `n` copies of `P_X` to a module `M`
sending the point of the `j`-th copy to `s j`. -/
private noncomputable def biproductLinearMap {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module (End ((subquotientHull X).ι ⋙ ω)) M] (s : Fin n → M) :
    ((subquotientHull X).ι ⋙ ω).obj
        ⟨_, subquotientHull_biproduct _ fun _ : Fin n ↦ ω.subquotientHull_hullRepresenting X⟩ →ₗ[
      End ((subquotientHull X).ι ⋙ ω)] M where
  toFun v := ∑ j, hullEndOfPoint ω ((ω.map (biproduct.π _ j)).hom v) • s j
  map_add' v v' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' η v := by
    simp only [RingHom.id_apply, Finset.smul_sum, ← mul_smul, ← hullEndOfPoint_app]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [natEndModule_smul, ω.map_hom_app_hom_apply η
      (Y := ⟨_, subquotientHull_biproduct _ fun _ : Fin n ↦ ω.subquotientHull_hullRepresenting X⟩)
      (Y' := ⟨_, ω.subquotientHull_hullRepresenting X⟩)]

private lemma biproductLinearMap_map_ι {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module (End ((subquotientHull X).ι ⋙ ω)) M] (s : Fin n → M)
    (j : Fin n) :
    biproductLinearMap ω s
      ((ω.map (biproduct.ι _ j)).hom (ω.fiberSpanPoint (ω.hullBasisPoint X))) = s j := by
  simp [biproductLinearMap, map_π_map_ι_apply, apply_ite, ite_smul, hullEndOfPoint_point]

/-- Every finitely generated `End (⟨X⟩.ι ⋙ ω)`-module is isomorphic to the fibre of an object of
the hull of `X`. -/
private lemma exists_iso (M : FGModuleCat.{w} (End ((subquotientHull X).ι ⋙ ω))) :
    ∃ Y, Nonempty (((subquotientHull X).ι ⋙ ω).toNatEndModule.obj Y ≅ M.obj) := by
  have : Module.Finite (End ((subquotientHull X).ι ⋙ ω)) M.obj := M.property
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := End ((subquotientHull X).ι ⋙ ω)) (M := M.obj)
  have hQ := subquotientHull_biproduct _ fun _ : Fin n ↦ ω.subquotientHull_hullRepresenting X
  let ρ : ((subquotientHull X).ι ⋙ ω).toNatEndModule.obj ⟨_, hQ⟩ →ₗ[
      End ((subquotientHull X).ι ⋙ ω)] M.obj :=
    biproductLinearMap ω s
  have hρ : Function.Surjective ρ :=
    surjective_of_span_range_eq_top hs ρ fun j ↦ ⟨_, biproductLinearMap_map_ι ω s j⟩
  obtain ⟨m, f, hf⟩ := exists_range_eq ω (LinearMap.ker ρ)
  have hY : subquotientHull X (cokernel f) :=
    (subquotientHull X).prop_of_epi (cokernel.π f) hQ
  let π := ((subquotientHull X).ι ⋙ ω).toNatEndModule.map
    (ObjectProperty.homMk (Y := ⟨_, hY⟩) (cokernel.π f))
  have hπ : Function.Surjective π.hom := fun z ↦ by
    obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective (ω.map (cokernel.π f))).1 inferInstance z
    exact ⟨v, (toNatEndModule_map_hom_apply _ _ v).trans hv⟩
  have := preservesHomology_of_preservesEpis_and_kernels ω
  have hex := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    ((ShortComplex.exact_cokernel f).map ω)
  have hker : LinearMap.ker π.hom = LinearMap.ker ρ := by
    ext v
    refine ⟨fun hv ↦ (hf v).2 (hex ((toNatEndModule_map_hom_apply _ _ v).symm.trans
      (LinearMap.mem_ker.1 hv))), fun hv ↦ ?_⟩
    obtain ⟨u, rfl⟩ := (hf v).1 hv
    exact LinearMap.mem_ker.2 ((toNatEndModule_map_hom_apply _ _ _).trans
      (map_map_apply_eq_zero ω (cokernel.condition f) u))
  exact ⟨⟨_, hY⟩, ⟨LinearEquiv.toModuleIso ((π.hom.quotKerEquivOfSurjective hπ).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ ρ.quotKerEquivOfSurjective hρ)⟩⟩

/-- Every `End (⟨X⟩.ι ⋙ ω)`-linear map between fibres of objects of the hull of `X` is the image
under `ω` of a morphism. -/
instance : (((subquotientHull X).ι ⋙ ω).toNatEndModule).Full where
  map_surjective {Y Y'} φ := by
    obtain ⟨g, hg⟩ := exists_map_eq ω φ.hom
    exact ⟨ObjectProperty.homMk g, ModuleCat.hom_ext (LinearMap.ext fun y ↦
      (toNatEndModule_map_hom_apply _ _ y).trans (hg y))⟩

/-- `hullModuleFunctor` is an equivalence of categories. -/
instance : (ω.hullModuleFunctor X).IsEquivalence where
  faithful := Functor.Faithful.of_comp_iso ((ModuleCat.isFG _).liftCompιIso _ _)
  full := Functor.Full.of_comp_faithful_iso ((ModuleCat.isFG _).liftCompιIso _ _)
  essSurj.mem_essImage M := by
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso ω M
    exact ⟨Y, ⟨(ModuleCat.isFG _).isoMk e⟩⟩

variable (X) in
/-- For an exact faithful `K`-linear functor `ω` to vector spaces and an object `X` with
finite-dimensional fibre, the hull `⟨X⟩` of subquotients of finite direct sums of copies of `X`
is equivalent, through `ω`, to the category of finitely generated modules over the algebra
`End (⟨X⟩.ι ⋙ ω)` of natural endomorphisms of the restricted fibre functor. -/
noncomputable def hullEquivalence :
    (subquotientHull X).FullSubcategory ≌ FGModuleCat.{w} (End ((subquotientHull X).ι ⋙ ω)) :=
  (ω.hullModuleFunctor X).asEquivalence

@[simp]
theorem hullEquivalence_functor : (ω.hullEquivalence X).functor = ω.hullModuleFunctor X :=
  (rfl)

end Equivalence

end CategoryTheory.Functor
