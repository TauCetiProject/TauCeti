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
public import TauCeti.CategoryTheory.Tannaka.HullAlgebra
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
`ω g` (`CategoryTheory.Functor.hullModuleFunctor_map_hom_hom_apply`); the coalgebra is assembled
from the duals of the algebras `A_X` as `X` varies.

The proof uses the representing object `P = CategoryTheory.Functor.hullRepresenting ω X` of `ω`
on `⟨X⟩`, with its point `p ∈ ω P`: evaluation at `p` identifies `P ⟶ Y` with `ω Y` for every
`Y ∈ ⟨X⟩`. Each `q ∈ ω P` defines a natural endomorphism of `ω` on `⟨X⟩`, sending `ω f p` to
`ω f q`; this identifies `A_X` with the regular module `ω P`. Consequently the `A_X`-submodules
of `ω Y` are the images of morphisms from finite direct sums of copies of `P`. Fullness then
follows by factoring through an epimorphism from such a direct sum, and every finitely generated
`A_X`-module is the fibre of a cokernel of a morphism between such direct sums.

## Main definitions and results

* `CategoryTheory.Functor.hullModuleFunctor`: the functor `⟨X⟩ ⥤ FGModuleCat A_X`, defined for
  a fibre functor to modules over a Noetherian ring that preserves monomorphisms and
  epimorphisms.
* `CategoryTheory.Functor.hullModuleFunctor_map_hom_hom_apply`: it acts on morphisms as `ω`.
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

/-- Every object of the hull of `X` has a finite fibre when `X` does. -/
theorem finite_obj_of_subquotientHull {Y : C} (hY : subquotientHull X Y) :
    Module.Finite R (ω.obj Y) := by
  obtain ⟨ι, _, Z, i, q, _, _⟩ := subquotientHull_iff.1 hY
  have : Module.Finite R (ω.obj Z) :=
    Module.Finite.of_injective _ ((ModuleCat.mono_iff_injective (ω.map i)).1 inferInstance)
  exact Module.Finite.of_surjective _ ((ModuleCat.epi_iff_surjective (ω.map q)).1 inferInstance)

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

/-- `hullModuleFunctor` acts on morphisms as `ω`. -/
@[simp]
theorem hullModuleFunctor_map_hom_hom_apply {Y Y' : (subquotientHull X).FullSubcategory}
    (g : Y ⟶ Y') (y : ω.obj Y.obj) :
    ((ω.hullModuleFunctor X).map g).hom.hom y = (ω.map g.hom).hom y :=
  (rfl)

end Functor

section Equivalence

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] {K : Type w} [Field K] [CategoryTheory.Linear K C]
  (ω : C ⥤ ModuleCat.{w} K) [ω.Additive] [ω.Linear K] [ω.Faithful] [PreservesFiniteLimits ω]
  [ω.PreservesEpimorphisms] (X : C) [FiniteDimensional K (ω.obj X)]

omit [CategoryTheory.Linear K C] [ω.Additive] [ω.Linear K] [ω.Faithful] [PreservesFiniteLimits ω]
  [ω.PreservesEpimorphisms] in
/-- The representing object `P_X` lies in the hull of `X`. -/
private lemma hullRepresenting_mem : subquotientHull X (ω.hullRepresenting X : C) :=
  subquotientHull.of_mono (ω.hullRepresenting X).arrow

variable {X}

/-- Evaluation at the point of `P_X`, as a linear equivalence `(P_X ⟶ Y) ≃ ω Y` for `Y` in the
hull of `X`. -/
private noncomputable def hullEvalEquiv {Y : C} (hY : subquotientHull X Y) :
    ((ω.hullRepresenting X : C) ⟶ Y) ≃ₗ[K] ω.obj Y :=
  LinearEquiv.ofBijective (ω.fiberSpanEval (ω.hullBasisPoint X) Y) (by
    obtain ⟨ι, _, Z, i, q, _, _⟩ := subquotientHull_iff.1 hY
    exact ω.bijective_fiberSpanEval_hullBasisPoint X i q)

private lemma hullEvalEquiv_apply {Y : C} (hY : subquotientHull X Y)
    (f : (ω.hullRepresenting X : C) ⟶ Y) :
    hullEvalEquiv ω hY f = (ω.map f).hom (ω.fiberSpanPoint (ω.hullBasisPoint X)) := by
  simp [hullEvalEquiv]

private lemma map_hullEvalEquiv_symm {Y : C} (hY : subquotientHull X Y) (y : ω.obj Y) :
    (ω.map ((hullEvalEquiv ω hY).symm y)).hom (ω.fiberSpanPoint (ω.hullBasisPoint X)) = y := by
  rw [← hullEvalEquiv_apply ω hY, LinearEquiv.apply_symm_apply]

private lemma hullEvalEquiv_symm_naturality {Y Y' : C} (hY : subquotientHull X Y)
    (hY' : subquotientHull X Y') (g : Y ⟶ Y') (y : ω.obj Y) :
    (hullEvalEquiv ω hY').symm ((ω.map g).hom y) = (hullEvalEquiv ω hY).symm y ≫ g := by
  rw [LinearEquiv.symm_apply_eq, hullEvalEquiv_apply, ω.map_comp, ModuleCat.comp_apply,
    map_hullEvalEquiv_symm]

/-- The natural endomorphism of `ω` on the hull of `X` attached to `q ∈ ω P_X`: it sends `ω f p`
to `ω f q` for every `f : P_X ⟶ Y`, where `p` is the point of `P_X`. -/
private noncomputable def hullEndOfPoint :
    ω.obj (ω.hullRepresenting X : C) →+ End ((subquotientHull X).ι ⋙ ω) :=
  AddMonoidHom.mk' (fun q ↦ .of
    { app Y := ModuleCat.ofHom
        { toFun y := (ω.map ((hullEvalEquiv ω Y.property).symm y)).hom q
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
    hullEndOfPoint ω q • y = (ω.map ((hullEvalEquiv ω Y.property).symm y)).hom q :=
  (rfl)

/-- The natural endomorphism attached to the point of `P_X` is the identity. -/
private lemma hullEndOfPoint_point :
    hullEndOfPoint (X := X) ω (ω.fiberSpanPoint (ω.hullBasisPoint X)) = 1 := by
  refine End.ext (NatTrans.ext (funext fun Y ↦ ?_))
  ext y
  rw [← natEndModule_smul, hullEndOfPoint_smul, map_hullEvalEquiv_symm, End.one_asHom,
    NatTrans.id_app, ModuleCat.id_apply]

/-- `hullEndOfPoint` is `End (⟨X⟩.ι ⋙ ω)`-linear: it identifies the algebra with the regular
module `ω P_X`. -/
private lemma hullEndOfPoint_app (η : End ((subquotientHull X).ι ⋙ ω))
    (q : ω.obj (ω.hullRepresenting X : C)) :
    hullEndOfPoint ω ((η.asHom.app ⟨_, hullRepresenting_mem ω X⟩).hom q) =
      η * hullEndOfPoint ω q := by
  refine End.ext (NatTrans.ext (funext fun Y ↦ ?_))
  ext y
  rw [← natEndModule_smul, ← natEndModule_smul, ← natEndModule_smul, mul_smul,
    hullEndOfPoint_smul, hullEndOfPoint_smul]
  simp only [natEndModule_smul]
  exact ω.map_hom_app_hom_apply η (Y := ⟨_, hullRepresenting_mem ω X⟩) _ q

/-- The value of a morphism out of a finite direct sum of copies of `P_X`, assembled from
morphisms with prescribed values `y j` at the point of `P_X`. -/
private lemma map_biproductDesc_apply {ι : Type} [Fintype ι]
    {Y : (subquotientHull X).FullSubcategory} (y : ι → ((subquotientHull X).ι ⋙ ω).obj Y)
    (v : ω.obj (⨁ fun _ : ι ↦ (ω.hullRepresenting X : C))) :
    (ω.map (biproduct.desc fun j ↦ (hullEvalEquiv ω Y.property).symm (y j))).hom v =
      ∑ j, hullEndOfPoint ω ((ω.map (biproduct.π _ j)).hom v) • y j := by
  conv_lhs => rw [← ω.sum_map_ι_map_π_apply _ v]
  rw [_root_.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hullEndOfPoint_smul, ← ModuleCat.comp_apply, ← ω.map_comp, biproduct.ι_desc]

/-- Every `End (⟨X⟩.ι ⋙ ω)`-linear map between fibres of objects of the hull of `X` is `ω g` for
some morphism `g`. -/
private lemma exists_map_eq {Y Y' : (subquotientHull X).FullSubcategory}
    (φ : ((subquotientHull X).ι ⋙ ω).obj Y →ₗ[End ((subquotientHull X).ι ⋙ ω)]
      ((subquotientHull X).ι ⋙ ω).obj Y') :
    ∃ g : Y.obj ⟶ Y'.obj, ∀ y, (ω.map g).hom y = φ y := by
  have : Module.Finite K (((subquotientHull X).ι ⋙ ω).obj Y) :=
    ω.finite_obj_of_subquotientHull Y.property
  let b := Module.finBasis K (((subquotientHull X).ι ⋙ ω).obj Y)
  let f₁ := biproduct.desc fun j ↦ (hullEvalEquiv ω Y.property).symm (b j)
  let f₂ := biproduct.desc fun j ↦ (hullEvalEquiv ω Y'.property).symm (φ (b j))
  have h₂ (v) : (ω.map f₂).hom v = φ ((ω.map f₁).hom v) := by
    simp only [f₁, f₂, map_biproductDesc_apply, _root_.map_sum, LinearMap.map_smul]
  have hsurj : Function.Surjective (ω.map f₁).hom := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨(ω.map (biproduct.ι _ j)).hom (ω.fiberSpanPoint (ω.hullBasisPoint X)), ?_⟩
    rw [← ModuleCat.comp_apply, ← ω.map_comp, biproduct.ι_desc, map_hullEvalEquiv_symm]
  have : Epi f₁ := ω.epi_of_epi_map ((ModuleCat.epi_iff_surjective _).2 hsurj)
  have hker : kernel.ι f₁ ≫ f₂ = 0 := ω.map_injective <| by
    ext z
    have hz : (ω.map f₁).hom ((ω.map (kernel.ι f₁)).hom z) = 0 := by
      rw [← ModuleCat.comp_apply, ← ω.map_comp, kernel.condition]
      simp
    rw [ω.map_comp, ModuleCat.comp_apply, h₂, hz, map_zero φ]
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
  refine ⟨_, biproduct.desc fun j ↦ (hullEvalEquiv ω Y.property).symm (b j).val, fun y ↦
    ⟨fun hy ↦ ?_, ?_⟩⟩
  · have hsum := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, SetLike.val_smul] at hsum
    refine ⟨∑ j, b.repr ⟨y, hy⟩ j •
      (ω.map (biproduct.ι _ j)).hom (ω.fiberSpanPoint (ω.hullBasisPoint X)), ?_⟩
    simp only [_root_.map_sum, _root_.map_smul, ← ModuleCat.comp_apply, ← ω.map_comp,
      biproduct.ι_desc, map_hullEvalEquiv_symm]
    exact hsum
  · rintro ⟨v, rfl⟩
    rw [map_biproductDesc_apply]
    exact N.sum_mem fun j _ ↦ N.smul_mem _ (b j).property

/-- The `End (⟨X⟩.ι ⋙ ω)`-linear map from the fibre of `n` copies of `P_X` to a module `M`
sending the point of the `j`-th copy to `s j`. -/
private noncomputable def biproductLinearMap {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module (End ((subquotientHull X).ι ⋙ ω)) M] (s : Fin n → M) :
    ((subquotientHull X).ι ⋙ ω).obj
        ⟨_, subquotientHull_biproduct _ fun _ : Fin n ↦ hullRepresenting_mem ω X⟩ →ₗ[
      End ((subquotientHull X).ι ⋙ ω)] M where
  toFun v := ∑ j, hullEndOfPoint ω ((ω.map (biproduct.π _ j)).hom v) • s j
  map_add' v v' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' η v := by
    simp only [RingHom.id_apply, Finset.smul_sum, ← mul_smul, ← hullEndOfPoint_app]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [natEndModule_smul, ω.map_hom_app_hom_apply η
      (Y := ⟨_, subquotientHull_biproduct _ fun _ : Fin n ↦ hullRepresenting_mem ω X⟩)
      (Y' := ⟨_, hullRepresenting_mem ω X⟩)]

private lemma biproductLinearMap_map_ι {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module (End ((subquotientHull X).ι ⋙ ω)) M] (s : Fin n → M)
    (j : Fin n) :
    biproductLinearMap ω s
      ((ω.map (biproduct.ι _ j)).hom (ω.fiberSpanPoint (ω.hullBasisPoint X))) = s j := by
  simp only [biproductLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single j]
  · rw [← ModuleCat.comp_apply, ← ω.map_comp, biproduct.ι_π_self, ω.map_id, ModuleCat.id_apply,
      hullEndOfPoint_point, one_smul]
  · intro k _ hk
    rw [← ModuleCat.comp_apply, ← ω.map_comp, biproduct.ι_π_ne _ (Ne.symm hk)]
    simp
  · simp

/-- Every finitely generated `End (⟨X⟩.ι ⋙ ω)`-module is isomorphic to the fibre of an object of
the hull of `X`. -/
private lemma exists_iso (M : FGModuleCat.{w} (End ((subquotientHull X).ι ⋙ ω))) :
    ∃ Y, Nonempty (((subquotientHull X).ι ⋙ ω).toNatEndModule.obj Y ≅ M.obj) := by
  have : Module.Finite (End ((subquotientHull X).ι ⋙ ω)) M.obj := M.property
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := End ((subquotientHull X).ι ⋙ ω)) (M := M.obj)
  have hQ := subquotientHull_biproduct _ fun _ : Fin n ↦ hullRepresenting_mem ω X
  let ρ : ((subquotientHull X).ι ⋙ ω).toNatEndModule.obj ⟨_, hQ⟩ →ₗ[
      End ((subquotientHull X).ι ⋙ ω)] M.obj :=
    biproductLinearMap ω s
  have hρ : Function.Surjective ρ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨_, biproductLinearMap_map_ι ω s j⟩
  obtain ⟨m, f, hf⟩ := exists_range_eq ω (LinearMap.ker ρ)
  have hY : subquotientHull X (cokernel f) :=
    (subquotientHull X).prop_of_epi (cokernel.π f) hQ
  let π := ((subquotientHull X).ι ⋙ ω).toNatEndModule.map
    (ObjectProperty.homMk (Y := ⟨_, hY⟩) (cokernel.π f))
  have hπ : Function.Surjective π.hom :=
    (ModuleCat.epi_iff_surjective (ω.map (cokernel.π f))).1 inferInstance
  have := preservesHomology_of_preservesEpis_and_kernels ω
  have hex := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    ((ShortComplex.exact_cokernel f).map ω)
  have hker : LinearMap.ker π.hom = LinearMap.ker ρ := by
    ext v
    refine ⟨fun hv ↦ (hf v).2 (hex hv), fun hv ↦ ?_⟩
    obtain ⟨u, rfl⟩ := (hf v).1 hv
    refine LinearMap.mem_ker.2 ?_
    rw [toNatEndModule_map_hom_apply, Functor.comp_map, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom, ← ModuleCat.comp_apply, ← ω.map_comp, cokernel.condition,
      ω.map_zero]
    -- The zero of the `End (⟨X⟩.ι ⋙ ω)`-module `toNatEndModule.obj Y` is by definition the zero
    -- of `ω Y`; the two sides differ only in which of these instances they display.
    rfl
  exact ⟨⟨_, hY⟩, ⟨LinearEquiv.toModuleIso ((π.hom.quotKerEquivOfSurjective hπ).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ ρ.quotKerEquivOfSurjective hρ)⟩⟩

/-- Every `End (⟨X⟩.ι ⋙ ω)`-linear map between fibres of objects of the hull of `X` is the image
under `ω` of a morphism. -/
instance : (((subquotientHull X).ι ⋙ ω).toNatEndModule).Full where
  map_surjective {Y Y'} φ := by
    obtain ⟨g, hg⟩ := exists_map_eq ω φ.hom
    exact ⟨ObjectProperty.homMk g, ModuleCat.hom_ext (LinearMap.ext hg)⟩

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
