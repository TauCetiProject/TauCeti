/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.BiproductPower
public import TauCeti.CategoryTheory.Abelian.SubquotientHull
public import TauCeti.CategoryTheory.Linear.FullSubcategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The endomorphism algebra of a fibre functor on the hull of an object

Let `ω : C ⥤ ModuleCat R` be an additive functor on an abelian category and let `X : C`. Write
`⟨X⟩` for the full subcategory `TauCeti.subquotientHull X` of subquotients of finite direct sums
of copies of `X`. This file studies the algebra `End (⟨X⟩.ι ⋙ ω)` of natural endomorphisms of
the restricted fibre functor. It is the finite algebra from which the coalgebra of a category
with an exact faithful fibre functor is assembled, by dualizing and passing to the filtered
colimit over nested hulls.

An endomorphism `f` of `ω X` acts diagonally on `ω (⨁ (fun _ : ι ↦ X))`
(`CategoryTheory.Functor.powerAlgHom`, from `TauCeti.Algebra.Category.ModuleCat.BiproductPower`).
The subalgebra `CategoryTheory.Functor.hullAlgebra` of `Module.End R (ω X)` consists of those
`f` whose diagonal actions preserve the image of `ω Z` for every subobject `Z` of every finite
power of `X`. Evaluation at `X` identifies the
natural endomorphisms with this subalgebra when `ω` is exact
(`CategoryTheory.Functor.hullEndAlgEquiv`). Preservation of the images of subobjects of `X`
alone would not suffice: subobjects of `X ⊞ X` include graphs of endomorphisms of `X`, and these
force the commutation with `ω` of morphisms in `⟨X⟩`.

## Main definitions and results

* `CategoryTheory.Functor.hullAlgebra`: the endomorphisms of `ω X` whose diagonal actions
  preserve the images of all subobjects of finite powers of `X`.
* `CategoryTheory.Functor.hullEvalAlgHom`: evaluation at `X` of natural endomorphisms of
  `⟨X⟩.ι ⋙ ω`. It is injective when `ω` preserves monomorphisms and epimorphisms
  (`CategoryTheory.Functor.hullEvalAlgHom_injective`), and its range is `hullAlgebra` when
  moreover `ω` preserves finite limits (`CategoryTheory.Functor.range_hullEvalAlgHom`).
* `CategoryTheory.Functor.hullEndAlgEquiv`: the resulting algebra isomorphism.
* The natural endomorphism algebra is a finite `R`-module when `ω X` is finite over a
  Noetherian ring and `ω` preserves monomorphisms and epimorphisms, in particular
  finite-dimensional over a field.
* `CategoryTheory.Functor.hullEvalAlgHom_restrictEndAlgHom`: for `Y ∈ ⟨X⟩`, the transition map
  `ObjectProperty.restrictEndAlgHom` from the algebra of `⟨X⟩` to that of `⟨Y⟩` followed by
  evaluation at `Y` is the component at `Y`. Unit and composition laws of the transition maps are
  `ObjectProperty.restrictEndAlgHom_refl` and `ObjectProperty.restrictEndAlgHom_comp`.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, Lemma 2.13.
-/

public section

namespace CategoryTheory.Functor

open Limits TauCeti

universe w v u u'

variable {R : Type u'} [CommRing R] {C : Type u} [Category.{v} C]

section Power

variable [Preadditive C] [HasFiniteBiproducts C] (ω : C ⥤ ModuleCat.{w} R) [ω.Additive]
  {X : C}

variable (X) in
/-- The endomorphisms `f` of `ω X` whose diagonal action on every finite power
`ω (⨁ fun _ : ι ↦ X)` preserves the image of `ω Z` for every subobject `Z` of that power. -/
noncomputable def hullAlgebra : Subalgebra R (Module.End R (ω.obj X)) where
  carrier := {f | ∀ (ι : Type) [Fintype ι] (Z : C) (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i],
    LinearMap.range (ω.map i).hom ∈ Module.End.invtSubmodule (ω.powerAlgHom X ι f)}
  mul_mem' {f g} hf hg ι _ Z i _ := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro v hv
    rw [_root_.map_mul, mul_apply_eq_comp]
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 (hf ι Z i) _
      ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 (hg ι Z i) v hv)
  add_mem' {f g} hf hg ι _ Z i _ := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro v hv
    rw [_root_.map_add, LinearMap.add_apply]
    exact add_mem ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 (hf ι Z i) v hv)
      ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 (hg ι Z i) v hv)
  algebraMap_mem' c ι _ Z i _ := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem, AlgHom.commutes]
    intro v hv
    simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ c hv

/-- Membership in `hullAlgebra`: the diagonal action preserves the images of all subobjects of
finite powers of `X`. -/
theorem mem_hullAlgebra_iff {f : Module.End R (ω.obj X)} :
    f ∈ ω.hullAlgebra X ↔ ∀ (ι : Type) [Fintype ι] (Z : C) (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i],
      LinearMap.range (ω.map i).hom ∈ Module.End.invtSubmodule (ω.powerAlgHom X ι f) :=
  Iff.rfl

end Power

section Hull

variable [Preadditive C] [HasFiniteBiproducts C] (ω : C ⥤ ModuleCat.{w} R) (X : C)

/-- Evaluation at `X` of natural endomorphisms of the fibre functor restricted to the hull of
`X`. -/
noncomputable def hullEvalAlgHom :
    End ((subquotientHull X).ι ⋙ ω) →ₐ[R] Module.End R (ω.obj X) where
  toFun η := (η.asHom.app ⟨X, subquotientHull_self⟩).hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {X}

@[simp]
theorem hullEvalAlgHom_apply (η : End ((subquotientHull X).ι ⋙ ω)) :
    ω.hullEvalAlgHom X η = (η.asHom.app ⟨X, subquotientHull_self⟩).hom :=
  (rfl)

/-- Naturality of an endomorphism of the restricted fibre functor, evaluated on elements. -/
theorem map_hom_app_hom_apply (η : End ((subquotientHull X).ι ⋙ ω))
    {Y Y' : (subquotientHull X).FullSubcategory} (g : Y.obj ⟶ Y'.obj) (v : ω.obj Y.obj) :
    (ω.map g).hom ((η.asHom.app Y).hom v) = (η.asHom.app Y').hom ((ω.map g).hom v) := by
  simpa using (congrArg (fun φ ↦ φ.hom v)
    (η.asHom.naturality (ObjectProperty.homMk (P := subquotientHull X) (X := Y) (Y := Y') g))).symm

variable [ω.Additive]

/-- The component of a natural endomorphism at a finite power of `X` is the diagonal action of
its component at `X`. -/
theorem hom_app_biproduct_eq_powerAlgHom (η : End ((subquotientHull X).ι ⋙ ω)) (ι : Type)
    [Fintype ι] :
    (η.asHom.app ⟨_, subquotientHull_biproduct_const (X := X) ι⟩).hom =
      ω.powerAlgHom X ι (ω.hullEvalAlgHom X η) :=
  (eq_powerAlgHom_iff ω _ _).2 fun j v ↦ by
    simpa using ω.map_hom_app_hom_apply η (Y := ⟨_, subquotientHull_biproduct_const ι⟩)
      (Y' := ⟨X, subquotientHull_self⟩) (biproduct.π _ j) v

/-- Evaluation at `X` lands in `hullAlgebra`. -/
theorem hullEvalAlgHom_mem (η : End ((subquotientHull X).ι ⋙ ω)) :
    ω.hullEvalAlgHom X η ∈ ω.hullAlgebra X := by
  intro ι _ Z i _
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  rintro _ ⟨z, rfl⟩
  refine ⟨(η.asHom.app ⟨Z, subquotientHull.of_mono i⟩).hom z, ?_⟩
  rw [← hom_app_biproduct_eq_powerAlgHom]
  exact ω.map_hom_app_hom_apply η (Y := ⟨Z, subquotientHull.of_mono i⟩)
    (Y' := ⟨_, subquotientHull_biproduct_const ι⟩) i z

/-- A natural endomorphism of the restricted fibre functor is determined by its component at
`X`, as every object of the hull is a quotient of a subobject of a finite power of `X`. -/
theorem hullEvalAlgHom_injective [ω.PreservesMonomorphisms] [ω.PreservesEpimorphisms] :
    Function.Injective (ω.hullEvalAlgHom X) := by
  intro η η' h
  refine End.ext (NatTrans.ext (funext fun Y ↦ ?_))
  obtain ⟨ι, _, Z, i, p, _, _⟩ := subquotientHull_iff.1 Y.property
  have := Fintype.ofFinite ι
  have hZ : subquotientHull X Z := .of_mono i
  have hpow := (hom_app_biproduct_eq_powerAlgHom ω η ι).trans
    (h ▸ (hom_app_biproduct_eq_powerAlgHom ω η' ι).symm)
  have hZeq : (η.asHom.app ⟨Z, hZ⟩).hom = (η'.asHom.app ⟨Z, hZ⟩).hom := by
    ext z
    apply (ModuleCat.mono_iff_injective (ω.map i)).1 inferInstance
    rw [ω.map_hom_app_hom_apply η (Y := ⟨Z, hZ⟩) (Y' := ⟨_, subquotientHull_biproduct_const ι⟩),
      ω.map_hom_app_hom_apply η' (Y := ⟨Z, hZ⟩) (Y' := ⟨_, subquotientHull_biproduct_const ι⟩),
      hpow]
  ext v
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (ω.map p)).1 inferInstance v
  rw [← ω.map_hom_app_hom_apply η (Y := ⟨Z, hZ⟩) (Y' := Y),
    ← ω.map_hom_app_hom_apply η' (Y := ⟨Z, hZ⟩) (Y' := Y), hZeq]

end Hull

section Exact

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] (ω : C ⥤ ModuleCat.{w} R) {X Y : C}

/-- Fibre compatibility of the transition maps between nested hulls: for `Y` in the hull of `X`,
restricting a natural endomorphism to the hull of `Y` and evaluating at `Y` gives its component
at `Y`. -/
theorem hullEvalAlgHom_restrictEndAlgHom (h : subquotientHull X Y)
    (η : End ((subquotientHull X).ι ⋙ ω)) :
    ω.hullEvalAlgHom Y
        (ObjectProperty.restrictEndAlgHom (R := R) (subquotientHull_le_of_mem h) ω η) =
      (η.asHom.app ⟨Y, h⟩).hom := by
  rw [hullEvalAlgHom_apply, ObjectProperty.restrictEndAlgHom_asHom_app]
  rfl

variable [ω.Additive]

section Construction

/-! ### From an element of `hullAlgebra` to a natural endomorphism -/

variable {ω} {f : Module.End R (ω.obj X)} (hf : f ∈ ω.hullAlgebra X)

include hf in
private lemma mapsTo_range {ι : Type} [Fintype ι] {Z : C} (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i] :
    ∀ v ∈ LinearMap.range (ω.map i).hom,
      ω.powerAlgHom X ι f v ∈ LinearMap.range (ω.map i).hom :=
  (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 (hf ι Z i)

/-- The endomorphism of `ω Z`, for a subobject `Z` of a finite power of `X`, induced by the
diagonal action of `f`. -/
private noncomputable def subEnd {ι : Type} [Fintype ι] {Z : C} (i : Z ⟶ ⨁ fun _ : ι ↦ X)
    [Mono i] [ω.PreservesMonomorphisms] : Module.End R (ω.obj Z) :=
  let e := LinearEquiv.ofInjective (ω.map i).hom
    ((ModuleCat.mono_iff_injective (ω.map i)).1 inferInstance)
  e.symm.toLinearMap ∘ₗ (ω.powerAlgHom X ι f).restrict (mapsTo_range hf i) ∘ₗ e.toLinearMap

private lemma map_subEnd {ι : Type} [Fintype ι] {Z : C} (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i]
    [ω.PreservesMonomorphisms] (z : ω.obj Z) :
    (ω.map i).hom (subEnd hf i z) = ω.powerAlgHom X ι f ((ω.map i).hom z) := by
  simp only [subEnd, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.ofInjective_symm_apply, LinearMap.coe_restrict_apply,
    LinearEquiv.ofInjective_apply]

/-- If `m : W ⟶ ⨁ fun _ : κ ↦ X` has, along an index map `e`, the components of `q ≫ i`, then
`ω q` intertwines lifts along `ω m` of the diagonal action with the induced endomorphism of the
subobject `Z`. -/
private lemma map_eq_subEnd [ω.PreservesMonomorphisms] {ι κ : Type} [Fintype ι] [Fintype κ]
    {W Z : C} (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i] (q : W ⟶ Z) (m : W ⟶ ⨁ fun _ : κ ↦ X)
    (e : ι → κ) (hm : ∀ j, m ≫ biproduct.π _ (e j) = q ≫ i ≫ biproduct.π _ j)
    {w w₁ : ω.obj W}
    (hw : (ω.map m).hom w₁ = ω.powerAlgHom X κ f ((ω.map m).hom w)) :
    (ω.map q).hom w₁ = subEnd hf i ((ω.map q).hom w) := by
  have hcomp : ∀ (j : ι) (x : ω.obj W), (ω.map (biproduct.π (fun _ : κ ↦ X) (e j))).hom
      ((ω.map m).hom x) = (ω.map (biproduct.π (fun _ : ι ↦ X) j)).hom
        ((ω.map i).hom ((ω.map q).hom x)) := fun j x ↦ by
    simpa using congrArg (fun φ ↦ (ω.map φ).hom x) (hm j)
  apply (ModuleCat.mono_iff_injective (ω.map i)).1 inferInstance
  refine ext_map_π_apply ω fun j ↦ ?_
  rw [map_subEnd, map_π_powerAlgHom_apply, ← hcomp, ← hcomp, hw, map_π_powerAlgHom_apply]

/-- The induced endomorphisms of two subobjects of finite powers of `X` are compatible with any
two morphisms `a`, `b` to a common target: this is the graph argument of Deligne–Milne. -/
private lemma map_subEnd_eq [PreservesFiniteLimits ω] {ι ι' : Type} [Fintype ι] [Fintype ι']
    {Z Z' T : C} (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i] (i' : Z' ⟶ ⨁ fun _ : ι' ↦ X) [Mono i']
    (a : Z ⟶ T) (b : Z' ⟶ T) {z : ω.obj Z} {z' : ω.obj Z'}
    (h : (ω.map a).hom z = (ω.map b).hom z') :
    (ω.map a).hom (subEnd hf i z) = (ω.map b).hom (subEnd hf i' z') := by
  -- An element of `ω` of the pullback lying over `(z, z')`.
  obtain ⟨w, hw, hw'⟩ : ∃ w, (ω.map (pullback.fst a b)).hom w = z ∧
      (ω.map (pullback.snd a b)).hom w = z' := by
    simpa using Types.exists_of_isPullback
      ((forget (ModuleCat.{w} R)).map_isPullback
        (ω.map_isPullback (IsPullback.of_hasPullback a b))) z z' h
  -- The pullback embeds in the finite power of `X` indexed by `ι ⊕ ι'`.
  let m : pullback a b ⟶ ⨁ fun _ : ι ⊕ ι' ↦ X := biproduct.lift (Sum.elim
    (fun j ↦ pullback.fst a b ≫ i ≫ biproduct.π _ j)
    (fun j ↦ pullback.snd a b ≫ i' ≫ biproduct.π _ j))
  have hl : ∀ j, m ≫ biproduct.π _ (Sum.inl j) = pullback.fst a b ≫ i ≫ biproduct.π _ j :=
    fun j ↦ by simp [m]
  have hr : ∀ j, m ≫ biproduct.π _ (Sum.inr j) = pullback.snd a b ≫ i' ≫ biproduct.π _ j :=
    fun j ↦ by simp [m]
  have : Mono m := ⟨fun u v huv ↦ by
    refine pullback.hom_ext ((cancel_mono i).1 (biproduct.hom_ext _ _ fun j ↦ ?_))
      ((cancel_mono i').1 (biproduct.hom_ext _ _ fun j ↦ ?_))
    · simpa [hl] using congrArg (· ≫ biproduct.π _ (Sum.inl j)) huv
    · simpa [hr] using congrArg (· ≫ biproduct.π _ (Sum.inr j)) huv⟩
  obtain ⟨w₁, hw₁⟩ := mapsTo_range hf m _ ⟨w, rfl⟩
  have h₁ := map_eq_subEnd hf i (pullback.fst a b) m Sum.inl hl hw₁
  have h₂ := map_eq_subEnd hf i' (pullback.snd a b) m Sum.inr hr hw₁
  rw [hw] at h₁
  rw [hw'] at h₂
  rw [← h₁, ← h₂, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← ω.map_comp, ← ω.map_comp,
    pullback.condition]

variable [PreservesFiniteLimits ω] [ω.PreservesEpimorphisms]

/-- On each object of the hull, `f` induces an endomorphism of the fibre compatible with every
quotient map from a subobject of a finite power of `X`. -/
private lemma exists_hullAction {Y : C} (hY : subquotientHull X Y) :
    ∃ g : Module.End R (ω.obj Y), ∀ (ι : Type) [Fintype ι] (Z : C)
      (i : Z ⟶ ⨁ fun _ : ι ↦ X) [Mono i] (p : Z ⟶ Y) (z : ω.obj Z),
      g ((ω.map p).hom z) = (ω.map p).hom (subEnd hf i z) := by
  obtain ⟨ι₀, _, Z₀, i₀, p₀, _, _⟩ := subquotientHull_iff.1 hY
  have := Fintype.ofFinite ι₀
  have hp₀ := (ModuleCat.epi_iff_surjective (ω.map p₀)).1 inferInstance
  refine ⟨(ω.map p₀).hom.liftOfSurjective hp₀
    ⟨(ω.map p₀).hom ∘ₗ subEnd hf i₀, fun z hz ↦ ?_⟩, fun ι _ Z i _ p z ↦ ?_⟩
  · rw [LinearMap.mem_ker] at hz ⊢
    rw [LinearMap.comp_apply, map_subEnd_eq hf i₀ i₀ p₀ p₀ (z' := 0) (by rw [hz, _root_.map_zero]),
      _root_.map_zero, _root_.map_zero]
  · obtain ⟨z₀, hz₀⟩ := hp₀ ((ω.map p).hom z)
    rw [← hz₀, LinearMap.equivOfSurjective_apply, LinearMap.comp_apply]
    exact map_subEnd_eq hf i₀ i p₀ p hz₀

/-- The natural endomorphism of the restricted fibre functor induced by `f ∈ hullAlgebra`. -/
private noncomputable def hullEndOfMem : End ((subquotientHull X).ι ⋙ ω) := .of
  { app Y := ModuleCat.ofHom (exists_hullAction hf Y.property).choose
    naturality Y Y' g := by
      obtain ⟨Y, hY⟩ := Y
      obtain ⟨Y', hY'⟩ := Y'
      obtain ⟨ι, _, Z, i, p, _, _⟩ := subquotientHull_iff.1 hY
      have := Fintype.ofFinite ι
      ext v
      obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (ω.map p)).1 inferInstance v
      have h₁ := (exists_hullAction hf hY).choose_spec ι Z i p z
      have h₂ := (exists_hullAction hf hY').choose_spec ι Z i (p ≫ g.hom) z
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h₂
      simp [h₁, h₂] }

private lemma hullEvalAlgHom_hullEndOfMem : ω.hullEvalAlgHom X (hullEndOfMem hf) = f := by
  ext x
  have h := (exists_hullAction hf (subquotientHull_self (X := X))).choose_spec Unit X
    (biproduct.ι (fun _ : Unit ↦ X) ()) (𝟙 X) x
  simp only [Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply] at h
  refine h.trans ((ModuleCat.mono_iff_injective (ω.map (biproduct.ι (fun _ : Unit ↦ X) ()))).1
    inferInstance ?_)
  rw [map_subEnd, powerAlgHom_map_ι_apply]

end Construction

variable [PreservesFiniteLimits ω] [ω.PreservesEpimorphisms]

/-- For an exact fibre functor, the components at `X` of natural endomorphisms of the restricted
fibre functor are exactly the elements of `hullAlgebra`: Deligne–Milne, Lemma 2.13. -/
theorem range_hullEvalAlgHom : (ω.hullEvalAlgHom X).range = ω.hullAlgebra X := by
  refine le_antisymm ?_ fun f hf ↦ ⟨hullEndOfMem hf, hullEvalAlgHom_hullEndOfMem hf⟩
  rintro _ ⟨η, rfl⟩
  exact ω.hullEvalAlgHom_mem η

variable (X) in
/-- For an exact fibre functor, evaluation at `X` identifies the natural endomorphisms of the
fibre functor restricted to the hull of `X` with `hullAlgebra`. -/
noncomputable def hullEndAlgEquiv : End ((subquotientHull X).ι ⋙ ω) ≃ₐ[R] ω.hullAlgebra X :=
  (AlgEquiv.ofInjective _ (ω.hullEvalAlgHom_injective)).trans
    (Subalgebra.equivOfEq _ _ (ω.range_hullEvalAlgHom))

@[simp]
theorem coe_hullEndAlgEquiv_apply (η : End ((subquotientHull X).ι ⋙ ω)) :
    (ω.hullEndAlgEquiv X η : Module.End R (ω.obj X)) = ω.hullEvalAlgHom X η :=
  (rfl)

end Exact

section Finite

variable [Preadditive C] [HasFiniteBiproducts C] (ω : C ⥤ ModuleCat.{w} R) [ω.Additive]
  [ω.PreservesMonomorphisms] [ω.PreservesEpimorphisms] (X : C)

/-- The endomorphism algebra of the fibre functor on the hull of `X` is a finite module when
`ω X` is a finite module over a Noetherian ring; over a field it is finite-dimensional. -/
instance [IsNoetherianRing R] [Module.Finite R (ω.obj X)] :
    Module.Finite R (End ((subquotientHull X).ι ⋙ ω)) :=
  Module.Finite.of_injective (R := R) (ω.hullEvalAlgHom X).toLinearMap
    (ω.hullEvalAlgHom_injective)

end Finite

end CategoryTheory.Functor
