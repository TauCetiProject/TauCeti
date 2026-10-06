/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.CategoryTheory.Monoidal.Internal.Module

/-!
# The relative spectrum of a quasi-coherent commutative algebra

Let `X` be a scheme. A commutative `𝒪ₓ`-algebra is a commutative monoid object `A` in the symmetric
monoidal category `X.Modules`, and it is quasi-coherent when its underlying module `A.X` is. This
file constructs the relative spectrum `Spec_X(A) ⟶ X` of a quasi-coherent commutative
`𝒪ₓ`-algebra by gluing the affine schemes `Spec Γ(A.X, U)` over the affine opens `U` of `X`.

The sections `Γ(A.X, U)` of a commutative `𝒪ₓ`-algebra form a commutative `Γ(X, U)`-algebra: the
sections functor `Scheme.Modules.sectionsFunctor U` is lax braided monoidal, so it carries `A` to a
commutative monoid in `Γ(X, U)`-modules. Restriction of sections is a ring homomorphism, which gives
a presheaf of commutative rings `A.sectionsPresheaf` on `X` under the structure presheaf. When `A`
is quasi-coherent, the sections over a basic open `X.basicOpen f` of an affine open `U` are the
localization of the sections over `U` at `f` (`CategoryTheory.CommMon.isLocalization_basicOpen`).
This is exactly the input of Mathlib's relative gluing on the small affine Zariski site
(`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`).

## Main declarations

* `CategoryTheory.CommMon.commRingSections`, `CategoryTheory.CommMon.algebraSections`: the sections
  of a commutative `𝒪ₓ`-algebra over an open `U` form a commutative `Γ(X, U)`-algebra;
* `CategoryTheory.CommMon.sectionsPresheaf A`: the presheaf of commutative rings of sections of
  `A`, with `CategoryTheory.CommMon.toSectionsPresheaf A : X.presheaf ⟶ A.sectionsPresheaf`;
* `CategoryTheory.CommMon.sectionsAlgHom` and `CategoryTheory.CommMon.sectionsPresheafMap`:
  algebra morphisms on sections and their compatibility with restriction and structure maps;
* `CategoryTheory.CommMon.isLocalization_basicOpen`: for quasi-coherent `A`, an affine open `U`
  and `f ∈ Γ(X, U)`, `Γ(A.X, X.basicOpen f)` is the localization of `Γ(A.X, U)` away from `f`;
* `CategoryTheory.CommMon.relativeSpec A`: the relative spectrum of a quasi-coherent commutative
  `𝒪ₓ`-algebra, with structure morphism `CategoryTheory.CommMon.relativeSpecToBase A`, which is
  affine;
* `CategoryTheory.CommMon.isPullback_relativeSpecCover`: over an affine open `U` of `X`, the
  relative spectrum is `Spec Γ(A.X, U)`.

## References

* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative spectrum
  via gluing).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon X.Modules)

/-- The sections over `U` of a commutative `𝒪ₓ`-algebra, as a commutative monoid object in
`Γ(X, U)`-modules: the image of `A` under the lax braided sections functor. -/
abbrev _root_.CategoryTheory.CommMon.sectionsCommMon (U : X.Opens) :
    CommMon (ModuleCat.{u} Γ(X, U)) :=
  (Scheme.Modules.sectionsFunctor U).mapCommMon.obj A

/-- The sections of a commutative `𝒪ₓ`-algebra over an open form a commutative ring. Its
multiplication is the monoid multiplication of `A` applied to the image of `x ⊗ₜ y` in the sections
of the tensor product (`CategoryTheory.CommMon.sections_mul_def`). -/
instance _root_.CategoryTheory.CommMon.commRingSections (U : X.Opens) : CommRing Γ(A.X, U) :=
  ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing (A.sectionsCommMon U).X

/-- The sections of a commutative `𝒪ₓ`-algebra over an open `U` form a `Γ(X, U)`-algebra, whose
scalar multiplication is that of the sections of the underlying `𝒪ₓ`-module. -/
instance _root_.CategoryTheory.CommMon.algebraSections (U : X.Opens) :
    Algebra Γ(X, U) Γ(A.X, U) :=
  ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ (A.sectionsCommMon U).X

/-- The product of two sections of a commutative `𝒪ₓ`-algebra is the multiplication of `A`
applied to the image of their tensor product under the tensor map of the sections functor. -/
lemma _root_.CategoryTheory.CommMon.sections_mul_def (U : X.Opens) (x y : Γ(A.X, U)) :
    x * y = (MonObj.mul (X := A.X)).app U
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) A.X A.X (x ⊗ₜ y)) :=
  (rfl)

/-- The structure map `Γ(X, U) → Γ(A.X, U)` of a commutative `𝒪ₓ`-algebra is the unit of `A` on
sections over `U`. -/
lemma _root_.CategoryTheory.CommMon.sections_algebraMap_def (U : X.Opens) (r : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(A.X, U) r = (MonObj.one (X := A.X)).app U
      (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r) :=
  (rfl)

/-- Restriction of sections of a commutative `𝒪ₓ`-algebra along an inclusion of opens `V ≤ U`,
as a ring homomorphism. -/
def _root_.CategoryTheory.CommMon.restrictSections {U V : X.Opens} (i : V ⟶ U) :
    Γ(A.X, U) →+* Γ(A.X, V) where
  toFun := A.X.presheaf.map i.op
  map_one' := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    -- The unit of sections is `η[A.X]` applied to `1`; both maps commute with restriction.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.one (X := A.X)).val i.op
      ((Functor.LaxMonoidal.ε F).app' (op U) (1 : Γ(X, U)))
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) i.op (1 : Γ(X, U))
    exact h₁.symm.trans (congrArg _ (h₂.symm.trans
      (congrArg _ (map_one (X.presheaf.map i.op).hom))))
  map_mul' x y := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    -- The product is `μ[A.X]` applied to the tensor map of `F`; both commute with restriction,
    -- and restriction of the sectionwise tensor product sends `x ⊗ₜ y` to the pure tensor of
    -- the restrictions.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.mul (X := A.X)).val i.op
      ((Functor.LaxMonoidal.μ F A.X A.X).app' (op U) (x ⊗ₜ y))
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.μ F A.X A.X) i.op (x ⊗ₜ y)
    exact h₁.symm.trans (congrArg _ h₂.symm)
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
lemma _root_.CategoryTheory.CommMon.restrictSections_apply {U V : X.Opens} (i : V ⟶ U)
    (x : Γ(A.X, U)) :
    A.restrictSections i x = A.X.presheaf.map i.op x :=
  (rfl)

/-- The presheaf of commutative rings of sections of a commutative `𝒪ₓ`-algebra. -/
@[expose]
def _root_.CategoryTheory.CommMon.sectionsPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of Γ(A.X, U.unop)
  map i := CommRingCat.ofHom (A.restrictSections i.unop)
  map_id U := by
    ext x
    exact congr($(A.X.presheaf.map_id U) x)
  map_comp i j := by
    ext x
    exact congr($(A.X.presheaf.map_comp i j) x)

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheaf_obj (U : X.Opensᵒᵖ) :
    A.sectionsPresheaf.obj U = CommRingCat.of Γ(A.X, U.unop) :=
  (rfl)

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheaf_map {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    A.sectionsPresheaf.map i = CommRingCat.ofHom (A.restrictSections i.unop) :=
  (rfl)

/-- The structure morphism from the structure presheaf of `X` to the presheaf of sections of a
commutative `𝒪ₓ`-algebra, given on each open by the algebra map. -/
def _root_.CategoryTheory.CommMon.toSectionsPresheaf : X.presheaf ⟶ A.sectionsPresheaf where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) Γ(A.X, U.unop))
  naturality {U V} i := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    ext r
    -- The algebra map is `η[A.X]` after the unit map of `F`; both commute with restriction.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.one (X := A.X)).val i
      ((Functor.LaxMonoidal.ε F).app' U r)
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) i r
    exact (congrArg _ h₂).trans h₁

@[simp]
lemma _root_.CategoryTheory.CommMon.toSectionsPresheaf_app (U : X.Opensᵒᵖ) :
    A.toSectionsPresheaf.app U = CommRingCat.ofHom (algebraMap Γ(X, U.unop) Γ(A.X, U.unop)) :=
  (rfl)

/-- The algebra map on sections induced by a morphism of commutative `𝒪ₓ`-algebras.
It sends each section to its image under the morphism and preserves the structure map
from `Γ(X, U)`. -/
def _root_.CategoryTheory.CommMon.sectionsAlgHom {A B : CommMon X.Modules}
    (f : A ⟶ B) (U : X.Opens) : Γ(A.X, U) →ₐ[Γ(X, U)] Γ(B.X, U) :=
  (ModuleCat.MonModuleEquivalenceAlgebra.functor.map
    (((Scheme.Modules.sectionsFunctor U).mapCommMon.map f).hom)).hom

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsAlgHom_apply {A B : CommMon X.Modules}
    (f : A ⟶ B) (U : X.Opens) (x : Γ(A.X, U)) :
    CommMon.sectionsAlgHom f U x = f.hom.hom.app U x :=
  (rfl)

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsAlgHom_id (A : CommMon X.Modules) (U : X.Opens) :
    CommMon.sectionsAlgHom (𝟙 A) U = AlgHom.id Γ(X, U) Γ(A.X, U) := by
  let F := (Scheme.Modules.sectionsFunctor U).mapCommMon ⋙
    CommMon.forget₂Mon (ModuleCat.{u} Γ(X, U)) ⋙ ModuleCat.MonModuleEquivalenceAlgebra.functor
  -- `sectionsAlgHom` spells out the three functor maps; `map_id` is stated for
  -- their composite `F`. `change` identifies these definitionally equal presentations.
  change (F.map (𝟙 A)).hom = _
  ext x
  -- The identities use the algebra instances on `F.obj A` and on `Γ(A.X, U)`.
  -- Rewriting the bundled maps does not match these instances; evaluation removes them.
  change (F.map (𝟙 A)).hom x = x
  simpa only [AlgCat.hom_id, AlgHom.id_apply] using
    congrArg (fun f ↦ f.hom x) (F.map_id A)

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsAlgHom_comp {A B C : CommMon X.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens) :
    CommMon.sectionsAlgHom (f ≫ g) U =
      (CommMon.sectionsAlgHom g U).comp (CommMon.sectionsAlgHom f U) := by
  let F := (Scheme.Modules.sectionsFunctor U).mapCommMon ⋙
    CommMon.forget₂Mon (ModuleCat.{u} Γ(X, U)) ⋙ ModuleCat.MonModuleEquivalenceAlgebra.functor
  -- `sectionsAlgHom` spells out the three functor maps; rewriting with `map_comp`
  -- requires first presenting them as the map of the composite functor `F`.
  change (F.map (f ≫ g)).hom = (F.map g).hom.comp (F.map f).hom
  simpa only [AlgCat.hom_comp] using congrArg AlgCat.Hom.hom (F.map_comp f g)

/-- A morphism of commutative sheaf algebras induces a morphism of their presheaves of rings. -/
def _root_.CategoryTheory.CommMon.sectionsPresheafMap {A B : CommMon X.Modules}
    (f : A ⟶ B) : A.sectionsPresheaf ⟶ B.sectionsPresheaf where
  app U := CommRingCat.ofHom (CommMon.sectionsAlgHom f U.unop).toRingHom
  naturality {U V} i := by
    dsimp only [CommMon.sectionsPresheaf]
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    -- The section rings have the same carriers as the module sections, but their
    -- ring instances are obtained through the sections functor.
    dsimp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    erw [CommMon.sectionsAlgHom_apply, CommMon.sectionsAlgHom_apply,
      CommMon.restrictSections_apply, CommMon.restrictSections_apply]
    exact PresheafOfModules.naturality_apply f.hom.hom.val i x

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheafMap_app {A B : CommMon X.Modules}
    (f : A ⟶ B) (U : X.Opensᵒᵖ) :
    (CommMon.sectionsPresheafMap f).app U =
      CommRingCat.ofHom (CommMon.sectionsAlgHom f U.unop).toRingHom :=
  (rfl)

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheafMap_id (A : CommMon X.Modules) :
    CommMon.sectionsPresheafMap (𝟙 A) = 𝟙 A.sectionsPresheaf := by
  apply NatTrans.ext
  funext U
  rw [CommMon.sectionsPresheafMap_app, CommMon.sectionsAlgHom_id, NatTrans.id_app]
  dsimp only [CommMon.sectionsPresheaf]
  ext x
  simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.id_apply, RingHom.id_apply]

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheafMap_comp {A B C : CommMon X.Modules}
    (f : A ⟶ B) (g : B ⟶ C) :
    CommMon.sectionsPresheafMap (f ≫ g) =
      CommMon.sectionsPresheafMap f ≫ CommMon.sectionsPresheafMap g := by
  apply NatTrans.ext
  funext U
  rw [NatTrans.comp_app, CommMon.sectionsPresheafMap_app,
    CommMon.sectionsPresheafMap_app, CommMon.sectionsPresheafMap_app,
    CommMon.sectionsAlgHom_comp]
  dsimp only [CommMon.sectionsPresheaf]
  rw [← CommRingCat.ofHom_comp]
  congr 1

/-- Algebra morphisms commute with the structure map from the structure presheaf. -/
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.CommMon.toSectionsPresheaf_comp_sectionsPresheafMap
    {A B : CommMon X.Modules} (f : A ⟶ B) :
    A.toSectionsPresheaf ≫ CommMon.sectionsPresheafMap f = B.toSectionsPresheaf := by
  ext U : 1
  rw [NatTrans.comp_app, CommMon.toSectionsPresheaf_app,
    CommMon.sectionsPresheafMap_app, CommMon.toSectionsPresheaf_app]
  -- The presheaf components and the explicitly bundled section rings agree
  -- after unfolding the sections construction.
  erw [← CommRingCat.ofHom_comp]
  congr 1
  ext r
  exact (CommMon.sectionsAlgHom f U).commutes r

/-- The `Γ(X, U)`-module structure on the sections over a basic open `X.basicOpen f` of an
`𝒪ₓ`-module (`Scheme.Modules.moduleBasicOpen`) is, for a commutative `𝒪ₓ`-algebra, multiplication
by the restriction of the structure map. -/
private lemma smul_basicOpen {U : X.Opens} (f r : Γ(X, U)) (x : Γ(A.X, X.basicOpen f)) :
    r • x = A.X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      (algebraMap Γ(X, U) Γ(A.X, U) r) * x := by
  have := congr($(A.toSectionsPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) r)
  exact (Algebra.smul_def (R := Γ(X, X.basicOpen f)) _ x).trans (congrArg (· * x) this)

/-- The sections of a quasi-coherent commutative `𝒪ₓ`-algebra over the basic open `X.basicOpen f`
of an affine open `U` are the localization of its sections over `U` away from `f`. This is the
algebra counterpart of `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`. -/
theorem _root_.CategoryTheory.CommMon.isLocalization_basicOpen [A.X.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI := (A.restrictSections (homOfLE (X.basicOpen_le f))).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) Γ(A.X, U) f) Γ(A.X, X.basicOpen f) := by
  let := (A.restrictSections (homOfLE (X.basicOpen_le f))).toAlgebra
  have hloc := A.X.isLocalizedModule_basicOpenRestrict hU f
  have hres : ∀ r : Γ(X, U), algebraMap Γ(A.X, U) Γ(A.X, X.basicOpen f)
      (algebraMap Γ(X, U) Γ(A.X, U) r) =
        algebraMap Γ(X, X.basicOpen f) Γ(A.X, X.basicOpen f) (algebraMap Γ(X, U) _ r) :=
    fun r ↦ congr($(A.toSectionsPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) r).symm
  -- Each condition for a localization is read off from the module localization `hloc`, using
  -- that `f` acts on sections by multiplication by the image of the structure map.
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    dsimp only
    rw [map_pow, hres]
    exact (X.toRingedSpace.isUnit_res_basicOpen f).map _ |>.pow n
  · intro z
    obtain ⟨⟨x, _, n, rfl⟩, hx⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (A.X.basicOpenRestrict f) z
    refine ⟨⟨x, ⟨algebraMap Γ(X, U) Γ(A.X, U) f ^ n, n, rfl⟩⟩, ?_⟩
    dsimp only at hx ⊢
    rw [Submonoid.smul_def, smul_basicOpen, Scheme.Modules.basicOpenRestrict_apply] at hx
    rw [mul_comm, ← map_pow]
    exact hx
  · intro x y h
    have h' : A.X.basicOpenRestrict f x = A.X.basicOpenRestrict f y := by
      rw [Scheme.Modules.basicOpenRestrict_apply, Scheme.Modules.basicOpenRestrict_apply]
      exact h
    obtain ⟨⟨s, hs⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
    rw [Submonoid.mk_smul, Submonoid.mk_smul] at hc
    obtain ⟨n, rfl⟩ := hs
    refine ⟨⟨_, n, rfl⟩, ?_⟩
    dsimp only
    rw [← map_pow]
    exact (Algebra.smul_def (R := Γ(X, U)) _ x).symm.trans
      (hc.trans (Algebra.smul_def (R := Γ(X, U)) _ y))

/-- On the affine opens of `X`, the presheaf of sections of a quasi-coherent commutative
`𝒪ₓ`-algebra is coequifibered over the structure presheaf: its sections over basic opens are
localizations. This is the condition under which Mathlib glues the spectra of its sections
(`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`). -/
theorem _root_.CategoryTheory.CommMon.coequifibered_toSectionsPresheaf [A.X.IsQuasicoherent] :
    ((toOpensFunctor X).op.whiskerLeft A.toSectionsPresheaf).Coequifibered :=
  coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦ A.isLocalization_basicOpen U.2 f

variable [A.X.IsQuasicoherent]

/-- The relative gluing datum of a quasi-coherent commutative `𝒪ₓ`-algebra: the affine schemes
`Spec Γ(A.X, U)` over the affine opens `U` of `X`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeSpecGluingData :
    (directedCover X).RelativeGluingData :=
  relativeGluingData A.coequifibered_toSectionsPresheaf

/-- The gluing diagram of the relative spectrum is locally directed. -/
instance _root_.CategoryTheory.CommMon.isLocallyDirected_relativeSpecGluingData :
    (A.relativeSpecGluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The relative spectrum `Spec_X(A)` of a quasi-coherent commutative `𝒪ₓ`-algebra `A`, glued from
the affine schemes `Spec Γ(A.X, U)` over the affine opens `U` of `X`. -/
@[expose, stacks 01LL]
def _root_.CategoryTheory.CommMon.relativeSpec : Scheme.{u} :=
  A.relativeSpecGluingData.glued

/-- The structure morphism `Spec_X(A) ⟶ X` of the relative spectrum. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeSpecToBase : A.relativeSpec ⟶ X :=
  A.relativeSpecGluingData.toBase

/-- The open cover of the relative spectrum by the spectra `Spec Γ(A.X, U)` of the sections over
the affine opens `U` of `X`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeSpecCover : A.relativeSpec.OpenCover :=
  A.relativeSpecGluingData.cover

instance _root_.CategoryTheory.CommMon.isOpenImmersion_relativeSpecCover_f
    (U : X.AffineZariskiSite) : IsOpenImmersion (A.relativeSpecCover.f U) :=
  A.relativeSpecCover.map_prop U

lemma _root_.CategoryTheory.CommMon.relativeSpecCover_X (U : X.AffineZariskiSite) :
    A.relativeSpecCover.X U = Spec (CommRingCat.of Γ(A.X, U.1)) :=
  (rfl)

/-- Over an affine open `U`, the structure morphism of the relative spectrum is `Spec` of the
structure map `Γ(X, U) ⟶ Γ(A.X, U)`. -/
@[reassoc]
lemma _root_.CategoryTheory.CommMon.relativeSpecCover_f_relativeSpecToBase
    (U : X.AffineZariskiSite) :
    A.relativeSpecCover.f U ≫ A.relativeSpecToBase =
      Spec.map (A.toSectionsPresheaf.app (op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

/-- The preimage of an affine open `U` under the structure morphism of the relative spectrum is the
image of the chart `Spec Γ(A.X, U)`. -/
lemma _root_.CategoryTheory.CommMon.relativeSpecToBase_preimage (U : X.AffineZariskiSite) :
    A.relativeSpecToBase ⁻¹ᵁ U.1 = (A.relativeSpecCover.f U).opensRange := by
  have h := A.relativeSpecGluingData.toBase_preimage_eq_opensRange_ι U
  simp only [Scheme.Opens.opensRange_ι] at h
  exact h

/-- Over an affine open `U` of `X`, the relative spectrum is `Spec Γ(A.X, U)`: the chart of the
relative spectrum over `U` is the base change of the structure morphism along `U ⟶ X`. -/
lemma _root_.CategoryTheory.CommMon.isPullback_relativeSpecCover (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (A.toSectionsPresheaf.app (op U.1)) ≫ U.2.isoSpec.inv)
      (A.relativeSpecCover.f U) U.1.ι A.relativeSpecToBase :=
  A.relativeSpecGluingData.isPullback_natTrans_ι_toBase U

/-- The structure morphism of the relative spectrum is affine. -/
instance _root_.CategoryTheory.CommMon.isAffineHom_relativeSpecToBase :
    IsAffineHom A.relativeSpecToBase := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  refine ⟨V.1, hxU, V.2, ?_⟩
  have : IsAffine (A.relativeSpecCover.X V) := by
    rw [A.relativeSpecCover_X]
    infer_instance
  rw [A.relativeSpecToBase_preimage V]
  exact isAffineOpen_opensRange _

end

end TauCeti
