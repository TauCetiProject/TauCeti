/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.CategoryTheory.Monoidal.Internal.Module

/-!
# Sections of commutative algebras of modules on schemes

A commutative monoid object in `X.Modules` has a commutative `Γ(X, U)`-algebra of sections
on each open `U`. Restriction is a ring homomorphism, giving a presheaf of commutative rings
under the structure presheaf of `X`, and this presheaf is a sheaf.

Conversely, a morphism of presheaves of section rings compatible with the structure maps is a
morphism of commutative `𝒪ₓ`-algebras (`CategoryTheory.CommMon.homOfSectionsPresheaf`). This
lets algebra morphisms and isomorphisms be constructed sectionwise, for instance by extending
ring maps given on affine opens.

These constructions use Mathlib's `Functor.mapCommMon` and the equivalence between monoid
objects in modules and algebras, applied to the lax braided sections functor.
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

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

/-- Restriction of sections commutes with the structure maps from regular functions. -/
-- Not a simp lemma: `restrictSections_apply` already simplifies its left-hand side, so adding
-- `[simp]` would violate `simpNF`.
lemma _root_.CategoryTheory.CommMon.restrictSections_algebraMap {U V : X.Opens} (i : V ⟶ U)
    (r : Γ(X, U)) :
    A.restrictSections i (algebraMap Γ(X, U) Γ(A.X, U) r) =
      algebraMap Γ(X, V) Γ(A.X, V) (X.presheaf.map i.op r) := by
  have h := A.toSectionsPresheaf.naturality i.op
  rw [CommMon.toSectionsPresheaf_app, CommMon.toSectionsPresheaf_app] at h
  exact congr($h r).symm

/-- The presheaf of section rings of a commutative `𝒪ₓ`-algebra is a sheaf: its underlying
presheaf of sets is that of the sheaf of modules `A.X`. -/
lemma _root_.CategoryTheory.CommMon.isSheaf_sectionsPresheaf :
    TopCat.Presheaf.IsSheaf (X := X) A.sectionsPresheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat)]
  have h := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) A.X.presheaf).mp
    A.X.isSheaf
  -- Both presheaves of sets have the sections `Γ(A.X, U)` as values, and restriction agrees by
  -- `CommMon.restrictSections_apply`.
  refine TopCat.Presheaf.isSheaf_of_iso (F := A.X.presheaf ⋙ forget AddCommGrpCat)
    (NatIso.ofComponents (fun U ↦ Iso.refl ((A.X.presheaf ⋙ forget AddCommGrpCat).obj U))
      fun i ↦ ?_) h
  ext x
  exact A.restrictSections_apply i.unop x |>.symm

variable {A} {B : CommMon X.Modules}

/-- The unit of a commutative `𝒪ₓ`-algebra sends a regular function to its image under the
structure map. -/
private lemma one_app_eq_algebraMap (A : CommMon X.Modules) (U : X.Opens) (r : Γ(X, U)) :
    (MonObj.one (X := A.X)).app U r = algebraMap Γ(X, U) Γ(A.X, U) r := by
  rw [CommMon.sections_algebraMap_def, Scheme.Modules.sectionsFunctor_ε]
  rfl

/-- Scalar multiplication on sections of a commutative `𝒪ₓ`-algebra is multiplication by the
image under the structure map. -/
private lemma smul_eq_algebraMap_mul (A : CommMon X.Modules) (U : X.Opens) (r : Γ(X, U))
    (x : Γ(A.X, U)) : r • x = algebraMap Γ(X, U) Γ(A.X, U) r * x :=
  Algebra.smul_def r x

/-- The module morphism underlying `CategoryTheory.CommMon.homOfSectionsPresheaf`: compatibility
with the structure maps makes the ring maps on sections `Γ(X, U)`-linear. -/
private def moduleHomOfSectionsPresheaf (φ : A.sectionsPresheaf ⟶ B.sectionsPresheaf)
    (h : A.toSectionsPresheaf ≫ φ = B.toSectionsPresheaf) : A.X ⟶ B.X :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (φ.app U).hom.toAddMonoidHom
      naturality U V i := by
        ext x
        have hx : φ.app V (A.restrictSections i.unop x) =
            B.restrictSections i.unop (φ.app U x) :=
          congrArg (fun f ↦ f.hom x) (φ.naturality i)
        exact (congrArg (φ.app V) (A.restrictSections_apply i.unop x).symm).trans
          (hx.trans (B.restrictSections_apply i.unop _)) }
    fun U r x ↦ by
      have hr : φ.app U (algebraMap Γ(X, U.unop) Γ(A.X, U.unop) r) =
          algebraMap Γ(X, U.unop) Γ(B.X, U.unop) r := by
        have hU := NatTrans.congr_app h U
        rw [NatTrans.comp_app, CommMon.toSectionsPresheaf_app,
          CommMon.toSectionsPresheaf_app] at hU
        exact congrArg (fun f ↦ f.hom r) hU
      exact (congrArg (φ.app U) (smul_eq_algebraMap_mul A U.unop r x)).trans
        ((map_mul (φ.app U).hom _ _).trans ((congrArg (· * φ.app U x) hr).trans
          (smul_eq_algebraMap_mul B U.unop r (φ.app U x)).symm))⟩

private lemma isMonHom_moduleHomOfSectionsPresheaf (φ : A.sectionsPresheaf ⟶ B.sectionsPresheaf)
    (h : A.toSectionsPresheaf ≫ φ = B.toSectionsPresheaf) :
    IsMonHom (moduleHomOfSectionsPresheaf φ h) where
  one_hom := by
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext r
    have hU := NatTrans.congr_app h (op U)
    rw [NatTrans.comp_app, CommMon.toSectionsPresheaf_app,
      CommMon.toSectionsPresheaf_app] at hU
    exact (congrArg (φ.app (op U)) (one_app_eq_algebraMap A U r)).trans
      ((congrArg (fun f ↦ f.hom r) hU).trans (one_app_eq_algebraMap B U r).symm)
  mul_hom := by
    -- Morphisms out of the sheafified tensor product are determined on pure tensors of
    -- sections, where both sides compute products of sections.
    apply SheafOfModules.tensor_hom_ext
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    let S := Scheme.Modules.sectionsFunctor (X := X) U.unop
    let m := moduleHomOfSectionsPresheaf φ h
    -- The sections over `U` of the tensor map of `forget` are the tensor map of the lax
    -- monoidal sections functor `S`; `change` records this definitional presentation, in which
    -- `CommMon.sections_mul_def` describes both multiplications.
    change S.map (MonObj.mul ≫ m) (Functor.LaxMonoidal.μ S A.X A.X (x ⊗ₜ y)) =
      S.map ((m ⊗ₘ m) ≫ MonObj.mul) (Functor.LaxMonoidal.μ S A.X A.X (x ⊗ₜ y))
    have hnat := congrArg (fun f ↦ f.hom (x ⊗ₜ y)) (Functor.LaxMonoidal.μ_natural S m m)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hnat
    have hmul : ∀ a b : Γ(A.X, U.unop), φ.app U (a * b) = φ.app U a * φ.app U b :=
      fun a b ↦ map_mul (φ.app U).hom a b
    rw [S.map_comp, S.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply]
    refine ((congrArg (φ.app U) (CommMon.sections_mul_def A U.unop x y)).symm.trans
      (hmul x y)).trans ((CommMon.sections_mul_def B U.unop _ _).trans ?_)
    exact congrArg (S.map MonObj.mul) ((congrArg (Functor.LaxMonoidal.μ S B.X B.X).hom
      (ModuleCat.MonoidalCategory.tensorHom_tmul (S.map m) (S.map m) x y)).symm.trans hnat)

/-- A morphism of presheaves of section rings compatible with the structure maps from the
structure presheaf is a morphism of commutative `𝒪ₓ`-algebras. -/
def _root_.CategoryTheory.CommMon.homOfSectionsPresheaf
    (φ : A.sectionsPresheaf ⟶ B.sectionsPresheaf)
    (h : A.toSectionsPresheaf ≫ φ = B.toSectionsPresheaf) : A ⟶ B :=
  CommMon.homMk
    { hom := moduleHomOfSectionsPresheaf φ h
      isMonHom_hom := isMonHom_moduleHomOfSectionsPresheaf φ h }

/-- On sections, the morphism of algebras built from a morphism of section rings is that
morphism. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.homOfSectionsPresheaf_hom_hom_app_apply
    (φ : A.sectionsPresheaf ⟶ B.sectionsPresheaf)
    (h : A.toSectionsPresheaf ≫ φ = B.toSectionsPresheaf) (U : X.Opens) (x : Γ(A.X, U)) :
    (CommMon.homOfSectionsPresheaf φ h).hom.hom.app U x = φ.app (op U) x :=
  (rfl)

/-- An isomorphism of presheaves of section rings compatible with the structure maps from the
structure presheaf is an isomorphism of commutative `𝒪ₓ`-algebras. -/
def _root_.CategoryTheory.CommMon.isoOfSectionsPresheaf
    (e : A.sectionsPresheaf ≅ B.sectionsPresheaf)
    (h : A.toSectionsPresheaf ≫ e.hom = B.toSectionsPresheaf) : A ≅ B where
  hom := CommMon.homOfSectionsPresheaf e.hom h
  inv := CommMon.homOfSectionsPresheaf e.inv
    (by rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    ext U x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id (op U)) x
  inv_hom_id := by
    ext U x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id (op U)) x

@[simp]
lemma _root_.CategoryTheory.CommMon.isoOfSectionsPresheaf_hom
    (e : A.sectionsPresheaf ≅ B.sectionsPresheaf)
    (h : A.toSectionsPresheaf ≫ e.hom = B.toSectionsPresheaf) :
    (CommMon.isoOfSectionsPresheaf e h).hom = CommMon.homOfSectionsPresheaf e.hom h :=
  (rfl)

@[simp]
lemma _root_.CategoryTheory.CommMon.isoOfSectionsPresheaf_inv
    (e : A.sectionsPresheaf ≅ B.sectionsPresheaf)
    (h : A.toSectionsPresheaf ≫ e.hom = B.toSectionsPresheaf) :
    (CommMon.isoOfSectionsPresheaf e h).inv = CommMon.homOfSectionsPresheaf e.inv
      (by rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]) :=
  (rfl)

end

end TauCeti
