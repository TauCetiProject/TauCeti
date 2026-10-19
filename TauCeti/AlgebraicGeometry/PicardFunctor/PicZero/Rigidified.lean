/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.Basic

/-!
# The degree-zero rigidified Picard functor

Let `f : X ⟶ S` be a smooth proper geometrically connected family of curves with a section
`x₀`. Forgetting the rigidification identifies rigidified line-bundle classes on every base
change of `X` with the relative Picard presheaf. This file restricts that comparison to the
classes having degree zero on every geometric fibre.

The degree-zero rigidified classes form a subgroup
`rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T` on every test scheme `T`. Pullback makes
these subgroups into the commutative-group-valued functor
`rigidifiedPicardDegreeZeroFunctor f x₀ hx₀`. The restricted comparison is the natural
isomorphism `rigidifiedPicardDegreeZeroFunctorIso`; its compatibility with both inclusions says
that it is the degree-zero part of `rigidifiedPicardFunctorIso`, rather than merely an abstract
isomorphism of groups.

This is the pointed description of functorial `Pic⁰` used when a rational point normalizes a
Poincaré bundle. Representability and the identification with the identity component of a Picard
scheme require further geometric input and are not asserted here.

## Main declarations

* `TauCeti.AlgebraicGeometry.rigidifiedPicardDegreeZeroSubgroup`: rigidified classes whose image
  in the relative Picard presheaf has degree zero on every geometric fibre;
* `TauCeti.AlgebraicGeometry.rigidifiedPicardDegreeZeroFunctor`: these classes as a presheaf of
  commutative groups;
* `TauCeti.AlgebraicGeometry.rigidifiedPicardDegreeZeroFunctorIso`: the natural comparison with
  `relativePicardDegreeZeroFunctor`, with components `rigidifiedPicardDegreeZeroToRelative` and
  `relativePicardDegreeZeroToRigidified`;
* `TauCeti.AlgebraicGeometry.rigidifiedPicardDegreeZeroToRelative_comp_
    relativePicardDegreeZeroFunctorι` and its inverse counterpart: compatibility of the comparison
  with the inclusions into the full rigidified and relative Picard presheaves.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.2 and 9.5.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)
variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- The subgroup of rigidified line-bundle classes whose image in `Pic(X_T) / Pic(T)` has degree
zero on every geometric fibre. -/
def rigidifiedPicardDegreeZeroSubgroup (T : (Over S)ᵒᵖ) :
    Subgroup ((rigidifiedPicardFunctor f x₀ hx₀).obj T) :=
  (relativePicardDegreeZeroSubgroup f T).comap
    ((rigidifiedPicardFunctorIso f x₀ hx₀).hom.app T).hom

/-- A rigidified line-bundle class has degree zero exactly when its image under the comparison
with the relative Picard presheaf has degree zero. -/
@[simp]
lemma mem_rigidifiedPicardDegreeZeroSubgroup_iff {T : (Over S)ᵒᵖ}
    {a : (rigidifiedPicardFunctor f x₀ hx₀).obj T} :
    a ∈ rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T ↔
      (rigidifiedPicardFunctorIso f x₀ hx₀).hom.app T a ∈
        relativePicardDegreeZeroSubgroup f T :=
  Iff.rfl

/-- A rigidified line-bundle class has degree zero exactly when the fibre degree of its
underlying relative Picard class vanishes at every geometric point. -/
lemma mem_rigidifiedPicardDegreeZeroSubgroup_iff_fiberDegree {T : (Over S)ᵒᵖ}
    {a : (rigidifiedPicardFunctor f x₀ hx₀).obj T} :
    a ∈ rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left),
        relativePicardFiberDegree f ξ
          ((rigidifiedPicardFunctorIso f x₀ hx₀).hom.app T a) = 0 := by
  rw [mem_rigidifiedPicardDegreeZeroSubgroup_iff,
    mem_relativePicardDegreeZeroSubgroup_iff,
    mem_relativePicardDegreeZeroSubfunctor_obj_iff]

/-- Pullback preserves the fibrewise degree-zero condition on rigidified line-bundle classes. -/
lemma rigidifiedPicardDegreeZero_map_mem {T T' : (Over S)ᵒᵖ} (g : T ⟶ T')
    {a : (rigidifiedPicardFunctor f x₀ hx₀).obj T}
    (ha : a ∈ rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T) :
    (rigidifiedPicardFunctor f x₀ hx₀).map g a ∈
      rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T' := by
  rw [mem_rigidifiedPicardDegreeZeroSubgroup_iff] at ha ⊢
  rw [NatTrans.naturality_apply]
  rw [mem_relativePicardDegreeZeroSubgroup_iff] at ha ⊢
  exact (relativePicardDegreeZeroSubfunctor f).map g ha

/-- **The degree-zero rigidified Picard functor.** It sends a test scheme `T` over `S` to the
subgroup of rigidified line-bundle classes having degree zero on every geometric fibre, and a
morphism of test schemes to pullback. -/
def rigidifiedPicardDegreeZeroFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T)
  map g := CommGrpCat.ofHom <|
    (((rigidifiedPicardFunctor f x₀ hx₀).map g).hom.comp
      (rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ _).subtype).codRestrict _
        fun a ↦ rigidifiedPicardDegreeZero_map_mem f x₀ hx₀ g a.2
  map_id T := CommGrpCat.ext fun a ↦ Subtype.ext <|
    ConcreteCategory.congr_hom ((rigidifiedPicardFunctor f x₀ hx₀).map_id T) a.1
  map_comp g h := CommGrpCat.ext fun a ↦ Subtype.ext <|
    ConcreteCategory.congr_hom ((rigidifiedPicardFunctor f x₀ hx₀).map_comp g h) a.1

/-- The value of the degree-zero rigidified Picard functor at `T` is the subgroup of rigidified
classes having degree zero on every geometric fibre. -/
lemma rigidifiedPicardDegreeZeroFunctor_obj (T : (Over S)ᵒᵖ) :
    (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).obj T =
      CommGrpCat.of (rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T) := by
  unfold rigidifiedPicardDegreeZeroFunctor
  rfl

/-- A degree-zero rigidified class regarded as a section of the degree-zero rigidified Picard
functor. -/
def rigidifiedPicardDegreeZeroFunctor.mk {T : (Over S)ᵒᵖ}
    (a : (rigidifiedPicardFunctor f x₀ hx₀).obj T)
    (ha : a ∈ rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T) :
    (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).obj T :=
  ⟨a, ha⟩

/-- Pullback in the degree-zero rigidified Picard functor is pullback in the full rigidified
Picard functor, together with preservation of the degree-zero condition. -/
@[simp]
lemma rigidifiedPicardDegreeZeroFunctor_map_mk {T T' : (Over S)ᵒᵖ} (g : T ⟶ T')
    (a : (rigidifiedPicardFunctor f x₀ hx₀).obj T)
    (ha : a ∈ rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T) :
    (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).map g
        (rigidifiedPicardDegreeZeroFunctor.mk f x₀ hx₀ a ha) =
      rigidifiedPicardDegreeZeroFunctor.mk f x₀ hx₀
        ((rigidifiedPicardFunctor f x₀ hx₀).map g a)
        (rigidifiedPicardDegreeZero_map_mem f x₀ hx₀ g ha) := by
  unfold rigidifiedPicardDegreeZeroFunctor rigidifiedPicardDegreeZeroFunctor.mk
  rfl

/-- The inclusion of the degree-zero rigidified Picard functor into the full rigidified Picard
functor. -/
def rigidifiedPicardDegreeZeroFunctorι :
    rigidifiedPicardDegreeZeroFunctor f x₀ hx₀ ⟶ rigidifiedPicardFunctor f x₀ hx₀ where
  app T := CommGrpCat.ofHom (rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T).subtype

/-- The inclusion of the degree-zero rigidified Picard functor forgets the proof of fibrewise
degree zero. -/
@[simp]
lemma rigidifiedPicardDegreeZeroFunctorι_app_mk {T : (Over S)ᵒᵖ}
    (a : (rigidifiedPicardFunctor f x₀ hx₀).obj T)
    (ha : a ∈ rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T) :
    (rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T
        (rigidifiedPicardDegreeZeroFunctor.mk f x₀ hx₀ a ha) = a := by
  unfold rigidifiedPicardDegreeZeroFunctorι rigidifiedPicardDegreeZeroFunctor.mk
  rfl

/-- The inclusion of the degree-zero rigidified Picard functor is injective on every test
scheme. -/
lemma rigidifiedPicardDegreeZeroFunctorι_app_injective (T : (Over S)ᵒᵖ) :
    Function.Injective ((rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T) :=
  Subtype.val_injective

/-- The image of a section of the degree-zero rigidified Picard functor satisfies the defining
fibrewise degree-zero condition. -/
lemma rigidifiedPicardDegreeZeroFunctorι_app_mem {T : (Over S)ᵒᵖ}
    (a : (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).obj T) :
    (rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T a ∈
      rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T :=
  a.2

private def rigidifiedPicardDegreeZeroToRelativeHom (T : (Over S)ᵒᵖ) :
    (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).obj T →*
      (relativePicardDegreeZeroFunctor f).obj T :=
  relativePicardDegreeZeroFunctor.mkHom f
    (((rigidifiedPicardFunctorIso f x₀ hx₀).hom.app T).hom.comp
      ((rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T).hom) fun a ↦
        (mem_relativePicardDegreeZeroSubgroup_iff f).mp <|
          (mem_rigidifiedPicardDegreeZeroSubgroup_iff f x₀ hx₀).mp
            (rigidifiedPicardDegreeZeroFunctorι_app_mem f x₀ hx₀ a)

@[simp]
private lemma relativePicardDegreeZeroFunctorι_app_toRelativeHom (T : (Over S)ᵒᵖ)
    (a : (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).obj T) :
    (relativePicardDegreeZeroFunctorι f).app T
        (rigidifiedPicardDegreeZeroToRelativeHom f x₀ hx₀ T a) =
      (rigidifiedPicardFunctorIso f x₀ hx₀).hom.app T
        ((rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T a) := by
  unfold rigidifiedPicardDegreeZeroToRelativeHom
  exact relativePicardDegreeZeroFunctorι_app_mkHom f _ _ _

/-- Forgetting the rigidification maps the degree-zero rigidified Picard functor to the
degree-zero relative Picard functor. -/
def rigidifiedPicardDegreeZeroToRelative :
    rigidifiedPicardDegreeZeroFunctor f x₀ hx₀ ⟶ relativePicardDegreeZeroFunctor f where
  app T := CommGrpCat.ofHom (rigidifiedPicardDegreeZeroToRelativeHom f x₀ hx₀ T)
  naturality := by
    intro T T' g
    ext a
    apply relativePicardDegreeZeroFunctorι_app_injective f _
    -- Both restricted functors are opaque, so compare their sections through the inclusion.
    change (relativePicardDegreeZeroFunctorι f).app T'
        (rigidifiedPicardDegreeZeroToRelativeHom f x₀ hx₀ T'
          ((rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).map g a)) =
      (relativePicardDegreeZeroFunctorι f).app T'
        ((relativePicardDegreeZeroFunctor f).map g
          (rigidifiedPicardDegreeZeroToRelativeHom f x₀ hx₀ T a))
    simp only [relativePicardDegreeZeroFunctorι_app_toRelativeHom,
      NatTrans.naturality_apply (relativePicardDegreeZeroFunctorι f),
      NatTrans.naturality_apply (rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀)]
    exact NatTrans.naturality_apply (rigidifiedPicardFunctorIso f x₀ hx₀).hom g _

@[simp]
private lemma rigidifiedPicardDegreeZeroToRelative_app_apply (T : (Over S)ᵒᵖ)
    (a : (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).obj T) :
    (rigidifiedPicardDegreeZeroToRelative f x₀ hx₀).app T a =
      rigidifiedPicardDegreeZeroToRelativeHom f x₀ hx₀ T a :=
  rfl

private def relativePicardDegreeZeroToRigidifiedHom (T : (Over S)ᵒᵖ) :
    (relativePicardDegreeZeroFunctor f).obj T →*
      (rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).obj T :=
  (((rigidifiedPicardFunctorIso f x₀ hx₀).inv.app T).hom.comp
    ((relativePicardDegreeZeroFunctorι f).app T).hom).codRestrict
      (rigidifiedPicardDegreeZeroSubgroup f x₀ hx₀ T) fun c ↦ by
        -- Membership is transported across the inverse of the full Picard comparison.
        change (rigidifiedPicardFunctorIso f x₀ hx₀).hom.app T
            ((rigidifiedPicardFunctorIso f x₀ hx₀).inv.app T
              ((relativePicardDegreeZeroFunctorι f).app T c)) ∈
          relativePicardDegreeZeroSubgroup f T
        rw [Iso.inv_hom_id_app_apply]
        exact (mem_relativePicardDegreeZeroSubgroup_iff f).mpr
          (relativePicardDegreeZeroFunctorι_app_mem f c)

@[simp]
private lemma rigidifiedPicardDegreeZeroFunctorι_app_toRigidifiedHom (T : (Over S)ᵒᵖ)
    (c : (relativePicardDegreeZeroFunctor f).obj T) :
    (rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T
        (relativePicardDegreeZeroToRigidifiedHom f x₀ hx₀ T c) =
      (rigidifiedPicardFunctorIso f x₀ hx₀).inv.app T
        ((relativePicardDegreeZeroFunctorι f).app T c) := by
  unfold relativePicardDegreeZeroToRigidifiedHom
  exact rigidifiedPicardDegreeZeroFunctorι_app_mk f x₀ hx₀ _ _

/-- Restoring the unique normalized rigidification maps the degree-zero relative Picard functor
to the degree-zero rigidified Picard functor. -/
def relativePicardDegreeZeroToRigidified :
    relativePicardDegreeZeroFunctor f ⟶ rigidifiedPicardDegreeZeroFunctor f x₀ hx₀ where
  app T := CommGrpCat.ofHom (relativePicardDegreeZeroToRigidifiedHom f x₀ hx₀ T)
  naturality := by
    intro T T' g
    ext c
    apply rigidifiedPicardDegreeZeroFunctorι_app_injective f x₀ hx₀ _
    -- Both restricted functors are opaque, so compare their sections through the inclusion.
    change (rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T'
        (relativePicardDegreeZeroToRigidifiedHom f x₀ hx₀ T'
          ((relativePicardDegreeZeroFunctor f).map g c)) =
      (rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T'
        ((rigidifiedPicardDegreeZeroFunctor f x₀ hx₀).map g
          (relativePicardDegreeZeroToRigidifiedHom f x₀ hx₀ T c))
    simp only [rigidifiedPicardDegreeZeroFunctorι_app_toRigidifiedHom,
      NatTrans.naturality_apply (rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀),
      NatTrans.naturality_apply (relativePicardDegreeZeroFunctorι f)]
    exact NatTrans.naturality_apply (rigidifiedPicardFunctorIso f x₀ hx₀).inv g _

@[simp]
private lemma relativePicardDegreeZeroToRigidified_app_apply (T : (Over S)ᵒᵖ)
    (c : (relativePicardDegreeZeroFunctor f).obj T) :
    (relativePicardDegreeZeroToRigidified f x₀ hx₀).app T c =
      relativePicardDegreeZeroToRigidifiedHom f x₀ hx₀ T c :=
  rfl

/-- **Rigidified degree-zero classes are functorial `Pic⁰`.** Forgetting the rigidification
identifies the degree-zero rigidified Picard functor naturally, as a presheaf of commutative
groups, with the degree-zero relative Picard functor. -/
def rigidifiedPicardDegreeZeroFunctorIso :
    rigidifiedPicardDegreeZeroFunctor f x₀ hx₀ ≅ relativePicardDegreeZeroFunctor f :=
  { hom := rigidifiedPicardDegreeZeroToRelative f x₀ hx₀
    inv := relativePicardDegreeZeroToRigidified f x₀ hx₀
    hom_inv_id := by
      ext T a
      apply rigidifiedPicardDegreeZeroFunctorι_app_injective f x₀ hx₀ T
      simp only [NatTrans.comp_app, CommGrpCat.comp_apply,
        rigidifiedPicardDegreeZeroToRelative_app_apply,
        relativePicardDegreeZeroToRigidified_app_apply,
        rigidifiedPicardDegreeZeroFunctorι_app_toRigidifiedHom,
        relativePicardDegreeZeroFunctorι_app_toRelativeHom]
      exact (rigidifiedPicardFunctorIso f x₀ hx₀).hom_inv_id_app_apply T
        ((rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀).app T a)
    inv_hom_id := by
      ext T c
      apply relativePicardDegreeZeroFunctorι_app_injective f T
      simp only [NatTrans.comp_app, CommGrpCat.comp_apply,
        relativePicardDegreeZeroToRigidified_app_apply,
        rigidifiedPicardDegreeZeroToRelative_app_apply,
        relativePicardDegreeZeroFunctorι_app_toRelativeHom,
        rigidifiedPicardDegreeZeroFunctorι_app_toRigidifiedHom]
      exact (rigidifiedPicardFunctorIso f x₀ hx₀).inv_hom_id_app_apply T
        ((relativePicardDegreeZeroFunctorι f).app T c) }

/-- Forgetting the rigidification of a degree-zero rigidified class and then forgetting the
degree-zero condition is the comparison of the full rigidified and relative Picard presheaves. -/
@[reassoc (attr := simp)]
theorem rigidifiedPicardDegreeZeroToRelative_comp_relativePicardDegreeZeroFunctorι :
    rigidifiedPicardDegreeZeroToRelative f x₀ hx₀ ≫ relativePicardDegreeZeroFunctorι f =
      rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀ ≫
        (rigidifiedPicardFunctorIso f x₀ hx₀).hom := by
  ext T a
  simp only [NatTrans.comp_app, CommGrpCat.comp_apply,
    rigidifiedPicardDegreeZeroToRelative_app_apply,
    relativePicardDegreeZeroFunctorι_app_toRelativeHom]

/-- Restoring the rigidification of a degree-zero relative Picard class and then forgetting the
degree-zero condition is the inverse comparison of the full Picard presheaves. -/
@[reassoc (attr := simp)]
theorem relativePicardDegreeZeroToRigidified_comp_rigidifiedPicardDegreeZeroFunctorι :
    relativePicardDegreeZeroToRigidified f x₀ hx₀ ≫ rigidifiedPicardDegreeZeroFunctorι f x₀ hx₀ =
      relativePicardDegreeZeroFunctorι f ≫ (rigidifiedPicardFunctorIso f x₀ hx₀).inv := by
  ext T c
  simp only [NatTrans.comp_app, CommGrpCat.comp_apply,
    relativePicardDegreeZeroToRigidified_app_apply,
    rigidifiedPicardDegreeZeroFunctorι_app_toRigidifiedHom]

/-- The forward map of `rigidifiedPicardDegreeZeroFunctorIso` forgets the rigidification. -/
@[simp]
lemma rigidifiedPicardDegreeZeroFunctorIso_hom :
    (rigidifiedPicardDegreeZeroFunctorIso f x₀ hx₀).hom =
      rigidifiedPicardDegreeZeroToRelative f x₀ hx₀ := by
  unfold rigidifiedPicardDegreeZeroFunctorIso
  rfl

/-- The inverse map of `rigidifiedPicardDegreeZeroFunctorIso` restores the normalized
rigidification. -/
@[simp]
lemma rigidifiedPicardDegreeZeroFunctorIso_inv :
    (rigidifiedPicardDegreeZeroFunctorIso f x₀ hx₀).inv =
      relativePicardDegreeZeroToRigidified f x₀ hx₀ := by
  unfold rigidifiedPicardDegreeZeroFunctorIso
  rfl

end

end TauCeti.AlgebraicGeometry
