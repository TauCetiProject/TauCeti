/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.RepresentationTheory.Induction.Mackey.Hom
import TauCeti.CategoryTheory.Linear.FullyFaithful
import TauCeti.RepresentationTheory.FiniteIndex

/-!
# The identity component of the Mackey Hom decomposition

The representative chosen for the identity double coset need not be `1`. It lies in `H`, so
its Mackey subgroup is all of `H`, and the conjugation twist is removed by the action of that
representative on the target. This identifies the actual identity component of
`Rep.indHomMackeyLinearEquiv` with `Hom_H(A, B)` over any commutative ring.

Under this identification induction of a morphism has identity component the original morphism.
In particular the same holds for the native finite-dimensional induced-endomorphism map over
any field, without semisimplicity or a restriction on the characteristic.
-/

public section

open CategoryTheory Representation TauCeti

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] {H : Subgroup G} {s : G}

private theorem mackeySelfSubtype_surjective (hs : s ∈ H) :
    Function.Surjective ((mackeySubgroup s H H).subgroupOf H).subtype := by
  intro h
  obtain ⟨y, hy⟩ := (mackeySubgroupSelfEquiv hs).surjective h
  exact ⟨y, (coe_mackeySubgroupSelfEquiv_apply hs y).symm.trans hy⟩

/-- The inner conjugation twist at a representative in `H` is removed by its action on `B`. -/
private noncomputable def mackeySelfTwistIso (hs : s ∈ H) (B : Rep.{u} k H) :
    Rep.res (mackeyToH s H H) B ≅
      Rep.res ((mackeySubgroup s H H).subgroupOf H).subtype B :=
  Rep.mkIso <| .mk (LinearEquiv.ofBijective (B.ρ ⟨s, hs⟩) (B.ρ.apply_bijective _))
    fun y ↦ by
      -- The restricted actions have the same carrier as B, but rewriting the restrictions
      -- changes their dependent carrier. Read them as B's action before using multiplication.
      change B.ρ ⟨s, hs⟩ ∘ₗ B.ρ (mackeyToH s H H y) =
        B.ρ (y : H) ∘ₗ B.ρ ⟨s, hs⟩
      change B.ρ ⟨s, hs⟩ * B.ρ (mackeyToH s H H y) =
        B.ρ (y : H) * B.ρ ⟨s, hs⟩
      rw [← map_mul, ← map_mul]
      congr 1
      ext
      simp only [Subgroup.coe_mul, coe_mackeyToH_apply]
      group

/-- A Mackey Hom component represented by an element of `H` is the ordinary Hom space over
`H`. The map removes inner conjugation by acting on the target with the representative. -/
noncomputable def mackeyHomSelfLinearEquiv (hs : s ∈ H) (A B : Rep.{u} k H) :
    (Rep.res ((mackeySubgroup s H H).subgroupOf H).subtype A ⟶
      Rep.res (mackeyToH s H H) B) ≃ₗ[k] (A ⟶ B) := by
  letI := Rep.full_res (k := k) _ (mackeySelfSubtype_surjective hs)
  exact (Linear.homCongr k (Iso.refl _) (mackeySelfTwistIso hs B)).trans
    ((Rep.resFunctor ((mackeySubgroup s H H).subgroupOf H).subtype).homLinearEquiv k A B).symm

/-- The identity-component identification postcomposes with the action of its representative. -/
theorem mackeyHomSelfLinearEquiv_apply (hs : s ∈ H) (A B : Rep.{u} k H)
    (f : Rep.res ((mackeySubgroup s H H).subgroupOf H).subtype A ⟶
      Rep.res (mackeyToH s H H) B) (a : A) :
    (mackeyHomSelfLinearEquiv hs A B f).hom a = B.ρ ⟨s, hs⟩ (f.hom a) := by
  let := Rep.full_res (k := k) _ (mackeySelfSubtype_surjective hs)
  have h := ((Rep.resFunctor ((mackeySubgroup s H H).subgroupOf H).subtype).homLinearEquiv
    k A B).apply_symm_apply (f ≫ (mackeySelfTwistIso hs B).hom)
  rw [Functor.homLinearEquiv_apply] at h
  have h' := congrArg (fun g ↦ g.hom a) h
  -- Restriction and the comparison isomorphism retain different dependent presentations of
  -- B's carrier; normalize those wrappers before comparing the evaluations.
  change (((Rep.resFunctor ((mackeySubgroup s H H).subgroupOf H).subtype).homLinearEquiv
    k A B).symm (f ≫ (mackeySelfTwistIso hs B).hom)).hom a =
      B.ρ ⟨s, hs⟩ (f.hom a) at h'
  simpa only [mackeyHomSelfLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Category.id_comp, Rep.resMap_hom_apply, Rep.hom_comp,
    IntertwiningMap.comp_apply] using h'

section Finite

variable [Finite G]

/-- On an induced morphism, the raw identity component includes precisely the inverse action
of the chosen representative. -/
theorem indHomMackeyLinearEquiv_indMap_apply (A B : Rep.{u} k H) (f : A ⟶ B)
    (D : DoubleCoset.Quotient (H : Set G) (H : Set G)) (hs : D.out ∈ H) (a : A) :
    (indHomMackeyLinearEquiv A B (Rep.indMap H.subtype f) D).hom a =
      B.ρ (⟨D.out, hs⟩ : H)⁻¹ (f.hom a) := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  rw [indHomMackeyLinearEquiv_apply]
  -- The adjunction evaluates at 1. Its morphism is wrapped in Rep.ofHom, and the
  -- composite targets a dependent coinduced carrier, so expose this evaluation together.
  change (((Rep.indCoindIso (Rep.res (mackeyToH D.out H H) B)).hom.hom
    ((Rep.homDirectSumLinearEquiv A (fun E : DoubleCoset.Quotient (H : Set G) (H : Set G) ↦
      Rep.mackeySummand H H E.out B)
      ((Rep.indResHomEquiv H.subtype A (Rep.ind H.subtype B) (Rep.indMap H.subtype f)) ≫
        (Rep.mackeyDecomposition (K := H) B).hom) D).hom a)).1 1) = _
  rw [Rep.homDirectSumLinearEquiv_apply]
  -- Likewise, the first adjunction is evaluation on the generator at 1; expressing its
  -- evaluation avoids rewriting a composition across the restricted target carrier.
  change (((Rep.indCoindIso (Rep.res (mackeyToH D.out H H) B)).hom.hom
    (((Rep.mackeyDecomposition (K := H) B).hom.hom
      ((Rep.indMap H.subtype f).hom (IndV.mk H.subtype A.ρ 1 a))) D)).1 1) = _
  have hmap : (Rep.indMap H.subtype f).hom (IndV.mk H.subtype A.ρ 1 a) =
      IndV.mk H.subtype B.ρ 1 (f.hom a) := by
    simp [Rep.indMap]
  rw [hmap]
  have hdecomp := Rep.mackeyDecomposition_hom_hom_apply_mk B D (⟨D.out, hs⟩ : H) 1
    (f.hom a)
  simp only [Subgroup.coe_one, mul_inv_cancel, one_mul] at hdecomp
  rw [hdecomp]
  rw [DirectSum.lof_apply]
  -- The public comparison equation is on the underlying linear map rather than the
  -- intertwining-map coercion selected by the adjunction.
  change (((Rep.indCoindIso (Rep.res (mackeyToH D.out H H) B)).hom.hom.toLinearMap
    (IndV.mk _ _ 1 (B.ρ (⟨D.out, hs⟩ : H)⁻¹ (f.hom a)))).1 1) = _
  rw [Rep.indCoindIso_hom_hom_toLinearMap]
  exact congrFun (TauCeti.indToCoind_mk 1 _) 1 |>.trans (Rep.indToCoindAux_self 1 _)

/-- Removing the inner conjugation identifies the actual identity component of an induced
morphism with the original morphism. This works for the chosen representative, even when it
is not `1`. -/
theorem mackeyHomSelfLinearEquiv_indMap
    (A B : Rep.{u} k H) (f : A ⟶ B)
    (D : DoubleCoset.Quotient (H : Set G) (H : Set G)) (hs : D.out ∈ H) :
    mackeyHomSelfLinearEquiv hs A B
      (indHomMackeyLinearEquiv A B (Rep.indMap H.subtype f) D) = f := by
  ext a
  -- ext selects toLinearMap evaluations; the characteristic equations use hom evaluations.
  change (mackeyHomSelfLinearEquiv hs A B
    (indHomMackeyLinearEquiv A B (Rep.indMap H.subtype f) D)).hom a = f.hom a
  rw [mackeyHomSelfLinearEquiv_apply, indHomMackeyLinearEquiv_indMap_apply]
  exact B.ρ.self_inv_apply _ _

/-- Projection of the Mackey Hom decomposition onto the identity double coset, identified
with the ordinary Hom space over `H`. -/
noncomputable def indHomMackeyIdentityComponent (A B : Rep.{u} k H) :
    (Rep.ind H.subtype A ⟶ Rep.ind H.subtype B) →ₗ[k] (A ⟶ B) :=
  (mackeyHomSelfLinearEquiv
    ((doubleCosetMk_eq_mk_one_iff_mem H _).mp
      (DoubleCoset.out_eq' (DoubleCoset.mk H H 1))) A B).toLinearMap.comp
    ((LinearMap.proj (DoubleCoset.mk H H 1)).comp
      (indHomMackeyLinearEquiv A B).toLinearMap)

/-- The identity component is computed from the actual chosen Mackey component by removing
its conjugation twist. -/
theorem indHomMackeyIdentityComponent_apply (A B : Rep.{u} k H)
    (φ : Rep.ind H.subtype A ⟶ Rep.ind H.subtype B) :
    indHomMackeyIdentityComponent A B φ =
      mackeyHomSelfLinearEquiv
        ((doubleCosetMk_eq_mk_one_iff_mem H _).mp
          (DoubleCoset.out_eq' (DoubleCoset.mk H H 1))) A B
        (indHomMackeyLinearEquiv A B φ (DoubleCoset.mk H H 1)) := by rfl

/-- Projection onto the identity component is a left inverse to induction on morphisms. -/
@[simp]
theorem indHomMackeyIdentityComponent_indMap (A B : Rep.{u} k H) (f : A ⟶ B) :
    indHomMackeyIdentityComponent A B (Rep.indMap H.subtype f) = f :=
  mackeyHomSelfLinearEquiv_indMap A B f _ _

end Finite

end Rep

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] {H : Subgroup G} {s : G}

/-- The finite-dimensional Mackey Hom component represented by an element of `H` identifies
with the original Hom space, by removing the inner conjugation twist. -/
noncomputable def mackeyHomSelfLinearEquiv (hs : s ∈ H) (A B : FDRep k H) :
    (Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj B) ≃ₗ[k] (A ⟶ B) :=
  (FDRep.forget₂HomLinearEquiv _ _).symm.trans <|
    (Rep.mackeyHomSelfLinearEquiv hs
      ((forget₂ (FDRep k H) (Rep k H)).obj A)
      ((forget₂ (FDRep k H) (Rep k H)).obj B)).trans <|
      FDRep.forget₂HomLinearEquiv A B

/-- The finite-dimensional identification acts by the chosen representative on the target. -/
theorem mackeyHomSelfLinearEquiv_apply (hs : s ∈ H) (A B : FDRep k H)
    (f : Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj B) (a : A) :
    (mackeyHomSelfLinearEquiv hs A B f) a =
      B.ρ ⟨s, hs⟩ (f a) := by
  exact Rep.mackeyHomSelfLinearEquiv_apply hs
    ((forget₂ (FDRep k H) (Rep k H)).obj A)
    ((forget₂ (FDRep k H) (Rep k H)).obj B)
    ((FDRep.forget₂HomLinearEquiv _ _).symm f) a

variable [Finite G]

/-- The identity double-coset projection of the actual finite-dimensional Mackey Hom
isomorphism, with its component identified with `Hom_H(A, B)`. -/
noncomputable def indHomMackeyIdentityComponent (A B : FDRep k H) :
    (indFDRep A ⟶ indFDRep B) →ₗ[k] (A ⟶ B) :=
  (mackeyHomSelfLinearEquiv
    ((doubleCosetMk_eq_mk_one_iff_mem H _).mp
      (DoubleCoset.out_eq' (DoubleCoset.mk H H 1))) A B).toLinearMap.comp
    ((LinearMap.proj (DoubleCoset.mk H H 1)).comp
      (indHomMackeyLinearEquiv A B).toLinearMap)

/-- The finite-dimensional identity component is the actual chosen Mackey component with its
inner conjugation twist removed. -/
theorem indHomMackeyIdentityComponent_apply (A B : FDRep k H)
    (φ : indFDRep A ⟶ indFDRep B) :
    indHomMackeyIdentityComponent A B φ =
      mackeyHomSelfLinearEquiv
        ((doubleCosetMk_eq_mk_one_iff_mem H _).mp
          (DoubleCoset.out_eq' (DoubleCoset.mk H H 1))) A B
        (indHomMackeyLinearEquiv A B φ (DoubleCoset.mk H H 1)) := by rfl

/-- Forgetting finite-dimensionality carries the identity component to the identity component
of the corresponding `Rep` morphism, after identifying the two induction models. -/
theorem indHomMackeyIdentityComponent_forget (A B : FDRep k H)
    (φ : indFDRep A ⟶ indFDRep B) :
    indHomMackeyIdentityComponent A B φ =
      FDRep.forget₂HomLinearEquiv A B
        (Rep.indHomMackeyIdentityComponent
          ((forget₂ (FDRep k H) (Rep k H)).obj A)
          ((forget₂ (FDRep k H) (Rep k H)).obj B)
          ((indFDRepForgetIso A).inv ≫
            (FDRep.forget₂HomLinearEquiv (indFDRep A) (indFDRep B)).symm φ ≫
              (indFDRepForgetIso B).hom)) := by
  simp only [indHomMackeyIdentityComponent, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe, FDRep.indHomMackeyLinearEquiv_apply,
    mackeyHomSelfLinearEquiv, Rep.indHomMackeyIdentityComponent_apply]
  -- The two forgetful equivalences present the same scalar action through different
  -- category instances; erw identifies those presentations before canceling them.
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The identity Mackey component of an induced finite-dimensional morphism is the original
morphism, over every field. -/
@[simp↓]
theorem indHomMackeyIdentityComponent_indFDRepMap (A B : FDRep k H) (f : A ⟶ B) :
    indHomMackeyIdentityComponent A B (indFDRepMap f) = f := by
  rw [indHomMackeyIdentityComponent_forget]
  -- Identify the inverse forgetful Hom equivalence with the actual forgetful functor map,
  -- so the public equation for indFDRepMap applies without unfolding its construction.
  change FDRep.forget₂HomLinearEquiv A B
    (Rep.indHomMackeyIdentityComponent _ _
      ((indFDRepForgetIso A).inv ≫
        (forget₂ (FDRep k G) (Rep k G)).map (indFDRepMap f) ≫
          (indFDRepForgetIso B).hom)) = f
  rw [forget₂_map_indFDRepMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    Rep.indFunctor_map, Rep.indHomMackeyIdentityComponent_indMap]
  exact (FDRep.forget₂HomLinearEquiv A B).apply_symm_apply f

/-- On the existing induced-endomorphism algebra map, the identity Mackey component is the
original native endomorphism. -/
@[simp↓]
theorem indHomMackeyIdentityComponent_indEndAlgHom (A : FDRep k H)
    (f : CategoryTheory.End A) :
    indHomMackeyIdentityComponent A A (A.indEndAlgHom f).asHom = f.asHom := by
  rw [FDRep.indEndAlgHom_asHom, indHomMackeyIdentityComponent_indFDRepMap]

end FDRep
