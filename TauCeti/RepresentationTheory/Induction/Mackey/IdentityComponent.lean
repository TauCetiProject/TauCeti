/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.RepresentationTheory.Induction.Mackey.Hom
import TauCeti.CategoryTheory.Linear.FullyFaithful
import TauCeti.RepresentationTheory.Coinduced
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

/-- The inner conjugation twist at a representative in `H` is removed by its action on `B`. -/
private noncomputable def mackeySelfTwistIso (hs : s ∈ H) (B : Rep.{u} k H) :
    Rep.res (mackeyToH s H H) B ≅
      Rep.res ((mackeySubgroup s H H).subgroupOf H).subtype B :=
  Rep.mkIso <| .mk (LinearEquiv.ofBijective (B.ρ ⟨s, hs⟩) (B.ρ.apply_bijective _))
    fun y ↦ by
      have h : (⟨s, hs⟩ : H) * mackeyToH s H H y = (y : H) * ⟨s, hs⟩ := by
        ext
        simp only [Subgroup.coe_mul, coe_mackeyToH_apply]
        group
      ext a
      simpa only [Rep.coe_res_obj_ρ', MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul,
        mul_apply_eq_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.ofBijective_apply] using
        congrArg (fun f : Module.End k B ↦ f a) (congrArg B.ρ h)

/-- The twist comparison acts by the chosen representative on the original carrier. -/
private theorem mackeySelfTwistIso_hom_hom_apply (hs : s ∈ H) (B : Rep.{u} k H) (b : B) :
    (mackeySelfTwistIso hs B).hom.hom b = B.ρ ⟨s, hs⟩ b :=
  rfl

/-- A Mackey Hom component represented by an element of `H` is the ordinary Hom space over
`H`. The map removes inner conjugation by acting on the target with the representative. -/
noncomputable def mackeyHomSelfLinearEquiv (hs : s ∈ H) (A B : Rep.{u} k H) :
    (Rep.res ((mackeySubgroup s H H).subgroupOf H).subtype A ⟶
      Rep.res (mackeyToH s H H) B) ≃ₗ[k] (A ⟶ B) := by
  letI := Rep.full_res (k := k) _ (mackeySubgroup_subgroupOf_subtype_surjective hs)
  exact (Linear.homCongr k (Iso.refl _) (mackeySelfTwistIso hs B)).trans
    ((Rep.resFunctor ((mackeySubgroup s H H).subgroupOf H).subtype).homLinearEquiv k A B).symm

/-- The identity-component identification postcomposes with the action of its representative. -/
@[simp]
theorem mackeyHomSelfLinearEquiv_apply (hs : s ∈ H) (A B : Rep.{u} k H)
    (f : Rep.res ((mackeySubgroup s H H).subgroupOf H).subtype A ⟶
      Rep.res (mackeyToH s H H) B) (a : A) :
    (mackeyHomSelfLinearEquiv hs A B f).hom a = B.ρ ⟨s, hs⟩ (f.hom a) := by
  let := Rep.full_res (k := k) _ (mackeySubgroup_subgroupOf_subtype_surjective hs)
  have h := ((Rep.resFunctor ((mackeySubgroup s H H).subgroupOf H).subtype).homLinearEquiv
    k A B).apply_symm_apply (f ≫ (mackeySelfTwistIso hs B).hom)
  rw [Functor.homLinearEquiv_apply] at h
  calc
    _ = (mackeySelfTwistIso hs B).hom.hom (f.hom a) := by
      simpa only [mackeyHomSelfLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
        Iso.refl_inv, Category.id_comp, Rep.resMap_hom_apply, Rep.hom_comp,
        IntertwiningMap.comp_apply] using congrArg (fun g ↦ g.hom a) h
    _ = _ := mackeySelfTwistIso_hom_hom_apply hs B (f.hom a)

/-- The inverse identity-component identification removes the representative's action. -/
@[simp↓]
theorem mackeyHomSelfLinearEquiv_symm_apply (hs : s ∈ H) (A B : Rep.{u} k H)
    (g : A ⟶ B) (a : A) :
    ((mackeyHomSelfLinearEquiv hs A B).symm g).hom a =
      B.ρ (⟨s, hs⟩ : H)⁻¹ (g.hom a) := by
  have h := mackeyHomSelfLinearEquiv_apply hs A B
    ((mackeyHomSelfLinearEquiv hs A B).symm g) a
  rw [LinearEquiv.apply_symm_apply] at h
  exact (Representation.inv_self_apply B.ρ ⟨s, hs⟩ _).symm.trans
    (congrArg (B.ρ (⟨s, hs⟩ : H)⁻¹) h.symm)

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
  rw [Rep.resCoindHomEquiv_symm_hom_apply, Rep.hom_comp,
    IntertwiningMap.comp_apply, Rep.homDirectSumLinearEquiv_apply,
    Rep.hom_comp, IntertwiningMap.comp_apply, Rep.indResHomEquiv_hom_apply]
  rw [Rep.indMap_hom_mk]
  have hdecomp := Rep.mackeyDecomposition_hom_hom_apply_mk B D (⟨D.out, hs⟩ : H) 1
    (f.hom a)
  simp only [Subgroup.coe_one, mul_inv_cancel, one_mul] at hdecomp
  rw [hdecomp]
  rw [DirectSum.lof_apply]
  rw [Rep.indCoindIso_hom_hom_apply]
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
    (H.doubleCoset_out_mk_one_mem) A B).toLinearMap.comp
    ((LinearMap.proj (DoubleCoset.mk H H 1)).comp
      (indHomMackeyLinearEquiv A B).toLinearMap)

/-- The identity component is computed from the actual chosen Mackey component by removing
its conjugation twist. -/
theorem indHomMackeyIdentityComponent_apply (A B : Rep.{u} k H)
    (φ : Rep.ind H.subtype A ⟶ Rep.ind H.subtype B) :
    indHomMackeyIdentityComponent A B φ =
      mackeyHomSelfLinearEquiv
        (H.doubleCoset_out_mk_one_mem) A B
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

variable {k G : Type u} [Group G] {H : Subgroup G} {s : G}

section

variable [CommRing k]

/-- For finitely generated representations, the Mackey Hom component represented by an
element of `H` identifies with the original Hom space, by removing the inner conjugation twist. -/
noncomputable def mackeyHomSelfLinearEquiv (hs : s ∈ H) (A B : FDRep k H) :
    (Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj B) ≃ₗ[k] (A ⟶ B) :=
  (FDRep.forget₂HomLinearEquiv _ _).symm.trans <|
    (Rep.mackeyHomSelfLinearEquiv hs
      ((forget₂ (FDRep k H) (Rep k H)).obj A)
      ((forget₂ (FDRep k H) (Rep k H)).obj B)).trans <|
      FDRep.forget₂HomLinearEquiv A B

/-- For finitely generated representations, the identification acts by the chosen representative
on the target. -/
@[simp]
theorem mackeyHomSelfLinearEquiv_apply (hs : s ∈ H) (A B : FDRep k H)
    (f : Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj B) (a : A) :
    (mackeyHomSelfLinearEquiv hs A B f) a =
      B.ρ ⟨s, hs⟩ (f a) := by
  exact Rep.mackeyHomSelfLinearEquiv_apply hs
    ((forget₂ (FDRep k H) (Rep k H)).obj A)
    ((forget₂ (FDRep k H) (Rep k H)).obj B)
    ((FDRep.forget₂HomLinearEquiv _ _).symm f) a

/-- For finitely generated representations, the inverse identification removes the
representative's action. -/
theorem mackeyHomSelfLinearEquiv_symm_apply (hs : s ∈ H) (A B : FDRep k H)
    (g : A ⟶ B) (a : A) :
    (mackeyHomSelfLinearEquiv hs A B).symm g a =
      B.ρ (⟨s, hs⟩ : H)⁻¹ (g a) := by
  have h := mackeyHomSelfLinearEquiv_apply hs A B
    ((mackeyHomSelfLinearEquiv hs A B).symm g) a
  rw [LinearEquiv.apply_symm_apply] at h
  exact (Representation.inv_self_apply B.ρ ⟨s, hs⟩ _).symm.trans
    (congrArg (B.ρ (⟨s, hs⟩ : H)⁻¹) h.symm)

end

variable [Field k] [Finite G]

/-- The identity double-coset projection of the actual finite-dimensional Mackey Hom
isomorphism, with its component identified with `Hom_H(A, B)`. -/
noncomputable def indHomMackeyIdentityComponent (A B : FDRep k H) :
    (indFDRep A ⟶ indFDRep B) →ₗ[k] (A ⟶ B) :=
  (mackeyHomSelfLinearEquiv
    (H.doubleCoset_out_mk_one_mem) A B).toLinearMap.comp
    ((LinearMap.proj (DoubleCoset.mk H H 1)).comp
      (indHomMackeyLinearEquiv A B).toLinearMap)

/-- The finite-dimensional identity component is the actual chosen Mackey component with its
inner conjugation twist removed. -/
theorem indHomMackeyIdentityComponent_apply (A B : FDRep k H)
    (φ : indFDRep A ⟶ indFDRep B) :
    indHomMackeyIdentityComponent A B φ =
      mackeyHomSelfLinearEquiv
        (H.doubleCoset_out_mk_one_mem) A B
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
  apply ConcreteCategory.hom_ext
  intro a
  simp only [indHomMackeyIdentityComponent_apply, mackeyHomSelfLinearEquiv_apply,
    FDRep.forget₂HomLinearEquiv_apply, Rep.indHomMackeyIdentityComponent_apply,
    indHomMackeyLinearEquiv_apply]
  let D := DoubleCoset.mk H H 1
  let A' := (forget₂ (FDRep k H) (Rep k H)).obj A
  let B' := (forget₂ (FDRep k H) (Rep k H)).obj B
  let φ' := (indFDRepForgetIso A).inv ≫
    (FDRep.forget₂HomLinearEquiv (indFDRep A) (indFDRep B)).symm φ ≫
      (indFDRepForgetIso B).hom
  let ψ := Rep.indHomMackeyLinearEquiv A' B' φ' D
  have h := FDRep.forget₂HomLinearEquiv_apply
    (Subgroup.resFDRep ((mackeySubgroup D.out H H).subgroupOf H) A)
    ((Action.res (FGModuleCat k) (mackeyToH D.out H H)).obj B) ψ a
  exact (congrArg (B.ρ ⟨D.out, H.doubleCoset_out_mk_one_mem⟩) h).trans
    (Rep.mackeyHomSelfLinearEquiv_apply (H.doubleCoset_out_mk_one_mem) A' B' ψ a).symm

/-- The identity Mackey component of an induced finite-dimensional morphism is the original
morphism, over every field. -/
@[simp↓]
theorem indHomMackeyIdentityComponent_indFDRepMap (A B : FDRep k H) (f : A ⟶ B) :
    indHomMackeyIdentityComponent A B (indFDRepMap f) = f := by
  rw [indHomMackeyIdentityComponent_forget]
  rw [FDRep.forget₂HomLinearEquiv_symm_apply]
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
