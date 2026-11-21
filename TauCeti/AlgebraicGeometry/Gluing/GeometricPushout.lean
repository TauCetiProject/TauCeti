/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic
import TauCeti.Topology.Sheaves.Limits
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Geometric pushouts of schemes

A square is a geometric pushout if it is a pushout on underlying spaces and sections on each
open are pairs of sections on the two inverse images that agree on the overlap. A Ferrand
pushout is a geometric pushout of a closed immersion and a finite morphism.

A geometric pushout is a categorical pushout of schemes. The topological pushout gives the
continuous map to a target; the pullbacks of section rings then give its structure maps.
Locality follows by checking the stalks after composition with the incoming maps, whose
images jointly cover the pushout. This is the two-map analogue of
`LocallyRingedSpace.Hom.descOfIsQuotientMap`.

References: D. Ferrand, *Conducteur, descente et pincement*, §4.1;
J. Witaszek, *Keel's base point free theorem and quotients in mixed characteristic*,
Definition 2.17 (geometric pushouts under the hypotheses there).
-/

public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {Z Y W P : Scheme.{u}} {i : Z ⟶ Y} {g : Z ⟶ W} {a : Y ⟶ P} {b : W ⟶ P}

/-- A geometric pushout is a topological pushout whose section rings on every open form a
pullback with the section rings on the three inverse images. -/
structure IsGeometricPushout (i : Z ⟶ Y) (g : Z ⟶ W) (a : Y ⟶ P) (b : W ⟶ P) : Prop
    extends CommSq i g a b where
  top : IsPushout i.base g.base a.base b.base
  app (U : P.Opens) : IsPullback (a.app U) (b.app U) (i.app (a ⁻¹ᵁ U))
    (g.appLE (b ⁻¹ᵁ U) (i ⁻¹ᵁ a ⁻¹ᵁ U) (by rw [← Hom.comp_preimage, ← Hom.comp_preimage, w]))

/-- A Ferrand pushout is a geometric pushout of a closed immersion `i` and a finite map `g`. -/
structure IsFerrandPushout (i : Z ⟶ Y) (g : Z ⟶ W) (a : Y ⟶ P) (b : W ⟶ P) : Prop
    extends IsGeometricPushout i g a b where
  isClosedImmersion : IsClosedImmersion i
  isFinite : IsFinite g

namespace IsGeometricPushout

/-- A topological pushout of schemes is geometric if the section-ring squares are pullbacks
on the affine opens of the target. The section comparison then holds on all opens. -/
theorem of_affine (w : CommSq i g a b) (htop : IsPushout i.base g.base a.base b.base)
    (haff : ∀ U : P.affineOpens, IsPullback (a.app U) (b.app U) (i.app (a ⁻¹ᵁ U.val))
      (g.appLE (b ⁻¹ᵁ U.val) (i ⁻¹ᵁ a ⁻¹ᵁ U.val)
        (by rw [← Hom.comp_preimage, ← Hom.comp_preimage, w.w]))) :
    IsGeometricPushout i g a b := by
  let push {S : Scheme.{u}} (f : S ⟶ P) := (TopCat.Sheaf.pushforward CommRingCat f.base).obj S.sheaf
  let fa : P.sheaf ⟶ push a := ObjectProperty.homMk a.c
  let fb : P.sheaf ⟶ push b := ObjectProperty.homMk b.c
  let l : push a ⟶ push (i ≫ a) :=
    ObjectProperty.homMk ((TopCat.Presheaf.pushforward CommRingCat a.base).map i.c)
  let r : push b ⟶ push (i ≫ a) := ObjectProperty.homMk
    { app := fun U ↦ g.appLE (b ⁻¹ᵁ U.unop) (i ⁻¹ᵁ a ⁻¹ᵁ U.unop)
        (by rw [← Hom.comp_preimage, ← Hom.comp_preimage, w.w])
      naturality := fun U V e ↦ by
        -- The source and target restrictions are the ones on the inverse images of `e`.
        change W.presheaf.map ((Opens.map b.base).map e.unop).op ≫ g.appLE _ _ _ =
          g.appLE _ _ _ ≫ Z.presheaf.map ((Opens.map i.base).map ((Opens.map a.base).map e.unop)).op
        simp only [Hom.map_appLE, Hom.appLE_map] }
  have hs : IsPullback fa fb l r :=
    TopCat.Sheaf.isPullback_of_isPullback_app_of_isBasis
      (by simpa only [Subtype.range_coe] using P.isBasis_affineOpens) haff
  refine ⟨w, htop, fun U ↦ ?_⟩
  exact ((CategoryTheory.evaluation _ CommRingCat.{u}).obj (op U)).map_isPullback
    ((TopCat.Sheaf.forget CommRingCat.{u} P.carrier).map_isPullback hs)

/-- Pinching along an isomorphism leaves the other scheme unchanged, with its structure sheaf. -/
theorem of_isIso (w : CommSq i g a b) [IsIso g] [IsIso a] : IsGeometricPushout i g a b where
  toCommSq := w
  top := IsPushout.of_vert_isIso (CommSq.mk (congrArg (fun f : Z ⟶ P ↦ f.base) w.w))
  app U := by
    let e : i ⁻¹ᵁ a ⁻¹ᵁ U = g ⁻¹ᵁ b ⁻¹ᵁ U := by
      rw [← Hom.comp_preimage, ← Hom.comp_preimage, w.w]
    have hg : IsIso (g.appLE (b ⁻¹ᵁ U) (i ⁻¹ᵁ a ⁻¹ᵁ U) e.le) := by
      rw [Hom.appLE]
      have : IsIso (Z.presheaf.map (homOfLE e.le).op) := Z.presheaf.map_isIso (eqToHom e).op
      infer_instance
    apply IsPullback.of_horiz_isIso
    constructor
    rw [i.app_eq_appLE, a.app_eq_appLE, b.app_eq_appLE,
      Hom.appLE_comp_appLE, Hom.appLE_comp_appLE]
    exact (i ≫ a).congr_appLE w.w U _ _ _

variable (h : IsGeometricPushout i g a b)

include h in
/-- The two incoming maps of a geometric pushout cover its underlying space. -/
theorem range_union : Set.range a ∪ Set.range b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, y, hxy⟩ := Concrete.isColimit_exists_rep _ h.top.isColimit x
  obtain (_ | ⟨_ | _⟩) := j
  · exact Or.inl ⟨i y, hxy⟩
  · exact Or.inl ⟨y, hxy⟩
  · exact Or.inr ⟨y, hxy⟩

section Desc

variable {T : Scheme.{u}} {y : Y ⟶ T} {z : W ⟶ T} (e : i ≫ y = g ≫ z)

private noncomputable def descBase : P.carrier ⟶ T.carrier :=
  h.top.desc y.base z.base (by simpa only [Hom.comp_base] using congrArg (fun f : Z ⟶ T ↦ f.base) e)

private theorem comp_descBase_left : a.base ≫ h.descBase e = y.base :=
  h.top.inl_desc _ _ _

private theorem comp_descBase_right : b.base ≫ h.descBase e = z.base :=
  h.top.inr_desc _ _ _

private theorem preimage_descBase_left (U : T.Opens) :
    a ⁻¹ᵁ (Opens.map (h.descBase e)).obj U ≤ y ⁻¹ᵁ U := by
  rw [← Opens.map_comp_obj, comp_descBase_left]

private theorem preimage_descBase_right (U : T.Opens) :
    b ⁻¹ᵁ (Opens.map (h.descBase e)).obj U ≤ z ⁻¹ᵁ U := by
  rw [← Opens.map_comp_obj, comp_descBase_right]

private noncomputable def descApp (U : T.Opens) :
    Γ(T, U) ⟶ Γ(P, (Opens.map (h.descBase e)).obj U) := by
  refine (h.app _).lift (y.appLE U _ (h.preimage_descBase_left e U))
    (z.appLE U _ (h.preimage_descBase_right e U)) ?_
  rw [i.app_eq_appLE, Hom.appLE_comp_appLE, Hom.appLE_comp_appLE]
  exact (i ≫ y).congr_appLE e U _ _ _

@[reassoc]
private theorem descApp_left (U : T.Opens) :
    h.descApp e U ≫ a.app ((Opens.map (h.descBase e)).obj U) =
      y.appLE U _ (h.preimage_descBase_left e U) := (h.app _).lift_fst ..

@[reassoc]
private theorem descApp_right (U : T.Opens) :
    h.descApp e U ≫ b.app ((Opens.map (h.descBase e)).obj U) =
      z.appLE U _ (h.preimage_descBase_right e U) := (h.app _).lift_snd ..

private noncomputable def descPsh : P.toPresheafedSpace ⟶ T.toPresheafedSpace where
  base := h.descBase e
  c :=
    { app U := h.descApp e U.unop
      naturality U V r := by
        apply (h.app ((Opens.map (h.descBase e)).obj V.unop)).hom_ext
        · simp only [TopCat.Presheaf.pushforward_obj_map, Category.assoc, descApp_left,
            a.naturality, descApp_left_assoc, Hom.appLE_map, Hom.map_appLE]
        · simp only [TopCat.Presheaf.pushforward_obj_map, Category.assoc, descApp_right,
            b.naturality, descApp_right_assoc, Hom.appLE_map, Hom.map_appLE] }

private theorem comp_descPsh_left : a.toPshHom ≫ h.descPsh e = y.toPshHom := by
  apply PresheafedSpace.ext_of_app (h.comp_descBase_left e)
  intro U
  rw [PresheafedSpace.comp_c_app]
  exact (congrArg (· ≫ _) (h.descApp_left e U)).trans
    (TopCat.Presheaf.comp_map_comp_map_eq_self _ _ _)

private theorem comp_descPsh_right : b.toPshHom ≫ h.descPsh e = z.toPshHom := by
  apply PresheafedSpace.ext_of_app (h.comp_descBase_right e)
  intro U
  rw [PresheafedSpace.comp_c_app]
  exact (congrArg (· ≫ _) (h.descApp_right e U)).trans
    (TopCat.Presheaf.comp_map_comp_map_eq_self _ _ _)

private theorem isLocalHom_stalkMap_descPsh (p : P) :
    IsLocalHom ((h.descPsh e).stalkMap p).hom := by
  have localAt {S : Scheme.{u}} (f : S ⟶ P) (k : S ⟶ T) (hk : f.toPshHom ≫ h.descPsh e =
      k.toPshHom) (x : S) : IsLocalHom ((h.descPsh e).stalkMap (f x)).hom := by
    have H : IsLocalHom ((f.toPshHom ≫ h.descPsh e).stalkMap x).hom := by
      rw [PresheafedSpace.stalkMap.congr_hom _ _ hk, CommRingCat.hom_comp]
      exact CommRingCat.isLocalHom_comp _ _
    rw [PresheafedSpace.stalkMap.comp] at H
    exact @isLocalHom_of_comp _ _ _ _ _ _ _ (f.stalkMap x).hom H
  have hp : p ∈ Set.range a ∪ Set.range b := h.range_union.symm ▸ Set.mem_univ p
  rcases hp with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact localAt a y (h.comp_descPsh_left e) x
  · exact localAt b z (h.comp_descPsh_right e) x

end Desc

include h in
private theorem hom_ext {T : Scheme.{u}} {j k : P ⟶ T}
    (ha : a ≫ j = a ≫ k) (hb : b ≫ j = b ≫ k) : j = k := by
  have hbase : j.base = k.base := h.top.hom_ext
    (congrArg (fun f : Y ⟶ T ↦ f.base) ha) (congrArg (fun f : W ⟶ T ↦ f.base) hb)
  refine Scheme.Hom.ext hbase fun U ↦ (h.app (k ⁻¹ᵁ U)).hom_ext ?_ ?_
  · rw [Category.assoc, a.naturality, ← Category.assoc]
    exact (Hom.congr_app ha.symm U).symm
  · rw [Category.assoc, b.naturality, ← Category.assoc]
    exact (Hom.congr_app hb.symm U).symm

include h in
/-- A geometric pushout is a categorical pushout against every scheme target. -/
theorem isPushout : IsPushout i g a b := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk a b h.w)
  refine PushoutCocone.isColimitAux' _ fun s ↦ ?_
  let m : P ⟶ s.pt := ⟨⟨h.descPsh s.condition, h.isLocalHom_stalkMap_descPsh s.condition⟩⟩
  have ha : a ≫ m = s.inl := Scheme.Hom.ext'
    (LocallyRingedSpace.Hom.ext' (h.comp_descPsh_left s.condition))
  have hb : b ≫ m = s.inr := Scheme.Hom.ext'
    (LocallyRingedSpace.Hom.ext' (h.comp_descPsh_right s.condition))
  exact ⟨m, ha, hb, fun ha' hb' ↦ h.hom_ext (ha'.trans ha.symm) (hb'.trans hb.symm)⟩

end IsGeometricPushout

/-- An isomorphism in the finite leg of a pinching gives a Ferrand pushout with the original
scheme as its target. -/
theorem IsFerrandPushout.of_isIso (w : CommSq i g a b) [IsClosedImmersion i]
    [IsIso g] [IsIso a] : IsFerrandPushout i g a b :=
  ⟨IsGeometricPushout.of_isIso w, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
