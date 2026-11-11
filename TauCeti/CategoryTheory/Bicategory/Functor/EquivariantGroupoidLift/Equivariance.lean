/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Normalized

/-!
# Equivariance of the normalized transport return comparison

Reconstructing a lift from normalized transport inserts identity action functors and chosen
inverse fiber comparisons. The canonical natural isomorphism `toLiftTransportIso` removes
these choices. This file proves that it also intertwines the commuting isomorphisms with the
prescribed actions. Thus its forward and inverse natural transformations are equivariant,
and the mixed square is an equality of actual natural isomorphisms between functors on the
prescribed fibers.

The proof uses the normalized reconstruction and characteristic equations from
`EquivariantGroupoidLift.Normalized`, the two factorizations defining
`EquivariantGroupoidLift.jointActCommIso`, and the mate equation
`EquivariantGroupoidLift.functor_map_actInverseIso_hom_app_comp` for inverse fiber comparisons.
This supplies the action compatibility of the return comparison; it does not construct a
biequivalence of the bicategories of lift packages and normalized data.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, arXiv:2002.06055, Chapter 4:
  strong transformations and their naturality isomorphisms.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.NormalizedTransport

open CategoryTheory Bicategory CategoryTheory.Prod

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (N : NormalizedTransport Γ actions)

private lemma joint_mapComp'_toNatIso {X Y Z : Γ × SingleObj H}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
    Cat.Hom.toNatIso (N.joint.mapComp' f.toLoc g.toLoc fg.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, hfg])) = N.jointComp f g fg hfg := by
  ext x
  -- The flexible comparison is assembled from the mapped equality and compositor.
  change (N.joint.map₂ (eqToHom (by simp [← Quiver.Hom.comp_toLoc, hfg] :
    fg.toLoc = f.toLoc ≫ g.toLoc))).toNatTrans.app x ≫
    (N.joint.mapComp f.toLoc g.toLoc).hom.toNatTrans.app x = _
  exact N.joint_map₂_comp_mapComp_hom_app f.toLoc g.toLoc fg.toLoc _ x

private lemma jointComp_hom_app_comp_source_return {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H)
    (x : fiber actions p) :
    (N.jointComp (𝟙 p ×ₘ a) (g ×ₘ 𝟙 _) (g ×ₘ a) (by simp)).hom.app x ≫
      (N.transport g).map ((act actions p (𝟙 _)).map ((N.transportId p).hom.app
        ((act actions p a).obj x))) ≫
      (N.transport g).map ((actId actions p).hom.app ((act actions p a).obj x)) = 𝟙 _ := by
  rw [jointComp_hom_app]
  dsimp only [Prod.fst, Prod.snd]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc (N.transport g)
    ((N.transportCommIso (𝟙 p) (𝟙 _)).hom.app _), N.transportCommIso_id]
  have ht := N.transportComp_left_unitality g (by simp)
  rw [← ht]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, actComp_right_unitality]
  exact (N.transport g).map_id _

private lemma jointComp_hom_app_comp_target_return {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (N.jointComp (g ×ₘ 𝟙 _) (𝟙 q ×ₘ a) (g ×ₘ a) (by simp)).hom.app x ≫
      (N.transportId q).hom.app ((act actions q a).obj
        ((N.transport g).obj ((act actions p (𝟙 _)).obj x))) ≫
      (act actions q a).map ((N.transport g).map ((actId actions p).hom.app x)) =
    (N.transportCommIso g a).hom.app x := by
  rw [jointComp_hom_app]
  dsimp only [Prod.fst, Prod.snd]
  simp only [Category.assoc]
  -- The composite functor objects in the joint comparison reduce to the prescribed fibers.
  erw [N.transportId_hom_naturality_assoc]
  have ht := N.transportComp_right_unitality g (by simp)
  rw [← ht]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← N.transportCommIso_hom_naturality, ← Functor.map_comp_assoc,
    actComp_left_unitality]
  simp

private lemma jointActCommIso_hom_app_comp_return {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (N.toLift.jointActCommIso g a).hom.app x ≫
      (N.transportId q).hom.app ((act actions q a).obj
        ((N.transport g).obj ((act actions p (𝟙 _)).obj x))) ≫
      (act actions q a).map ((N.transport g).map ((actId actions p).hom.app x)) =
    (N.transport g).map ((act actions p (𝟙 _)).map ((N.transportId p).hom.app
        ((act actions p a).obj x))) ≫
      (N.transport g).map ((actId actions p).hom.app ((act actions p a).obj x)) ≫
      (N.transportCommIso g a).hom.app x := by
  -- Evaluate on the prescribed fiber, identified with the reconstructed joint fiber.
  erw [jointActCommIso_hom_app]
  have hl := N.joint_mapComp'_toNatIso (𝟙 p ×ₘ a) (g ×ₘ 𝟙 _) (g ×ₘ a) (by simp)
  have hr := N.joint_mapComp'_toNatIso (g ×ₘ 𝟙 _) (𝟙 q ×ₘ a) (g ×ₘ a) (by simp)
  have hli := congrArg (fun e => e.inv.app x) hl
  have hrh := congrArg (fun e => e.hom.app x) hr
  erw [hli, hrh]
  have hi : (N.jointComp (𝟙 p ×ₘ a) (g ×ₘ 𝟙 _) (g ×ₘ a) (by simp)).inv.app x =
    (N.transport g).map ((act actions p (𝟙 _)).map ((N.transportId p).hom.app
      ((act actions p a).obj x))) ≫
    (N.transport g).map ((actId actions p).hom.app ((act actions p a).obj x)) := by
    rw [← cancel_epi ((N.jointComp (𝟙 p ×ₘ a) (g ×ₘ 𝟙 _) (g ×ₘ a) (by simp)).hom.app x)]
    simpa only [Iso.hom_inv_id_app, Category.assoc] using
      (N.jointComp_hom_app_comp_source_return g a x).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (N.jointComp_hom_app_comp_target_return g a x)).trans
      ((congrArg (· ≫ _) hi).trans (Category.assoc _ _ _)))

/-- The inverse comparison of the action on a fiber, followed by the unit transport and the
action of the counit, is the counit at the acted-on object: the mate equation for
`actInverseIso`. -/
private lemma actInverseIso_hom_app_comp_transportId_comp_map_counit {p : Γ}
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (N.toLift.actInverseIso p a).hom.app x ≫
      (N.transportId p).hom.app
        ((act actions p a).obj ((N.toLift.fiberEquivalence p).inverse.obj x)) ≫
      (act actions p a).map ((N.toLift.fiberEquivalence p).counit.app x) =
    (N.toLift.fiberEquivalence p).counit.app ((act actions p a).obj x) := by
  have hh : (N.toLift.actInverseIso p a).hom.app x ≫
      (N.transportId p).hom.app
        ((act actions p a).obj ((N.toLift.fiberEquivalence p).inverse.obj x)) =
      (N.toLift.fiberEquivalence p).counit.app ((act actions p a).obj x) ≫
        (act actions p a).map ((N.toLift.fiberEquivalence p).counitInv.app x) := by
    have h := N.toLift.functor_map_actInverseIso_hom_app_comp p a x
    simp only [fiberEquivalence_functor, toLift_comparison, comparison_app,
      Cat.Hom.id_toFunctor] at h
    erw [comparisonNaturality_hom_app, N.comparison_naturality_hom_app] at h
    exact h
  -- `erw`: the goal lives in the joint fiber `N.toLift.jointFiber p`, which is only
  -- definitionally equal to `fiber actions p` (the type of `hh`), so `rw` cannot match `hh`.
  erw [← Category.assoc, hh, Category.assoc, ← Functor.map_comp]
  have hi : (N.toLift.fiberEquivalence p).counitInv.app x ≫
      (N.toLift.fiberEquivalence p).counit.app x = 𝟙 x :=
    (N.toLift.fiberEquivalence p).counitIso.inv_hom_id_app x
  -- `erw`: same joint-fiber versus `fiber actions p` defeq as above.
  erw [hi, (act actions p a).map_id, Category.comp_id]

/-- The canonical comparison with reconstructed transport commutes with every prescribed
action, including its chosen commuting isomorphism. -/
@[reassoc]
lemma toLiftTransportIso_hom_app_comp_transportCommIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (N.toLiftTransportIso g).hom.app ((act actions p a).obj x) ≫
      (N.transportCommIso g a).hom.app x =
    (N.toLift.transportCommIso g a).hom.app x ≫
      (act actions q a).map ((N.toLiftTransportIso g).hom.app x) := by
  -- Name the inverse-comparison carriers in the prescribed fibers.
  let y : fiber actions p := (N.toLift.fiberEquivalence p).inverse.obj x
  let ε : y ⟶ x := (N.toLift.fiberEquivalence p).counit.app x
  let εi : x ⟶ y := (N.toLift.fiberEquivalence p).counitInv.app x
  let z : fiber actions p := (N.toLift.fiberEquivalence p).inverse.obj ((act actions p a).obj x)
  let εa : z ⟶ (act actions p a).obj x :=
    (N.toLift.fiberEquivalence p).counit.app ((act actions p a).obj x)
  let α : z ⟶ (N.transport (𝟙 p)).obj ((act actions p a).obj y) :=
    (N.toLift.actInverseIso p a).hom.app x
  let κ : (N.transport g).obj ((act actions p (𝟙 _)).obj
      ((N.transport (𝟙 p)).obj ((act actions p a).obj y))) ⟶
      (N.transport (𝟙 q)).obj ((act actions q a).obj
        ((N.transport g).obj ((act actions p (𝟙 _)).obj y))) :=
    (N.toLift.jointActCommIso g a).hom.app y
  rw [N.toLift.transportCommIso_hom_app, N.toLiftTransportIso_hom_app]
  simp only [fiberEquivalence_functor, toLift_comparison, comparison_app, Cat.Hom.id_toFunctor]
  erw [comparisonNaturality_hom_app, N.comparison_naturality_hom_app]
  rw [N.toLiftTransportIso_hom_app]
  -- Present the identity fiber comparisons in the prescribed fibers, retaining their counits.
  change ((N.transport g).map ((act actions p (𝟙 _)).map εa) ≫
      (N.transport g).map ((actId actions p).hom.app ((act actions p a).obj x))) ≫
      (N.transportCommIso g a).hom.app x =
    (((N.transport g).map ((act actions p (𝟙 _)).map α) ≫ κ) ≫
      (N.transportId q).hom.app ((act actions q a).obj
        ((N.transport g).obj ((act actions p (𝟙 _)).obj y)))) ≫
      (act actions q a).map ((N.transport g).map ((act actions p (𝟙 _)).map ε) ≫
        (N.transport g).map ((actId actions p).hom.app x))
  have hnat := (Functor.whiskerRight (actId actions p).hom (N.transport g)).naturality ε
  simp only [Functor.comp_map, Functor.id_map, Functor.whiskerRight_app] at hnat
  rw [hnat]
  simp only [Functor.map_comp, Category.assoc]
  -- Remove the unit transports from the two factorizations of the joint arrow.
  have hk : κ ≫ (N.transportId q).hom.app ((act actions q a).obj
        ((N.transport g).obj ((act actions p (𝟙 _)).obj y))) ≫
      (act actions q a).map ((N.transport g).map ((actId actions p).hom.app y)) =
      (N.transport g).map ((act actions p (𝟙 _)).map
        ((N.transportId p).hom.app ((act actions p a).obj y))) ≫
      (N.transport g).map ((actId actions p).hom.app ((act actions p a).obj y)) ≫
      (N.transportCommIso g a).hom.app y := N.jointActCommIso_hom_app_comp_return g a y
  have hk' := congrArg (· ≫ (act actions q a).map ((N.transport g).map ε)) hk
  simp only [Category.assoc] at hk'
  erw [hk']
  -- The mate equation for the source inverse comparison cancels the remaining counits.
  have hα : α ≫ (N.transportId p).hom.app ((act actions p a).obj y) ≫
      (act actions p a).map ε = εa := N.actInverseIso_hom_app_comp_transportId_comp_map_counit a x
  -- Naturality carries the source counit through the prescribed commuting cell.
  rw [← N.transportCommIso_hom_naturality]
  have hn := (actId actions p).hom.naturality ((act actions p a).map ε)
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc (N.transport g) ((actId actions p).hom.app _),
    ← hn, Functor.map_comp]
  simp only [Category.assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    (congrArg (fun f => (N.transport g).map ((act actions p (𝟙 _)).map f) ≫
      (N.transport g).map ((actId actions p).hom.app ((act actions p a).obj x)) ≫
      (N.transportCommIso g a).hom.app x) hα).symm

/-- The inverse canonical return comparison is equivariant for the prescribed actions. -/
@[reassoc]
lemma toLiftTransportIso_inv_app_comp_transportCommIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (N.toLiftTransportIso g).inv.app ((act actions p a).obj x) ≫
      (N.toLift.transportCommIso g a).hom.app x =
    (N.transportCommIso g a).hom.app x ≫
      (act actions q a).map ((N.toLiftTransportIso g).inv.app x) := by
  rw [← cancel_epi ((N.toLiftTransportIso g).hom.app ((act actions p a).obj x))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, N.toLiftTransportIso_hom_app_comp_transportCommIso]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact ((congrArg (_ ≫ ·) ((act actions q a).map_id _)).trans (Category.comp_id _)).symm

/-- The natural-isomorphism square expressing equivariance of the canonical return comparison. -/
lemma toLiftTransportIso_transportCommIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) :
    Functor.isoWhiskerLeft (act actions p a) (N.toLiftTransportIso g) ≪≫
        N.transportCommIso g a =
    N.toLift.transportCommIso g a ≪≫
        Functor.isoWhiskerRight (N.toLiftTransportIso g) (act actions q a) := by
  ext x
  exact N.toLiftTransportIso_hom_app_comp_transportCommIso g a x

end TauCeti.EquivariantGroupoidLift.NormalizedTransport
