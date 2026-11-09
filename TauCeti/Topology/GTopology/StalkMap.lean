/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.GTopology.ContinuousMap
public import TauCeti.Topology.GTopology.Points

/-!
# Stalk maps for continuous maps of G-topologies

For a continuous map `f : G.ContinuousMap G'` and a presheaf `P` on `G`,
`f.stalkPushforward P x` maps the stalk of the direct image at `f x` to the stalk of
`P` at `x`. It sends the germ of a section on `V` to its germ on `f⁻¹(V)`.
The construction uses the native site-point fibers, and works for presheaves valued
in any category with the relevant colimits.

The maps are natural in the presheaf and compatible with identities and composition.
Together with a presheaf morphism `Q → f_* P` they give `f.stalkMap`, the map on
stalks needed to express locality of morphisms of ringed G-spaces. For ordinary
open covers the construction agrees with Mathlib's `TopCat.Presheaf.stalkPushforward`
under the canonical stalk comparisons.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §9.1.
* The construction follows Mathlib's `TopCat.Presheaf.stalkPushforward`, using
  `GrothendieckTopology.Point.presheafFiberDesc` instead of a neighbourhood colimit.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v' u'' v'' w t

namespace TauCeti.GTopology.ContinuousMap

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B]
  {ι : B ↪o Set X} {G : GTopology ι}
  {Y : Type u'} {B' : Type v'} [SemilatticeInf B'] [OrderTop B']
  {ι' : B' ↪o Set Y} {G' : GTopology ι'}
  {Z : Type u''} {B'' : Type v''} [SemilatticeInf B''] [OrderTop B'']
  {ι'' : B'' ↪o Set Z} {G'' : GTopology ι''}
  {A : Type w} [Category.{t} A]
  [HasColimitsOfSize.{v, v} A] [HasColimitsOfSize.{v', v'} A]

/-- The map from the stalk of the direct image at `f x` to the stalk at `x`.
No sheaf condition is required. -/
noncomputable def stalkPushforward (f : G.ContinuousMap G') (P : Bᵒᵖ ⥤ A) (x : X) :
    (G'.point (f x)).presheafFiber.obj (f.comapFunctor.op ⋙ P) ⟶
      (G.point x).presheafFiber.obj P :=
  (G'.point (f x)).presheafFiberDesc
    (fun V h ↦ (G.point x).toPresheafFiber (f.comapFunctor.obj V)
      (G.pointElement x (by simpa using h.down.down)) P)
    (by intros; simp)

/-- The direct-image stalk map sends a germ on `V` to the germ on its preimage. -/
@[simp, reassoc (attr := simp)]
theorem toPresheafFiber_stalkPushforward (f : G.ContinuousMap G') (P : Bᵒᵖ ⥤ A)
    (x : X) (V : B') (h : (G'.point (f x)).fiber.obj V) :
    (G'.point (f x)).toPresheafFiber V h (f.comapFunctor.op ⋙ P) ≫
        f.stalkPushforward P x =
      (G.point x).toPresheafFiber (f.comapFunctor.obj V)
        (G.pointElement x (by simpa using h.down.down)) P :=
  (G'.point (f x)).toPresheafFiber_presheafFiberDesc _ _ _ _

/-- The direct-image stalk map is natural in the presheaf. -/
@[reassoc]
theorem stalkPushforward_naturality (f : G.ContinuousMap G') {P Q : Bᵒᵖ ⥤ A}
    (α : P ⟶ Q) (x : X) :
    (G'.point (f x)).presheafFiber.map (Functor.whiskerLeft f.comapFunctor.op α) ≫
        f.stalkPushforward Q x =
      f.stalkPushforward P x ≫ (G.point x).presheafFiber.map α := by
  ext V h
  simp

omit [HasColimitsOfSize.{v', v'} A] in
/-- The stalk map for the identity continuous map is the identity, after the canonical
identification of its source. -/
@[simp]
theorem stalkPushforward_id (P : Bᵒᵖ ⥤ A) (x : X) :
    (ContinuousMap.id G).stalkPushforward P x = eqToHom (by simp; rfl) := by
  ext U h
  rw [G.toPresheafFiber_congr (by simp) (by simp; rfl)
    (V := (ContinuousMap.id G).comapFunctor.obj U) (by simp)]
  simp

/-- Direct-image stalk maps compose in the same order as restriction of germs. -/
@[reassoc]
theorem stalkPushforward_comp [HasColimitsOfSize.{v'', v''} A]
    (g : G'.ContinuousMap G'') (f : G.ContinuousMap G') (P : Bᵒᵖ ⥤ A) (x : X) :
    (g.comp f).stalkPushforward P x =
      eqToHom (by simp; rfl) ≫
        (G''.point (g (f x))).presheafFiber.map
          (Functor.associator g.comapFunctor.op f.comapFunctor.op P).hom ≫
        g.stalkPushforward (f.comapFunctor.op ⋙ P) (f x) ≫ f.stalkPushforward P x := by
  ext V h
  rw [G''.toPresheafFiber_congr_assoc (by simp) (by simp; rfl) rfl]
  simpa using G.toPresheafFiber_congr rfl rfl
    (U := (g.comp f).comapFunctor.obj V) (V := f.comapFunctor.obj (g.comapFunctor.obj V))
    (by simp) (G.pointElement x (by simpa using h.down.down))

/-- The stalk map of a morphism of presheaves over a continuous map. For ring-valued
presheaves this is the ring homomorphism on which locality is imposed. -/
noncomputable def stalkMap (f : G.ContinuousMap G') {P : Bᵒᵖ ⥤ A} {Q : B'ᵒᵖ ⥤ A}
    (α : Q ⟶ f.comapFunctor.op ⋙ P) (x : X) :
    (G'.point (f x)).presheafFiber.obj Q ⟶ (G.point x).presheafFiber.obj P :=
  (G'.point (f x)).presheafFiber.map α ≫ f.stalkPushforward P x

/-- On germs the stalk map is given by the corresponding component of the presheaf morphism. -/
@[simp, reassoc (attr := simp)]
theorem toPresheafFiber_stalkMap (f : G.ContinuousMap G') {P : Bᵒᵖ ⥤ A}
    {Q : B'ᵒᵖ ⥤ A} (α : Q ⟶ f.comapFunctor.op ⋙ P) (x : X) (V : B')
    (h : (G'.point (f x)).fiber.obj V) :
    (G'.point (f x)).toPresheafFiber V h Q ≫ f.stalkMap α x =
      α.app (op V) ≫ (G.point x).toPresheafFiber (f.comapFunctor.obj V)
        (G.pointElement x (by simpa using h.down.down)) P := by
  simp [stalkMap]

omit [HasColimitsOfSize.{v', v'} A] in
/-- Over the identity map, the stalk map is the ordinary fiber functor applied to the
presheaf morphism. -/
@[simp]
theorem stalkMap_id {P Q : Bᵒᵖ ⥤ A} (α : Q ⟶ (ContinuousMap.id G).comapFunctor.op ⋙ P)
    (x : X) : (ContinuousMap.id G).stalkMap α x =
      (G.point ((ContinuousMap.id G) x)).presheafFiber.map α ≫ eqToHom (by simp; rfl) := by
  simp [stalkMap]

/-- Stalk maps of composable morphisms of presheaves over continuous maps compose.
The associator and equality map identify the two presentations of the direct image. -/
@[reassoc]
theorem stalkMap_comp [HasColimitsOfSize.{v'', v''} A]
    (g : G'.ContinuousMap G'') (f : G.ContinuousMap G')
    {P : Bᵒᵖ ⥤ A} {Q : B'ᵒᵖ ⥤ A} {R : B''ᵒᵖ ⥤ A}
    (β : R ⟶ g.comapFunctor.op ⋙ Q) (α : Q ⟶ f.comapFunctor.op ⋙ P) (x : X) :
    (g.comp f).stalkMap
        (β ≫ Functor.whiskerLeft g.comapFunctor.op α ≫
          (Functor.associator g.comapFunctor.op f.comapFunctor.op P).inv ≫
          eqToHom (by rw [comapFunctor_comp]; rfl)) x =
      eqToHom (by simp) ≫ g.stalkMap β (f x) ≫ f.stalkMap α x := by
  ext V h
  rw [G''.toPresheafFiber_congr_assoc (by simp) rfl rfl]
  have hc := G.toPresheafFiber_congr rfl rfl (P := P)
    (U := f.comapFunctor.obj (g.comapFunctor.obj V)) (V := (g.comp f).comapFunctor.obj V)
    (by simp) (G.pointElement x (by simpa using h.down.down))
  simpa [stalkMap] using congrArg
    (fun k ↦ (β.app (op V) ≫ α.app (op (g.comapFunctor.obj V))) ≫ k) hc.symm

section Topological

variable {X₀ Y₀ : TopCat.{v}} {A₀ : Type w} [Category.{v} A₀]
  [HasColimitsOfSize.{v, v} A₀]

/-- For ordinary open covers, direct-image stalk maps agree with the topological ones,
compatibly with the canonical comparison from site fibers to stalks. -/
@[reassoc]
theorem stalkPushforward_topological (f : X₀ ⟶ Y₀) (P : X₀.Presheaf A₀) (x : X₀) :
    (ofContinuousMap f.hom).stalkPushforward P x ≫ (topologicalStalkIso x P).hom =
      eqToHom (by simp [comapFunctor_ofContinuousMap]) ≫
        (topologicalStalkIso (f x) ((TopologicalSpace.Opens.map f).op ⋙ P)).hom ≫
        P.stalkPushforward A₀ f x := by
  ext V h
  rw [(topological Y₀).toPresheafFiber_congr_assoc (by simp)
    (by rw [comapFunctor_ofContinuousMap]; rfl) rfl]
  simp only [toPresheafFiber_stalkPushforward_assoc,
    toPresheafFiber_topologicalStalkIso_hom_assoc]
  -- Mathlib's topological pushforward bundles the same composite presheaf separately.
  erw [TopCat.Presheaf.stalkPushforward_germ]
  have hV : (ofContinuousMap f.hom).comapFunctor.obj V =
      (TopologicalSpace.Opens.map f).obj V := by
    rw [comapFunctor_ofContinuousMap]
    rfl
  simpa using (topological X₀).toPresheafFiber_congr_assoc rfl rfl hV
    ((topological X₀).pointElement x (by simpa using h.down.down))
    (topologicalStalkIso x P).hom

end Topological

end TauCeti.GTopology.ContinuousMap
