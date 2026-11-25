/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Base change of a cofiltered limit

Let `D : I ⥤ C` be a diagram in a category with pullbacks, `i : I`, and `r : Z ⟶ Dᵢ`. The members
`Dⱼ` over `i` base change along `r` to the diagram `D.pullbackOver r : Over i ⥤ C`,
`j ↦ Dⱼ ×_{Dᵢ} Z`, and a cone `c` over `D` base changes to the cone `c.pullbackOver r` with point
`c.pt ×_{Dᵢ} Z`. When `I` is cofiltered, the base change of a limit cone is a limit cone
(`CategoryTheory.Limits.IsLimit.pullbackOver`).

Objectwise, `D.pullbackOver r` is the composite `Over.post D ⋙ Over.pullback r ⋙ Over.forget Z`,
and the limit statement is transported from that composite. It is stated with the objects
`pullback (D.map j.hom) r` and the transition maps `pullback.map` so that the pullback projections
apply to its members directly, with the lemmas `Functor.pullbackOver_map_fst` and
`Functor.pullbackOver_map_snd` describing the transition maps.

For a cone `c` over `D` with point `S`, a morphism `b : X ×_{Dᵢ} Dⱼ ⟶ Y ×_{Dᵢ} Dⱼ` over `Dⱼ` that is
compatible with a morphism `a : X ×_{Dᵢ} S ⟶ Y ×_{Dᵢ} S` over `S` base changes along `S ⟶ Dⱼ` to `a`
up to the canonical isomorphisms, so it shares every property of morphisms respecting isomorphisms
with `a` (`CategoryTheory.MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq`).
The comparison is `Cone.pullbackOverIso`, with the underlying identity recorded in
`Cone.pullbackMap_eq_of_pullbackMap_comp_eq`.

Inheritance of a morphism property can be reduced to the diagram base changed along the target
(`CategoryTheory.MorphismProperty.exists_pullbackMap_of_pullbackOver`). This transport requires
only pullbacks and invariance under precomposition with isomorphisms; the cone need not be limiting
and the diagram need not be cofiltered.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasPullbacks C] {I : Type*} [Category* I] (D : I ⥤ C) {i : I}
  {Z : C} (r : Z ⟶ D.obj i)

/-- The base change `j ↦ Dⱼ ×_{Dᵢ} Z` of the members of `D` over `i` along `r : Z ⟶ Dᵢ`. -/
noncomputable abbrev _root_.CategoryTheory.Functor.pullbackOver : Over i ⥤ C where
  obj j := pullback (D.map j.hom) r
  map {j k} f := pullback.map _ _ _ _ (D.map f.left) (𝟙 Z) (𝟙 _)
    (by simp [← D.map_comp]) (by simp)
  map_id j := by ext <;> simp
  map_comp f g := by ext <;> simp

@[reassoc]
lemma _root_.CategoryTheory.Functor.pullbackOver_map_fst {j k : Over i} (f : j ⟶ k) :
    (D.pullbackOver r).map f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.map f.left := by
  simp [Functor.pullbackOver]

@[reassoc]
lemma _root_.CategoryTheory.Functor.pullbackOver_map_snd {j k : Over i} (f : j ⟶ k) :
    (D.pullbackOver r).map f ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [Functor.pullbackOver]

variable {D}

/-- The base change `c.pt ×_{Dᵢ} Z` of a cone `c` over `D` along `r : Z ⟶ Dᵢ`. -/
noncomputable abbrev Cone.pullbackOver (c : Cone D) : Cone (D.pullbackOver r) where
  pt := pullback (c.π.app i) r
  π :=
    { app j := pullback.map _ _ _ _ (c.π.app j.left) (𝟙 Z) (𝟙 _) (by simp) (by simp)
      naturality j k f := by ext <;> simp [Functor.pullbackOver] }

@[reassoc]
lemma Cone.pullbackOver_π_app_fst (c : Cone D) (j : Over i) :
    (c.pullbackOver r).π.app j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ c.π.app j.left := by
  simp [Cone.pullbackOver]

@[reassoc]
lemma Cone.pullbackOver_π_app_snd (c : Cone D) (j : Over i) :
    (c.pullbackOver r).π.app j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [Cone.pullbackOver]

/-- The base change of a limit cone of a cofiltered diagram is a limit cone. -/
noncomputable def IsLimit.pullbackOver [IsCofilteredOrEmpty I] {c : Cone D}
    (hc : IsLimit c) : IsLimit (c.pullbackOver r) := by
  -- `Over.isLimitConePost` lifts the limit to `Over Dᵢ`, `Over.pullback r` is a right adjoint,
  -- and `Over.forget Z` preserves cofiltered limits; the composite agrees with
  -- `D.pullbackOver r` objectwise.
  let e : Over.post D ⋙ Over.pullback r ⋙ Over.forget Z ≅ D.pullbackOver r :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by ext <;> simp [Functor.pullbackOver]
  exact (IsLimit.postcomposeHomEquiv e _).symm
      (isLimitOfPreserves (Over.pullback r ⋙ Over.forget Z) (Over.isLimitConePost i hc))
    |>.ofIsoLimit (Cone.ext (Iso.refl _) fun j ↦ by
      ext <;> simp [Cone.pullbackOver, e, Over.conePost])

/-- Pulling a stage base change back to the point of a cone agrees with direct base change
along the cone projection. -/
noncomputable def Cone.pullbackOverIso (c : Cone D) {i j : I} (hji : j ⟶ i)
    {Z : C} (s : Z ⟶ D.obj i) :
    pullback (c.π.app j) (pullback.fst (D.map hji) s) ≅ pullback (c.π.app i) s :=
  pullbackRightPullbackFstIso (D.map hji) s (c.π.app j) ≪≫ pullback.congrHom (c.w hji) rfl

/-- The cone base-change comparison commutes with projection to the cone point. -/
@[reassoc (attr := simp)]
lemma Cone.pullbackOverIso_hom_fst (c : Cone D) {i j : I} (hji : j ⟶ i)
    {Z : C} (s : Z ⟶ D.obj i) :
    (c.pullbackOverIso hji s).hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [Cone.pullbackOverIso]

/-- The cone base-change comparison preserves the projection to the source of the base-changed
map. -/
@[reassoc (attr := simp)]
lemma Cone.pullbackOverIso_hom_snd (c : Cone D) {i j : I} (hji : j ⟶ i)
    {Z : C} (s : Z ⟶ D.obj i) :
    (c.pullbackOverIso hji s).hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp [Cone.pullbackOverIso]

/-- The cone base-change comparison followed by the map to the stage is the second projection
of the iterated pullback. -/
@[reassoc (attr := simp)]
lemma Cone.pullbackOverIso_hom_pullbackMap (c : Cone D) {i j : I} (hji : j ⟶ i)
    {Z : C} (s : Z ⟶ D.obj i) :
    (c.pullbackOverIso hji s).hom ≫
        pullback.map (c.π.app i) s (D.map hji) s (c.π.app j) (𝟙 Z) (𝟙 _) (by simp) (by simp) =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

/-- The inverse cone base-change comparison commutes with projection to the cone point. -/
@[reassoc (attr := simp)]
lemma Cone.pullbackOverIso_inv_fst (c : Cone D) {i j : I} (hji : j ⟶ i)
    {Z : C} (s : Z ⟶ D.obj i) :
    (c.pullbackOverIso hji s).inv ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [Cone.pullbackOverIso]

/-- The inverse cone base-change comparison followed by projection to the stage is the cone
projection. -/
@[reassoc (attr := simp)]
lemma Cone.pullbackOverIso_inv_snd_fst (c : Cone D) {i j : I} (hji : j ⟶ i)
    {Z : C} (s : Z ⟶ D.obj i) :
    (c.pullbackOverIso hji s).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ c.π.app j := by
  simp [Cone.pullbackOverIso]

/-- The inverse cone base-change comparison preserves the projection to the source of the
base-changed map. -/
@[reassoc (attr := simp)]
lemma Cone.pullbackOverIso_inv_snd_snd (c : Cone D) {i j : I} (hji : j ⟶ i)
    {Z : C} (s : Z ⟶ D.obj i) :
    (c.pullbackOverIso hji s).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [Cone.pullbackOverIso]

/-- Compatible maps at a stage and at the cone point are conjugate by the canonical
base-change comparisons. -/
theorem Cone.pullbackMap_eq_of_pullbackMap_comp_eq (c : Cone D)
    {i j : I} (hji : j ⟶ i) {X Y : C} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i}
    {a : pullback (c.π.app i) p ⟶ pullback (c.π.app i) q}
    (ha : a ≫ pullback.fst _ _ = pullback.fst _ _)
    {b : pullback (D.map hji) p ⟶ pullback (D.map hji) q}
    (hb₁ : b ≫ pullback.fst _ _ = pullback.fst _ _)
    (hb₂ : pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp) ≫
      b = a ≫ pullback.map (c.π.app i) q (D.map hji) q (c.π.app j) (𝟙 Y) (𝟙 _) (by simp)
        (by simp)) :
    pullback.map (c.π.app j) (pullback.fst (D.map hji) p) (c.π.app j)
      (pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁]) =
      (c.pullbackOverIso hji p).hom ≫ a ≫ (c.pullbackOverIso hji q).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  apply pullback.hom_ext
  · simp [ha]
  · have h := congrArg (· ≫ pullback.snd (D.map hji) q) hb₂
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at h
    have key := c.pullbackOverIso_hom_pullbackMap hji p
    rw [Category.assoc, Category.assoc, ← h, reassoc_of% key]
    simp

end CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C] [HasPullbacks C] {I : Type*} [Category* I] {D : I ⥤ C}
  {c : Cone D}

/-- Transport inheritance of a morphism property from the diagram base changed along the
morphism's target. The property need only be stable under precomposition with isomorphisms.

For `g : X ⟶ Y` over `D.obj i`, suppose the property descends for the second projection in
`D.pullbackOver q`, after identifying its identity stage with `Y`. If the base change of `g` to
the cone point has the property, then so does its base change at some stage of `D`.
The cone need not be limiting, and the indexing category need not be cofiltered. -/
theorem exists_pullbackMap_of_pullbackOver (P : MorphismProperty C)
    [P.RespectsLeft (isomorphisms C)] (c : Cone D)
    {i : I} {X Y : C} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i}
    (g : X ⟶ Y) (hg : g ≫ q = p)
    (h : ∀ (b : (D.pullbackOver q).obj (Over.mk (𝟙 i)) ≅ Y),
      P (pullback.snd (g ≫ b.inv) ((c.pullbackOver q).π.app (Over.mk (𝟙 i)))) →
      ∃ (j : Over i) (a : j ⟶ Over.mk (𝟙 i)),
        P (pullback.snd (g ≫ b.inv) ((D.pullbackOver q).map a)))
    (hP : P (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _)
      (by simp) (by simp [hg]))) :
    ∃ (j : I) (a : j ⟶ i),
      P (pullback.map (D.map a) p (D.map a) q (𝟙 _) g (𝟙 _)
        (by simp) (by simp [hg])) := by
  let m {T : C} (t : T ⟶ D.obj i) :=
    pullback.map t p t q (𝟙 T) g (𝟙 _) (by simp) (by simp [hg])
  have hsq {T : C} (t : T ⟶ D.obj i) :
      IsPullback (m t) (pullback.snd t p) (pullback.snd t q) g := by
    refine IsPullback.of_right ?_ (by simp [m]) (IsPullback.of_hasPullback t q)
    simpa [m, hg] using (IsPullback.of_hasPullback t p)
  have : IsIso (D.map (𝟙 i)) := by rw [D.map_id]; infer_instance
  let b := asIso (pullback.snd (D.map (𝟙 i)) q)
  have hs {T : C} (t : T ⟶ D.obj i)
      (d : pullback t q ⟶ (D.pullbackOver q).obj (Over.mk (𝟙 i)))
      (hd : d ≫ b.hom = pullback.snd t q) :
      IsPullback (pullback.snd t p) (m t) (g ≫ b.inv) d := by
    exact (hsq t).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) b.symm
      (by simp) (by simp) (by simp) (by
        simpa using (congrArg (fun f ↦ f ≫ b.inv) hd).symm)
  have hlim := hs (c.π.app i) ((c.pullbackOver q).π.app (Over.mk (𝟙 i))) (by
    exact c.pullbackOver_π_app_snd q (Over.mk (𝟙 i)))
  obtain ⟨j, a, ha⟩ := h b (by
    rw [← hlim.isoPullback_inv_snd]
    exact RespectsLeft.precomp (Q := isomorphisms C) _ inferInstance _ hP)
  have hstage := hs (D.map j.hom) ((D.pullbackOver q).map a) (by
    exact D.pullbackOver_map_snd q a)
  have hfinal : P (m (D.map j.hom)) := by
    rw [← hstage.isoPullback_hom_snd]
    exact RespectsLeft.precomp (Q := isomorphisms C) _ inferInstance _ ha
  exact ⟨j.left, j.hom, hfinal⟩

/-- Let `c` be a cone over `D` with point `S`, and let `b : X ×_{Dᵢ} Dⱼ ⟶ Y ×_{Dᵢ} Dⱼ` over `Dⱼ`
be compatible with a morphism `a : X ×_{Dᵢ} S ⟶ Y ×_{Dᵢ} S` over `S`. Then the base change of `b`
to `S` is `a` up to the canonical isomorphisms, so it has every property of morphisms respecting
isomorphisms that `a` has. -/
theorem pullbackMap_iff_of_pullbackMap_comp_eq (P : MorphismProperty C) [P.RespectsIso]
    {i j : I} (hji : j ⟶ i) {X Y : C} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i}
    {a : pullback (c.π.app i) p ⟶ pullback (c.π.app i) q}
    (ha : a ≫ pullback.fst _ _ = pullback.fst _ _)
    {b : pullback (D.map hji) p ⟶ pullback (D.map hji) q}
    (hb₁ : b ≫ pullback.fst _ _ = pullback.fst _ _)
    (hb₂ : pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp) ≫
      b = a ≫ pullback.map (c.π.app i) q (D.map hji) q (c.π.app j) (𝟙 Y) (𝟙 _) (by simp)
        (by simp)) :
    P (pullback.map (c.π.app j) (pullback.fst (D.map hji) p) (c.π.app j)
      (pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁])) ↔ P a := by
  rw [c.pullbackMap_eq_of_pullbackMap_comp_eq hji ha hb₁ hb₂,
    P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]

end CategoryTheory.MorphismProperty
