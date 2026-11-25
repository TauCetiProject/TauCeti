/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Comma.WeakPullback
public import TauCeti.Topology.CategoryTheory.Comma
public import TauCeti.Topology.CategoryTheory.Functor.Continuous
public import TauCeti.Topology.CategoryTheory.Functor.IsomorphismClasses
public import TauCeti.Topology.Constructions.Basic

/-!
# Continuous functors and coarse spaces of weak fiber products

This module connects the categorical universal property and base-change equivalences of
`CategoryTheory.Comma L R` with the comma topologies on objects and total arrows:

* `CategoryTheory.Comma.isTopologicallyContinuous_iff` characterizes `IsTopologicallyContinuous` for
  functors into `Comma L R` in terms of the two projections and the structure-arrow map into
  `Quiver.Total T`, yielding `IsTopologicallyContinuous` for `Comma.fst`, `Comma.snd`, `Comma.lift`,
  `Comma.preLeft`, `Comma.preRight`, `Comma.post`, `Comma.mapLeft`, `Comma.mapRight`, and the
  symmetry, identity, associativity, and pasting functors.
* `CategoryTheory.Comma.preLeftHomeomorph`, `CategoryTheory.Comma.isOpenMap_preLeft_obj`, and
  `CategoryTheory.Comma.preLeftIsomorphismClassesHomeomorph` (and their `preRight` duals) prove
  refinement invariance of the coarse space along open surjective fully faithful refinements.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2–3.
-/

public section

open Topology

namespace CategoryTheory.Comma

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

section ContinuousFunctors

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T] {D : Type u₄} [Category.{v₄} D]
  {S : Type u₅} [Category.{v₅} S]
  [TopologicalSpace A] [TopologicalSpace (Quiver.Total A)]
  [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)]
  [TopologicalSpace (Quiver.Total T)]
  [TopologicalSpace D] [TopologicalSpace (Quiver.Total D)]
  [TopologicalSpace (Quiver.Total S)]

/-- The left projection `Comma.fst L R` is continuous on objects and total arrows. -/
@[simp]
theorem isTopologicallyContinuous_fst (L : A ⥤ T) (R : B ⥤ T) :
    (fst L R).IsTopologicallyContinuous :=
  ⟨continuous_left, continuous_homLeft⟩

/-- The right projection `Comma.snd L R` is continuous on objects and total arrows. -/
@[simp]
theorem isTopologicallyContinuous_snd (L : A ⥤ T) (R : B ⥤ T) :
    (snd L R).IsTopologicallyContinuous :=
  ⟨continuous_right, continuous_homRight⟩

/-- A functor `H : D ⥤ Comma L R` out of a category with continuous source and target maps on total
arrows is continuous on objects and total arrows if and only if its two projections are and the
structure arrow of `H.obj d` depends continuously on `d`. -/
theorem isTopologicallyContinuous_iff {L : A ⥤ T} {R : B ⥤ T}
    (hsD : Continuous (Quiver.Total.left : Quiver.Total D → D))
    (htD : Continuous (Quiver.Total.right : Quiver.Total D → D)) (H : D ⥤ Comma L R) :
    H.IsTopologicallyContinuous ↔
      (H ⋙ fst L R).IsTopologicallyContinuous ∧
        (H ⋙ snd L R).IsTopologicallyContinuous ∧
        Continuous fun d : D ↦ (⟨_, _, (H.obj d).hom⟩ : Quiver.Total T) := by
  refine ⟨fun hH ↦ ⟨hH.comp (isTopologicallyContinuous_fst L R),
    hH.comp (isTopologicallyContinuous_snd L R), continuous_totalHom.comp hH.continuous_obj⟩, ?_⟩
  rintro ⟨hl, hr, hhom⟩
  have hobj : Continuous H.obj := continuous_iff.mpr ⟨hl.continuous_obj, hhom, hr.continuous_obj⟩
  exact ⟨hobj, continuous_total_iff.mpr
    ⟨hobj.comp hsD, hobj.comp htD, hl.continuous_mapTotal, hr.continuous_mapTotal⟩⟩

/-- Topological universal property of `Comma.lift`: when `D` has continuous source and target on
total arrows, `Comma.lift F G α` is continuous on objects and total arrows if and only if `F` and
`G` are and `d ↦ α.app d` is continuous into `Quiver.Total T`. -/
theorem isTopologicallyContinuous_lift_iff {L : A ⥤ T} {R : B ⥤ T}
    (hsD : Continuous (Quiver.Total.left : Quiver.Total D → D))
    (htD : Continuous (Quiver.Total.right : Quiver.Total D → D))
    (F : D ⥤ A) (G : D ⥤ B) (α : F ⋙ L ⟶ G ⋙ R) :
    (Comma.lift F G α).IsTopologicallyContinuous ↔
      F.IsTopologicallyContinuous ∧ G.IsTopologicallyContinuous ∧
        Continuous fun d : D ↦ (⟨_, _, α.app d⟩ : Quiver.Total T) :=
  isTopologicallyContinuous_iff hsD htD (Comma.lift F G α)

/-- Precomposing the left leg with a continuous functor `F : D ⥤ A` induces a continuous functor
`Comma (F ⋙ L) R ⥤ Comma L R`, with no hypotheses on `L`, `R`, or `T`. -/
theorem isTopologicallyContinuous_preLeft {F : D ⥤ A} (hF : F.IsTopologicallyContinuous)
    (L : A ⥤ T) (R : B ⥤ T) : (preLeft F L R).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨(isTopologicallyContinuous_fst _ _).comp hF, isTopologicallyContinuous_snd _ _,
      continuous_totalHom⟩

/-- Precomposing the right leg with a continuous functor `F : D ⥤ B` induces a continuous functor
`Comma L (F ⋙ R) ⥤ Comma L R`, with no hypotheses on `L`, `R`, or `T`. -/
theorem isTopologicallyContinuous_preRight (L : A ⥤ T) {F : D ⥤ B}
    (hF : F.IsTopologicallyContinuous) (R : B ⥤ T) :
    (preRight L F R).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨isTopologicallyContinuous_fst _ _, (isTopologicallyContinuous_snd _ _).comp hF,
      continuous_totalHom⟩

/-- Postcomposing both legs with a functor `F : T ⥤ S` continuous on total arrows induces a
continuous functor `Comma L R ⥤ Comma (L ⋙ F) (R ⋙ F)`. -/
theorem isTopologicallyContinuous_post (L : A ⥤ T) (R : B ⥤ T) {F : T ⥤ S}
    (hF : Continuous F.toPrefunctor.mapTotal) : (post L R F).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨isTopologicallyContinuous_fst _ _, isTopologicallyContinuous_snd _ _,
      hF.comp continuous_totalHom⟩

/-- Whiskering on the left by a natural transformation `l : L₁ ⟶ L₂` with continuous components in
`Quiver.Total T` induces a continuous functor `Comma L₂ R ⥤ Comma L₁ R` when composition in `T` is
continuous. -/
theorem isTopologicallyContinuous_mapLeft {L₁ L₂ : A ⥤ T} (R : B ⥤ T) (l : L₁ ⟶ L₂)
    (hl : Continuous fun a : A ↦ (⟨_, _, l.app a⟩ : Quiver.Total T))
    (hcompT : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      p.val.1.comp p.val.2 p.property) :
    (mapLeft R l).IsTopologicallyContinuous := by
  refine (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨isTopologicallyContinuous_fst _ _, isTopologicallyContinuous_snd _ _, ?_⟩
  convert hcompT.comp
    (((hl.comp continuous_left).prodMk continuous_totalHom).subtype_mk fun _ ↦ rfl) using 1
  funext X; simp [Quiver.Total.comp_def]

/-- Whiskering on the right by a natural transformation `r : R₁ ⟶ R₂` with continuous components in
`Quiver.Total T` induces a continuous functor `Comma L R₁ ⥤ Comma L R₂` when composition in `T` is
continuous. -/
theorem isTopologicallyContinuous_mapRight (L : A ⥤ T) {R₁ R₂ : B ⥤ T} (r : R₁ ⟶ R₂)
    (hr : Continuous fun b : B ↦ (⟨_, _, r.app b⟩ : Quiver.Total T))
    (hcompT : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      p.val.1.comp p.val.2 p.property) :
    (mapRight L r).IsTopologicallyContinuous := by
  refine (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨isTopologicallyContinuous_fst _ _, isTopologicallyContinuous_snd _ _, ?_⟩
  convert hcompT.comp
    ((continuous_totalHom.prodMk (hr.comp continuous_right)).subtype_mk fun _ ↦ rfl) using 1
  funext X; simp [Quiver.Total.comp_def]

/-- Over a groupoid `T` with continuous inversion on total arrows, `Comma.flipFunctor L R` is
continuous on objects and total arrows. -/
theorem isTopologicallyContinuous_flipFunctor (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid T]
    (hinvT : Continuous fun f : Quiver.Total T ↦ (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total T)) :
    (flipFunctor L R).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨isTopologicallyContinuous_snd L R, isTopologicallyContinuous_fst L R,
      hinvT.comp continuous_totalHom⟩

/-- The canonical section `Comma.fromRight R : B ⥤ Comma (𝟭 T) R` is continuous on objects and
total arrows when `B` has continuous source and target, `R` is continuous, and `T` has continuous
units. -/
theorem isTopologicallyContinuous_fromRight [TopologicalSpace T] {R : B ⥤ T}
    (hsB : Continuous (Quiver.Total.left : Quiver.Total B → B))
    (htB : Continuous (Quiver.Total.right : Quiver.Total B → B))
    (hR : R.IsTopologicallyContinuous)
    (huT : Continuous fun t : T ↦ (⟨t, t, 𝟙 t⟩ : Quiver.Total T)) :
    (fromRight R).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff hsB htB _).mpr
    ⟨hR, Functor.isTopologicallyContinuous_id, huT.comp hR.continuous_obj⟩

/-- The canonical section `Comma.fromLeft L : A ⥤ Comma L (𝟭 T)` is continuous on objects and total
arrows when `A` has continuous source and target, `L` is continuous, and `T` has continuous
units. -/
theorem isTopologicallyContinuous_fromLeft [TopologicalSpace T] {L : A ⥤ T}
    (hsA : Continuous (Quiver.Total.left : Quiver.Total A → A))
    (htA : Continuous (Quiver.Total.right : Quiver.Total A → A))
    (hL : L.IsTopologicallyContinuous)
    (huT : Continuous fun t : T ↦ (⟨t, t, 𝟙 t⟩ : Quiver.Total T)) :
    (fromLeft L).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff hsA htA _).mpr
    ⟨Functor.isTopologicallyContinuous_id, hL, huT.comp hL.continuous_obj⟩

/-- Reassociating an iterated comma category via `Comma.assocFunctor` is continuous on objects and
total arrows, with no hypotheses on the functors or target categories. -/
theorem isTopologicallyContinuous_assocFunctor (L : A ⥤ T) (F : B ⥤ T) (G : B ⥤ S) (M : D ⥤ S) :
    (assocFunctor L F G M).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨(isTopologicallyContinuous_fst _ _).comp (isTopologicallyContinuous_fst L F),
      (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
        ⟨(isTopologicallyContinuous_fst _ _).comp (isTopologicallyContinuous_snd L F),
          isTopologicallyContinuous_snd _ _, continuous_totalHom⟩,
      (continuous_totalHom (L := L) (R := F)).comp continuous_left⟩

/-- Inverse reassociation `Comma.assocInverse` is continuous on objects and total arrows, with no
hypotheses on the functors or target categories. -/
theorem isTopologicallyContinuous_assocInverse (L : A ⥤ T) (F : B ⥤ T) (G : B ⥤ S) (M : D ⥤ S) :
    (assocInverse L F G M).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨(isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
        ⟨isTopologicallyContinuous_fst _ _,
          (isTopologicallyContinuous_snd _ _).comp (isTopologicallyContinuous_fst G M),
          continuous_totalHom⟩,
      (isTopologicallyContinuous_snd _ _).comp (isTopologicallyContinuous_snd G M),
      (continuous_totalHom (L := G) (R := M)).comp continuous_right⟩

/-- Right pasting `Comma.pastingRightFunctor L R M` is continuous on objects and total arrows when
`R` is continuous on total arrows and composition in `T` is continuous. -/
theorem isTopologicallyContinuous_pastingRightFunctor (L : A ⥤ T) {R : B ⥤ T} (M : D ⥤ B)
    (hR : Continuous R.toPrefunctor.mapTotal)
    (hcompT : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      p.val.1.comp p.val.2 p.property) :
    (pastingRightFunctor L R M).IsTopologicallyContinuous := by
  refine (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨(isTopologicallyContinuous_fst _ _).comp (isTopologicallyContinuous_fst L R),
      isTopologicallyContinuous_snd _ _, ?_⟩
  convert hcompT.comp
    ((((continuous_totalHom (L := L) (R := R)).comp continuous_left).prodMk
      (hR.comp (continuous_totalHom (L := snd L R) (R := M)))).subtype_mk fun _ ↦ rfl) using 1
  funext P; simp [Quiver.Total.comp_def]

/-- The right-pasting section `Comma.pastingRightInverse L R M` is continuous on objects and total
arrows when `M` is continuous and `B` has continuous units. -/
theorem isTopologicallyContinuous_pastingRightInverse (L : A ⥤ T) (R : B ⥤ T) {M : D ⥤ B}
    (hM : M.IsTopologicallyContinuous)
    (huB : Continuous fun b : B ↦ (⟨b, b, 𝟙 b⟩ : Quiver.Total B)) :
    (pastingRightInverse L R M).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨(isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
        ⟨isTopologicallyContinuous_fst _ _, (isTopologicallyContinuous_snd _ _).comp hM,
          continuous_totalHom⟩,
      isTopologicallyContinuous_snd _ _, huB.comp (hM.continuous_obj.comp continuous_right)⟩

/-- Left pasting `Comma.pastingLeftFunctor N L R` is continuous on objects and total arrows when `L`
is continuous on total arrows and composition in `T` is continuous. -/
theorem isTopologicallyContinuous_pastingLeftFunctor (N : D ⥤ A) {L : A ⥤ T} (R : B ⥤ T)
    (hL : Continuous L.toPrefunctor.mapTotal)
    (hcompT : Continuous fun p : {p : Quiver.Total T × Quiver.Total T // p.1.right = p.2.left} ↦
      p.val.1.comp p.val.2 p.property) :
    (pastingLeftFunctor N L R).IsTopologicallyContinuous := by
  refine (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨isTopologicallyContinuous_fst _ _,
      (isTopologicallyContinuous_snd _ _).comp (isTopologicallyContinuous_snd L R), ?_⟩
  convert hcompT.comp
    (((hL.comp (continuous_totalHom (L := N) (R := fst L R))).prodMk
      ((continuous_totalHom (L := L) (R := R)).comp continuous_right)).subtype_mk
      fun _ ↦ rfl) using 1
  funext P; simp [Quiver.Total.comp_def]

/-- The left-pasting section `Comma.pastingLeftInverse N L R` is continuous on objects and total
arrows when `N` is continuous and `A` has continuous units. -/
theorem isTopologicallyContinuous_pastingLeftInverse {N : D ⥤ A} (L : A ⥤ T) (R : B ⥤ T)
    (hN : N.IsTopologicallyContinuous)
    (huA : Continuous fun a : A ↦ (⟨a, a, 𝟙 a⟩ : Quiver.Total A)) :
    (pastingLeftInverse N L R).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
    ⟨isTopologicallyContinuous_fst _ _,
      (isTopologicallyContinuous_iff continuous_source continuous_target _).mpr
        ⟨(isTopologicallyContinuous_fst _ _).comp hN, isTopologicallyContinuous_snd _ _,
          continuous_totalHom⟩,
      huA.comp (hN.continuous_obj.comp continuous_left)⟩

end ContinuousFunctors

section CoarseSpace

variable {A' : Type u₁} [Category.{v₁} A'] {A : Type u₁} [Category.{v₁} A]
  {B' : Type u₂} [Category.{v₂} B'] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T]

/-- Surjectivity of `F.obj` lifts to `(Comma.preLeft F L R).obj`. -/
theorem surjective_preLeft_obj {C : Type u₄} [Category.{v₄} C]
    (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) (hFs : Function.Surjective F.obj) :
    Function.Surjective (preLeft F L R).obj := by
  rintro ⟨a, b, h⟩; obtain ⟨c, rfl⟩ := hFs a; exact ⟨⟨c, b, h⟩, rfl⟩

/-- Surjectivity of `F.obj` lifts to `(Comma.preRight L F R).obj`. -/
theorem surjective_preRight_obj {C : Type u₄} [Category.{v₄} C]
    (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) (hFs : Function.Surjective F.obj) :
    Function.Surjective (preRight L F R).obj := by
  rintro ⟨a, b, h⟩; obtain ⟨c, rfl⟩ := hFs b; exact ⟨⟨a, c, h⟩, rfl⟩

variable [TopologicalSpace A'] [TopologicalSpace A]
  [TopologicalSpace B'] [TopologicalSpace B]
  [TopologicalSpace (Quiver.Total T)]

/-- Precomposing the left leg with `F : C ⥤ A` identifies `Comma (F ⋙ L) R` homeomorphically with
the topological pullback of `F.obj : C → A` along `Comma.left : Comma L R → A`, assuming only that
`F.obj` is continuous. -/
def preLeftHomeomorph {C : Type u₄} [Category.{v₄} C] [TopologicalSpace C]
    (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) (hF : Continuous F.obj) :
    Comma (F ⋙ L) R ≃ₜ {q : C × Comma L R // F.obj q.1 = q.2.left} where
  toFun X := ⟨(X.left, (preLeft F L R).obj X), rfl⟩
  invFun q := ⟨q.val.1, q.val.2.right, eqToHom (congrArg L.obj q.property) ≫ q.val.2.hom⟩
  left_inv X := by cases X; simp
  right_inv := by rintro ⟨⟨c, ⟨a, b, h⟩⟩, hq⟩; dsimp only at hq; subst hq; simp [preLeft]
  continuous_toFun :=
    ((continuous_left (L := F ⋙ L) (R := R)).prodMk
      ((continuous_iff (L := L) (R := R)).mpr
        ⟨hF.comp (continuous_left (L := F ⋙ L) (R := R)),
          by convert continuous_totalHom (L := F ⋙ L) (R := R) using 1; rfl,
          continuous_right (L := F ⋙ L) (R := R)⟩)).subtype_mk fun _ ↦ rfl
  continuous_invFun := by
    refine (continuous_iff (L := F ⋙ L) (R := R)).mpr
      ⟨continuous_fst.comp continuous_subtypeVal, ?_,
        (continuous_right (L := L) (R := R)).comp (continuous_snd.comp continuous_subtypeVal)⟩
    convert (continuous_totalHom (L := L) (R := R)).comp
      (continuous_snd.comp continuous_subtypeVal) using 1
    funext ⟨⟨c, ⟨a, b, h⟩⟩, hq⟩; dsimp only at hq; subst hq; simp

@[simp]
theorem preLeftHomeomorph_apply_coe {C : Type u₄} [Category.{v₄} C] [TopologicalSpace C]
    (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) (hF : Continuous F.obj) (X : Comma (F ⋙ L) R) :
    (preLeftHomeomorph F L R hF X : C × Comma L R) = (X.left, (preLeft F L R).obj X) := (rfl)

/-- Precomposing the right leg with `F : C ⥤ B` identifies `Comma L (F ⋙ R)` homeomorphically with
the topological pullback of `F.obj : C → B` along `Comma.right : Comma L R → B`, assuming only that
`F.obj` is continuous. -/
def preRightHomeomorph {C : Type u₄} [Category.{v₄} C] [TopologicalSpace C]
    (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) (hF : Continuous F.obj) :
    Comma L (F ⋙ R) ≃ₜ {q : C × Comma L R // F.obj q.1 = q.2.right} where
  toFun X := ⟨(X.right, (preRight L F R).obj X), rfl⟩
  invFun q := ⟨q.val.2.left, q.val.1, q.val.2.hom ≫ eqToHom (congrArg R.obj q.property.symm)⟩
  left_inv X := by cases X; simp
  right_inv := by rintro ⟨⟨c, ⟨a, b, h⟩⟩, hq⟩; dsimp only at hq; subst hq; simp [preRight]
  continuous_toFun :=
    ((continuous_right (L := L) (R := F ⋙ R)).prodMk
      ((continuous_iff (L := L) (R := R)).mpr
        ⟨continuous_left (L := L) (R := F ⋙ R),
          by convert continuous_totalHom (L := L) (R := F ⋙ R) using 1; rfl,
          hF.comp (continuous_right (L := L) (R := F ⋙ R))⟩)).subtype_mk fun _ ↦ rfl
  continuous_invFun := by
    refine (continuous_iff (L := L) (R := F ⋙ R)).mpr
      ⟨(continuous_left (L := L) (R := R)).comp (continuous_snd.comp continuous_subtypeVal),
        ?_, continuous_fst.comp continuous_subtypeVal⟩
    convert (continuous_totalHom (L := L) (R := R)).comp
      (continuous_snd.comp continuous_subtypeVal) using 1
    funext ⟨⟨c, ⟨a, b, h⟩⟩, hq⟩; dsimp only at hq; subst hq; simp

@[simp]
theorem preRightHomeomorph_apply_coe {C : Type u₄} [Category.{v₄} C] [TopologicalSpace C]
    (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) (hF : Continuous F.obj) (X : Comma L (F ⋙ R)) :
    (preRightHomeomorph L F R hF X : C × Comma L R) = (X.right, (preRight L F R).obj X) := (rfl)

/-- If `F.obj` is an open map, then `(Comma.preLeft F L R).obj` is an open map, with no continuity
hypothesis on `F.obj` and no hypotheses on `L`, `R`, or `T`. -/
theorem isOpenMap_preLeft_obj {C : Type u₄} [Category.{v₄} C] [TopologicalSpace C]
    (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) (hFo : IsOpenMap F.obj) :
    IsOpenMap (preLeft F L R).obj := by
  intro U hU
  obtain ⟨W, hW, rfl⟩ := isEmbedding_left_totalHom_right.isInducing.isOpen_iff.mp hU
  have hEq : (preLeft F L R).obj '' ((fun Z : Comma (F ⋙ L) R ↦
      (Z.left, (⟨_, _, Z.hom⟩ : Quiver.Total T), Z.right)) ⁻¹' W) =
      (fun Y : Comma L R ↦ (Y.left, (⟨_, _, Y.hom⟩ : Quiver.Total T), Y.right)) ⁻¹'
        (_root_.Prod.map F.obj id '' W) := by
    ext Y; refine ⟨fun ⟨X, hXW, hXY⟩ ↦ hXY ▸ ⟨(X.left, ⟨_, _, X.hom⟩, X.right), hXW, rfl⟩, ?_⟩
    rcases Y with ⟨a, bY, h⟩
    rintro ⟨⟨c, t, b⟩, hcW, hct⟩
    simp only [_root_.Prod.map_apply, id_eq, _root_.Prod.mk.injEq] at hct
    obtain ⟨rfl, rfl, rfl⟩ := hct
    exact ⟨⟨c, b, h⟩, hcW, rfl⟩
  rw [hEq]
  exact (hFo.prodMap IsOpenMap.id W hW).preimage
    (continuous_left.prodMk (continuous_totalHom.prodMk continuous_right))

/-- If `F.obj` is an open map, then `(Comma.preRight L F R).obj` is an open map, with no continuity
hypothesis on `F.obj` and no hypotheses on `L`, `R`, or `T`. -/
theorem isOpenMap_preRight_obj {C : Type u₄} [Category.{v₄} C] [TopologicalSpace C]
    (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) (hFo : IsOpenMap F.obj) :
    IsOpenMap (preRight L F R).obj := by
  intro U hU
  obtain ⟨W, hW, rfl⟩ := isEmbedding_left_totalHom_right.isInducing.isOpen_iff.mp hU
  have hEq : (preRight L F R).obj '' ((fun Z : Comma L (F ⋙ R) ↦
      (Z.left, (⟨_, _, Z.hom⟩ : Quiver.Total T), Z.right)) ⁻¹' W) =
      (fun Y : Comma L R ↦ (Y.left, (⟨_, _, Y.hom⟩ : Quiver.Total T), Y.right)) ⁻¹'
        (_root_.Prod.map id (_root_.Prod.map id F.obj) '' W) := by
    ext Y; refine ⟨fun ⟨X, hXW, hXY⟩ ↦ hXY ▸ ⟨(X.left, ⟨_, _, X.hom⟩, X.right), hXW, rfl⟩, ?_⟩
    rcases Y with ⟨aY, b, h⟩
    rintro ⟨⟨a, t, c⟩, hcW, hct⟩
    simp only [_root_.Prod.map_apply, id_eq, _root_.Prod.mk.injEq] at hct
    obtain ⟨rfl, rfl, rfl⟩ := hct
    exact ⟨⟨a, c, h⟩, hcW, rfl⟩
  rw [hEq]
  exact (IsOpenMap.id.prodMap (IsOpenMap.id.prodMap hFo) W hW).preimage
    (continuous_left.prodMk (continuous_totalHom.prodMk continuous_right))

/-- Left refinement invariance of coarse spaces: a fully faithful refinement `F₁ : A' ⥤ A` with
continuous, open, surjective object map induces a homeomorphism between the coarse spaces of
`Comma (F₁ ⋙ L) R` and `Comma L R`, with no hypotheses on `L`, `R`, or `T`. -/
noncomputable def preLeftIsomorphismClassesHomeomorph (F₁ : A' ⥤ A) [F₁.Full] [F₁.Faithful]
    (L : A ⥤ T) (R : B ⥤ T) (hF₁ : Continuous F₁.obj) (hF₁o : IsOpenMap F₁.obj)
    (hF₁s : Function.Surjective F₁.obj) :
    Quotient (isIsomorphicSetoid (Comma (F₁ ⋙ L) R)) ≃ₜ
      Quotient (isIsomorphicSetoid (Comma L R)) :=
  (preLeft F₁ L R).isomorphismClassesHomeomorph <|
    (isOpenMap_preLeft_obj F₁ L R hF₁o).isQuotientMap
      ((continuous_iff (L := L) (R := R)).mpr
        ⟨hF₁.comp continuous_left, continuous_totalHom, continuous_right⟩)
      (surjective_preLeft_obj F₁ L R hF₁s)

@[simp]
theorem preLeftIsomorphismClassesHomeomorph_apply_mk (F₁ : A' ⥤ A) [F₁.Full] [F₁.Faithful]
    (L : A ⥤ T) (R : B ⥤ T) (hF₁ : Continuous F₁.obj) (hF₁o : IsOpenMap F₁.obj)
    (hF₁s : Function.Surjective F₁.obj) (X : Comma (F₁ ⋙ L) R) :
    preLeftIsomorphismClassesHomeomorph F₁ L R hF₁ hF₁o hF₁s (Quotient.mk _ X) =
      Quotient.mk _ ((preLeft F₁ L R).obj X) := by
  simp [preLeftIsomorphismClassesHomeomorph]

/-- Right refinement invariance of coarse spaces: a fully faithful refinement `F₂ : B' ⥤ B` with
continuous, open, surjective object map induces a homeomorphism between the coarse spaces of
`Comma L (F₂ ⋙ R)` and `Comma L R`, with no hypotheses on `L`, `R`, or `T`. -/
noncomputable def preRightIsomorphismClassesHomeomorph (L : A ⥤ T) (F₂ : B' ⥤ B)
    [F₂.Full] [F₂.Faithful] (R : B ⥤ T) (hF₂ : Continuous F₂.obj) (hF₂o : IsOpenMap F₂.obj)
    (hF₂s : Function.Surjective F₂.obj) :
    Quotient (isIsomorphicSetoid (Comma L (F₂ ⋙ R))) ≃ₜ
      Quotient (isIsomorphicSetoid (Comma L R)) :=
  (preRight L F₂ R).isomorphismClassesHomeomorph <|
    (isOpenMap_preRight_obj L F₂ R hF₂o).isQuotientMap
      ((continuous_iff (L := L) (R := R)).mpr
        ⟨continuous_left, continuous_totalHom, hF₂.comp continuous_right⟩)
      (surjective_preRight_obj L F₂ R hF₂s)

@[simp]
theorem preRightIsomorphismClassesHomeomorph_apply_mk (L : A ⥤ T) (F₂ : B' ⥤ B)
    [F₂.Full] [F₂.Faithful] (R : B ⥤ T) (hF₂ : Continuous F₂.obj) (hF₂o : IsOpenMap F₂.obj)
    (hF₂s : Function.Surjective F₂.obj) (X : Comma L (F₂ ⋙ R)) :
    preRightIsomorphismClassesHomeomorph L F₂ R hF₂ hF₂o hF₂s (Quotient.mk _ X) =
      Quotient.mk _ ((preRight L F₂ R).obj X) := by
  simp [preRightIsomorphismClassesHomeomorph]

end CoarseSpace

end CategoryTheory.Comma
