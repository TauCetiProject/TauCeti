/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
import TauCeti.Data.Fin.Basic

/-!
# Faces and coordinate projections of algebraic cubes

Use affine coordinates on the cube: the coordinate `t / (t - 1)` on `ℙ¹ \ {1}` sends
its zero and infinity faces to `0` and `1`, respectively. In these coordinates a face
inserts a constant, while a degeneracy on cycles comes from the projection forgetting
one coordinate. We construct the scheme maps, the cubical identities, and the pullback
that exhibits a coordinate projection as a relative affine line.

The cube and its indexing conventions in the cycle construction are described in
Burgos Gil and Feliu, *Higher arithmetic Chow groups*, arXiv:0907.5169v1, §§1.6, 2.1.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AffineSpace

universe u

variable {n : ℕ} {S T : Scheme.{u}}

/-- The face of the affine cube obtained by inserting the base section `a` into coordinate `i`.
The cubical zero and infinity faces are obtained by taking `a = 0` and `a = 1`. -/
def cubeFace (S : Scheme.{u}) (i : Fin (n + 1)) (a : Γ(S, ⊤)) :
    𝔸(ULift.{u} (Fin n); S) ⟶ 𝔸(ULift.{u} (Fin (n + 1)); S) :=
  homOfVector (𝔸(ULift.{u} (Fin n); S) ↘ S) fun j ↦
    i.insertNth (α := fun _ ↦ Γ(𝔸(ULift.{u} (Fin n); S), ⊤))
      ((𝔸(ULift.{u} (Fin n); S) ↘ S).appTop a) (fun k ↦ coord S (ULift.up k)) j.down

/-- The projection underlying the `i`-th cubical degeneracy deletes coordinate `i`. -/
def cubeForget (S : Scheme.{u}) (i : Fin (n + 1)) :
    𝔸(ULift.{u} (Fin (n + 1)); S) ⟶ 𝔸(ULift.{u} (Fin n); S) :=
  reindex (ULift.up ∘ i.succAbove ∘ ULift.down) S

/-- The cubical projection is reindexing along the order-preserving inclusion omitting `i`. -/
lemma cubeForget_def (i : Fin (n + 1)) :
    cubeForget S i = reindex (ULift.up ∘ i.succAbove ∘ ULift.down) S :=
  (rfl)

/-- The coordinate formula defining a face via the universal property of affine space. -/
lemma cubeFace_def (i : Fin (n + 1)) (a : Γ(S, ⊤)) :
    cubeFace S i a = homOfVector (𝔸(ULift.{u} (Fin n); S) ↘ S) (fun j ↦
      i.insertNth (α := fun _ ↦ Γ(𝔸(ULift.{u} (Fin n); S), ⊤))
        ((𝔸(ULift.{u} (Fin n); S) ↘ S).appTop a) (fun k ↦ coord S (ULift.up k)) j.down) :=
  (rfl)

instance (i : Fin (n + 1)) (a : Γ(S, ⊤)) : (cubeFace S i a).IsOver S where
  comp_over := homOfVector_over _ _

instance (i : Fin (n + 1)) : (cubeForget S i).IsOver S where
  comp_over := reindex_over _ _

/-- The inserted coordinate is pulled back from the base. -/
@[simp]
lemma cubeFace_appTop_coord_self (i : Fin (n + 1)) (a : Γ(S, ⊤)) :
    (cubeFace S i a).appTop (coord S (ULift.up i)) = (𝔸(ULift.{u} (Fin n); S) ↘ S).appTop a := by
  simp [cubeFace]

/-- Every coordinate other than the inserted one is pulled back to its original position. -/
@[simp]
lemma cubeFace_appTop_coord_succAbove (i : Fin (n + 1)) (a : Γ(S, ⊤)) (j : Fin n) :
    (cubeFace S i a).appTop (coord S (ULift.up (i.succAbove j))) = coord S (ULift.up j) := by
  simp [cubeFace]

/-- The pullback of a coordinate along the cubical projection is the corresponding undeleted
coordinate. -/
@[simp]
lemma cubeForget_appTop_coord (i : Fin (n + 1)) (j : ULift.{u} (Fin n)) :
    (cubeForget S i).appTop (coord S j) = coord S (ULift.up (i.succAbove j.down)) :=
  reindex_appTop_coord _ _ _

/-- Postcomposing with a cube face inserts the corresponding base section into the tuple of
pulled-back coordinates. -/
lemma comp_cubeFace_appTop_coord (i : Fin (n + 1)) (a : Γ(S, ⊤)) {X : Scheme.{u}}
    (f : X ⟶ 𝔸(ULift.{u} (Fin n); S)) (j : ULift.{u} (Fin (n + 1))) :
    (f ≫ cubeFace S i a).appTop (coord S j) =
      i.insertNth (α := fun _ ↦ Γ(X, ⊤)) ((f ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S).appTop a)
        (fun k ↦ f.appTop (coord S (ULift.up k))) j.down := by
  obtain ⟨j⟩ := j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp only [Fin.insertNth_apply_same, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      cubeFace_appTop_coord_self]
  · simp only [Fin.insertNth_apply_succAbove, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      cubeFace_appTop_coord_succAbove]

/-- Inserting a coordinate and forgetting that same coordinate gives the identity. -/
@[reassoc (attr := simp)]
lemma cubeFace_cubeForget (i : Fin (n + 1)) (a : Γ(S, ⊤)) :
    cubeFace S i a ≫ cubeForget S i = 𝟙 𝔸(ULift.{u} (Fin n); S) := by
  apply hom_ext (by simp)
  intro j
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cubeForget_appTop_coord,
    cubeFace_appTop_coord_succAbove, Scheme.Hom.id_appTop]
  rfl

/-- Inserting two face coordinates is independent of the order, with the indices adjusted. -/
@[reassoc]
lemma cubeFace_cubeFace (i : Fin (n + 2)) (j : Fin (n + 1)) (a b : Γ(S, ⊤)) :
    cubeFace S j b ≫ cubeFace S i a =
      cubeFace S (j.predAbove i) a ≫ cubeFace S (i.succAbove j) b := by
  apply hom_ext (by simp)
  intro k
  simp only [comp_cubeFace_appTop_coord, comp_over]
  have h (l : Fin (n + 1)) (c : Γ(S, ⊤)) :
      (fun r : Fin (n + 1) ↦ (cubeFace S l c).appTop (coord S (ULift.up r))) =
        l.insertNth ((𝔸(ULift.{u} (Fin n); S) ↘ S).appTop c) (fun r ↦ coord S (ULift.up r)) := by
    apply Fin.eq_insertNth_iff.mpr
    exact ⟨by simp, by funext r; simp [Fin.removeNth]⟩
  rw [h, h, Fin.insertNth_insertNth]

/-- Deleting two cubical coordinates is independent of the order, with the indices adjusted. -/
@[reassoc]
lemma cubeForget_cubeForget (i : Fin (n + 2)) (j : Fin (n + 1)) :
    cubeForget S i ≫ cubeForget S j =
      cubeForget S (i.succAbove j) ≫ cubeForget S (j.predAbove i) := by
  apply hom_ext (by simp)
  intro k
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cubeForget_appTop_coord,
    Fin.succAbove_succAbove_succAbove_predAbove]

/-- Inserting a face and deleting a different coordinate commute after reindexing. -/
@[reassoc]
lemma cubeFace_cubeForget_succAbove (i : Fin (n + 2)) (j : Fin (n + 1)) (a : Γ(S, ⊤)) :
    cubeFace S (i.succAbove j) a ≫ cubeForget S i =
      cubeForget S (j.predAbove i) ≫ cubeFace S j a := by
  apply hom_ext (by simp)
  rintro ⟨k⟩
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k, rfl⟩
  · simp only [comp_cubeFace_appTop_coord, Fin.insertNth_apply_same, comp_over]
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cubeForget_appTop_coord, ULift.down_up,
      cubeFace_appTop_coord_self]
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cubeForget_appTop_coord,
      ← Fin.succAbove_succAbove_succAbove_predAbove i j k, cubeFace_appTop_coord_succAbove]

/-- Cube faces commute with change of base, with the inserted section pulled back to the new
base. In particular this applies to insertion at `0` and `1`. -/
@[reassoc]
lemma map_cubeFace (i : Fin (n + 1)) (a : Γ(T, ⊤)) (f : S ⟶ T) :
    map (ULift.{u} (Fin n)) f ≫ cubeFace T i a =
      cubeFace S i (f.appTop a) ≫ map (ULift.{u} (Fin (n + 1))) f := by
  apply hom_ext (by simp)
  rintro ⟨k⟩
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨k, rfl⟩
  · rw [comp_cubeFace_appTop_coord, Fin.insertNth_apply_same, map_over]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_appTop_coord,
      cubeFace_appTop_coord_self]
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_appTop_coord,
      cubeFace_appTop_coord_succAbove]

/-- Keeping all but coordinate `i` and keeping just `i` exhibits the cube as a product over `S`
with an affine line. -/
lemma isPullback_cubeForget (i : Fin (n + 1)) :
    IsPullback (cubeForget S i) (reindex (fun _ : ULift.{u} (Fin 1) ↦ ULift.up i) S)
      (𝔸(ULift.{u} (Fin n); S) ↘ S) (𝔸(ULift.{u} (Fin 1); S) ↘ S) := by
  let p := reindex (fun _ : ULift.{u} (Fin 1) ↦ ULift.up i) S
  have hw : cubeForget S i ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S = p ≫ 𝔸(ULift.{u} (Fin 1); S) ↘ S := by
    simp [p]
  refine IsPullback.of_isLimit (c := PullbackCone.mk (cubeForget S i) p hw) ?_
  refine PullbackCone.IsLimit.mk hw (fun s ↦ homOfVector (s.fst ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S)
    (fun j ↦ i.insertNth (α := fun _ ↦ Γ(s.pt, ⊤))
      (s.snd.appTop (coord S (ULift.up (0 : Fin 1))))
      (fun k ↦ s.fst.appTop (coord S (ULift.up k))) j.down)) ?_ ?_ ?_
  · intro s
    apply hom_ext (by simp)
    intro j
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cubeForget_appTop_coord,
      homOfVector_appTop_coord, Fin.insertNth_apply_succAbove]
  · intro s
    apply hom_ext (by simpa [p] using s.condition)
    intro j
    have hj : j = ULift.up 0 := Subsingleton.elim _ _
    subst j
    simp only [p, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
      homOfVector_appTop_coord, Fin.insertNth_apply_same]
  · intro s m hf hg
    apply hom_ext
    · rw [homOfVector_over, ← hf, Category.assoc, comp_over (f := cubeForget S i)]
    · rintro ⟨j⟩
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
      · simpa only [p, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
          homOfVector_appTop_coord, ULift.down_up, Fin.insertNth_apply_same] using
          congrArg (fun g ↦ g.appTop (coord S (ULift.up (0 : Fin 1)))) hg
      · simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cubeForget_appTop_coord,
          homOfVector_appTop_coord, ULift.down_up, Fin.insertNth_apply_succAbove] using
          congrArg (fun g ↦ g.appTop (coord S (ULift.up j))) hf

/-- A cubical coordinate projection is smooth of relative dimension one. -/
instance (i : Fin (n + 1)) : SmoothOfRelativeDimension 1 (cubeForget S i) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_cubeForget (S := S) i).flip
    (smoothOfRelativeDimension_fin 1)

instance (i : Fin (n + 1)) : Smooth (cubeForget S i) :=
  SmoothOfRelativeDimension.smooth 1 _

/-- A cube face is a closed immersion: it is a section of the separated coordinate projection. -/
instance (i : Fin (n + 1)) (a : Γ(S, ⊤)) : IsClosedImmersion (cubeFace S i a) := by
  have : IsSeparated (cubeForget S i) :=
    haveI : IsSeparated (cubeForget S i ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S) := by
      rw [comp_over]
      infer_instance
    IsSeparated.of_comp (cubeForget S i) (𝔸(ULift.{u} (Fin n); S) ↘ S)
  have : IsClosedImmersion (cubeFace S i a ≫ cubeForget S i) := by
    rw [cubeFace_cubeForget]
    infer_instance
  exact IsClosedImmersion.of_comp _ (cubeForget S i)

/-- The intersection of two faces in different coordinates is the double face, as a scheme
pullback. No disjointness or reducedness assumption on the base is needed. -/
lemma isPullback_cubeFace_cubeFace (i : Fin (n + 2)) (j : Fin (n + 1)) (a b : Γ(S, ⊤)) :
    IsPullback (cubeFace S j b) (cubeFace S (j.predAbove i) a)
      (cubeFace S i a) (cubeFace S (i.succAbove j) b) := by
  have w := cubeFace_cubeFace i j a b
  have fac (s : PullbackCone (cubeFace S i a) (cubeFace S (i.succAbove j) b)) :
      s.fst ≫ cubeForget S j ≫ cubeFace S j b = s.fst := by
    apply hom_ext (by simp)
    rintro ⟨k⟩
    rcases Fin.eq_self_or_eq_succAbove j k with hk | ⟨k, rfl⟩
    · subst k
      have h := congrArg (fun g ↦ g.appTop (coord S (ULift.up (i.succAbove j)))) s.condition
      rw [← Category.assoc, comp_cubeFace_appTop_coord]
      simp only [Fin.insertNth_apply_same, Category.assoc, comp_over]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cubeFace_appTop_coord_succAbove,
        cubeFace_appTop_coord_self] at h
      have hbase : s.fst ≫ 𝔸(ULift.{u} (Fin (n + 1)); S) ↘ S =
          s.snd ≫ 𝔸(ULift.{u} (Fin (n + 1)); S) ↘ S := by
        simpa using (reassoc_of% s.condition) (𝔸(ULift.{u} (Fin (n + 2)); S) ↘ S)
      simpa only [hbase, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h.symm
    · rw [← Category.assoc, comp_cubeFace_appTop_coord]
      simp only [Fin.insertNth_apply_succAbove, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        cubeForget_appTop_coord]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun s ↦ s.fst ≫ cubeForget S j)
    (fun s ↦ by simpa only [Category.assoc] using fac s) ?_ ?_)
  · intro s
    apply (cancel_mono (cubeFace S (i.succAbove j) b)).mp
    rw [Category.assoc, ← w]
    simpa only [Category.assoc, reassoc_of% (fac s)] using s.condition
  · intro s m hm _
    simpa using congrArg (fun f ↦ f ≫ cubeForget S j) hm

end AlgebraicGeometry.AffineSpace
