/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.BasepointSet
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue

import TauCeti.CategoryTheory.InducedCategory

/-!
# The two-set Seifert--van Kampen theorem for fundamental groupoids

Suppose that the interiors of two sets `A` and `B` cover a space `X`. This file proves that the
square of fundamental groupoids induced by the inclusions

```
Π(A ∩ B) ⟶ Π(A)
    ↓         ↓
  Π(B)   ⟶  Π(X)
```

is a pushout in the category of groupoids, with no connectedness assumption on `A`, `B` or
`A ∩ B`. More usefully for calculations, the same holds for the fundamental groupoids on a set
`S` of basepoints, provided that `S` meets every path component of `A`, of `B` and of `A ∩ B`:
the full subgroupoids on `S` of the four fundamental groupoids again form a pushout square. For
the circle covered by two arcs, whose intersection has two path components, this requires two
basepoints; with a single basepoint, it recovers the hypotheses of the based theorem
`TauCeti.isPushout_fundamentalGroup`.

The first statement is the gluing theorem `TauCeti.FundamentalGroupoid.glue` for the cover of
`X` by `A` and `B`, packaged as `TauCeti.FundamentalGroupoid.glueTwo`. For the second, choose for
every point `x` a point `r x` of `S` together with a homotopy class of paths from `x` to `r x`,
inside `A ∩ B` if `x ∈ A ∩ B`, inside `A` or `B` otherwise, and trivial if `x ∈ S`. Conjugating by
these classes retracts each of the four fundamental groupoids onto its full subgroupoid on `S`,
compatibly with the inclusions (`TauCeti.InducedCategory.retraction`). A cocone over the square on
`S` then becomes a cocone over the full square, to which the first statement applies.

## Main declarations

* `TauCeti.FundamentalGroupoid.glueTwo`: the functor out of the fundamental groupoid of `X`
  glued from functors out of the fundamental groupoids of `A` and `B` which agree on `A ∩ B`.
* `TauCeti.isPushout_fundamentalGroupoid`: **the two-set van Kampen theorem for fundamental
  groupoids**.
* `TauCeti.isPushout_fundamentalGroupoidOn`: **the two-set van Kampen theorem for fundamental
  groupoids on a set of basepoints**.

## References

* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
* R. Brown, *Groupoids and van Kampen's theorem*, Proc. London Math. Soc. (3) 17 (1967), 385--401.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {A B : Set X}

namespace FundamentalGroupoid

open _root_.FundamentalGroupoid

section Glue

/-- The cover of `X` by `A` and `B`, indexed by `Bool`. -/
private abbrev twoCover (A B : Set X) : Bool → Set X := fun b ↦ Bool.rec B A b

private theorem exists_twoCover_mem_nhds (hCover : interior A ∪ interior B = univ) (y : X) :
    ∃ b, twoCover A B b ∈ 𝓝 y := by
  rcases (hCover ▸ mem_univ y : y ∈ interior A ∪ interior B) with hy | hy
  · exact ⟨true, mem_interior_iff_mem_nhds.1 hy⟩
  · exact ⟨false, mem_interior_iff_mem_nhds.1 hy⟩

private def swapInter : C(↥(B ∩ A), ↥(A ∩ B)) where
  toFun z := ⟨z.1, z.2.2, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun z ↦ ⟨z.2.2, z.2.1⟩

variable {D : Type*} [Category D]

/-- Functors out of the fundamental groupoids of `A` and `B` which agree on `A ∩ B`, as a family
indexed by `twoCover A B`, satisfy the compatibility hypothesis of the gluing theorem. -/
private theorem twoCover_compatibility (FA : FundamentalGroupoid A ⥤ D)
    (FB : FundamentalGroupoid B ⥤ D)
    (h : map (ContinuousMap.inclusion inter_subset_left) ⋙ FA =
      map (ContinuousMap.inclusion inter_subset_right) ⋙ FB) (i j : Bool) :
    map (ContinuousMap.inclusion
        (inter_subset_left : twoCover A B i ∩ twoCover A B j ⊆ twoCover A B i)) ⋙
        (Bool.rec FB FA i : FundamentalGroupoid (twoCover A B i) ⥤ D) =
      map (ContinuousMap.inclusion
        (inter_subset_right : twoCover A B i ∩ twoCover A B j ⊆ twoCover A B j)) ⋙
        (Bool.rec FB FA j : FundamentalGroupoid (twoCover A B j) ⥤ D) := by
  cases i <;> cases j
  · rfl
  · -- The inclusions of `B ∩ A` factor through the swap `B ∩ A ≃ A ∩ B`.
    have hr : map (ContinuousMap.inclusion (inter_subset_left : B ∩ A ⊆ B)) =
        map (swapInter (A := A) (B := B)) ⋙
          map (ContinuousMap.inclusion (inter_subset_right : A ∩ B ⊆ B)) := by
      rw [← FundamentalGroupoid.map_comp]
      congr 1
    have hl : map (ContinuousMap.inclusion (inter_subset_right : B ∩ A ⊆ A)) =
        map (swapInter (A := A) (B := B)) ⋙
          map (ContinuousMap.inclusion (inter_subset_left : A ∩ B ⊆ A)) := by
      rw [← FundamentalGroupoid.map_comp]
      congr 1
    rw [hr, hl]
    exact congrArg (map (swapInter (A := A) (B := B)) ⋙ ·) h.symm
  · exact h
  · rfl

variable (hCover : interior A ∪ interior B = univ) (FA : FundamentalGroupoid A ⥤ D)
  (FB : FundamentalGroupoid B ⥤ D)
  (h : map (ContinuousMap.inclusion inter_subset_left) ⋙ FA =
    map (ContinuousMap.inclusion inter_subset_right) ⋙ FB)

/-- **Gluing two functors out of fundamental groupoids.** If the interiors of `A` and `B` cover
`X`, and `FA` and `FB` are functors out of the fundamental groupoids of `A` and `B` which agree
on the fundamental groupoid of `A ∩ B`, this is the functor out of the fundamental groupoid of
`X` which restricts to `FA` and to `FB` (`map_subtypeVal_comp_glueTwo_left`,
`map_subtypeVal_comp_glueTwo_right`); it is the unique such functor (`eq_glueTwo`). -/
def glueTwo : FundamentalGroupoid X ⥤ D :=
  glue (exists_twoCover_mem_nhds hCover)
    (fun b ↦ (Bool.rec FB FA b : FundamentalGroupoid (twoCover A B b) ⥤ D))
    (twoCover_compatibility FA FB h)

/-- The glued functor restricts to `FA` on the fundamental groupoid of `A`. -/
@[simp]
theorem map_subtypeVal_comp_glueTwo_left :
    map (ContinuousMap.subtypeVal A) ⋙ glueTwo hCover FA FB h = FA :=
  map_subtypeVal_comp_glue (exists_twoCover_mem_nhds hCover) _ (twoCover_compatibility FA FB h)
    true

/-- The glued functor restricts to `FB` on the fundamental groupoid of `B`. -/
@[simp]
theorem map_subtypeVal_comp_glueTwo_right :
    map (ContinuousMap.subtypeVal B) ⋙ glueTwo hCover FA FB h = FB :=
  map_subtypeVal_comp_glue (exists_twoCover_mem_nhds hCover) _ (twoCover_compatibility FA FB h)
    false

/-- A functor out of the fundamental groupoid of `X` which restricts to `FA` and to `FB` is the
glued functor. -/
theorem eq_glueTwo {G : FundamentalGroupoid X ⥤ D} (hA : map (ContinuousMap.subtypeVal A) ⋙ G = FA)
    (hB : map (ContinuousMap.subtypeVal B) ⋙ G = FB) : G = glueTwo hCover FA FB h :=
  eq_glue _ _ _ fun b ↦ by cases b <;> assumption

end Glue

end FundamentalGroupoid

open _root_.FundamentalGroupoid

/-- **The two-set van Kampen theorem for fundamental groupoids.** If the interiors of `A` and `B`
cover `X`, the square of fundamental groupoids induced by the inclusions of `A ∩ B` into `A` and
`B` and of `A` and `B` into `X` is a pushout in the category of groupoids. -/
theorem isPushout_fundamentalGroupoid (hCover : interior A ∪ interior B = univ) :
    IsPushout (C := Grpd.{u, u}) (Z := Grpd.of (FundamentalGroupoid ↥(A ∩ B)))
      (X := Grpd.of (FundamentalGroupoid A)) (Y := Grpd.of (FundamentalGroupoid B))
      (P := Grpd.of (FundamentalGroupoid X))
      (map (ContinuousMap.inclusion inter_subset_left))
      (map (ContinuousMap.inclusion inter_subset_right))
      (map (ContinuousMap.subtypeVal A)) (map (ContinuousMap.subtypeVal B)) := by
  refine ⟨⟨?_⟩, ⟨PushoutCocone.IsColimit.mk (C := Grpd.{u, u}) _ (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s ↦ ?_) fun s m h₁ h₂ ↦ ?_⟩⟩
  · -- Both composites are induced by the inclusion of `A ∩ B` into `X`.
    exact (FundamentalGroupoid.map_comp _ _).symm.trans (FundamentalGroupoid.map_comp
      (ContinuousMap.subtypeVal B) (ContinuousMap.inclusion inter_subset_right))
  · exact FundamentalGroupoid.glueTwo hCover s.inl s.inr s.condition
  · exact FundamentalGroupoid.map_subtypeVal_comp_glueTwo_left hCover _ _ s.condition
  · exact FundamentalGroupoid.map_subtypeVal_comp_glueTwo_right hCover _ _ s.condition
  · exact FundamentalGroupoid.eq_glueTwo hCover _ _ s.condition h₁ h₂

section Basepoints

/-! ### The theorem on a set of basepoints -/

variable (S : Set X)

/-- For a map `r` which is the identity on `S` and joins every point `x` of `T` to `r x` by a path
in `T`, a morphism of the fundamental groupoid of `T` from `z` to `r z`: the identity if `z ∈ S`,
and the class of a chosen path in `T` otherwise. -/
private def conn (r : X → X) (hrS : ∀ x ∈ S, r x = x) (T : Set X)
    (hT : ∀ x ∈ T, JoinedIn T x (r x)) (z : T) :
    mk z ⟶ mk (⟨r z, (hT z z.2).target_mem⟩ : T) := by
  classical
  exact if hz : (z : X) ∈ S then eqToHom (congrArg mk (Subtype.ext (hrS z hz).symm))
    else Path.Homotopic.Quotient.mk (hT z z.2).joined_subtype.somePath

/-- For `T ⊆ U`, the morphisms `conn` of `U`, replaced on the points of `T` by the images of the
morphisms `conn` of `T`. -/
private def connExt (r : X → X) (hrS : ∀ x ∈ S, r x = x) {T U : Set X} (hTU : T ⊆ U)
    (hT : ∀ x ∈ T, JoinedIn T x (r x)) (hU : ∀ x ∈ U, JoinedIn U x (r x)) (z : U) :
    mk z ⟶ mk (⟨r z, (hU z z.2).target_mem⟩ : U) := by
  classical
  exact if hz : (z : X) ∈ T then (map (ContinuousMap.inclusion hTU)).map (conn S r hrS T hT ⟨z, hz⟩)
    else conn S r hrS U hU z

private theorem connExt_of_mem (r : X → X) (hrS : ∀ x ∈ S, r x = x) {T U : Set X} (hTU : T ⊆ U)
    (hT : ∀ x ∈ T, JoinedIn T x (r x)) (hU : ∀ x ∈ U, JoinedIn U x (r x)) (z : U)
    (hz : (z : X) ∈ T) :
    connExt S r hrS hTU hT hU z =
      (map (ContinuousMap.inclusion hTU)).map (conn S r hrS T hT ⟨z, hz⟩) :=
  dite_eq_left hz

/-- On the points of `S`, the morphisms `connExt` are identities. -/
private theorem connExt_of_mem_basepoints (r : X → X) (hrS : ∀ x ∈ S, r x = x) {T U : Set X}
    (hTU : T ⊆ U) (hT : ∀ x ∈ T, JoinedIn T x (r x)) (hU : ∀ x ∈ U, JoinedIn U x (r x)) (z : U)
    (hz : (z : X) ∈ S) :
    connExt S r hrS hTU hT hU z = eqToHom (congrArg mk (Subtype.ext (hrS z hz).symm)) := by
  by_cases hzT : (z : X) ∈ T
  · refine (connExt_of_mem S r hrS hTU hT hU z hzT).trans ?_
    rw [conn, dite_eq_left hz, eqToHom_map]
    rfl
  · unfold connExt
    refine (dite_eq_right hzT).trans ?_
    unfold conn
    exact dite_eq_left hz

/-- Conjugation by morphisms `c z` from every point `z` of `U` to `r z ∈ S`, as a retraction of
the fundamental groupoid of `U` onto its full subgroupoid on `S`. -/
private def retractionOn (r : X → X) (hrS : ∀ x, r x ∈ S) (U : Set X) (hU : ∀ x ∈ U, r x ∈ U)
    (c : ∀ z : U, mk z ⟶ mk (⟨r z, hU z z.2⟩ : U)) :
    FundamentalGroupoid U ⥤ FundamentalGroupoidOn (Subtype.val ⁻¹' S : Set U) :=
  InducedCategory.retraction _ (fun z ↦ ⟨⟨r z.as, hU _ z.as.2⟩, hrS _⟩) fun z ↦ asIso (c z.as)

/-- Conjugation by morphisms `c x` from every point `x` of `X` to `r x ∈ S`, as a retraction of
the fundamental groupoid of `X` onto its full subgroupoid on `S`. -/
private def retraction (r : X → X) (hrS : ∀ x, r x ∈ S) (c : ∀ x : X, mk x ⟶ mk (r x)) :
    FundamentalGroupoid X ⥤ FundamentalGroupoidOn S :=
  InducedCategory.retraction _ (fun z ↦ ⟨r z.as, hrS _⟩) fun z ↦ asIso (c z.as)

/-- The retractions of `T ⊆ U` commute with the inclusions if their connecting morphisms do. -/
private theorem map_inclusion_comp_retractionOn (r : X → X) (hrS : ∀ x, r x ∈ S) {T U : Set X}
    (hTU : T ⊆ U) (hT : ∀ x ∈ T, r x ∈ T) (hU : ∀ x ∈ U, r x ∈ U)
    (cT : ∀ z : T, mk z ⟶ mk (⟨r z, hT z z.2⟩ : T)) (cU : ∀ z : U, mk z ⟶ mk (⟨r z, hU z z.2⟩ : U))
    (hc : ∀ z : T, cU (ContinuousMap.inclusion hTU z) =
      (map (ContinuousMap.inclusion hTU)).map (cT z)) :
    map (ContinuousMap.inclusion hTU) ⋙ retractionOn S r hrS U hU cU =
      retractionOn S r hrS T hT cT ⋙
        FundamentalGroupoidOn.map (ContinuousMap.inclusion hTU) fun _ h ↦ h := by
  -- Both functors send `z` to `r z`, so it suffices to compare them on morphisms.
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun a b f ↦ heq_of_eq ?_
  ext
  -- Unfold both sides, writing the endpoints of `f` as points of `U` rather than as objects of
  -- the image of `map (ContinuousMap.inclusion hTU)`, so that `hc` applies.
  change inv (cU (ContinuousMap.inclusion hTU a.as)) ≫ (map (ContinuousMap.inclusion hTU)).map f ≫
      cU (ContinuousMap.inclusion hTU b.as) =
    (map (ContinuousMap.inclusion hTU)).map (inv (cT a.as) ≫ f ≫ cT b.as)
  rw [hc, hc, Functor.map_comp, Functor.map_comp, Functor.map_inv]
  -- The two sides differ only in how the endpoints of the morphisms are written.
  rfl

/-- The retraction of `X` restricts to the retraction of `U` if their connecting morphisms
agree. -/
private theorem map_subtypeVal_comp_retraction (r : X → X) (hrS : ∀ x, r x ∈ S) {U : Set X}
    (hU : ∀ x ∈ U, r x ∈ U) (cU : ∀ z : U, mk z ⟶ mk (⟨r z, hU z z.2⟩ : U))
    (c : ∀ x : X, mk x ⟶ mk (r x))
    (hc : ∀ z : U, c z = (map (ContinuousMap.subtypeVal U)).map (cU z)) :
    map (ContinuousMap.subtypeVal U) ⋙ retraction S r hrS c =
      retractionOn S r hrS U hU cU ⋙
        FundamentalGroupoidOn.map (ContinuousMap.subtypeVal U) fun _ h ↦ h := by
  -- Both functors send `z` to `r z`, so it suffices to compare them on morphisms.
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun a b f ↦ heq_of_eq ?_
  ext
  -- Unfold both sides, writing the endpoints of `f` as points of `X` rather than as objects of
  -- the image of `map (ContinuousMap.subtypeVal U)`, so that `hc` applies.
  change inv (c a.as) ≫ (map (ContinuousMap.subtypeVal U)).map f ≫ c b.as =
    (map (ContinuousMap.subtypeVal U)).map (inv (cU a.as) ≫ f ≫ cU b.as)
  rw [hc, hc, Functor.map_comp, Functor.map_comp, Functor.map_inv]
  -- The two sides differ only in how the endpoints of the morphisms are written.
  rfl

/-- The retraction of `U` restricts to the identity on the full subgroupoid on `S` if its
connecting morphisms are identities on `S`. -/
private theorem incl_comp_retractionOn (r : X → X) (hrS : ∀ x, r x ∈ S) (hrS' : ∀ x ∈ S, r x = x)
    {U : Set X} (hU : ∀ x ∈ U, r x ∈ U) (cU : ∀ z : U, mk z ⟶ mk (⟨r z, hU z z.2⟩ : U))
    (hc : ∀ (z : U) (hz : (z : X) ∈ S),
      cU z = eqToHom (congrArg mk (Subtype.ext (hrS' z hz).symm))) :
    FundamentalGroupoidOn.incl _ ⋙ retractionOn S r hrS U hU cU = 𝟭 _ :=
  InducedCategory.inducedFunctor_comp_retraction _ _ _
    (fun s ↦ Subtype.ext (Subtype.ext (hrS' _ s.2))) fun s ↦ hc s.1 s.2

/-- The retraction of `X` restricts to the identity on the full subgroupoid on `S` if its
connecting morphisms are identities on `S`. -/
private theorem incl_comp_retraction (r : X → X) (hrS : ∀ x, r x ∈ S) (hrS' : ∀ x ∈ S, r x = x)
    (c : ∀ x : X, mk x ⟶ mk (r x))
    (hc : ∀ (x : X) (hx : x ∈ S), c x = eqToHom (congrArg mk (hrS' x hx).symm)) :
    FundamentalGroupoidOn.incl S ⋙ retraction S r hrS c = 𝟭 _ :=
  InducedCategory.inducedFunctor_comp_retraction _ _ _ (fun s ↦ Subtype.ext (hrS' _ s.2))
    fun s ↦ hc s.1 s.2

variable {S} (hSA : ∀ x ∈ A, ∃ y ∈ S, JoinedIn A x y) (hSB : ∀ x ∈ B, ∃ y ∈ S, JoinedIn B x y)
  (hSAB : ∀ x ∈ A ∩ B, ∃ y ∈ S, JoinedIn (A ∩ B) x y)

open Classical in
/-- A point of `S` joined to `x`: `x` itself if `x ∈ S`, and otherwise a point joined to `x`
inside `A ∩ B`, `A` or `B`, the first of these sets which contains `x`. -/
private def retr (x : X) : X :=
  if x ∈ S then x else if hx : x ∈ A ∩ B then (hSAB x hx).choose
    else if hx : x ∈ A then (hSA x hx).choose else if hx : x ∈ B then (hSB x hx).choose else x

private theorem retr_of_mem {x : X} (hx : x ∈ S) : retr hSA hSB hSAB x = x :=
  ite_eq_left hx

private theorem retr_mem (hCover : interior A ∪ interior B = univ) (x : X) :
    retr hSA hSB hSAB x ∈ S := by
  have hx : x ∈ A ∪ B := union_subset_union interior_subset interior_subset (hCover ▸ mem_univ x)
  unfold retr
  split_ifs with h₁ h₂ h₃ h₄
  exacts [h₁, (hSAB x h₂).choose_spec.1, (hSA x h₃).choose_spec.1, (hSB x h₄).choose_spec.1,
    (hx.elim h₃ h₄).elim]

private theorem joinedIn_retr_inter {x : X} (hx : x ∈ A ∩ B) :
    JoinedIn (A ∩ B) x (retr hSA hSB hSAB x) := by
  unfold retr
  split_ifs with h
  exacts [JoinedIn.refl hx, (hSAB x hx).choose_spec.2]

private theorem joinedIn_retr_left {x : X} (hx : x ∈ A) : JoinedIn A x (retr hSA hSB hSAB x) := by
  unfold retr
  split_ifs with h₁ h₂
  exacts [JoinedIn.refl hx, (hSAB x h₂).choose_spec.2.mono inter_subset_left,
    (hSA x hx).choose_spec.2]

private theorem joinedIn_retr_right {x : X} (hx : x ∈ B) : JoinedIn B x (retr hSA hSB hSAB x) := by
  unfold retr
  split_ifs with h₁ h₂ h₃
  exacts [JoinedIn.refl hx, (hSAB x h₂).choose_spec.2.mono inter_subset_right,
    absurd ⟨h₃, hx⟩ h₂, (hSB x hx).choose_spec.2]

include hSA hSB hSAB in
/-- If `S` meets every path component of `A`, of `B` and of `A ∩ B`, the fundamental groupoids
of `A ∩ B`, `A`, `B` and `X` retract onto their full subgroupoids on `S`, compatibly with the
inclusions. -/
private theorem exists_retractions (hCover : interior A ∪ interior B = univ) :
    ∃ (RAB : FundamentalGroupoid ↥(A ∩ B) ⥤
        FundamentalGroupoidOn (Subtype.val ⁻¹' S : Set ↥(A ∩ B)))
      (RA : FundamentalGroupoid A ⥤ FundamentalGroupoidOn (Subtype.val ⁻¹' S : Set A))
      (RB : FundamentalGroupoid B ⥤ FundamentalGroupoidOn (Subtype.val ⁻¹' S : Set B))
      (RX : FundamentalGroupoid X ⥤ FundamentalGroupoidOn S),
      map (ContinuousMap.inclusion inter_subset_left) ⋙ RA =
          RAB ⋙ FundamentalGroupoidOn.map (ContinuousMap.inclusion inter_subset_left)
            (fun _ h ↦ h) ∧
        map (ContinuousMap.inclusion inter_subset_right) ⋙ RB =
          RAB ⋙ FundamentalGroupoidOn.map (ContinuousMap.inclusion inter_subset_right)
            (fun _ h ↦ h) ∧
        map (ContinuousMap.subtypeVal A) ⋙ RX =
          RA ⋙ FundamentalGroupoidOn.map (ContinuousMap.subtypeVal A) (fun _ h ↦ h) ∧
        map (ContinuousMap.subtypeVal B) ⋙ RX =
          RB ⋙ FundamentalGroupoidOn.map (ContinuousMap.subtypeVal B) (fun _ h ↦ h) ∧
        FundamentalGroupoidOn.incl _ ⋙ RA = 𝟭 _ ∧ FundamentalGroupoidOn.incl _ ⋙ RB = 𝟭 _ ∧
        FundamentalGroupoidOn.incl S ⋙ RX = 𝟭 _ := by
  classical
  -- Choose for every point `x` a point `r x` of `S` and morphisms from `x` to `r x` in the
  -- fundamental groupoids of `A ∩ B`, `A`, `B` and `X`, compatible with the inclusions.
  set r := retr hSA hSB hSAB
  have hrS (x : X) (hx : x ∈ S) : r x = x := retr_of_mem hSA hSB hSAB hx
  have hjAB (x : X) (hx : x ∈ A ∩ B) := joinedIn_retr_inter hSA hSB hSAB hx
  have hjA (x : X) (hx : x ∈ A) := joinedIn_retr_left hSA hSB hSAB hx
  have hjB (x : X) (hx : x ∈ B) := joinedIn_retr_right hSA hSB hSAB hx
  have hmemB (x : X) (hx : x ∉ A) : x ∈ B :=
    (union_subset_union interior_subset interior_subset (hCover ▸ mem_univ x)).resolve_left hx
  let cAB := conn S r hrS (A ∩ B) hjAB
  let cA := connExt S r hrS inter_subset_left hjAB hjA
  let cB := connExt S r hrS inter_subset_right hjAB hjB
  let c (x : X) : mk x ⟶ mk (r x) := if hx : x ∈ A then (map (ContinuousMap.subtypeVal A)).map
    (cA ⟨x, hx⟩) else (map (ContinuousMap.subtypeVal B)).map (cB ⟨x, hmemB x hx⟩)
  have hc (x : X) (hx : x ∈ S) : c x = eqToHom (congrArg mk (hrS x hx).symm) := by
    by_cases hxA : x ∈ A
    · exact (dite_eq_left hxA).trans ((congrArg (map (ContinuousMap.subtypeVal A)).map
        (connExt_of_mem_basepoints S r hrS _ hjAB hjA ⟨x, hxA⟩ hx)).trans (eqToHom_map _ _))
    · exact (dite_eq_right hxA).trans ((congrArg (map (ContinuousMap.subtypeVal B)).map
        (connExt_of_mem_basepoints S r hrS _ hjAB hjB ⟨x, hmemB x hxA⟩ hx)).trans
          (eqToHom_map _ _))
  have hcB (z : B) : c z = (map (ContinuousMap.subtypeVal B)).map (cB z) := by
    by_cases hzA : (z : X) ∈ A
    · -- On `A ∩ B`, both connecting morphisms are images of those of `A ∩ B`.
      refine (dite_eq_left hzA).trans <| (congrArg (map (ContinuousMap.subtypeVal A)).map
        (connExt_of_mem S r hrS _ hjAB hjA ⟨z, hzA⟩ ⟨hzA, z.2⟩)).trans <|
          (FundamentalGroupoid.map_comp_map _ _ _).symm.trans <|
            (FundamentalGroupoid.map_comp_map (ContinuousMap.subtypeVal B)
              (ContinuousMap.inclusion inter_subset_right) _).trans ?_
      exact congrArg (map (ContinuousMap.subtypeVal B)).map
        (connExt_of_mem S r hrS _ hjAB hjB z ⟨hzA, z.2⟩).symm
    · exact dite_eq_right hzA
  have hrmem (x : X) : r x ∈ S := retr_mem hSA hSB hSAB hCover x
  have hmAB (x : X) (hx : x ∈ A ∩ B) : r x ∈ A ∩ B := (hjAB x hx).target_mem
  have hmA (x : X) (hx : x ∈ A) : r x ∈ A := (hjA x hx).target_mem
  have hmB (x : X) (hx : x ∈ B) : r x ∈ B := (hjB x hx).target_mem
  refine ⟨retractionOn S r hrmem (A ∩ B) hmAB cAB, retractionOn S r hrmem A hmA cA,
    retractionOn S r hrmem B hmB cB, retraction S r hrmem c,
    map_inclusion_comp_retractionOn S r hrmem inter_subset_left hmAB hmA cAB cA fun z ↦
      connExt_of_mem S r hrS _ hjAB hjA _ z.2,
    map_inclusion_comp_retractionOn S r hrmem inter_subset_right hmAB hmB cAB cB fun z ↦
      connExt_of_mem S r hrS _ hjAB hjB _ z.2,
    map_subtypeVal_comp_retraction S r hrmem hmA cA c fun z ↦ dite_eq_left z.2,
    map_subtypeVal_comp_retraction S r hrmem hmB cB c hcB,
    incl_comp_retractionOn S r hrmem hrS hmA cA fun z hz ↦
      connExt_of_mem_basepoints S r hrS _ hjAB hjA z hz,
    incl_comp_retractionOn S r hrmem hrS hmB cB fun z hz ↦
      connExt_of_mem_basepoints S r hrS _ hjAB hjB z hz,
    incl_comp_retraction S r hrmem hrS c hc⟩

include hSA hSB hSAB in
/-- **The two-set van Kampen theorem for fundamental groupoids on a set of basepoints.** If the
interiors of `A` and `B` cover `X` and the set `S` meets every path component of `A`, of `B`
and of `A ∩ B`, then the square of fundamental groupoids on `S` induced by the inclusions of
`A ∩ B` into `A` and `B` and of `A` and `B` into `X` is a pushout in the category of groupoids. -/
theorem isPushout_fundamentalGroupoidOn (hCover : interior A ∪ interior B = univ) :
    IsPushout (C := Grpd.{u, u})
      (Z := Grpd.of (FundamentalGroupoidOn (Subtype.val ⁻¹' S : Set ↥(A ∩ B))))
      (X := Grpd.of (FundamentalGroupoidOn (Subtype.val ⁻¹' S : Set A)))
      (Y := Grpd.of (FundamentalGroupoidOn (Subtype.val ⁻¹' S : Set B)))
      (P := Grpd.of (FundamentalGroupoidOn S))
      (FundamentalGroupoidOn.map (ContinuousMap.inclusion inter_subset_left) fun _ h ↦ h)
      (FundamentalGroupoidOn.map (ContinuousMap.inclusion inter_subset_right) fun _ h ↦ h)
      (FundamentalGroupoidOn.map (ContinuousMap.subtypeVal A) fun _ h ↦ h)
      (FundamentalGroupoidOn.map (ContinuousMap.subtypeVal B) fun _ h ↦ h) := by
  obtain ⟨RAB, RA, RB, RX, hRA, hRB, hXA, hXB, hiA, hiB, hiX⟩ :=
    exists_retractions hSA hSB hSAB hCover
  -- A cocone over the square on `S` becomes, after the retractions, a cocone over the square of
  -- full fundamental groupoids, which glues by the two-set gluing theorem.
  refine ⟨⟨?_⟩, ⟨PushoutCocone.IsColimit.mk (C := Grpd.{u, u}) _ (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s ↦ ?_) fun s m h₁ h₂ ↦ ?_⟩⟩
  · exact (FundamentalGroupoidOn.map_comp _ _ _ _).symm.trans (FundamentalGroupoidOn.map_comp
      (ContinuousMap.subtypeVal B) (ContinuousMap.inclusion inter_subset_right) _ _)
  · refine FundamentalGroupoidOn.incl S ⋙
      FundamentalGroupoid.glueTwo hCover (RA ⋙ s.inl) (RB ⋙ s.inr) ?_
    calc map (ContinuousMap.inclusion inter_subset_left) ⋙ RA ⋙ s.inl
        = RAB ⋙ (FundamentalGroupoidOn.map (ContinuousMap.inclusion inter_subset_left)
            fun _ h ↦ h) ⋙ s.inl := congrArg (· ⋙ s.inl) hRA
      _ = RAB ⋙ (FundamentalGroupoidOn.map (ContinuousMap.inclusion inter_subset_right)
            fun _ h ↦ h) ⋙ s.inr := congrArg (RAB ⋙ ·) s.condition
      _ = map (ContinuousMap.inclusion inter_subset_right) ⋙ RB ⋙ s.inr :=
        (congrArg (· ⋙ s.inr) hRB).symm
  · exact (congrArg (FundamentalGroupoidOn.incl _ ⋙ ·)
      (FundamentalGroupoid.map_subtypeVal_comp_glueTwo_left hCover _ _ _)).trans
      (congrArg (· ⋙ s.inl) hiA)
  · exact (congrArg (FundamentalGroupoidOn.incl _ ⋙ ·)
      (FundamentalGroupoid.map_subtypeVal_comp_glueTwo_right hCover _ _ _)).trans
      (congrArg (· ⋙ s.inr) hiB)
  · -- `m` is determined by its composite with the retraction of `X`, which restricts to the
    -- composites of the retractions of `A` and `B` with the legs of the cocone.
    exact (congrArg (· ⋙ m) hiX).symm.trans (congrArg (FundamentalGroupoidOn.incl S ⋙ ·)
      (FundamentalGroupoid.eq_glueTwo (G := RX ⋙ m) hCover _ _ _ ((congrArg (· ⋙ m) hXA).trans
        (congrArg (RA ⋙ ·) h₁)) ((congrArg (· ⋙ m) hXB).trans (congrArg (RB ⋙ ·) h₂))))

end Basepoints

end TauCeti
