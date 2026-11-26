/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Cycle
public import TauCeti.Dynamics.PeriodicPts.Orbit
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import TauCeti.KnotTheory.Foam.ClosedWeb.Tetrahedron
import Mathlib.Data.Fintype.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Unlabelled prefoams with specified boundary

An unlabelled prefoam `F : FoamWithBoundary W` bounded by a closed web `W` is a compact oriented
2-dimensional CW-like stratified object with singular seams (1-strata where three facet sheets meet
with a cyclic order) and singular tetrahedral vertices (0-strata whose local link is one of the two
chiral tetrahedral webs `ClosedWeb.tetWeb c`), meeting the boundary strictly transversely in `W`.

Following Goertz–Marino–Wedrich and Robert–Wagner, `FoamWithBoundary W` is represented purely
combinatorially with finite carrier types and zero redundant gauge choices:

* `Vertex`, `Seam`, `SeamCircle`, `Facet`, `Boundary` are finite types in the same universe as `W`.
* `chirality : Vertex → Bool` records whether the local link of each interior singular vertex is
  `ClosedWeb.tetrahedronPos` (`true`) or `ClosedWeb.tetrahedronNeg` (`false`).
* `seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool` pairs the four seam-ends at each interior
  vertex and the unique seam-end at each boundary vertex into oriented interval seams (`false` for
  source, `true` for target), constrained so an interior ray exiting `v` meets the local link at a
  split (`seamEnds_inl_snd`) and a boundary merge of `W` initiates a seam (`seamEnds_inr_snd`).
* Around every interval seam `s` and circular seam `c`, the three incident local sheet occurrences
  are indexed by `Fin 3`, where slot `0` carries the opposite boundary orientation `-s` and slots
  `1, 2` carry the seam orientation `+s`; every boundary web edge `e : W.Edge` carries `+e`.
* From `(chirality, seamEnds)` alone, `cornerSide` (`cornerIncoming` and `cornerOutgoing`)
  identifies the corners `(Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)` with the sides
  `(Seam × Fin 3) ⊕ W.Edge`, producing the canonical successor permutation
  `nextSide : Equiv.Perm Side`.
* Each `b : Boundary` belongs to a facet `boundaryFacet b : Facet`, so a single facet may have
  multiple indexed boundary components (`FacetBoundary f`) and may appear multiple times in the
  three local sheet slots around a seam. Orbits of `nextSide` and circle sides
  `(SeamCircle × Fin 3) ⊕ W.Circle` partition `Boundary` bijectively (`boundaryEquiv`).

## Main definitions

* `TauCeti.FoamWithBoundary`: combinatorial prefoams bounded by `W : ClosedWeb`.
* `TauCeti.ClosedFoam`: prefoams with empty boundary `ClosedWeb.empty`.
* `TauCeti.FoamWithBoundary.cornerSide`, `cornerIncoming`, `cornerOutgoing`, `nextSide`: canonical
  corner-to-side bijections and boundary-walk successor permutation.
* `TauCeti.FoamWithBoundary.sideCycle`, `sideWord`: nonempty cyclic side orbits and signed cyclic
  words on segmented boundary components.
* `TauCeti.FoamWithBoundary.numBoundaryComponents`, `facetEulerChar`: boundary-component count and
  Euler characteristic `2 - 2g - b` of each facet.
* `TauCeti.FoamWithBoundary.IsNilvalent`: prefoams without singular vertices or seams.

## References

* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definitions 2.1 and 3.1 (extended here to allow repeated global facet-seam
  incidences via local occurrence slots).
* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1 and Remark 2.2.
-/

public section

namespace TauCeti

universe u

namespace FoamWithBoundary

/-! ### Slot-orientation lemma and corner-side equivalences -/

private theorem ends_snd_eq_iff (T : ClosedWeb.{u}) (k : T.Vertex) (i : Fin 3) (b : Bool) :
    (T.ends (k, i)).2 = b ↔ (b != decide (i = 0)) = !(T.ends (k, 0)).2 := by
  have h : (T.ends (k, i)).2 = (T.ends (k, 0)).2 ↔ decide (i = 0) = true := by simp
  revert h
  generalize (T.ends (k, i)).2 = x, (T.ends (k, 0)).2 = y, decide (i = 0) = z
  cases x <;> cases y <;> cases z <;> cases b <;> decide

-- Forward map sending each interior or boundary corner to the side incident in direction `dir`
-- (`true` for incoming, `false` for outgoing).
private def cornerSideFun (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool) :
    (Vertex × Fin 6) ⊕ (W.Vertex × Fin 3) → (Seam × Fin 3) ⊕ W.Edge
  | Sum.inl (v, e) =>
    let ki := (ClosedWeb.tetWeb (chirality v)).ends.symm (e, dir)
    Sum.inl ((seamEnds (Sum.inl (v, ki.1))).1, ki.2)
  | Sum.inr (w, i) =>
    let eb := W.ends (w, i)
    if eb.2 == dir then Sum.inr eb.1 else Sum.inl ((seamEnds (Sum.inr w)).1, i)

-- Inverse map sending each side to the corner it meets in direction `dir` (`true` for incoming,
-- `false` for outgoing) along its facet boundary orientation.
private def cornerSideInv (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool) :
    (Seam × Fin 3) ⊕ W.Edge → (Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)
  | Sum.inr e => Sum.inr (W.ends.symm (e, dir))
  | Sum.inl (s, i) =>
    match seamEnds.symm (s, dir != decide (i = 0)) with
    | Sum.inl (v, k) => Sum.inl (v, ((ClosedWeb.tetWeb (chirality v)).ends (k, i)).1)
    | Sum.inr w => Sum.inr (w, i)

private theorem leftInverse_cornerSideInv (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    Function.LeftInverse (cornerSideInv dir chirality seamEnds)
      (cornerSideFun dir chirality seamEnds) := by
  rintro (⟨v, e⟩ | ⟨w, i⟩)
  · dsimp only [cornerSideFun, cornerSideInv]
    set ki := (ClosedWeb.tetWeb (chirality v)).ends.symm (e, dir)
    have hki : (ClosedWeb.tetWeb (chirality v)).ends (ki.1, ki.2) = (e, dir) :=
      (ClosedWeb.tetWeb (chirality v)).ends.apply_symm_apply (e, dir)
    have hb : (dir != decide (ki.2 = 0)) = (seamEnds (Sum.inl (v, ki.1))).2 := by
      rw [h_inl, ← ends_snd_eq_iff]
      exact congrArg Prod.snd hki
    have hpair : ((seamEnds (Sum.inl (v, ki.1))).1, dir != decide (ki.2 = 0)) =
        seamEnds (Sum.inl (v, ki.1)) := Prod.ext rfl hb
    rw [hpair, seamEnds.symm_apply_apply]
    dsimp only
    rw [congrArg Prod.fst hki]
  · dsimp only [cornerSideFun]
    by_cases hdir : (W.ends (w, i)).2 = dir
    · simp only [hdir, BEq.rfl, ↓reduceIte, cornerSideInv]
      have he : ((W.ends (w, i)).1, dir) = W.ends (w, i) := Prod.ext rfl hdir.symm
      rw [he, W.ends.symm_apply_apply]
    · have hnot : (W.ends (w, i)).2 = !dir := by
        revert hdir
        generalize (W.ends (w, i)).2 = x
        cases x <;> cases dir <;> decide
      have hbeq : ((W.ends (w, i)).2 == dir) = false := by
        rw [hnot]; cases dir <;> rfl
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, cornerSideInv]
      have hd : (dir != decide (i = 0)) = (seamEnds (Sum.inr w)).2 := by
        have h1 := (ends_snd_eq_iff W w i (!dir)).mp hnot
        rw [h_inr]
        revert h1
        generalize decide (i = 0) = z, (W.ends (w, 0)).2 = y
        cases dir <;> cases z <;> cases y <;> decide
      have hpair : ((seamEnds (Sum.inr w)).1, dir != decide (i = 0)) = seamEnds (Sum.inr w) :=
        Prod.ext rfl hd
      rw [hpair, seamEnds.symm_apply_apply]

private theorem rightInverse_cornerSideInv (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    Function.RightInverse (cornerSideInv dir chirality seamEnds)
      (cornerSideFun dir chirality seamEnds) := by
  rintro (⟨s, i⟩ | e)
  · dsimp only [cornerSideInv]
    cases hse : seamEnds.symm (s, dir != decide (i = 0)) with
    | inl vk =>
      rcases vk with ⟨v, k⟩
      have happ : seamEnds (Sum.inl (v, k)) = (s, dir != decide (i = 0)) :=
        seamEnds.eq_symm_apply.mp hse.symm
      have hd : ((ClosedWeb.tetWeb (chirality v)).ends (k, i)).2 = dir := by
        rw [ends_snd_eq_iff, ← h_inl]
        exact (congrArg Prod.snd happ).symm
      dsimp only [cornerSideFun]
      have hp : (((ClosedWeb.tetWeb (chirality v)).ends (k, i)).1, dir) =
          (ClosedWeb.tetWeb (chirality v)).ends (k, i) := Prod.ext rfl hd.symm
      rw [hp, Equiv.symm_apply_apply, congrArg Prod.fst happ]
    | inr w =>
      have happ : seamEnds (Sum.inr w) = (s, dir != decide (i = 0)) :=
        seamEnds.eq_symm_apply.mp hse.symm
      have hnot : (W.ends (w, i)).2 = !dir := by
        rw [ends_snd_eq_iff]
        have hsnd : (W.ends (w, 0)).2 = (dir != decide (i = 0)) := by
          simpa [h_inr] using congrArg Prod.snd happ
        rw [hsnd]
        cases dir <;> cases decide (i = 0) <;> rfl
      have hbeq : ((W.ends (w, i)).2 == dir) = false := by
        rw [hnot]; cases dir <;> rfl
      dsimp only [cornerSideFun]
      rw [hbeq, congrArg Prod.fst happ]
      rfl
  · dsimp only [cornerSideInv, cornerSideFun]
    rw [W.ends.apply_symm_apply]
    simp

/-- Equivalence between corners and their incident facet-boundary sides in direction `dir`
(`true` for incoming, `false` for outgoing). -/
def cornerSideEquiv (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    ((Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)) ≃ ((Seam × Fin 3) ⊕ W.Edge) where
  toFun := cornerSideFun dir chirality seamEnds
  invFun := cornerSideInv dir chirality seamEnds
  left_inv := by exact leftInverse_cornerSideInv dir chirality seamEnds h_inl h_inr
  right_inv := by exact rightInverse_cornerSideInv dir chirality seamEnds h_inl h_inr

/-- Equivalence between corners and their incoming facet-boundary sides. -/
abbrev cornerIncomingEquiv {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideEquiv true Vertex Seam W

/-- Equivalence between corners and their outgoing facet-boundary sides. -/
abbrev cornerOutgoingEquiv {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideEquiv false Vertex Seam W

/-- Successor permutation advancing each side along the oriented boundary of its facet through the
corner it enters. -/
def nextSidePerm {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    Equiv.Perm ((Seam × Fin 3) ⊕ W.Edge) :=
  (cornerIncomingEquiv chirality seamEnds h_inl h_inr).symm.trans
    (cornerOutgoingEquiv chirality seamEnds h_inl h_inr)

section CornerSideEquivSimp

variable (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
  (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
  (h_inl : ∀ v k,
    (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
  (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2)

@[simp] theorem cornerSideEquiv_inl (v : Vertex) (e : Fin 6) :
    cornerSideEquiv dir chirality seamEnds h_inl h_inr (Sum.inl (v, e)) =
      Sum.inl ((seamEnds
        (Sum.inl (v, ((ClosedWeb.tetWeb (chirality v)).ends.symm (e, dir)).1))).1,
        ((ClosedWeb.tetWeb (chirality v)).ends.symm (e, dir)).2) := (rfl)

@[simp] theorem cornerSideEquiv_inr (w : W.Vertex) (i : Fin 3) :
    cornerSideEquiv dir chirality seamEnds h_inl h_inr (Sum.inr (w, i)) =
      if (W.ends (w, i)).2 == dir then Sum.inr (W.ends (w, i)).1
      else Sum.inl ((seamEnds (Sum.inr w)).1, i) := (rfl)

@[simp] theorem cornerSideEquiv_symm_inl (s : Seam) (i : Fin 3) :
    (cornerSideEquiv dir chirality seamEnds h_inl h_inr).symm (Sum.inl (s, i)) =
      match seamEnds.symm (s, dir != decide (i = 0)) with
      | Sum.inl (v, k) => Sum.inl (v, ((ClosedWeb.tetWeb (chirality v)).ends (k, i)).1)
      | Sum.inr w => Sum.inr (w, i) := (rfl)

@[simp] theorem cornerSideEquiv_symm_inr (e : W.Edge) :
    (cornerSideEquiv dir chirality seamEnds h_inl h_inr).symm (Sum.inr e) =
      Sum.inr (W.ends.symm (e, dir)) := (rfl)

theorem nextSidePerm_apply (x : (Seam × Fin 3) ⊕ W.Edge) :
    nextSidePerm chirality seamEnds h_inl h_inr x =
      cornerOutgoingEquiv chirality seamEnds h_inl h_inr
        ((cornerIncomingEquiv chirality seamEnds h_inl h_inr).symm x) := (rfl)

end CornerSideEquivSimp

end FoamWithBoundary

/-! ### Core prefoam structure -/

/-- A combinatorial unlabelled prefoam bounded by a closed web `W`.

All local seam cyclic orders `(Fin 3)` and interior vertex link data (`ClosedWeb.tetWeb`) are
determined without redundant gauge data: at each seam, slot `0` is the sheet inducing the opposite
orientation on the seam and slots `1, 2` are the two sheets inducing the seam orientation in
right-hand cyclic order. -/
structure FoamWithBoundary (W : ClosedWeb.{u}) : Type (u + 1) where
  /-- Interior singular tetrahedral vertices. -/
  Vertex : Type u
  /-- Oriented interval seams with endpoints at interior or boundary vertices. -/
  Seam : Type u
  /-- Oriented closed seam circles without vertices. -/
  SeamCircle : Type u
  /-- Connected oriented 2-dimensional facets. -/
  Facet : Type u
  /-- Oriented boundary components of facets. -/
  Boundary : Type u
  [finite_vertex : Finite Vertex]
  [finite_seam : Finite Seam]
  [finite_seamCircle : Finite SeamCircle]
  [finite_facet : Finite Facet]
  [finite_boundary : Finite Boundary]
  /-- Chirality (`true` positive, `false` negative) of the tetrahedral link at each vertex. -/
  chirality : Vertex → Bool
  /-- Pairing of interior and boundary seam-ends into oriented interval seams (`false` source,
  `true` target). -/
  seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool
  /-- A seam leaving an interior vertex (`false`) meets its local link sphere at a split (`true`),
  and a seam entering an interior vertex (`true`) meets its local link sphere at a merge
  (`false`). -/
  seamEnds_inl_snd : ∀ (v : Vertex) (k : Fin 4),
    (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2
  /-- Merges of `W` (`false`) are seam sources and splits of `W` (`true`) are seam targets. -/
  seamEnds_inr_snd : ∀ w : W.Vertex,
    (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2
  /-- Topological genus of each connected oriented facet. -/
  genus : Facet → ℕ
  /-- Assignment of each boundary component to the facet it bounds. -/
  boundaryFacet : Boundary → Facet
  /-- Boundary component containing each segmented side `(Seam × Fin 3) ⊕ W.Edge`. -/
  sideBoundary : (Seam × Fin 3) ⊕ W.Edge → Boundary
  /-- Boundary component formed by each circle side `(SeamCircle × Fin 3) ⊕ W.Circle`. -/
  circleBoundary : (SeamCircle × Fin 3) ⊕ W.Circle → Boundary
  /-- Two segmented sides lie on the same boundary component iff they lie in the same `nextSide`
  cycle. -/
  sideBoundary_eq_iff : ∀ x y,
    sideBoundary x = sideBoundary y ↔
      (FoamWithBoundary.nextSidePerm chirality seamEnds seamEnds_inl_snd
        seamEnds_inr_snd).SameCycle x y
  /-- Distinct circle sides form distinct vertex-free boundary components. -/
  circleBoundary_injective : Function.Injective circleBoundary
  /-- Segmented boundary components and vertex-free circle boundary components are disjoint. -/
  sideBoundary_ne_circleBoundary : ∀ x z, sideBoundary x ≠ circleBoundary z
  /-- Every boundary component is either a cycle of segmented sides or a vertex-free circle side. -/
  boundary_surjective : ∀ b, (∃ x, sideBoundary x = b) ∨ (∃ z, circleBoundary z = b)

attribute [instance] FoamWithBoundary.finite_vertex FoamWithBoundary.finite_seam
  FoamWithBoundary.finite_seamCircle FoamWithBoundary.finite_facet
  FoamWithBoundary.finite_boundary

/-- A closed unlabelled prefoam is a prefoam bounded by `ClosedWeb.empty`. -/
abbrev ClosedFoam : Type (u + 1) := FoamWithBoundary ClosedWeb.empty.{u}

namespace FoamWithBoundary

section BasicAPI

variable {W : ClosedWeb.{u}} (F : FoamWithBoundary W)

/-! ### Derived types, corners, endpoints, and boundary decomposition -/

/-- Segmented boundary sides: the three local sheet slots at each interval seam together with the
interval edges of `W`. -/
abbrev Side : Type u := (F.Seam × Fin 3) ⊕ W.Edge

/-- Vertex-free circle sides: the three local sheet slots at each circular seam together with the
vertex-free circles of `W`. -/
abbrev CircleSide : Type u := (F.SeamCircle × Fin 3) ⊕ W.Circle

/-- Facet corners: the six local link sectors at each interior vertex together with the three
half-edge corners at each boundary vertex of `W`. -/
abbrev Corner : Type u := (F.Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)

/-- The indexed family of boundary components belonging to a facet `f`. -/
abbrev FacetBoundary (f : F.Facet) : Type u := {b : F.Boundary // F.boundaryFacet b = f}

/-- Equivalence sending each corner of `F` to the side incident in direction `dir` (`true` for
incoming, `false` for outgoing). -/
def cornerSide (dir : Bool) : F.Corner ≃ F.Side :=
  cornerSideEquiv dir F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd

theorem cornerSide_def (dir : Bool) : F.cornerSide dir =
    cornerSideEquiv dir F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd := (rfl)

/-- Equivalence sending each corner of `F` to the side entering that corner. -/
abbrev cornerIncoming : F.Corner ≃ F.Side := F.cornerSide true

theorem cornerIncoming_def : F.cornerIncoming =
    cornerIncomingEquiv F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd := (rfl)

/-- Equivalence sending each corner of `F` to the side leaving that corner. -/
abbrev cornerOutgoing : F.Corner ≃ F.Side := F.cornerSide false

theorem cornerOutgoing_def : F.cornerOutgoing =
    cornerOutgoingEquiv F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd := (rfl)

@[simp] theorem cornerSide_inl (dir : Bool) (v : F.Vertex) (e : Fin 6) :
    F.cornerSide dir (Sum.inl (v, e)) =
      Sum.inl ((F.seamEnds
        (Sum.inl (v, ((ClosedWeb.tetWeb (F.chirality v)).ends.symm (e, dir)).1))).1,
        ((ClosedWeb.tetWeb (F.chirality v)).ends.symm (e, dir)).2) := (rfl)

@[simp] theorem cornerSide_inr (dir : Bool) (w : W.Vertex) (i : Fin 3) :
    F.cornerSide dir (Sum.inr (w, i)) =
      if (W.ends (w, i)).2 == dir then Sum.inr (W.ends (w, i)).1
      else Sum.inl ((F.seamEnds (Sum.inr w)).1, i) := (rfl)

@[simp] theorem cornerSide_symm_inl (dir : Bool) (s : F.Seam) (i : Fin 3) :
    (F.cornerSide dir).symm (Sum.inl (s, i)) =
      match F.seamEnds.symm (s, dir != decide (i = 0)) with
      | Sum.inl (v, k) => Sum.inl (v, ((ClosedWeb.tetWeb (F.chirality v)).ends (k, i)).1)
      | Sum.inr w => Sum.inr (w, i) := by
  rw [cornerSide_def, cornerSideEquiv_symm_inl]
  rcases F.seamEnds.symm (s, dir != decide (i = 0)) with ⟨v, k⟩ | w <;> rfl

@[simp] theorem cornerSide_symm_inr (dir : Bool) (e : W.Edge) :
    (F.cornerSide dir).symm (Sum.inr e) = Sum.inr (W.ends.symm (e, dir)) := by
  rw [cornerSide_def, cornerSideEquiv_symm_inr]

/-- Successor permutation stepping from each segmented side to the next side along the oriented
boundary of its facet. -/
def nextSide : Equiv.Perm F.Side :=
  nextSidePerm F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd

theorem nextSide_def : F.nextSide =
    nextSidePerm F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd := (rfl)

theorem nextSide_apply (x : F.Side) :
    F.nextSide x = F.cornerOutgoing (F.cornerIncoming.symm x) := (rfl)

@[simp] theorem cornerOutgoing_symm_nextSide (x : F.Side) :
    F.cornerOutgoing.symm (F.nextSide x) = F.cornerIncoming.symm x :=
  F.cornerOutgoing.symm_apply_apply (F.cornerIncoming.symm x)

@[simp] theorem cornerIncoming_symm_nextSide_symm (x : F.Side) :
    F.cornerIncoming.symm (F.nextSide.symm x) = F.cornerOutgoing.symm x :=
  F.cornerIncoming.symm_apply_apply (F.cornerOutgoing.symm x)

@[simp] theorem nextSide_cornerIncoming (c : F.Corner) :
    F.nextSide (F.cornerIncoming c) = F.cornerOutgoing c := by
  rw [nextSide_apply, Equiv.symm_apply_apply]

@[simp] theorem nextSide_symm_cornerOutgoing (c : F.Corner) :
    F.nextSide.symm (F.cornerOutgoing c) = F.cornerIncoming c := by
  apply F.nextSide.injective
  simp

/-- Underlying interior or boundary vertex of a corner. -/
def cornerVertex : F.Corner → F.Vertex ⊕ W.Vertex :=
  Sum.map Prod.fst Prod.fst

theorem cornerVertex_def (c : F.Corner) :
    F.cornerVertex c = Sum.map Prod.fst Prod.fst c := (rfl)

@[simp] theorem cornerVertex_inl (v : F.Vertex) (e : Fin 6) :
    F.cornerVertex (Sum.inl (v, e)) = Sum.inl v := (rfl)

@[simp] theorem cornerVertex_inr (w : W.Vertex) (i : Fin 3) :
    F.cornerVertex (Sum.inr (w, i)) = Sum.inr w := (rfl)

/-- Endpoint (interior or boundary vertex) of a segmented side in direction `dir` (`false` for
start, `true` for end) along its facet boundary walk. -/
def sideEndpoint (dir : Bool) (x : F.Side) : F.Vertex ⊕ W.Vertex :=
  F.cornerVertex ((F.cornerSide dir).symm x)

theorem sideEndpoint_def (dir : Bool) (x : F.Side) :
    F.sideEndpoint dir x = F.cornerVertex ((F.cornerSide dir).symm x) := (rfl)

/-- Starting vertex (interior or boundary) of a segmented side along its facet boundary walk. -/
abbrev sideStart : F.Side → F.Vertex ⊕ W.Vertex := F.sideEndpoint false

theorem sideStart_def (x : F.Side) :
    F.sideStart x = F.cornerVertex (F.cornerOutgoing.symm x) := (rfl)

/-- Ending vertex (interior or boundary) of a segmented side along its facet boundary walk. -/
abbrev sideEnd : F.Side → F.Vertex ⊕ W.Vertex := F.sideEndpoint true

theorem sideEnd_def (x : F.Side) :
    F.sideEnd x = F.cornerVertex (F.cornerIncoming.symm x) := (rfl)

/-- Consecutive sides in a facet boundary walk share their intermediate vertex. -/
@[simp] theorem sideStart_nextSide (x : F.Side) :
    F.sideStart (F.nextSide x) = F.sideEnd x := by
  rw [sideStart_def, cornerOutgoing_symm_nextSide, sideEnd_def]

/-- Endpoint (interior or boundary vertex) of an interval seam `s` (`false` for source, `true` for
target). -/
def seamEndpoint (dir : Bool) (s : F.Seam) : F.Vertex ⊕ W.Vertex :=
  Sum.map Prod.fst id (F.seamEnds.symm (s, dir))

theorem seamEndpoint_def (dir : Bool) (s : F.Seam) :
    F.seamEndpoint dir s = Sum.map Prod.fst id (F.seamEnds.symm (s, dir)) := (rfl)

/-- Source endpoint (interior or boundary vertex) of an interval seam `s`. -/
abbrev seamSource : F.Seam → F.Vertex ⊕ W.Vertex := F.seamEndpoint false

theorem seamSource_def (s : F.Seam) :
    F.seamSource s = Sum.map Prod.fst id (F.seamEnds.symm (s, false)) := (rfl)

/-- Target endpoint (interior or boundary vertex) of an interval seam `s`. -/
abbrev seamTarget : F.Seam → F.Vertex ⊕ W.Vertex := F.seamEndpoint true

theorem seamTarget_def (s : F.Seam) :
    F.seamTarget s = Sum.map Prod.fst id (F.seamEnds.symm (s, true)) := (rfl)

/-- Endpoint of a boundary web edge `e` in direction `dir`. -/
theorem sideEndpoint_inr (dir : Bool) (e : W.Edge) :
    F.sideEndpoint dir (Sum.inr e) = Sum.inr (W.incident (e, dir)) := by
  rw [sideEndpoint_def, cornerSide_symm_inr, cornerVertex_inr, W.incident_def]

/-- Every boundary web edge starts at its `W`-source. -/
@[simp] theorem sideStart_inr (e : W.Edge) :
    F.sideStart (Sum.inr e) = Sum.inr (W.source e) :=
  (F.sideEndpoint_inr false e).trans (congrArg Sum.inr (W.source_def e).symm)

/-- Every boundary web edge ends at its `W`-target. -/
@[simp] theorem sideEnd_inr (e : W.Edge) :
    F.sideEnd (Sum.inr e) = Sum.inr (W.target e) :=
  (F.sideEndpoint_inr true e).trans (congrArg Sum.inr (W.target_def e).symm)

/-- Endpoint of local sheet `i` along interval seam `s` in direction `dir`. -/
@[simp] theorem sideEndpoint_inl (dir : Bool) (s : F.Seam) (i : Fin 3) :
    F.sideEndpoint dir (Sum.inl (s, i)) = F.seamEndpoint (dir != decide (i = 0)) s := by
  rw [sideEndpoint_def, cornerSide_symm_inl, seamEndpoint_def]
  rcases F.seamEnds.symm (s, dir != decide (i = 0)) with ⟨v, k⟩ | w <;> rfl

/-- Sheet `0` along a seam `s` starts at `seamTarget s` (opposite to `s`). -/
theorem sideStart_inl_zero (s : F.Seam) : F.sideStart (Sum.inl (s, 0)) = F.seamTarget s := by simp

/-- Sheet `0` along a seam `s` ends at `seamSource s` (opposite to `s`). -/
theorem sideEnd_inl_zero (s : F.Seam) : F.sideEnd (Sum.inl (s, 0)) = F.seamSource s := by simp

/-- Sheets `1` and `2` along a seam `s` start at `seamSource s` (matching `s`). -/
theorem sideStart_inl_of_ne_zero (s : F.Seam) {i : Fin 3} (hi : i ≠ 0) :
    F.sideStart (Sum.inl (s, i)) = F.seamSource s := by simp [hi]

/-- Sheets `1` and `2` along a seam `s` end at `seamTarget s` (matching `s`). -/
theorem sideEnd_inl_of_ne_zero (s : F.Seam) {i : Fin 3} (hi : i ≠ 0) :
    F.sideEnd (Sum.inl (s, i)) = F.seamTarget s := by simp [hi]

@[simp] theorem sideBoundary_nextSide (x : F.Side) :
    F.sideBoundary (F.nextSide x) = F.sideBoundary x :=
  (F.sideBoundary_eq_iff _ _).mpr
    (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- Canonical bijection identifying the boundary components of `F` with the disjoint union of the
cycle quotient of `F.nextSide` and `F.CircleSide`. -/
noncomputable def boundaryEquiv :
    Quotient (Equiv.Perm.SameCycle.setoid F.nextSide) ⊕ F.CircleSide ≃ F.Boundary :=
  Equiv.ofBijective
    (Sum.elim
      (Quotient.lift F.sideBoundary fun x y h ↦ (F.sideBoundary_eq_iff x y).mpr h)
      F.circleBoundary)
    ⟨by
      rintro (q₁ | z₁) (q₂ | z₂) h
      · induction q₁ using Quotient.inductionOn with | _ x => ?_
        induction q₂ using Quotient.inductionOn with | _ y => ?_
        exact congrArg Sum.inl (Quotient.sound ((F.sideBoundary_eq_iff x y).mp h))
      · induction q₁ using Quotient.inductionOn with | _ x => ?_
        exact (F.sideBoundary_ne_circleBoundary x z₂ h).elim
      · induction q₂ using Quotient.inductionOn with | _ y => ?_
        exact (F.sideBoundary_ne_circleBoundary y z₁ h.symm).elim
      · exact congrArg Sum.inr (F.circleBoundary_injective h),
     fun b ↦ by
      rcases F.boundary_surjective b with ⟨x, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨Sum.inl (Quotient.mk _ x), rfl⟩
      · exact ⟨Sum.inr z, rfl⟩⟩

@[simp] theorem boundaryEquiv_inl_mk (x : F.Side) :
    F.boundaryEquiv (Sum.inl (Quotient.mk _ x)) = F.sideBoundary x := (rfl)

@[simp] theorem boundaryEquiv_inr (z : F.CircleSide) :
    F.boundaryEquiv (Sum.inr z) = F.circleBoundary z := (rfl)

/-- The number of boundary components of `F` equals the orbit count of `F.nextSide` plus the number
of vertex-free circle sides. -/
theorem card_boundary :
    Nat.card F.Boundary = orbitCount F.nextSide + Nat.card F.CircleSide := by
  rw [← Nat.card_congr F.boundaryEquiv, Nat.card_sum, orbitCount_def]

/-! ### Nonempty signed cyclic words on segmented boundary components -/

/-- Underlying signed 1-stratum of a segmented side: `(Sum.inl s, false)` for sheet `0` (`-s`),
`(Sum.inl s, true)` for sheets `1, 2` (`+s`), and `(Sum.inr e, true)` for boundary edge `+e`. -/
def signedSegment : F.Side → (F.Seam ⊕ W.Edge) × Bool
  | Sum.inl (s, i) => (Sum.inl s, decide (i ≠ 0))
  | Sum.inr e => (Sum.inr e, true)

@[simp] theorem signedSegment_inl (s : F.Seam) (i : Fin 3) :
    F.signedSegment (Sum.inl (s, i)) = (Sum.inl s, decide (i ≠ 0)) := (rfl)
theorem signedSegment_inl_zero (s : F.Seam) :
    F.signedSegment (Sum.inl (s, 0)) = (Sum.inl s, false) := (rfl)
theorem signedSegment_inl_one (s : F.Seam) :
    F.signedSegment (Sum.inl (s, 1)) = (Sum.inl s, true) := (rfl)
theorem signedSegment_inl_two (s : F.Seam) :
    F.signedSegment (Sum.inl (s, 2)) = (Sum.inl s, true) := (rfl)
@[simp] theorem signedSegment_inr (e : W.Edge) :
    F.signedSegment (Sum.inr e) = (Sum.inr e, true) := (rfl)

/-- The nonempty cyclic orbit of segmented sides traced by `F.nextSide` starting from `x`. -/
noncomputable def sideCycle (x : F.Side) : Cycle F.Side :=
  Function.periodicOrbit F.nextSide x

theorem sideCycle_def (x : F.Side) :
    F.sideCycle x = Function.periodicOrbit F.nextSide x := (rfl)

private theorem mem_periodicPts_nextSide (x : F.Side) : x ∈ Function.periodicPts F.nextSide :=
  F.nextSide.injective.mem_periodicPts x

@[simp] theorem mem_sideCycle_self (x : F.Side) : x ∈ F.sideCycle x :=
  Function.self_mem_periodicOrbit (F.mem_periodicPts_nextSide x)

@[simp] theorem sideCycle_ne_nil (x : F.Side) : F.sideCycle x ≠ Cycle.nil :=
  Function.periodicOrbit_eq_nil_iff_not_periodic_pt.not.mpr
    (not_not.mpr (F.mem_periodicPts_nextSide x))

@[simp] theorem nodup_sideCycle (x : F.Side) : (F.sideCycle x).Nodup :=
  Function.nodup_periodicOrbit

/-- Membership in `F.sideCycle x` characterizes sides on the same boundary component as `x`. -/
theorem mem_sideCycle_iff (x y : F.Side) :
    y ∈ F.sideCycle x ↔ F.sideBoundary x = F.sideBoundary y := by
  rw [sideCycle_def, F.nextSide.mem_periodicOrbit_iff_sameCycle, F.sideBoundary_eq_iff,
    F.nextSide_def]

@[simp] theorem sideCycle_nextSide (x : F.Side) :
    F.sideCycle (F.nextSide x) = F.sideCycle x :=
  Function.periodicOrbit_apply_eq (F.mem_periodicPts_nextSide x)

/-- Two segmented sides generate the exact same cyclic side orbit iff they lie on the same boundary
component. -/
theorem sideCycle_eq_iff (x y : F.Side) :
    F.sideCycle x = F.sideCycle y ↔ F.sideBoundary x = F.sideBoundary y := by
  refine ⟨fun h ↦ (F.mem_sideCycle_iff x y).mp (h ▸ F.mem_sideCycle_self y), fun h ↦ ?_⟩
  obtain ⟨n, rfl⟩ :=
    (Function.mem_periodicOrbit_iff (F.mem_periodicPts_nextSide x)).mp
      ((F.mem_sideCycle_iff x y).mpr h)
  exact (Function.periodicOrbit_apply_iterate_eq (F.mem_periodicPts_nextSide x) n).symm

/-- A fixed point of `F.nextSide` forms a singleton cyclic side orbit. -/
theorem sideCycle_of_nextSide_eq {x : F.Side} (hx : F.nextSide x = x) :
    F.sideCycle x = ([x] : List F.Side) :=
  Function.IsFixedPt.periodicOrbit_eq hx

/-- Every adjacent pair in `F.sideCycle x` steps by `F.nextSide`. -/
theorem chain_sideCycle (x : F.Side) :
    (F.sideCycle x).Chain (fun a b ↦ F.nextSide a = b) := by
  rw [sideCycle_def, Function.periodicOrbit_chain' _ (F.mem_periodicPts_nextSide x)]
  intro n
  rw [Function.iterate_succ_apply']

/-- Stepping along `F.sideCycle x` via `Cycle.next` agrees with `F.nextSide`. -/
@[simp] theorem next_sideCycle [DecidableEq F.Side] (x y : F.Side) (hy : y ∈ F.sideCycle x) :
    (F.sideCycle x).next (F.nodup_sideCycle x) y hy = F.nextSide y :=
  Function.next_periodicOrbit hy

/-- Nonempty signed cyclic word of seams and boundary edges along the segmented boundary component
containing `x`. -/
noncomputable def sideWord (x : F.Side) : Cycle ((F.Seam ⊕ W.Edge) × Bool) :=
  (F.sideCycle x).map F.signedSegment

theorem sideWord_def (x : F.Side) :
    F.sideWord x = (F.sideCycle x).map F.signedSegment := (rfl)

theorem mem_sideWord_iff {x : F.Side} {p : (F.Seam ⊕ W.Edge) × Bool} :
    p ∈ F.sideWord x ↔ ∃ y, F.sideBoundary x = F.sideBoundary y ∧ F.signedSegment y = p := by
  simp [sideWord_def, F.mem_sideCycle_iff]

@[simp] theorem sideWord_ne_nil (x : F.Side) : F.sideWord x ≠ Cycle.nil := by
  simp [sideWord_def, F.sideCycle_ne_nil]

theorem sideWord_eq_of_sideBoundary_eq {x y : F.Side}
    (h : F.sideBoundary x = F.sideBoundary y) : F.sideWord x = F.sideWord y := by
  rw [sideWord_def, sideWord_def, (F.sideCycle_eq_iff x y).mpr h]

/-! ### Local occurrence fibres, handshake counts, and boundary restriction -/

/-- Facet containing a segmented side `x`. -/
def sideFacet (x : F.Side) : F.Facet :=
  F.boundaryFacet (F.sideBoundary x)

@[simp] theorem sideFacet_def (x : F.Side) :
    F.sideFacet x = F.boundaryFacet (F.sideBoundary x) := (rfl)

/-- Facet containing a vertex-free circle side `z`. -/
def circleSideFacet (z : F.CircleSide) : F.Facet :=
  F.boundaryFacet (F.circleBoundary z)

@[simp] theorem circleSideFacet_def (z : F.CircleSide) :
    F.circleSideFacet z = F.boundaryFacet (F.circleBoundary z) := (rfl)

theorem sideFacet_nextSide (x : F.Side) :
    F.sideFacet (F.nextSide x) = F.sideFacet x := by
  rw [sideFacet, sideBoundary_nextSide, sideFacet]

/-- Indexed family of the three local facet occurrences meeting interval seam `s`. Distinct slots
may evaluate to the same global facet when a sheet meets `s` along multiple local branches. -/
def seamSheetFacet (s : F.Seam) (i : Fin 3) : F.Facet :=
  F.sideFacet (Sum.inl (s, i))

@[simp] theorem seamSheetFacet_def (s : F.Seam) (i : Fin 3) :
    F.seamSheetFacet s i = F.sideFacet (Sum.inl (s, i)) := (rfl)

/-- Indexed family of the three local facet occurrences meeting circular seam `c`. -/
def seamCircleSheetFacet (c : F.SeamCircle) (i : Fin 3) : F.Facet :=
  F.circleSideFacet (Sum.inl (c, i))

@[simp] theorem seamCircleSheetFacet_def (c : F.SeamCircle) (i : Fin 3) :
    F.seamCircleSheetFacet c i = F.circleSideFacet (Sum.inl (c, i)) := (rfl)

/-- Unique facet meeting a boundary web edge `e`. -/
def boundaryEdgeFacet (e : W.Edge) : F.Facet :=
  F.sideFacet (Sum.inr e)

@[simp] theorem boundaryEdgeFacet_def (e : W.Edge) :
    F.boundaryEdgeFacet e = F.sideFacet (Sum.inr e) := (rfl)

/-- Unique facet meeting a boundary web circle `c`. -/
def boundaryCircleFacet (c : W.Circle) : F.Facet :=
  F.circleSideFacet (Sum.inr c)

@[simp] theorem boundaryCircleFacet_def (c : W.Circle) :
    F.boundaryCircleFacet c = F.circleSideFacet (Sum.inr c) := (rfl)

/-- Indexed family of the six local facet sectors around an interior tetrahedral vertex `v`. -/
def vertexSectorFacet (v : F.Vertex) (e : Fin 6) : F.Facet :=
  F.sideFacet (F.cornerOutgoing (Sum.inl (v, e)))

theorem vertexSectorFacet_def (v : F.Vertex) (e : Fin 6) :
    F.vertexSectorFacet v e = F.sideFacet (F.cornerOutgoing (Sum.inl (v, e))) := (rfl)

theorem vertexSectorFacet_eq_incoming (v : F.Vertex) (e : Fin 6) :
    F.vertexSectorFacet v e = F.sideFacet (F.cornerIncoming (Sum.inl (v, e))) := by
  rw [vertexSectorFacet, ← F.nextSide_cornerIncoming, F.sideFacet_nextSide]

/-- Seam-end handshake identity: four ends per interior vertex plus one end per boundary vertex
equals two ends per interval seam. -/
theorem four_mul_card_vertex_add_card_boundaryVertex_eq_two_mul_card_seam :
    4 * Nat.card F.Vertex + Nat.card W.Vertex = 2 * Nat.card F.Seam := by
  have h := Nat.card_congr F.seamEnds
  simp only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  omega

/-- Corners and segmented sides of `F` have equal cardinality. -/
theorem card_corner_eq_card_side : Nat.card F.Corner = Nat.card F.Side :=
  Nat.card_congr F.cornerIncoming

/-- Corner-side handshake identity: six corners per interior vertex plus three corners per boundary
vertex equals three sheet sides per interval seam plus one side per boundary edge. -/
theorem six_mul_card_vertex_add_three_mul_card_boundaryVertex_eq_three_mul_card_seam_add_card_edge :
    6 * Nat.card F.Vertex + 3 * Nat.card W.Vertex =
      3 * Nat.card F.Seam + Nat.card W.Edge := by
  have h := F.card_corner_eq_card_side
  simp only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 6),
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h
  omega

/-- Boundary merges of `W` are characterized by initiating their incident seam in `F`. -/
theorem isMerge_iff_seamEnds_inr_snd (w : W.Vertex) :
    W.IsMerge w ↔ (F.seamEnds (Sum.inr w)).2 = false := by
  rw [W.isMerge_def, F.seamEnds_inr_snd]

/-- Boundary splits of `W` are characterized by terminating their incident seam in `F`. -/
theorem isSplit_iff_seamEnds_inr_snd (w : W.Vertex) :
    W.IsSplit w ↔ (F.seamEnds (Sum.inr w)).2 = true := by
  rw [W.isSplit_def, F.seamEnds_inr_snd]

/-- A boundary corner `(w, i)` meets boundary edge `e` in direction `dir` if and only if
`W.ends (w, i) = (e, dir)`. -/
theorem cornerSide_inr_eq_inr_iff (dir : Bool) (w : W.Vertex) (i : Fin 3) (e : W.Edge) :
    F.cornerSide dir (Sum.inr (w, i)) = Sum.inr e ↔ W.ends (w, i) = (e, dir) := by
  rw [F.cornerSide_inr]
  rcases W.ends (w, i) with ⟨e', _ | _⟩ <;> cases dir <;> simp

/-- At every boundary corner `(w, i)`, exactly one of `F.cornerIncoming` and `F.cornerOutgoing` is
a boundary edge `Sum.inr e`, recovering `some (W.ends (w, i))` without referencing `W.ends` on the
right-hand side. -/
theorem some_ends_eq_match_cornerIncoming_cornerOutgoing (w : W.Vertex) (i : Fin 3) :
    some (W.ends (w, i)) =
      match F.cornerIncoming (Sum.inr (w, i)), F.cornerOutgoing (Sum.inr (w, i)) with
      | Sum.inr e, Sum.inl _ => some (e, true)
      | Sum.inl _, Sum.inr e => some (e, false)
      | _, _ => none := by
  rw [F.cornerSide_inr, F.cornerSide_inr]
  rcases W.ends (w, i) with ⟨e, _ | _⟩ <;> rfl

/-! ### Facet Euler characteristic and nilvalent prefoams -/

/-- Number of boundary components of a facet `f`. -/
noncomputable def numBoundaryComponents (f : F.Facet) : ℕ :=
  Nat.card (F.FacetBoundary f)

theorem numBoundaryComponents_def (f : F.Facet) :
    F.numBoundaryComponents f = Nat.card (F.FacetBoundary f) := (rfl)

/-- When `F.boundaryFacet` is bijective, every facet has a unique boundary component. -/
theorem numBoundaryComponents_eq_one_of_bijective_boundaryFacet
    (h : Function.Bijective F.boundaryFacet) (f : F.Facet) :
    F.numBoundaryComponents f = 1 := by
  rw [numBoundaryComponents_def]
  obtain ⟨b, hb⟩ := h.2 f
  have : Unique (F.FacetBoundary f) :=
    { default := ⟨b, hb⟩
      uniq := fun ⟨b', hb'⟩ ↦ Subtype.ext (h.1 (hb'.trans hb.symm)) }
  exact Nat.card_unique

/-- Euler characteristic `χ(f) = 2 - 2g(f) - b(f)` of a compact connected oriented surface facet
of genus `g(f)` with `b(f)` boundary components. -/
noncomputable def facetEulerChar (f : F.Facet) : ℤ :=
  2 - 2 * (F.genus f : ℤ) - (F.numBoundaryComponents f : ℤ)

theorem facetEulerChar_def (f : F.Facet) :
    F.facetEulerChar f = 2 - 2 * (F.genus f : ℤ) - (F.numBoundaryComponents f : ℤ) := (rfl)

/-- Absence of interval seams forces `F.Vertex` to be empty via `seamEnds`. -/
theorem isEmpty_vertex_of_isEmpty_seam [IsEmpty F.Seam] : IsEmpty F.Vertex :=
  ⟨fun v ↦ isEmptyElim (F.seamEnds (Sum.inl (v, 0))).1⟩

/-- Absence of interval seams forces `W.Vertex` to be empty via `seamEnds`. -/
theorem isEmpty_boundary_vertex_of_isEmpty_seam [IsEmpty F.Seam] : IsEmpty W.Vertex :=
  ⟨fun w ↦ isEmptyElim (F.seamEnds (Sum.inr w)).1⟩

/-- Absence of interval seams forces `W.Edge` to be empty. -/
theorem isEmpty_boundary_edge_of_isEmpty_seam [IsEmpty F.Seam] : IsEmpty W.Edge :=
  have := F.isEmpty_boundary_vertex_of_isEmpty_seam
  ClosedWeb.isEmpty_edge_of_isEmpty_vertex W

/-- Absence of interval seams forces `F.Side` to be empty. -/
theorem isEmpty_side_of_isEmpty_seam [IsEmpty F.Seam] : IsEmpty F.Side :=
  have := F.isEmpty_boundary_edge_of_isEmpty_seam
  inferInstance

/-- A prefoam is nilvalent when it has no interior singular vertices, interval seams, or circular
seams. -/
def IsNilvalent : Prop :=
  IsEmpty F.Vertex ∧ IsEmpty F.Seam ∧ IsEmpty F.SeamCircle

theorem isNilvalent_def :
    F.IsNilvalent ↔ IsEmpty F.Vertex ∧ IsEmpty F.Seam ∧ IsEmpty F.SeamCircle := Iff.rfl

/-- Absence of seams automatically forces `F.Vertex` to be empty via `seamEnds`. -/
theorem isNilvalent_iff : F.IsNilvalent ↔ IsEmpty F.Seam ∧ IsEmpty F.SeamCircle :=
  ⟨fun ⟨_, hs, hc⟩ ↦ ⟨hs, hc⟩, fun ⟨hs, hc⟩ ↦
    have := hs; ⟨F.isEmpty_vertex_of_isEmpty_seam, hs, hc⟩⟩

end BasicAPI

/-- On a nilvalent prefoam, boundary components correspond bijectively to the circles of `W`. -/
noncomputable def IsNilvalent.circleEquivBoundary {W : ClosedWeb.{u}} {F : FoamWithBoundary W}
    (h : F.IsNilvalent) : W.Circle ≃ F.Boundary :=
  have := h.2.1
  Equiv.ofBijective (fun c ↦ F.circleBoundary (Sum.inr c))
    ⟨fun _ _ hab ↦ Sum.inr.inj (F.circleBoundary_injective hab),
     fun b ↦ by
      rcases F.boundary_surjective b with ⟨x, rfl⟩ | ⟨⟨sc, _⟩ | c, rfl⟩
      · exact F.isEmpty_side_of_isEmpty_seam.elim x
      · exact h.2.2.elim sc
      · exact ⟨c, rfl⟩⟩

@[simp] theorem IsNilvalent.circleEquivBoundary_apply {W : ClosedWeb.{u}} {F : FoamWithBoundary W}
    (h : F.IsNilvalent) (c : W.Circle) :
    h.circleEquivBoundary c = F.circleBoundary (Sum.inr c) := (rfl)

end FoamWithBoundary

end TauCeti
