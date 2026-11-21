/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Cycle
public import Mathlib.Dynamics.PeriodicPts.Defs
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import TauCeti.KnotTheory.Foam.ClosedWeb.Tetrahedron
import Mathlib.Data.Fintype.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import TauCeti.GroupTheory.Perm.Basic

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
* `TauCeti.FoamWithBoundary.IsoOver`, `Iso`: structure-preserving prefoam isomorphisms over a
  boundary web isomorphism (or fixing `W`), together with `relabelOver`, `mapBoundary`, and
  `empty`.

## References

* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definitions 2.1 and 3.1 (extended here to allow repeated global facet-seam
  incidences via local occurrence slots).
* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1 and Remark 2.2.
-/

public section

namespace TauCeti

universe u v w t

namespace FoamWithBoundary

/-! ### Slot-orientation lemma and corner-side equivalences -/

private theorem ends_snd_eq_iff (T : ClosedWeb.{u}) (k : T.Vertex) (i : Fin 3) (b : Bool) :
    (T.ends (k, i)).2 = b ↔ (b != decide (i = 0)) = !(T.ends (k, 0)).2 := by
  have h : (T.ends (k, i)).2 = (T.ends (k, 0)).2 ↔ decide (i = 0) = true := by simp
  revert h
  generalize (T.ends (k, i)).2 = x, (T.ends (k, 0)).2 = y, decide (i = 0) = z
  cases x <;> cases y <;> cases z <;> cases b <;> decide

/-- Forward map sending each interior or boundary corner to the side incident in direction `dir`
(`true` for incoming, `false` for outgoing). -/
@[expose] def cornerSideFun (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool) :
    (Vertex × Fin 6) ⊕ (W.Vertex × Fin 3) → (Seam × Fin 3) ⊕ W.Edge
  | Sum.inl (v, e) =>
    let ki := (ClosedWeb.tetWeb (chirality v)).ends.symm (e, dir)
    Sum.inl ((seamEnds (Sum.inl (v, ki.1))).1, ki.2)
  | Sum.inr (w, i) =>
    let eb := W.ends (w, i)
    if eb.2 == dir then Sum.inr eb.1 else Sum.inl ((seamEnds (Sum.inr w)).1, i)

/-- Inverse map sending each side to the corner it meets in direction `dir` (`true` for incoming,
`false` for outgoing) along its facet boundary orientation. -/
@[expose] def cornerSideInv (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
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
@[expose] def cornerSideEquiv (dir : Bool) {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    ((Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)) ≃ ((Seam × Fin 3) ⊕ W.Edge) where
  toFun := cornerSideFun dir chirality seamEnds
  invFun := cornerSideInv dir chirality seamEnds
  left_inv := by exact leftInverse_cornerSideInv dir chirality seamEnds h_inl h_inr
  right_inv := by exact rightInverse_cornerSideInv dir chirality seamEnds h_inl h_inr

/-- Forward map sending each interior or boundary corner to the side entering that corner. -/
abbrev cornerIncomingFun {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideFun true Vertex Seam W

/-- Inverse map sending each side to the corner it enters along its facet boundary orientation. -/
abbrev cornerIncomingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideInv true Vertex Seam W

/-- Equivalence between corners and their incoming facet-boundary sides. -/
abbrev cornerIncomingEquiv {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideEquiv true Vertex Seam W

/-- Forward map sending each interior or boundary corner to the side leaving that corner. -/
abbrev cornerOutgoingFun {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideFun false Vertex Seam W

/-- Inverse map sending each side to the corner it leaves along its facet boundary orientation. -/
abbrev cornerOutgoingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideInv false Vertex Seam W

/-- Equivalence between corners and their outgoing facet-boundary sides. -/
abbrev cornerOutgoingEquiv {Vertex Seam : Type u} {W : ClosedWeb.{u}} :=
  @cornerSideEquiv false Vertex Seam W

/-- Successor permutation advancing each side along the oriented boundary of its facet through the
corner it enters. -/
@[expose] def nextSidePerm {Vertex Seam : Type u} {W : ClosedWeb.{u}}
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

private theorem cornerSideFun_comp (dir : Bool)
    {Vertex₁ Seam₁ : Type u} {W₁ : ClosedWeb.{u}}
    {Vertex₂ Seam₂ : Type v} {W₂ : ClosedWeb.{v}}
    (φ : W₁.Iso W₂) (eV : Vertex₁ ≃ Vertex₂) (eS : Seam₁ ≃ Seam₂)
    (chirality₁ : Vertex₁ → Bool) (chirality₂ : Vertex₂ → Bool)
    (seamEnds₁ : (Vertex₁ × Fin 4) ⊕ W₁.Vertex ≃ Seam₁ × Bool)
    (seamEnds₂ : (Vertex₂ × Fin 4) ⊕ W₂.Vertex ≃ Seam₂ × Bool)
    (h_chir : ∀ v, chirality₂ (eV v) = chirality₁ v)
    (h_seam : ∀ x,
      seamEnds₂ (Sum.map (Prod.map eV id) φ.vertex x) = Prod.map eS id (seamEnds₁ x))
    (c : (Vertex₁ × Fin 6) ⊕ (W₁.Vertex × Fin 3)) :
    cornerSideFun dir chirality₂ seamEnds₂
        (((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
          (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) c) =
      ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge)
        (cornerSideFun dir chirality₁ seamEnds₁ c) := by
  rcases c with ⟨v, e⟩ | ⟨w, i⟩
  · simp only [Equiv.sumCongr_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Sum.map_inl,
      Prod.map_apply, cornerSideFun, h_chir v]
    set ki := (ClosedWeb.tetWeb (chirality₁ v)).ends.symm (e, dir)
    have hse := congrArg Prod.fst (h_seam (Sum.inl (v, ki.1)))
    simp only [Sum.map_inl, Prod.map_apply, Prod.map_fst, id_eq] at hse
    rw [hse]
  · simp only [Equiv.sumCongr_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Sum.map_inr,
      Prod.map_apply, cornerSideFun, φ.map_ends_apply w i]
    have hse := congrArg Prod.fst (h_seam (Sum.inr w))
    simp only [Sum.map_inr, Prod.map_fst] at hse
    cases (W₁.ends (w, i)).2 == dir <;> simp [hse]

private theorem nextSidePerm_eq_permCongr
    {Vertex₁ Seam₁ : Type u} {W₁ : ClosedWeb.{u}}
    {Vertex₂ Seam₂ : Type v} {W₂ : ClosedWeb.{v}}
    (φ : W₁.Iso W₂) (eV : Vertex₁ ≃ Vertex₂) (eS : Seam₁ ≃ Seam₂)
    (chirality₁ : Vertex₁ → Bool) (chirality₂ : Vertex₂ → Bool)
    (seamEnds₁ : (Vertex₁ × Fin 4) ⊕ W₁.Vertex ≃ Seam₁ × Bool)
    (seamEnds₂ : (Vertex₂ × Fin 4) ⊕ W₂.Vertex ≃ Seam₂ × Bool)
    (h_inl₁ : ∀ v k,
      (seamEnds₁ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₁ v)).ends (k, 0)).2)
    (h_inr₁ : ∀ w, (seamEnds₁ (Sum.inr w)).2 = (W₁.ends (w, 0)).2)
    (h_inl₂ : ∀ v k,
      (seamEnds₂ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₂ v)).ends (k, 0)).2)
    (h_inr₂ : ∀ w, (seamEnds₂ (Sum.inr w)).2 = (W₂.ends (w, 0)).2)
    (h_chir : ∀ v, chirality₂ (eV v) = chirality₁ v)
    (h_seam : ∀ x,
      seamEnds₂ (Sum.map (Prod.map eV id) φ.vertex x) = Prod.map eS id (seamEnds₁ x)) :
    nextSidePerm chirality₂ seamEnds₂ h_inl₂ h_inr₂ =
      ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge).permCongr
        (nextSidePerm chirality₁ seamEnds₁ h_inl₁ h_inr₁) := by
  set eSide := (eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge
  ext y
  obtain ⟨x, rfl⟩ := eSide.surjective y
  obtain ⟨c, rfl⟩ := (cornerSideEquiv true chirality₁ seamEnds₁ h_inl₁ h_inr₁).surjective x
  have hcs (dir : Bool) : cornerSideEquiv dir chirality₂ seamEnds₂ h_inl₂ h_inr₂
      (((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
        (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) c) =
      eSide (cornerSideEquiv dir chirality₁ seamEnds₁ h_inl₁ h_inr₁ c) :=
    cornerSideFun_comp dir φ eV eS chirality₁ chirality₂ seamEnds₁ seamEnds₂ h_chir h_seam c
  rw [Equiv.permCongr_apply, eSide.symm_apply_apply, ← hcs true]
  dsimp only [nextSidePerm, cornerIncomingEquiv, cornerOutgoingEquiv, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hcs false]

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
  rw [sideCycle_def, Function.mem_periodicOrbit_iff (F.mem_periodicPts_nextSide x),
    F.sideBoundary_eq_iff, ← F.nextSide_def]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, by simpa [Equiv.Perm.iterate_eq_pow] using hn⟩, fun hxy ↦ ?_⟩
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  exact ⟨n, by simpa [Equiv.Perm.iterate_eq_pow] using hn⟩

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
    F.sideCycle x = ([x] : List F.Side) := by
  have hm : Function.minimalPeriod F.nextSide x = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hx
  simp [sideCycle_def, Function.periodicOrbit_def, hm]

/-- Every adjacent pair in `F.sideCycle x` steps by `F.nextSide`. -/
theorem chain_sideCycle (x : F.Side) :
    (F.sideCycle x).Chain (fun a b ↦ F.nextSide a = b) := by
  rw [sideCycle_def, Function.periodicOrbit_chain' _ (F.mem_periodicPts_nextSide x)]
  intro n
  rw [Function.iterate_succ_apply']

/-- Stepping along `F.sideCycle x` via `Cycle.next` agrees with `F.nextSide`. -/
@[simp] theorem next_sideCycle [DecidableEq F.Side] (x y : F.Side) (hy : y ∈ F.sideCycle x) :
    (F.sideCycle x).next (F.nodup_sideCycle x) y hy = F.nextSide y := by
  have hcongr : ∀ {c₁ c₂ : Cycle F.Side} (_ : c₁ = c₂) (hn₁ : c₁.Nodup) (hn₂ : c₂.Nodup)
      (hy₁ : y ∈ c₁) (hy₂ : y ∈ c₂), c₁.next hn₁ y hy₁ = c₂.next hn₂ y hy₂ := by
    rintro _ _ rfl _ _ _ _; rfl
  have hxy : F.sideCycle x = F.sideCycle y :=
    (F.sideCycle_eq_iff x y).mpr ((F.mem_sideCycle_iff x y).mp hy)
  rw [hcongr hxy _ (F.nodup_sideCycle y) _ (F.mem_sideCycle_self y)]
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (F.mem_periodicPts_nextSide y)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rcases k with _ | d
  · have hfix : F.nextSide y = y := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hk
    rw [hcongr (F.sideCycle_of_nextSide_eq hfix) _ (by simp) _ (by simp)]
    exact hfix.symm
  · have hcyc : F.sideCycle y =
        (y :: F.nextSide y :: (List.range d).map (fun m ↦ F.nextSide^[m + 2] y) :
          List F.Side) := by
      rw [sideCycle_def, Function.periodicOrbit_def, hk, List.range_succ_eq_map, List.map_cons,
        List.map_map, List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl
    rw [hcongr hcyc _ (hcyc ▸ F.nodup_sideCycle y) _ (by simp)]
    exact List.next_cons_cons_eq _ y (F.nextSide y) (List.mem_cons_self ..)

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

/-! ### Isomorphisms, relabelling, boundary transport, and empty prefoam -/

/-- A combinatorial prefoam isomorphism from `F : FoamWithBoundary W` to `G : FoamWithBoundary V`
lying over a boundary web isomorphism `φ : W.Iso V`. -/
@[ext]
structure IsoOver {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (φ : W.Iso V)
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) : Type (max u v) where
  /-- Bijection on interior singular vertices. -/
  vertex : F.Vertex ≃ G.Vertex
  /-- Bijection on interval seams. -/
  seam : F.Seam ≃ G.Seam
  /-- Bijection on circular seams. -/
  seamCircle : F.SeamCircle ≃ G.SeamCircle
  /-- Bijection on facets. -/
  facet : F.Facet ≃ G.Facet
  /-- Bijection on boundary components. -/
  boundary : F.Boundary ≃ G.Boundary
  /-- Preservation of vertex chiralities. -/
  map_chirality : ∀ v, G.chirality (vertex v) = F.chirality v
  /-- Compatibility with seam-end incidence and orientations. -/
  map_seamEnds : ∀ x,
    G.seamEnds (Sum.map (Prod.map vertex id) φ.vertex x) = Prod.map seam id (F.seamEnds x)
  /-- Preservation of facet genus. -/
  map_genus : ∀ f, G.genus (facet f) = F.genus f
  /-- Compatibility with the boundary-to-facet map. -/
  map_boundaryFacet : ∀ b, G.boundaryFacet (boundary b) = facet (F.boundaryFacet b)
  /-- Compatibility with segmented side boundary assignments. -/
  map_sideBoundary : ∀ x,
    G.sideBoundary (Sum.map (Prod.map seam id) φ.edge x) = boundary (F.sideBoundary x)
  /-- Compatibility with vertex-free circle side boundary assignments. -/
  map_circleBoundary : ∀ z,
    G.circleBoundary (Sum.map (Prod.map seamCircle id) φ.circle z) = boundary (F.circleBoundary z)

attribute [simp] IsoOver.map_chirality IsoOver.map_genus IsoOver.map_boundaryFacet

/-- A boundary-fixing isomorphism of prefoams over the same closed web `W`. -/
abbrev Iso {W : ClosedWeb.{u}} (F G : FoamWithBoundary W) : Type u :=
  F.IsoOver (ClosedWeb.Iso.refl W) G

namespace IsoOver

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}} {T : ClosedWeb.{t}}

section Cast

variable {φ₁ φ₂ φ₃ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}

/-- Reindex the underlying boundary web isomorphism along an equality. -/
def cast (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) : F.IsoOver φ₂ G := by subst h; exact ψ

@[simp] theorem cast_vertex (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).vertex = ψ.vertex := by subst h; rfl
@[simp] theorem cast_seam (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).seam = ψ.seam := by subst h; rfl
@[simp] theorem cast_seamCircle (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).seamCircle = ψ.seamCircle := by subst h; rfl
@[simp] theorem cast_facet (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).facet = ψ.facet := by subst h; rfl
@[simp] theorem cast_boundary (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).boundary = ψ.boundary := by subst h; rfl
@[simp] theorem cast_rfl (ψ : F.IsoOver φ₁ G) : ψ.cast rfl = ψ := (rfl)
@[simp] theorem cast_cast (h₁ : φ₁ = φ₂) (h₂ : φ₂ = φ₃) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h₁).cast h₂ = ψ.cast (h₁.trans h₂) := by subst h₁ h₂; rfl

end Cast

section InducedEquiv

variable {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V} (ψ : F.IsoOver φ G)

/-- Equivalence on segmented sides induced by `ψ : F.IsoOver φ G`. -/
def sideEquiv : F.Side ≃ G.Side :=
  (ψ.seam.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge

theorem sideEquiv_def :
    ψ.sideEquiv = (ψ.seam.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge := (rfl)

@[simp] theorem sideEquiv_inl (s : F.Seam) (i : Fin 3) :
    ψ.sideEquiv (Sum.inl (s, i)) = Sum.inl (ψ.seam s, i) := (rfl)
@[simp] theorem sideEquiv_inr (e : W.Edge) :
    ψ.sideEquiv (Sum.inr e) = Sum.inr (φ.edge e) := (rfl)
@[simp] theorem sideEquiv_symm_inl (s : G.Seam) (i : Fin 3) :
    ψ.sideEquiv.symm (Sum.inl (s, i)) = Sum.inl (ψ.seam.symm s, i) := (rfl)
@[simp] theorem sideEquiv_symm_inr (e : V.Edge) :
    ψ.sideEquiv.symm (Sum.inr e) = Sum.inr (φ.edge.symm e) := (rfl)

@[simp] theorem map_sideBoundary_sideEquiv (x : F.Side) :
    G.sideBoundary (ψ.sideEquiv x) = ψ.boundary (F.sideBoundary x) := by
  simpa [sideEquiv_def] using ψ.map_sideBoundary x

/-- Equivalence on circle sides induced by `ψ : F.IsoOver φ G`. -/
def circleSideEquiv : F.CircleSide ≃ G.CircleSide :=
  (ψ.seamCircle.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle

theorem circleSideEquiv_def :
    ψ.circleSideEquiv = (ψ.seamCircle.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle := (rfl)

@[simp] theorem circleSideEquiv_inl (c : F.SeamCircle) (i : Fin 3) :
    ψ.circleSideEquiv (Sum.inl (c, i)) = Sum.inl (ψ.seamCircle c, i) := (rfl)
@[simp] theorem circleSideEquiv_inr (c : W.Circle) :
    ψ.circleSideEquiv (Sum.inr c) = Sum.inr (φ.circle c) := (rfl)
@[simp] theorem circleSideEquiv_symm_inl (c : G.SeamCircle) (i : Fin 3) :
    ψ.circleSideEquiv.symm (Sum.inl (c, i)) = Sum.inl (ψ.seamCircle.symm c, i) := (rfl)
@[simp] theorem circleSideEquiv_symm_inr (c : V.Circle) :
    ψ.circleSideEquiv.symm (Sum.inr c) = Sum.inr (φ.circle.symm c) := (rfl)

@[simp] theorem map_circleBoundary_circleSideEquiv (z : F.CircleSide) :
    G.circleBoundary (ψ.circleSideEquiv z) = ψ.boundary (F.circleBoundary z) := by
  simpa [circleSideEquiv_def] using ψ.map_circleBoundary z

/-- Equivalence on corners induced by `ψ : F.IsoOver φ G`. -/
def cornerEquiv : F.Corner ≃ G.Corner :=
  (ψ.vertex.prodCongr (Equiv.refl (Fin 6))).sumCongr (φ.vertex.prodCongr (Equiv.refl (Fin 3)))

theorem cornerEquiv_def : ψ.cornerEquiv =
    (ψ.vertex.prodCongr (Equiv.refl (Fin 6))).sumCongr
      (φ.vertex.prodCongr (Equiv.refl (Fin 3))) := (rfl)

@[simp] theorem cornerEquiv_inl (v : F.Vertex) (e : Fin 6) :
    ψ.cornerEquiv (Sum.inl (v, e)) = Sum.inl (ψ.vertex v, e) := (rfl)
@[simp] theorem cornerEquiv_inr (w : W.Vertex) (i : Fin 3) :
    ψ.cornerEquiv (Sum.inr (w, i)) = Sum.inr (φ.vertex w, i) := (rfl)
@[simp] theorem cornerEquiv_symm_inl (v : G.Vertex) (e : Fin 6) :
    ψ.cornerEquiv.symm (Sum.inl (v, e)) = Sum.inl (ψ.vertex.symm v, e) := (rfl)
@[simp] theorem cornerEquiv_symm_inr (w : V.Vertex) (i : Fin 3) :
    ψ.cornerEquiv.symm (Sum.inr (w, i)) = Sum.inr (φ.vertex.symm w, i) := (rfl)

end InducedEquiv

/-- Identity isomorphism of `F` over `ClosedWeb.Iso.refl W`. -/
def refl (F : FoamWithBoundary W) : F.Iso F where
  vertex := Equiv.refl _
  seam := Equiv.refl _
  seamCircle := Equiv.refl _
  facet := Equiv.refl _
  boundary := Equiv.refl _
  map_chirality _ := rfl
  map_seamEnds x := by rcases x with ⟨v, k⟩ | w <;> simp
  map_genus _ := rfl
  map_boundaryFacet _ := rfl
  map_sideBoundary x := by rcases x with ⟨s, i⟩ | e <;> simp
  map_circleBoundary z := by rcases z with ⟨c, i⟩ | c <;> simp

@[simp] theorem refl_vertex (F : FoamWithBoundary W) : (refl F).vertex = Equiv.refl _ := (rfl)
@[simp] theorem refl_seam (F : FoamWithBoundary W) : (refl F).seam = Equiv.refl _ := (rfl)
@[simp] theorem refl_seamCircle (F : FoamWithBoundary W) :
    (refl F).seamCircle = Equiv.refl _ := (rfl)
@[simp] theorem refl_facet (F : FoamWithBoundary W) : (refl F).facet = Equiv.refl _ := (rfl)
@[simp] theorem refl_boundary (F : FoamWithBoundary W) : (refl F).boundary = Equiv.refl _ := (rfl)

/-- Inverse isomorphism over `φ.symm`. -/
def symm {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) : G.IsoOver φ.symm F where
  vertex := ψ.vertex.symm
  seam := ψ.seam.symm
  seamCircle := ψ.seamCircle.symm
  facet := ψ.facet.symm
  boundary := ψ.boundary.symm
  map_chirality v := by
    have h := ψ.map_chirality (ψ.vertex.symm v)
    rw [ψ.vertex.apply_symm_apply] at h
    exact h.symm
  map_seamEnds y := by
    set x : (F.Vertex × Fin 4) ⊕ W.Vertex :=
      Sum.map (Prod.map ψ.vertex.symm id) φ.symm.vertex y
    have hxy : Sum.map (Prod.map ψ.vertex id) φ.vertex x = y := by
      rcases y with ⟨v, k⟩ | w <;> simp [x]
    have h := ψ.map_seamEnds x
    rw [hxy] at h
    rcases hp : F.seamEnds x with ⟨s, b⟩
    rw [hp] at h
    rw [h]
    simp
  map_genus f := by
    have h := ψ.map_genus (ψ.facet.symm f)
    rw [ψ.facet.apply_symm_apply] at h
    exact h.symm
  map_boundaryFacet b := ψ.facet.injective (by
    rw [ψ.facet.apply_symm_apply, ← ψ.map_boundaryFacet, ψ.boundary.apply_symm_apply])
  map_sideBoundary y := ψ.boundary.injective (by
    set x : F.Side := Sum.map (Prod.map ψ.seam.symm id) φ.symm.edge y
    have hxy : Sum.map (Prod.map ψ.seam id) φ.edge x = y := by
      rcases y with ⟨s, i⟩ | e <;> simp [x]
    rw [ψ.boundary.apply_symm_apply, ← ψ.map_sideBoundary x, hxy])
  map_circleBoundary z := ψ.boundary.injective (by
    set x : F.CircleSide := Sum.map (Prod.map ψ.seamCircle.symm id) φ.symm.circle z
    have hxz : Sum.map (Prod.map ψ.seamCircle id) φ.circle x = z := by
      rcases z with ⟨c, i⟩ | c <;> simp [x]
    rw [ψ.boundary.apply_symm_apply, ← ψ.map_circleBoundary x, hxz])

/-- Composition of prefoam isomorphisms over `φ₁.trans φ₂`. -/
def trans {φ₁ : W.Iso V} {φ₂ : V.Iso U}
    {F : FoamWithBoundary W} {G : FoamWithBoundary V} {H : FoamWithBoundary U}
    (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) : F.IsoOver (φ₁.trans φ₂) H where
  vertex := ψ₁.vertex.trans ψ₂.vertex
  seam := ψ₁.seam.trans ψ₂.seam
  seamCircle := ψ₁.seamCircle.trans ψ₂.seamCircle
  facet := ψ₁.facet.trans ψ₂.facet
  boundary := ψ₁.boundary.trans ψ₂.boundary
  map_chirality v := by simp
  map_seamEnds x := by
    have h := ψ₂.map_seamEnds (Sum.map (Prod.map ψ₁.vertex id) φ₁.vertex x)
    rw [ψ₁.map_seamEnds] at h
    rcases x with ⟨v, k⟩ | w <;> simpa [Prod.map] using h
  map_genus f := by simp
  map_boundaryFacet b := by simp
  map_sideBoundary x := by
    have h := ψ₂.map_sideBoundary (Sum.map (Prod.map ψ₁.seam id) φ₁.edge x)
    rw [ψ₁.map_sideBoundary] at h
    rcases x with ⟨s, i⟩ | e <;> simpa using h
  map_circleBoundary z := by
    have h := ψ₂.map_circleBoundary (Sum.map (Prod.map ψ₁.seamCircle id) φ₁.circle z)
    rw [ψ₁.map_circleBoundary] at h
    rcases z with ⟨c, i⟩ | c <;> simpa using h

section Groupoid

variable {φ : W.Iso V} {φ₁ : W.Iso V} {φ₂ : V.Iso U} {φ₃ : U.Iso T}
  {F : FoamWithBoundary W} {G : FoamWithBoundary V}
  {H : FoamWithBoundary U} {K : FoamWithBoundary T}

@[simp] theorem symm_vertex (ψ : F.IsoOver φ G) : ψ.symm.vertex = ψ.vertex.symm := (rfl)
@[simp] theorem symm_seam (ψ : F.IsoOver φ G) : ψ.symm.seam = ψ.seam.symm := (rfl)
@[simp] theorem symm_seamCircle (ψ : F.IsoOver φ G) :
    ψ.symm.seamCircle = ψ.seamCircle.symm := (rfl)
@[simp] theorem symm_facet (ψ : F.IsoOver φ G) : ψ.symm.facet = ψ.facet.symm := (rfl)
@[simp] theorem symm_boundary (ψ : F.IsoOver φ G) : ψ.symm.boundary = ψ.boundary.symm := (rfl)

@[simp] theorem trans_vertex (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).vertex = ψ₁.vertex.trans ψ₂.vertex := (rfl)
@[simp] theorem trans_seam (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).seam = ψ₁.seam.trans ψ₂.seam := (rfl)
@[simp] theorem trans_seamCircle (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).seamCircle = ψ₁.seamCircle.trans ψ₂.seamCircle := (rfl)
@[simp] theorem trans_facet (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).facet = ψ₁.facet.trans ψ₂.facet := (rfl)
@[simp] theorem trans_boundary (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).boundary = ψ₁.boundary.trans ψ₂.boundary := (rfl)

@[simp] theorem symm_symm (ψ : F.IsoOver φ G) : ψ.symm.symm.cast φ.symm_symm = ψ := by ext <;> simp
@[simp] theorem refl_symm (F : FoamWithBoundary W) :
    (refl F).symm.cast ClosedWeb.Iso.refl_symm = refl F := by ext <;> simp
@[simp] theorem symm_trans (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).symm.cast (ClosedWeb.Iso.symm_trans φ₁ φ₂) = ψ₂.symm.trans ψ₁.symm := by
  ext <;> simp
@[simp] theorem refl_trans (ψ : F.IsoOver φ G) :
    ((refl F).trans ψ).cast (ClosedWeb.Iso.refl_trans φ) = ψ := by ext <;> simp
@[simp] theorem trans_refl (ψ : F.IsoOver φ G) :
    (ψ.trans (refl G)).cast (ClosedWeb.Iso.trans_refl φ) = ψ := by ext <;> simp
@[simp] theorem symm_trans_self (ψ : F.IsoOver φ G) :
    (ψ.symm.trans ψ).cast (ClosedWeb.Iso.symm_trans_self φ) = refl G := by ext <;> simp
@[simp] theorem self_trans_symm (ψ : F.IsoOver φ G) :
    (ψ.trans ψ.symm).cast (ClosedWeb.Iso.self_trans_symm φ) = refl F := by ext <;> simp
theorem trans_assoc (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) (ψ₃ : H.IsoOver φ₃ K) :
    ((ψ₁.trans ψ₂).trans ψ₃).cast (ClosedWeb.Iso.trans_assoc φ₁ φ₂ φ₃) =
      ψ₁.trans (ψ₂.trans ψ₃) := by ext <;> simp

end Groupoid

section Preservation

variable {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V} (ψ : F.IsoOver φ G)

/-- Every isomorphism commutes with `cornerSide dir` (`cornerIncoming` and `cornerOutgoing`). -/
@[simp] theorem map_cornerSide (dir : Bool) (c : F.Corner) :
    G.cornerSide dir (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerSide dir c) :=
  cornerSideFun_comp dir φ ψ.vertex ψ.seam F.chirality G.chirality F.seamEnds G.seamEnds
    ψ.map_chirality ψ.map_seamEnds c

/-- Every isomorphism commutes with `cornerIncoming`. -/
theorem map_cornerIncoming (c : F.Corner) :
    G.cornerIncoming (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerIncoming c) :=
  ψ.map_cornerSide true c

/-- Every isomorphism commutes with `cornerOutgoing`. -/
theorem map_cornerOutgoing (c : F.Corner) :
    G.cornerOutgoing (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerOutgoing c) :=
  ψ.map_cornerSide false c

theorem nextSide_eq_permCongr : G.nextSide = ψ.sideEquiv.permCongr F.nextSide :=
  nextSidePerm_eq_permCongr φ ψ.vertex ψ.seam F.chirality G.chirality F.seamEnds G.seamEnds
    F.seamEnds_inl_snd F.seamEnds_inr_snd G.seamEnds_inl_snd G.seamEnds_inr_snd
    ψ.map_chirality ψ.map_seamEnds

/-- Every isomorphism intertwines `nextSide` via `sideEquiv`. -/
@[simp] theorem map_nextSide (x : F.Side) :
    G.nextSide (ψ.sideEquiv x) = ψ.sideEquiv (F.nextSide x) := by
  rw [ψ.nextSide_eq_permCongr, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Every isomorphism commutes with `signedSegment`, relabelling seams and boundary edges while
preserving orientation signs. -/
@[simp] theorem map_signedSegment (x : F.Side) :
    G.signedSegment (ψ.sideEquiv x) =
      Prod.map (Sum.map ψ.seam φ.edge) id (F.signedSegment x) := by
  rcases x with ⟨s, i⟩ | e <;> rfl

/-- Every isomorphism transports cyclic side orbits via `sideEquiv`. -/
@[simp] theorem map_sideCycle (x : F.Side) :
    G.sideCycle (ψ.sideEquiv x) = (F.sideCycle x).map ψ.sideEquiv := by
  have hsc : Function.Semiconj ψ.sideEquiv F.nextSide G.nextSide :=
    fun y ↦ (ψ.map_nextSide y).symm
  have hiter : ∀ n, G.nextSide^[n] (ψ.sideEquiv x) = ψ.sideEquiv (F.nextSide^[n] x) :=
    fun n ↦ (hsc.iterate_right n x).symm
  have hper : Function.minimalPeriod G.nextSide (ψ.sideEquiv x) =
      Function.minimalPeriod F.nextSide x :=
    Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ by
      simp [Function.IsPeriodicPt, Function.IsFixedPt, hiter]
  rw [sideCycle_def, sideCycle_def, Function.periodicOrbit_def, Function.periodicOrbit_def,
    hper, Cycle.map_coe, List.map_map]
  exact congrArg ((↑) : List G.Side → Cycle G.Side) (List.map_congr_left fun n _ ↦ hiter n)

/-- Every isomorphism transports signed cyclic boundary words by relabelling seams and boundary
edges while preserving orientation signs. -/
@[simp] theorem map_sideWord (x : F.Side) :
    G.sideWord (ψ.sideEquiv x) =
      (F.sideWord x).map (Prod.map (Sum.map ψ.seam φ.edge) id) := by
  rw [sideWord_def, sideWord_def, ψ.map_sideCycle]
  induction F.sideCycle x with
  | nil => rfl
  | cons a l _ =>
    simp only [Cycle.map_coe, List.map_map]
    congr 1
    exact List.map_congr_left fun y _ ↦ ψ.map_signedSegment y

/-- Equivalence of boundary component fibres over `f` and `ψ.facet f`. -/
def facetBoundaryEquiv (f : F.Facet) : F.FacetBoundary f ≃ G.FacetBoundary (ψ.facet f) :=
  Equiv.subtypeEquiv ψ.boundary fun b ↦ by rw [ψ.map_boundaryFacet, ψ.facet.apply_eq_iff_eq]

@[simp] theorem facetBoundaryEquiv_apply_coe (f : F.Facet) (b : F.FacetBoundary f) :
    (ψ.facetBoundaryEquiv f b).1 = ψ.boundary b.1 := (rfl)
@[simp] theorem facetBoundaryEquiv_symm_apply_coe
    (f : F.Facet) (b : G.FacetBoundary (ψ.facet f)) :
    ((ψ.facetBoundaryEquiv f).symm b).1 = ψ.boundary.symm b.1 := (rfl)

/-- Isomorphisms preserve the number of boundary components of each facet. -/
@[simp] theorem map_numBoundaryComponents (f : F.Facet) :
    G.numBoundaryComponents (ψ.facet f) = F.numBoundaryComponents f :=
  (Nat.card_congr (ψ.facetBoundaryEquiv f)).symm

/-- Isomorphisms preserve the Euler characteristic of each facet. -/
@[simp] theorem map_facetEulerChar (f : F.Facet) :
    G.facetEulerChar (ψ.facet f) = F.facetEulerChar f := by
  simp only [facetEulerChar, ψ.map_genus, ψ.map_numBoundaryComponents]

/-- Isomorphisms preserve nilvalence. -/
theorem isNilvalent_iff (ψ : F.IsoOver φ G) : F.IsNilvalent ↔ G.IsNilvalent :=
  and_congr ψ.vertex.isEmpty_congr
    (and_congr ψ.seam.isEmpty_congr ψ.seamCircle.isEmpty_congr)

end Preservation

end IsoOver

namespace Iso

variable {W : ClosedWeb.{u}} {F G H K : FoamWithBoundary W}

/-- Identity boundary-fixing isomorphism. -/
abbrev refl (F : FoamWithBoundary W) : F.Iso F := IsoOver.refl F

/-- Inverse of a boundary-fixing isomorphism. -/
def symm (ψ : F.Iso G) : G.Iso F :=
  IsoOver.cast ClosedWeb.Iso.refl_symm (IsoOver.symm ψ)

@[simp] theorem symm_vertex (ψ : F.Iso G) : (Iso.symm ψ).vertex = ψ.vertex.symm := by simp [symm]
@[simp] theorem symm_seam (ψ : F.Iso G) : (Iso.symm ψ).seam = ψ.seam.symm := by simp [symm]
@[simp] theorem symm_seamCircle (ψ : F.Iso G) :
    (Iso.symm ψ).seamCircle = ψ.seamCircle.symm := by simp [symm]
@[simp] theorem symm_facet (ψ : F.Iso G) : (Iso.symm ψ).facet = ψ.facet.symm := by simp [symm]
@[simp] theorem symm_boundary (ψ : F.Iso G) :
    (Iso.symm ψ).boundary = ψ.boundary.symm := by simp [symm]

/-- Composition of boundary-fixing isomorphisms. -/
def trans (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) : F.Iso H :=
  IsoOver.cast (ClosedWeb.Iso.refl_trans _) (IsoOver.trans ψ₁ ψ₂)

@[simp] theorem trans_vertex (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).vertex = ψ₁.vertex.trans ψ₂.vertex := by simp [trans]
@[simp] theorem trans_seam (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).seam = ψ₁.seam.trans ψ₂.seam := by simp [trans]
@[simp] theorem trans_seamCircle (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).seamCircle = ψ₁.seamCircle.trans ψ₂.seamCircle := by simp [trans]
@[simp] theorem trans_facet (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).facet = ψ₁.facet.trans ψ₂.facet := by simp [trans]
@[simp] theorem trans_boundary (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).boundary = ψ₁.boundary.trans ψ₂.boundary := by simp [trans]

@[simp] theorem symm_symm (ψ : F.Iso G) : Iso.symm (Iso.symm ψ) = ψ := by ext <;> simp
@[simp] theorem refl_symm (F : FoamWithBoundary W) : Iso.symm (Iso.refl F) = Iso.refl F := by
  ext <;> simp
@[simp] theorem symm_trans (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    Iso.symm (Iso.trans ψ₁ ψ₂) = Iso.trans (Iso.symm ψ₂) (Iso.symm ψ₁) := by ext <;> simp
@[simp] theorem refl_trans (ψ : F.Iso G) : Iso.trans (Iso.refl F) ψ = ψ := by ext <;> simp
@[simp] theorem trans_refl (ψ : F.Iso G) : Iso.trans ψ (Iso.refl G) = ψ := by ext <;> simp
@[simp] theorem symm_trans_self (ψ : F.Iso G) : Iso.trans (Iso.symm ψ) ψ = Iso.refl G := by
  ext <;> simp
@[simp] theorem self_trans_symm (ψ : F.Iso G) : Iso.trans ψ (Iso.symm ψ) = Iso.refl F := by
  ext <;> simp
theorem trans_assoc (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) (ψ₃ : H.Iso K) :
    Iso.trans (Iso.trans ψ₁ ψ₂) ψ₃ = Iso.trans ψ₁ (Iso.trans ψ₂ ψ₃) := by ext <;> simp

end Iso

/-! ### Transport along boundary web isomorphisms and the empty prefoam -/

section Relabel

private theorem relabel_map_seamEnds {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (φ : W.Iso V) {Vertex' Seam' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam')
    (x : (F.Vertex × Fin 4) ⊕ W.Vertex) :
    ((((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans F.seamEnds).trans
      (eS.prodCongr (Equiv.refl Bool))) (Sum.map (Prod.map eV id) φ.vertex x) =
      Prod.map eS id (F.seamEnds x) := by
  rcases x with ⟨v, k⟩ | w <;> simp [Prod.map]

/-- Relabel all internal carrier types of `F` and transport its boundary along `φ : W.Iso V`. -/
abbrev relabelOver {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (F : FoamWithBoundary W) (φ : W.Iso V)
    {Vertex' Seam' SeamCircle' Facet' Boundary' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (eSC : F.SeamCircle ≃ SeamCircle')
    (eF : F.Facet ≃ Facet') (eB : F.Boundary ≃ Boundary') : FoamWithBoundary V where
  Vertex := Vertex'
  Seam := Seam'
  SeamCircle := SeamCircle'
  Facet := Facet'
  Boundary := Boundary'
  finite_vertex := Finite.of_equiv F.Vertex eV
  finite_seam := Finite.of_equiv F.Seam eS
  finite_seamCircle := Finite.of_equiv F.SeamCircle eSC
  finite_facet := Finite.of_equiv F.Facet eF
  finite_boundary := Finite.of_equiv F.Boundary eB
  chirality := F.chirality ∘ eV.symm
  seamEnds := (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans
    F.seamEnds).trans (eS.prodCongr (Equiv.refl Bool))
  seamEnds_inl_snd v k := by simp [F.seamEnds_inl_snd (eV.symm v) k]
  seamEnds_inr_snd w := by
    have hw := congrArg Prod.snd (φ.map_ends_apply (φ.vertex.symm w) 0)
    rw [φ.vertex.apply_symm_apply] at hw
    simpa [hw] using F.seamEnds_inr_snd (φ.vertex.symm w)
  genus := F.genus ∘ eF.symm
  boundaryFacet := eF ∘ F.boundaryFacet ∘ eB.symm
  sideBoundary :=
    eB ∘ F.sideBoundary ∘ ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge).symm
  circleBoundary :=
    eB ∘ F.circleBoundary ∘ ((eSC.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle).symm
  sideBoundary_eq_iff x y := by
    have hnp := nextSidePerm_eq_permCongr φ eV eS F.chirality (F.chirality ∘ eV.symm) F.seamEnds _
      F.seamEnds_inl_snd F.seamEnds_inr_snd
      (fun v k ↦ by simp [F.seamEnds_inl_snd (eV.symm v) k])
      (fun w ↦ by
        have hw := congrArg Prod.snd (φ.map_ends_apply (φ.vertex.symm w) 0)
        rw [φ.vertex.apply_symm_apply] at hw
        simpa [hw] using F.seamEnds_inr_snd (φ.vertex.symm w))
      (fun v ↦ by simp) (relabel_map_seamEnds F φ eV eS)
    rw [hnp]
    set eSide := (eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge
    dsimp only [Function.comp_apply]
    rw [eB.apply_eq_iff_eq, F.sideBoundary_eq_iff]
    exact (Equiv.Perm.sameCycle_permCongr_iff (σ := F.nextSide) eSide).symm
  circleBoundary_injective := eB.injective.comp
    (F.circleBoundary_injective.comp
      ((eSC.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle).symm.injective)
  sideBoundary_ne_circleBoundary x z h :=
    F.sideBoundary_ne_circleBoundary _ _ (eB.injective h)
  boundary_surjective b := by
    rcases F.boundary_surjective (eB.symm b) with ⟨x, hx⟩ | ⟨z, hz⟩
    · refine Or.inl ⟨((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge) x, ?_⟩
      simp only [Function.comp_apply, Equiv.symm_apply_apply, hx, eB.apply_symm_apply]
    · refine Or.inr ⟨((eSC.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle) z, ?_⟩
      simp only [Function.comp_apply, Equiv.symm_apply_apply, hz, eB.apply_symm_apply]

/-- Canonical isomorphism from `F` to `F.relabelOver φ eV eS eSC eF eB` over `φ`. -/
def relabelOverIso {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (F : FoamWithBoundary W) (φ : W.Iso V)
    {Vertex' Seam' SeamCircle' Facet' Boundary' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (eSC : F.SeamCircle ≃ SeamCircle')
    (eF : F.Facet ≃ Facet') (eB : F.Boundary ≃ Boundary') :
    F.IsoOver φ (F.relabelOver φ eV eS eSC eF eB) where
  vertex := eV
  seam := eS
  seamCircle := eSC
  facet := eF
  boundary := eB
  map_chirality v := by simp [relabelOver]
  map_seamEnds := relabel_map_seamEnds F φ eV eS
  map_genus f := by simp [relabelOver]
  map_boundaryFacet b := by simp [relabelOver]
  map_sideBoundary x := by rcases x with ⟨s, i⟩ | e <;> simp [relabelOver]
  map_circleBoundary z := by rcases z with ⟨c, i⟩ | c <;> simp [relabelOver]

section RelabelSimp

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (F : FoamWithBoundary W) (φ : W.Iso V)
  {Vertex' Seam' SeamCircle' Facet' Boundary' : Type v}
  (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (eSC : F.SeamCircle ≃ SeamCircle')
  (eF : F.Facet ≃ Facet') (eB : F.Boundary ≃ Boundary')

@[simp] theorem relabelOverIso_vertex : (F.relabelOverIso φ eV eS eSC eF eB).vertex = eV := (rfl)
@[simp] theorem relabelOverIso_seam : (F.relabelOverIso φ eV eS eSC eF eB).seam = eS := (rfl)
@[simp] theorem relabelOverIso_seamCircle :
    (F.relabelOverIso φ eV eS eSC eF eB).seamCircle = eSC := (rfl)
@[simp] theorem relabelOverIso_facet : (F.relabelOverIso φ eV eS eSC eF eB).facet = eF := (rfl)
@[simp] theorem relabelOverIso_boundary :
    (F.relabelOverIso φ eV eS eSC eF eB).boundary = eB := (rfl)

end RelabelSimp

/-- Transport a prefoam `F : FoamWithBoundary W` along a boundary web isomorphism `φ : W.Iso V`
within the same universe. -/
abbrev mapBoundary {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V) :
    FoamWithBoundary V :=
  F.relabelOver φ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

/-- Canonical isomorphism `F.IsoOver φ (F.mapBoundary φ)`. -/
def mapBoundaryIso {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V) :
    F.IsoOver φ (F.mapBoundary φ) :=
  F.relabelOverIso φ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

section MapBoundarySimp
variable {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V)
@[simp] theorem mapBoundaryIso_vertex : (F.mapBoundaryIso φ).vertex = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_seam : (F.mapBoundaryIso φ).seam = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_seamCircle : (F.mapBoundaryIso φ).seamCircle = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_facet : (F.mapBoundaryIso φ).facet = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_boundary : (F.mapBoundaryIso φ).boundary = Equiv.refl _ := (rfl)
end MapBoundarySimp

end Relabel

/-- The empty closed prefoam. -/
abbrev empty : ClosedFoam.{u} where
  Vertex := PEmpty
  Seam := PEmpty
  SeamCircle := PEmpty
  Facet := PEmpty
  Boundary := PEmpty
  chirality := PEmpty.elim
  seamEnds := Equiv.equivOfIsEmpty _ _
  seamEnds_inl_snd v := v.elim
  seamEnds_inr_snd w := w.elim
  genus := PEmpty.elim
  boundaryFacet := PEmpty.elim
  sideBoundary := isEmptyElim
  circleBoundary := isEmptyElim
  sideBoundary_eq_iff x := isEmptyElim x
  circleBoundary_injective z := isEmptyElim z
  sideBoundary_ne_circleBoundary x := isEmptyElim x
  boundary_surjective b := b.elim

@[simp] theorem isNilvalent_empty : (empty.{u}).IsNilvalent :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end FoamWithBoundary

end TauCeti
