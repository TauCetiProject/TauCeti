/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Cycle
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import TauCeti.KnotTheory.Foam.ClosedWeb.Tetrahedron
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
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
* From `(chirality, seamEnds)` alone, `cornerIncoming` and `cornerOutgoing` identify the corners
  `(Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)` with the sides `(Seam × Fin 3) ⊕ W.Edge`, producing the
  canonical successor permutation `nextSide : Equiv.Perm Side`.
* Each `b : Boundary` belongs to a facet `boundaryFacet b : Facet`, so a single facet may have
  multiple indexed boundary components (`FacetBoundary f`) and may appear multiple times in the
  three local sheet slots around a seam. Orbits of `nextSide` and circle sides
  `(SeamCircle × Fin 3) ⊕ W.Circle` partition `Boundary` bijectively (`boundaryEquiv`).

## Main definitions

* `TauCeti.FoamWithBoundary`: combinatorial prefoams bounded by `W : ClosedWeb`.
* `TauCeti.ClosedFoam`: prefoams with empty boundary `ClosedWeb.empty`.
* `TauCeti.FoamWithBoundary.cornerIncoming`, `cornerOutgoing`, `nextSide`: canonical corner-to-side
  bijections and boundary-walk successor permutation.
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
  arXiv:2602.11120v1, Definition 2.4 and Remark 2.5.
* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1 and Remark 2.2.
-/

public section

namespace TauCeti

universe u v w

namespace FoamWithBoundary

/-! ### Slot-orientation lemmas and corner-side equivalences -/

private theorem ends_snd_true_iff_decide_ne_zero (T : ClosedWeb.{u}) (k : T.Vertex) (i : Fin 3) :
    (T.ends (k, i)).2 = true ↔ decide (i ≠ 0) = !(T.ends (k, 0)).2 := by
  fin_cases i
  · change (T.ends (k, 0)).2 = true ↔ decide ((0 : Fin 3) ≠ 0) = !(T.ends (k, 0)).2
    cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 1)).2 = true ↔ decide ((1 : Fin 3) ≠ 0) = !(T.ends (k, 0)).2
    rw [T.orientation_one k]; cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 2)).2 = true ↔ decide ((2 : Fin 3) ≠ 0) = !(T.ends (k, 0)).2
    rw [T.orientation_two k]; cases (T.ends (k, 0)).2 <;> decide

private theorem ends_snd_false_iff_decide_ne_zero (T : ClosedWeb.{u}) (k : T.Vertex) (i : Fin 3) :
    (T.ends (k, i)).2 = false ↔ decide (i ≠ 0) = (T.ends (k, 0)).2 := by
  fin_cases i
  · change (T.ends (k, 0)).2 = false ↔ decide ((0 : Fin 3) ≠ 0) = (T.ends (k, 0)).2
    cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 1)).2 = false ↔ decide ((1 : Fin 3) ≠ 0) = (T.ends (k, 0)).2
    rw [T.orientation_one k]; cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 2)).2 = false ↔ decide ((2 : Fin 3) ≠ 0) = (T.ends (k, 0)).2
    rw [T.orientation_two k]; cases (T.ends (k, 0)).2 <;> decide

private theorem ends_snd_false_iff_decide_eq_zero (T : ClosedWeb.{u}) (k : T.Vertex) (i : Fin 3) :
    (T.ends (k, i)).2 = false ↔ decide (i = 0) = !(T.ends (k, 0)).2 := by
  fin_cases i
  · change (T.ends (k, 0)).2 = false ↔ decide ((0 : Fin 3) = 0) = !(T.ends (k, 0)).2
    cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 1)).2 = false ↔ decide ((1 : Fin 3) = 0) = !(T.ends (k, 0)).2
    rw [T.orientation_one k]; cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 2)).2 = false ↔ decide ((2 : Fin 3) = 0) = !(T.ends (k, 0)).2
    rw [T.orientation_two k]; cases (T.ends (k, 0)).2 <;> decide

private theorem ends_snd_true_iff_decide_eq_zero (T : ClosedWeb.{u}) (k : T.Vertex) (i : Fin 3) :
    (T.ends (k, i)).2 = true ↔ decide (i = 0) = (T.ends (k, 0)).2 := by
  fin_cases i
  · change (T.ends (k, 0)).2 = true ↔ decide ((0 : Fin 3) = 0) = (T.ends (k, 0)).2
    cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 1)).2 = true ↔ decide ((1 : Fin 3) = 0) = (T.ends (k, 0)).2
    rw [T.orientation_one k]; cases (T.ends (k, 0)).2 <;> decide
  · change (T.ends (k, 2)).2 = true ↔ decide ((2 : Fin 3) = 0) = (T.ends (k, 0)).2
    rw [T.orientation_two k]; cases (T.ends (k, 0)).2 <;> decide

/-- Forward map sending each interior or boundary corner to the side entering that corner. -/
@[expose] def cornerIncomingFun {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool) :
    (Vertex × Fin 6) ⊕ (W.Vertex × Fin 3) → (Seam × Fin 3) ⊕ W.Edge
  | Sum.inl (v, e) =>
    let ki := (ClosedWeb.tetWeb (chirality v)).ends.symm (e, true)
    Sum.inl ((seamEnds (Sum.inl (v, ki.1))).1, ki.2)
  | Sum.inr (w, i) =>
    let eb := W.ends (w, i)
    if eb.2 then Sum.inr eb.1 else Sum.inl ((seamEnds (Sum.inr w)).1, i)

/-- Inverse map sending each side to the corner it enters along its facet boundary orientation. -/
@[expose] def cornerIncomingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool) :
    (Seam × Fin 3) ⊕ W.Edge → (Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)
  | Sum.inr e => Sum.inr (W.ends.symm (e, true))
  | Sum.inl (s, i) =>
    match seamEnds.symm (s, decide (i ≠ 0)) with
    | Sum.inl (v, k) => Sum.inl (v, ((ClosedWeb.tetWeb (chirality v)).ends (k, i)).1)
    | Sum.inr w => Sum.inr (w, i)

theorem leftInverse_cornerIncomingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    Function.LeftInverse (cornerIncomingInv chirality seamEnds)
      (cornerIncomingFun chirality seamEnds) := by
  rintro (⟨v, e⟩ | ⟨w, i⟩)
  · dsimp only [cornerIncomingFun, cornerIncomingInv]
    set ki := (ClosedWeb.tetWeb (chirality v)).ends.symm (e, true)
    have hki : (ClosedWeb.tetWeb (chirality v)).ends (ki.1, ki.2) = (e, true) :=
      (ClosedWeb.tetWeb (chirality v)).ends.apply_symm_apply (e, true)
    have hb : decide (ki.2 ≠ 0) = (seamEnds (Sum.inl (v, ki.1))).2 := by
      rw [h_inl, ← ends_snd_true_iff_decide_ne_zero]
      exact congrArg Prod.snd hki
    have hpair : ((seamEnds (Sum.inl (v, ki.1))).1, decide (ki.2 ≠ 0)) =
        seamEnds (Sum.inl (v, ki.1)) := Prod.ext rfl hb
    rw [hpair, seamEnds.symm_apply_apply]
    dsimp only
    rw [congrArg Prod.fst hki]
  · dsimp only [cornerIncomingFun]
    cases hb : (W.ends (w, i)).2
    · simp only [Bool.false_eq_true, ↓reduceIte, cornerIncomingInv]
      have hd : decide (i ≠ 0) = (seamEnds (Sum.inr w)).2 := by
        rw [h_inr, ← ends_snd_false_iff_decide_ne_zero]
        exact hb
      have hpair : ((seamEnds (Sum.inr w)).1, decide (i ≠ 0)) = seamEnds (Sum.inr w) :=
        Prod.ext rfl hd
      rw [hpair, seamEnds.symm_apply_apply]
    · simp only [↓reduceIte, cornerIncomingInv]
      have he : ((W.ends (w, i)).1, true) = W.ends (w, i) := Prod.ext rfl hb.symm
      rw [he, W.ends.symm_apply_apply]

theorem rightInverse_cornerIncomingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    Function.RightInverse (cornerIncomingInv chirality seamEnds)
      (cornerIncomingFun chirality seamEnds) := by
  rintro (⟨s, i⟩ | e)
  · dsimp only [cornerIncomingInv]
    cases hse : seamEnds.symm (s, decide (i ≠ 0)) with
    | inl vk =>
      rcases vk with ⟨v, k⟩
      have happ : seamEnds (Sum.inl (v, k)) = (s, decide (i ≠ 0)) :=
        seamEnds.eq_symm_apply.mp hse.symm
      have ht : ((ClosedWeb.tetWeb (chirality v)).ends (k, i)).2 = true := by
        rw [ends_snd_true_iff_decide_ne_zero, ← h_inl]
        exact (congrArg Prod.snd happ).symm
      dsimp only [cornerIncomingFun]
      have hp : (((ClosedWeb.tetWeb (chirality v)).ends (k, i)).1, true) =
          (ClosedWeb.tetWeb (chirality v)).ends (k, i) := Prod.ext rfl ht.symm
      rw [hp, Equiv.symm_apply_apply, congrArg Prod.fst happ]
    | inr w =>
      have happ : seamEnds (Sum.inr w) = (s, decide (i ≠ 0)) :=
        seamEnds.eq_symm_apply.mp hse.symm
      have hf : (W.ends (w, i)).2 = false := by
        rw [ends_snd_false_iff_decide_ne_zero, ← h_inr]
        exact (congrArg Prod.snd happ).symm
      dsimp only [cornerIncomingFun]
      rw [hf, congrArg Prod.fst happ]
      rfl
  · dsimp only [cornerIncomingInv, cornerIncomingFun]
    rw [W.ends.apply_symm_apply]
    rfl

/-- Equivalence between corners and their incoming facet-boundary sides. -/
@[expose] def cornerIncomingEquiv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    ((Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)) ≃ ((Seam × Fin 3) ⊕ W.Edge) where
  toFun := cornerIncomingFun chirality seamEnds
  invFun := cornerIncomingInv chirality seamEnds
  left_inv := leftInverse_cornerIncomingInv chirality seamEnds h_inl h_inr
  right_inv := rightInverse_cornerIncomingInv chirality seamEnds h_inl h_inr

/-- Forward map sending each interior or boundary corner to the side leaving that corner. -/
@[expose] def cornerOutgoingFun {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool) :
    (Vertex × Fin 6) ⊕ (W.Vertex × Fin 3) → (Seam × Fin 3) ⊕ W.Edge
  | Sum.inl (v, e) =>
    let ki := (ClosedWeb.tetWeb (chirality v)).ends.symm (e, false)
    Sum.inl ((seamEnds (Sum.inl (v, ki.1))).1, ki.2)
  | Sum.inr (w, i) =>
    let eb := W.ends (w, i)
    if eb.2 then Sum.inl ((seamEnds (Sum.inr w)).1, i) else Sum.inr eb.1

/-- Inverse map sending each side to the corner it leaves along its facet boundary orientation. -/
@[expose] def cornerOutgoingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool) :
    (Seam × Fin 3) ⊕ W.Edge → (Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)
  | Sum.inr e => Sum.inr (W.ends.symm (e, false))
  | Sum.inl (s, i) =>
    match seamEnds.symm (s, decide (i = 0)) with
    | Sum.inl (v, k) => Sum.inl (v, ((ClosedWeb.tetWeb (chirality v)).ends (k, i)).1)
    | Sum.inr w => Sum.inr (w, i)

theorem leftInverse_cornerOutgoingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    Function.LeftInverse (cornerOutgoingInv chirality seamEnds)
      (cornerOutgoingFun chirality seamEnds) := by
  rintro (⟨v, e⟩ | ⟨w, i⟩)
  · dsimp only [cornerOutgoingFun, cornerOutgoingInv]
    set ki := (ClosedWeb.tetWeb (chirality v)).ends.symm (e, false)
    have hki : (ClosedWeb.tetWeb (chirality v)).ends (ki.1, ki.2) = (e, false) :=
      (ClosedWeb.tetWeb (chirality v)).ends.apply_symm_apply (e, false)
    have hb : decide (ki.2 = 0) = (seamEnds (Sum.inl (v, ki.1))).2 := by
      rw [h_inl, ← ends_snd_false_iff_decide_eq_zero]
      exact congrArg Prod.snd hki
    have hpair : ((seamEnds (Sum.inl (v, ki.1))).1, decide (ki.2 = 0)) =
        seamEnds (Sum.inl (v, ki.1)) := Prod.ext rfl hb
    rw [hpair, seamEnds.symm_apply_apply]
    dsimp only
    rw [congrArg Prod.fst hki]
  · dsimp only [cornerOutgoingFun]
    cases hb : (W.ends (w, i)).2
    · simp only [Bool.false_eq_true, ↓reduceIte, cornerOutgoingInv]
      have he : ((W.ends (w, i)).1, false) = W.ends (w, i) := Prod.ext rfl hb.symm
      rw [he, W.ends.symm_apply_apply]
    · simp only [↓reduceIte, cornerOutgoingInv]
      have hd : decide (i = 0) = (seamEnds (Sum.inr w)).2 := by
        rw [h_inr, ← ends_snd_true_iff_decide_eq_zero]
        exact hb
      have hpair : ((seamEnds (Sum.inr w)).1, decide (i = 0)) = seamEnds (Sum.inr w) :=
        Prod.ext rfl hd
      rw [hpair, seamEnds.symm_apply_apply]

theorem rightInverse_cornerOutgoingInv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    Function.RightInverse (cornerOutgoingInv chirality seamEnds)
      (cornerOutgoingFun chirality seamEnds) := by
  rintro (⟨s, i⟩ | e)
  · dsimp only [cornerOutgoingInv]
    cases hse : seamEnds.symm (s, decide (i = 0)) with
    | inl vk =>
      rcases vk with ⟨v, k⟩
      have happ : seamEnds (Sum.inl (v, k)) = (s, decide (i = 0)) :=
        seamEnds.eq_symm_apply.mp hse.symm
      have hf : ((ClosedWeb.tetWeb (chirality v)).ends (k, i)).2 = false := by
        rw [ends_snd_false_iff_decide_eq_zero, ← h_inl]
        exact (congrArg Prod.snd happ).symm
      dsimp only [cornerOutgoingFun]
      have hp : (((ClosedWeb.tetWeb (chirality v)).ends (k, i)).1, false) =
          (ClosedWeb.tetWeb (chirality v)).ends (k, i) := Prod.ext rfl hf.symm
      rw [hp, Equiv.symm_apply_apply, congrArg Prod.fst happ]
    | inr w =>
      have happ : seamEnds (Sum.inr w) = (s, decide (i = 0)) :=
        seamEnds.eq_symm_apply.mp hse.symm
      have ht : (W.ends (w, i)).2 = true := by
        rw [ends_snd_true_iff_decide_eq_zero, ← h_inr]
        exact (congrArg Prod.snd happ).symm
      dsimp only [cornerOutgoingFun]
      rw [ht, congrArg Prod.fst happ]
      rfl
  · dsimp only [cornerOutgoingInv, cornerOutgoingFun]
    rw [W.ends.apply_symm_apply]
    rfl

/-- Equivalence between corners and their outgoing facet-boundary sides. -/
@[expose] def cornerOutgoingEquiv {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) :
    ((Vertex × Fin 6) ⊕ (W.Vertex × Fin 3)) ≃ ((Seam × Fin 3) ⊕ W.Edge) where
  toFun := cornerOutgoingFun chirality seamEnds
  invFun := cornerOutgoingInv chirality seamEnds
  left_inv := leftInverse_cornerOutgoingInv chirality seamEnds h_inl h_inr
  right_inv := rightInverse_cornerOutgoingInv chirality seamEnds h_inl h_inr

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

@[simp] theorem cornerIncomingEquiv_inl {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) (v : Vertex) (e : Fin 6) :
    cornerIncomingEquiv chirality seamEnds h_inl h_inr (Sum.inl (v, e)) =
      Sum.inl ((seamEnds
        (Sum.inl (v, ((ClosedWeb.tetWeb (chirality v)).ends.symm (e, true)).1))).1,
        ((ClosedWeb.tetWeb (chirality v)).ends.symm (e, true)).2) := (rfl)

@[simp] theorem cornerIncomingEquiv_inr {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) (w : W.Vertex) (i : Fin 3) :
    cornerIncomingEquiv chirality seamEnds h_inl h_inr (Sum.inr (w, i)) =
      if (W.ends (w, i)).2 then Sum.inr (W.ends (w, i)).1
      else Sum.inl ((seamEnds (Sum.inr w)).1, i) := (rfl)

@[simp] theorem cornerOutgoingEquiv_inl {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) (v : Vertex) (e : Fin 6) :
    cornerOutgoingEquiv chirality seamEnds h_inl h_inr (Sum.inl (v, e)) =
      Sum.inl ((seamEnds
        (Sum.inl (v, ((ClosedWeb.tetWeb (chirality v)).ends.symm (e, false)).1))).1,
        ((ClosedWeb.tetWeb (chirality v)).ends.symm (e, false)).2) := (rfl)

@[simp] theorem cornerOutgoingEquiv_inr {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2) (w : W.Vertex) (i : Fin 3) :
    cornerOutgoingEquiv chirality seamEnds h_inl h_inr (Sum.inr (w, i)) =
      if (W.ends (w, i)).2 then Sum.inl ((seamEnds (Sum.inr w)).1, i)
      else Sum.inr (W.ends (w, i)).1 := (rfl)

theorem nextSidePerm_apply {Vertex Seam : Type u} {W : ClosedWeb.{u}}
    (chirality : Vertex → Bool) (seamEnds : (Vertex × Fin 4) ⊕ W.Vertex ≃ Seam × Bool)
    (h_inl : ∀ v k,
      (seamEnds (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w, (seamEnds (Sum.inr w)).2 = (W.ends (w, 0)).2)
    (x : (Seam × Fin 3) ⊕ W.Edge) :
    nextSidePerm chirality seamEnds h_inl h_inr x =
      cornerOutgoingEquiv chirality seamEnds h_inl h_inr
        ((cornerIncomingEquiv chirality seamEnds h_inl h_inr).symm x) := (rfl)

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

/-- Equivalence sending each corner of `F` to the side entering that corner. -/
def cornerIncoming : F.Corner ≃ F.Side :=
  cornerIncomingEquiv F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd

theorem cornerIncoming_def : F.cornerIncoming =
    cornerIncomingEquiv F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd := (rfl)

/-- Equivalence sending each corner of `F` to the side leaving that corner. -/
def cornerOutgoing : F.Corner ≃ F.Side :=
  cornerOutgoingEquiv F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd

theorem cornerOutgoing_def : F.cornerOutgoing =
    cornerOutgoingEquiv F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd := (rfl)

/-- Successor permutation stepping from each segmented side to the next side along the oriented
boundary of its facet. -/
def nextSide : Equiv.Perm F.Side :=
  nextSidePerm F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd

theorem nextSide_def : F.nextSide =
    nextSidePerm F.chirality F.seamEnds F.seamEnds_inl_snd F.seamEnds_inr_snd := (rfl)

theorem nextSide_apply (x : F.Side) :
    F.nextSide x = F.cornerOutgoing (F.cornerIncoming.symm x) := (rfl)

@[simp] theorem cornerIncoming_symm_nextSide (x : F.Side) :
    F.cornerOutgoing.symm (F.nextSide x) = F.cornerIncoming.symm x :=
  F.cornerOutgoing.symm_apply_apply (F.cornerIncoming.symm x)

/-- Underlying interior or boundary vertex of a corner. -/
def cornerVertex : F.Corner → F.Vertex ⊕ W.Vertex :=
  Sum.map Prod.fst Prod.fst

/-- Starting vertex (interior or boundary) of a segmented side along its facet boundary walk. -/
def sideStart (x : F.Side) : F.Vertex ⊕ W.Vertex :=
  F.cornerVertex (F.cornerOutgoing.symm x)

/-- Ending vertex (interior or boundary) of a segmented side along its facet boundary walk. -/
def sideEnd (x : F.Side) : F.Vertex ⊕ W.Vertex :=
  F.cornerVertex (F.cornerIncoming.symm x)

/-- Consecutive sides in a facet boundary walk share their intermediate vertex. -/
@[simp] theorem sideStart_nextSide (x : F.Side) :
    F.sideStart (F.nextSide x) = F.sideEnd x := by
  rw [sideStart, cornerIncoming_symm_nextSide, sideEnd]

/-- Source endpoint (interior or boundary vertex) of an interval seam `s`. -/
def seamSource (s : F.Seam) : F.Vertex ⊕ W.Vertex :=
  Sum.map Prod.fst id (F.seamEnds.symm (s, false))

/-- Target endpoint (interior or boundary vertex) of an interval seam `s`. -/
def seamTarget (s : F.Seam) : F.Vertex ⊕ W.Vertex :=
  Sum.map Prod.fst id (F.seamEnds.symm (s, true))

/-- Every boundary web edge is traversed from its `W`-source to its `W`-target. -/
@[simp] theorem sideStart_inr (e : W.Edge) :
    F.sideStart (Sum.inr e) = Sum.inr (W.source e) := by
  rw [W.source_def, W.incident_def]
  rfl

/-- Every boundary web edge ends at its `W`-target. -/
@[simp] theorem sideEnd_inr (e : W.Edge) :
    F.sideEnd (Sum.inr e) = Sum.inr (W.target e) := by
  rw [W.target_def, W.incident_def]
  rfl

/-- Sheet `0` along a seam `s` starts at `seamTarget s` (opposite to `s`). -/
@[simp] theorem sideStart_inl_zero (s : F.Seam) :
    F.sideStart (Sum.inl (s, 0)) = F.seamTarget s := by
  simp only [sideStart, seamTarget, cornerOutgoing, cornerOutgoingEquiv, cornerOutgoingInv,
    cornerVertex, Equiv.coe_fn_symm_mk, decide_true]
  rcases F.seamEnds.symm (s, true) with ⟨v, k⟩ | w <;> rfl

/-- Sheet `0` along a seam `s` ends at `seamSource s` (opposite to `s`). -/
@[simp] theorem sideEnd_inl_zero (s : F.Seam) :
    F.sideEnd (Sum.inl (s, 0)) = F.seamSource s := by
  simp only [sideEnd, seamSource, cornerIncoming, cornerIncomingEquiv, cornerIncomingInv,
    cornerVertex, Equiv.coe_fn_symm_mk, ne_self_iff_false, decide_false]
  rcases F.seamEnds.symm (s, false) with ⟨v, k⟩ | w <;> rfl

/-- Sheets `1` and `2` along a seam `s` start at `seamSource s` (matching `s`). -/
theorem sideStart_inl_of_ne_zero (s : F.Seam) {i : Fin 3} (hi : i ≠ 0) :
    F.sideStart (Sum.inl (s, i)) = F.seamSource s := by
  simp only [sideStart, seamSource, cornerOutgoing, cornerOutgoingEquiv, cornerOutgoingInv,
    cornerVertex, Equiv.coe_fn_symm_mk, decide_eq_false hi]
  rcases F.seamEnds.symm (s, false) with ⟨v, k⟩ | w <;> rfl

/-- Sheets `1` and `2` along a seam `s` end at `seamTarget s` (matching `s`). -/
theorem sideEnd_inl_of_ne_zero (s : F.Seam) {i : Fin 3} (hi : i ≠ 0) :
    F.sideEnd (Sum.inl (s, i)) = F.seamTarget s := by
  simp only [sideEnd, seamTarget, cornerIncoming, cornerIncomingEquiv, cornerIncomingInv,
    cornerVertex, Equiv.coe_fn_symm_mk, decide_eq_true hi]
  rcases F.seamEnds.symm (s, true) with ⟨v, k⟩ | w <;> rfl

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

@[simp] theorem signedSegment_inl_zero (s : F.Seam) :
    F.signedSegment (Sum.inl (s, 0)) = (Sum.inl s, false) := (rfl)

@[simp] theorem signedSegment_inl_one (s : F.Seam) :
    F.signedSegment (Sum.inl (s, 1)) = (Sum.inl s, true) := (rfl)

@[simp] theorem signedSegment_inl_two (s : F.Seam) :
    F.signedSegment (Sum.inl (s, 2)) = (Sum.inl s, true) := (rfl)

@[simp] theorem signedSegment_inr (e : W.Edge) :
    F.signedSegment (Sum.inr e) = (Sum.inr e, true) := (rfl)

/-- The nonempty cyclic orbit of segmented sides traced by `F.nextSide` starting from `x`. -/
noncomputable def sideCycle (x : F.Side) : Cycle F.Side :=
  letI := Fintype.ofFinite F.Side
  letI := Classical.decEq F.Side
  if F.nextSide x = x then ([x] : List F.Side) else F.nextSide.toList x

theorem mem_sideCycle_self (x : F.Side) : x ∈ F.sideCycle x := by
  let _ := Fintype.ofFinite F.Side
  let _ := Classical.decEq F.Side
  unfold sideCycle
  split_ifs with hx
  · simp
  · rw [Cycle.mem_coe_iff, Equiv.Perm.mem_toList_iff]
    exact ⟨Equiv.Perm.SameCycle.refl _ _, Equiv.Perm.mem_support.mpr hx⟩

theorem sideCycle_ne_nil (x : F.Side) : F.sideCycle x ≠ Cycle.nil := by
  intro h
  have hx := F.mem_sideCycle_self x
  rw [h] at hx
  simp at hx

theorem nodup_sideCycle (x : F.Side) : (F.sideCycle x).Nodup := by
  let _ := Fintype.ofFinite F.Side
  let _ := Classical.decEq F.Side
  unfold sideCycle
  split_ifs
  · simp
  · exact Cycle.nodup_coe_iff.mpr (Equiv.Perm.nodup_toList F.nextSide x)

/-- Two segmented sides generate the exact same cyclic side orbit iff they lie on the same boundary
component. -/
theorem sideCycle_eq_iff (x y : F.Side) :
    F.sideCycle x = F.sideCycle y ↔ F.sideBoundary x = F.sideBoundary y := by
  let _ := Fintype.ofFinite F.Side
  let _ := Classical.decEq F.Side
  rw [F.sideBoundary_eq_iff]
  constructor
  · intro h
    have hx : x ∈ F.sideCycle y := h ▸ F.mem_sideCycle_self x
    unfold sideCycle at hx
    split_ifs at hx with hy
    · rw [Cycle.mem_coe_iff, List.mem_singleton] at hx
      exact hx ▸ Equiv.Perm.SameCycle.refl _ _
    · rw [Cycle.mem_coe_iff, Equiv.Perm.mem_toList_iff] at hx
      exact hx.1.symm
  · intro hxy
    change F.nextSide.SameCycle x y at hxy
    by_cases hx : F.nextSide x = x <;> by_cases hy : F.nextSide y = y <;>
      simp only [sideCycle, hx, hy, ↓reduceIte]
    · obtain ⟨k, rfl⟩ := hxy
      rw [Function.IsFixedPt.perm_zpow hx k]
    · exfalso
      apply hy
      exact Equiv.Perm.notMem_support.mp
        (mt hxy.mem_support_iff.mpr (Equiv.Perm.notMem_support.mpr hx))
    · exfalso
      apply hx
      exact Equiv.Perm.notMem_support.mp
        (mt hxy.mem_support_iff.mp (Equiv.Perm.notMem_support.mpr hy))
    · exact Cycle.coe_eq_coe.mpr hxy.toList_isRotated

/-- Nonempty signed cyclic word of seams and boundary edges along the segmented boundary component
containing `x`. -/
noncomputable def sideWord (x : F.Side) : Cycle ((F.Seam ⊕ W.Edge) × Bool) :=
  (F.sideCycle x).map F.signedSegment

theorem sideWord_ne_nil (x : F.Side) : F.sideWord x ≠ Cycle.nil := by
  intro h
  have hx : F.signedSegment x ∈ F.sideWord x :=
    Cycle.mem_map.mpr ⟨x, F.mem_sideCycle_self x, rfl⟩
  rw [h] at hx
  simp at hx

theorem sideWord_eq_of_sideBoundary_eq {x y : F.Side}
    (h : F.sideBoundary x = F.sideBoundary y) : F.sideWord x = F.sideWord y := by
  rw [sideWord, sideWord, (F.sideCycle_eq_iff x y).mpr h]

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
  rw [vertexSectorFacet, ← F.sideFacet_nextSide (F.cornerIncoming (Sum.inl (v, e))),
    nextSide_apply, Equiv.symm_apply_apply]

/-- Seam-end handshake identity: four ends per interior vertex plus one end per boundary vertex
equals two ends per interval seam. -/
theorem card_seamEnds :
    4 * Nat.card F.Vertex + Nat.card W.Vertex = 2 * Nat.card F.Seam := by
  have h := Nat.card_congr F.seamEnds
  simp only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  omega

/-- Corner-side count identity: six corners per interior vertex plus three corners per boundary
vertex equals three sheet sides per interval seam plus one side per boundary edge. -/
theorem card_corners_eq_card_sides :
    6 * Nat.card F.Vertex + 3 * Nat.card W.Vertex =
      3 * Nat.card F.Seam + Nat.card W.Edge := by
  have h := Nat.card_congr F.cornerIncoming
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

/-- Boundary corner data of `F` recovers the full incidence equivalence `W.ends` on `W`. -/
theorem boundary_corner_recovers_ends (w : W.Vertex) (i : Fin 3) :
    W.ends (w, i) =
      match F.cornerIncoming (Sum.inr (w, i)), F.cornerOutgoing (Sum.inr (w, i)) with
      | Sum.inr e, _ => (e, true)
      | _, Sum.inr e => (e, false)
      | Sum.inl _, Sum.inl _ => W.ends (w, i) := by
  change W.ends (w, i) =
    match (if (W.ends (w, i)).2 then Sum.inr (W.ends (w, i)).1
           else Sum.inl ((F.seamEnds (Sum.inr w)).1, i)),
          (if (W.ends (w, i)).2 then Sum.inl ((F.seamEnds (Sum.inr w)).1, i)
           else Sum.inr (W.ends (w, i)).1) with
    | Sum.inr e, _ => (e, true)
    | _, Sum.inr e => (e, false)
    | Sum.inl _, Sum.inl _ => W.ends (w, i)
  rcases W.ends (w, i) with ⟨e, _ | _⟩ <;> rfl

/-! ### Facet Euler characteristic and nilvalent prefoams -/

/-- Number of boundary components of a facet `f`. -/
noncomputable def numBoundaryComponents (f : F.Facet) : ℕ :=
  Nat.card (F.FacetBoundary f)

theorem numBoundaryComponents_def (f : F.Facet) :
    F.numBoundaryComponents f = Nat.card (F.FacetBoundary f) := (rfl)

/-- Euler characteristic `χ(f) = 2 - 2g(f) - b(f)` of a compact connected oriented surface facet
of genus `g(f)` with `b(f)` boundary components. -/
noncomputable def facetEulerChar (f : F.Facet) : ℤ :=
  2 - 2 * (F.genus f : ℤ) - (F.numBoundaryComponents f : ℤ)

theorem facetEulerChar_def (f : F.Facet) :
    F.facetEulerChar f = 2 - 2 * (F.genus f : ℤ) - (F.numBoundaryComponents f : ℤ) := (rfl)

/-- A prefoam is nilvalent when it has no interior singular vertices, interval seams, or circular
seams. -/
def IsNilvalent : Prop :=
  IsEmpty F.Vertex ∧ IsEmpty F.Seam ∧ IsEmpty F.SeamCircle

theorem isNilvalent_def :
    F.IsNilvalent ↔ IsEmpty F.Vertex ∧ IsEmpty F.Seam ∧ IsEmpty F.SeamCircle := Iff.rfl

/-- Absence of seams automatically forces `F.Vertex` to be empty via `seamEnds`. -/
theorem isNilvalent_iff : F.IsNilvalent ↔ IsEmpty F.Seam ∧ IsEmpty F.SeamCircle :=
  ⟨fun ⟨_, hs, hc⟩ ↦ ⟨hs, hc⟩, fun ⟨hs, hc⟩ ↦
    ⟨⟨fun v ↦ hs.false (F.seamEnds (Sum.inl (v, 0))).1⟩, hs, hc⟩⟩

end BasicAPI

theorem IsNilvalent.isEmpty_boundary_vertex {W : ClosedWeb.{u}} {F : FoamWithBoundary W}
    (h : F.IsNilvalent) : IsEmpty W.Vertex :=
  ⟨fun w ↦ h.2.1.false (F.seamEnds (Sum.inr w)).1⟩

theorem IsNilvalent.isEmpty_boundary_edge {W : ClosedWeb.{u}} {F : FoamWithBoundary W}
    (h : F.IsNilvalent) : IsEmpty W.Edge :=
  have := h.isEmpty_boundary_vertex
  ⟨fun e ↦ isEmptyElim (W.ends.symm (e, false)).1⟩

theorem IsNilvalent.isEmpty_side {W : ClosedWeb.{u}} {F : FoamWithBoundary W}
    (h : F.IsNilvalent) : IsEmpty F.Side := by
  have := h.2.1
  have := h.isEmpty_boundary_edge
  infer_instance

/-- On a nilvalent prefoam, boundary components correspond bijectively to the circles of `W`. -/
noncomputable def IsNilvalent.circleEquivBoundary {W : ClosedWeb.{u}} {F : FoamWithBoundary W}
    (h : F.IsNilvalent) : W.Circle ≃ F.Boundary :=
  Equiv.ofBijective (fun c ↦ F.circleBoundary (Sum.inr c))
    ⟨fun _ _ hab ↦ Sum.inr.inj (F.circleBoundary_injective hab),
     fun b ↦ by
      rcases F.boundary_surjective b with ⟨x, rfl⟩ | ⟨⟨sc, _⟩ | c, rfl⟩
      · exact h.isEmpty_side.elim x
      · exact h.2.2.elim sc
      · exact ⟨c, rfl⟩⟩

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

/-- A boundary-fixing isomorphism of prefoams over the same closed web `W`. -/
abbrev Iso {W : ClosedWeb.{u}} (F G : FoamWithBoundary W) : Type u :=
  F.IsoOver (ClosedWeb.Iso.refl W) G

namespace IsoOver

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}}

/-- Reindex the underlying boundary web isomorphism along an equality. -/
def cast {φ₁ φ₂ : W.Iso V} (h : φ₁ = φ₂) {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ₁ G) : F.IsoOver φ₂ G := by
  subst h
  exact ψ

/-- Equivalence on segmented sides induced by `ψ : F.IsoOver φ G`. -/
def sideEquiv {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) : F.Side ≃ G.Side :=
  (ψ.seam.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge

/-- Equivalence on circle sides induced by `ψ : F.IsoOver φ G`. -/
def circleSideEquiv {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) : F.CircleSide ≃ G.CircleSide :=
  (ψ.seamCircle.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle

/-- Equivalence on corners induced by `ψ : F.IsoOver φ G`. -/
def cornerEquiv {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) : F.Corner ≃ G.Corner :=
  (ψ.vertex.prodCongr (Equiv.refl (Fin 6))).sumCongr (φ.vertex.prodCongr (Equiv.refl (Fin 3)))

/-- Identity isomorphism of `F` over `ClosedWeb.Iso.refl W`. -/
def refl (F : FoamWithBoundary W) : F.Iso F where
  vertex := Equiv.refl _
  seam := Equiv.refl _
  seamCircle := Equiv.refl _
  facet := Equiv.refl _
  boundary := Equiv.refl _
  map_chirality _ := rfl
  map_seamEnds x := by rcases x with ⟨v, k⟩ | w <;> simp [ClosedWeb.Iso.refl_vertex]
  map_genus _ := rfl
  map_boundaryFacet _ := rfl
  map_sideBoundary x := by rcases x with ⟨s, i⟩ | e <;> simp [ClosedWeb.Iso.refl_edge]
  map_circleBoundary z := by rcases z with ⟨c, i⟩ | c <;> simp [ClosedWeb.Iso.refl_circle]

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
  map_chirality v := by rw [Equiv.trans_apply, ψ₂.map_chirality, ψ₁.map_chirality]
  map_seamEnds x := by
    have hsum : Sum.map (Prod.map (ψ₁.vertex.trans ψ₂.vertex) id) (φ₁.trans φ₂).vertex x =
        Sum.map (Prod.map ψ₂.vertex id) φ₂.vertex
          (Sum.map (Prod.map ψ₁.vertex id) φ₁.vertex x) := by
      rcases x with ⟨v, k⟩ | w <;> simp
    rw [hsum, ψ₂.map_seamEnds, ψ₁.map_seamEnds]
    rcases F.seamEnds x with ⟨s, b⟩
    rfl
  map_genus f := by rw [Equiv.trans_apply, ψ₂.map_genus, ψ₁.map_genus]
  map_boundaryFacet b := by simp [ψ₂.map_boundaryFacet, ψ₁.map_boundaryFacet]
  map_sideBoundary x := by
    have hsum : Sum.map (Prod.map (ψ₁.seam.trans ψ₂.seam) id) (φ₁.trans φ₂).edge x =
        Sum.map (Prod.map ψ₂.seam id) φ₂.edge (Sum.map (Prod.map ψ₁.seam id) φ₁.edge x) := by
      rcases x with ⟨s, i⟩ | e <;> simp
    rw [hsum, ψ₂.map_sideBoundary, ψ₁.map_sideBoundary]
    rfl
  map_circleBoundary z := by
    have hsum : Sum.map (Prod.map (ψ₁.seamCircle.trans ψ₂.seamCircle) id) (φ₁.trans φ₂).circle z =
        Sum.map (Prod.map ψ₂.seamCircle id) φ₂.circle
          (Sum.map (Prod.map ψ₁.seamCircle id) φ₁.circle z) := by
      rcases z with ⟨c, i⟩ | c <;> simp
    rw [hsum, ψ₂.map_circleBoundary, ψ₁.map_circleBoundary]
    rfl

/-- Every isomorphism commutes with `cornerIncoming`. -/
theorem map_cornerIncoming {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) (c : F.Corner) :
    G.cornerIncoming (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerIncoming c) := by
  rcases c with ⟨v, e⟩ | ⟨w, i⟩
  · have hc : ψ.cornerEquiv (Sum.inl (v, e)) = Sum.inl (ψ.vertex v, e) := rfl
    rw [hc]
    dsimp only [sideEquiv, cornerIncoming, cornerIncomingEquiv, cornerIncomingFun,
      Equiv.coe_fn_mk]
    rw [ψ.map_chirality v]
    set ki := (ClosedWeb.tetWeb (F.chirality v)).ends.symm (e, true)
    have hse := congrArg Prod.fst (ψ.map_seamEnds (Sum.inl (v, ki.1)))
    dsimp only [Sum.map_inl, Prod.map_apply, id_eq] at hse
    rw [hse]
    rfl
  · have hc : ψ.cornerEquiv (Sum.inr (w, i)) = Sum.inr (φ.vertex w, i) := rfl
    rw [hc]
    dsimp only [sideEquiv, cornerIncoming, cornerIncomingEquiv, cornerIncomingFun,
      Equiv.coe_fn_mk]
    rw [φ.map_ends_apply w i]
    have hse := congrArg Prod.fst (ψ.map_seamEnds (Sum.inr w))
    dsimp only [Sum.map_inr, Prod.map_apply] at hse
    cases (W.ends (w, i)).2 <;> simp [hse]

/-- Every isomorphism commutes with `cornerOutgoing`. -/
theorem map_cornerOutgoing {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) (c : F.Corner) :
    G.cornerOutgoing (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerOutgoing c) := by
  rcases c with ⟨v, e⟩ | ⟨w, i⟩
  · have hc : ψ.cornerEquiv (Sum.inl (v, e)) = Sum.inl (ψ.vertex v, e) := rfl
    rw [hc]
    dsimp only [sideEquiv, cornerOutgoing, cornerOutgoingEquiv, cornerOutgoingFun,
      Equiv.coe_fn_mk]
    rw [ψ.map_chirality v]
    set ki := (ClosedWeb.tetWeb (F.chirality v)).ends.symm (e, false)
    have hse := congrArg Prod.fst (ψ.map_seamEnds (Sum.inl (v, ki.1)))
    dsimp only [Sum.map_inl, Prod.map_apply, id_eq] at hse
    rw [hse]
    rfl
  · have hc : ψ.cornerEquiv (Sum.inr (w, i)) = Sum.inr (φ.vertex w, i) := rfl
    rw [hc]
    dsimp only [sideEquiv, cornerOutgoing, cornerOutgoingEquiv, cornerOutgoingFun,
      Equiv.coe_fn_mk]
    rw [φ.map_ends_apply w i]
    have hse := congrArg Prod.fst (ψ.map_seamEnds (Sum.inr w))
    dsimp only [Sum.map_inr, Prod.map_apply] at hse
    cases (W.ends (w, i)).2 <;> simp [hse]

/-- Every isomorphism intertwines `nextSide` via `sideEquiv`. -/
theorem map_nextSide {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) (x : F.Side) :
    G.nextSide (ψ.sideEquiv x) = ψ.sideEquiv (F.nextSide x) := by
  obtain ⟨c, rfl⟩ := F.cornerIncoming.surjective x
  rw [← ψ.map_cornerIncoming c, nextSide_apply, nextSide_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, ψ.map_cornerOutgoing c]

theorem nextSide_eq_permCongr {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) : G.nextSide = ψ.sideEquiv.permCongr F.nextSide := by
  ext y
  obtain ⟨x, rfl⟩ := ψ.sideEquiv.surjective y
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, ψ.map_nextSide]

/-- Equivalence of boundary component fibres over `f` and `ψ.facet f`. -/
def facetBoundaryEquiv {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) (f : F.Facet) :
    F.FacetBoundary f ≃ G.FacetBoundary (ψ.facet f) where
  toFun b := ⟨ψ.boundary b.1, by rw [ψ.map_boundaryFacet, b.2]⟩
  invFun b := ⟨ψ.boundary.symm b.1, ψ.facet.injective (by
    rw [← ψ.map_boundaryFacet, ψ.boundary.apply_symm_apply, b.2])⟩
  left_inv b := Subtype.ext (ψ.boundary.symm_apply_apply b.1)
  right_inv b := Subtype.ext (ψ.boundary.apply_symm_apply b.1)

/-- Isomorphisms preserve the number of boundary components of each facet. -/
theorem map_numBoundaryComponents {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) (f : F.Facet) :
    G.numBoundaryComponents (ψ.facet f) = F.numBoundaryComponents f :=
  (Nat.card_congr (ψ.facetBoundaryEquiv f)).symm

/-- Isomorphisms preserve the Euler characteristic of each facet. -/
theorem map_facetEulerChar {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) (f : F.Facet) :
    G.facetEulerChar (ψ.facet f) = F.facetEulerChar f := by
  simp only [facetEulerChar, ψ.map_genus, ψ.map_numBoundaryComponents]

/-- Isomorphisms preserve nilvalence. -/
theorem isNilvalent_iff {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) : F.IsNilvalent ↔ G.IsNilvalent :=
  and_congr ψ.vertex.isEmpty_congr
    (and_congr ψ.seam.isEmpty_congr ψ.seamCircle.isEmpty_congr)

end IsoOver

namespace Iso

variable {W : ClosedWeb.{u}} {F G H : FoamWithBoundary W}

/-- Identity boundary-fixing isomorphism. -/
abbrev refl (F : FoamWithBoundary W) : F.Iso F := IsoOver.refl F

/-- Inverse of a boundary-fixing isomorphism. -/
def symm (ψ : F.Iso G) : G.Iso F :=
  IsoOver.cast
    (ClosedWeb.Iso.ext (Equiv.ext fun _ ↦ by simp) (Equiv.ext fun _ ↦ by simp)
      (Equiv.ext fun _ ↦ by simp))
    (IsoOver.symm ψ)

/-- Composition of boundary-fixing isomorphisms. -/
def trans (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) : F.Iso H :=
  IsoOver.cast (ClosedWeb.Iso.refl_trans _) (IsoOver.trans ψ₁ ψ₂)

end Iso

/-! ### Transport along boundary web isomorphisms and the empty prefoam -/

private theorem transport_cornerIncomingFun {Vertex₁ Seam₁ : Type u} {W₁ : ClosedWeb.{u}}
    {Vertex₂ Seam₂ : Type v} {W₂ : ClosedWeb.{v}}
    (φ : W₁.Iso W₂) (eV : Vertex₁ ≃ Vertex₂) (eS : Seam₁ ≃ Seam₂)
    (chirality₁ : Vertex₁ → Bool)
    (seamEnds₁ : (Vertex₁ × Fin 4) ⊕ W₁.Vertex ≃ Seam₁ × Bool)
    (c : (Vertex₁ × Fin 6) ⊕ (W₁.Vertex × Fin 3)) :
    cornerIncomingFun (chirality₁ ∘ eV.symm)
        ((((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans seamEnds₁).trans
          (eS.prodCongr (Equiv.refl Bool)))
        (((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
          (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) c) =
      ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge)
        (cornerIncomingFun chirality₁ seamEnds₁ c) := by
  rcases c with ⟨v, e⟩ | ⟨w, i⟩
  · have hc : ((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
        (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) (Sum.inl (v, e)) = Sum.inl (eV v, e) := rfl
    rw [hc]
    dsimp only [cornerIncomingFun, Equiv.trans_apply, Function.comp_apply]
    rw [eV.symm_apply_apply]
    have hs : (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm)
        (Sum.inl (eV v, ((ClosedWeb.tetWeb (chirality₁ v)).ends.symm (e, true)).1))) =
        Sum.inl (v, ((ClosedWeb.tetWeb (chirality₁ v)).ends.symm (e, true)).1) := by simp
    rw [hs]
    rfl
  · have hc : ((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
        (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) (Sum.inr (w, i)) =
        Sum.inr (φ.vertex w, i) := rfl
    rw [hc]
    dsimp only [cornerIncomingFun, Equiv.trans_apply]
    rw [φ.map_ends_apply w i]
    have hs : (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm)
        (Sum.inr (φ.vertex w))) = Sum.inr w := by simp
    rw [hs]
    cases (W₁.ends (w, i)).2 <;> rfl

private theorem transport_cornerOutgoingFun {Vertex₁ Seam₁ : Type u} {W₁ : ClosedWeb.{u}}
    {Vertex₂ Seam₂ : Type v} {W₂ : ClosedWeb.{v}}
    (φ : W₁.Iso W₂) (eV : Vertex₁ ≃ Vertex₂) (eS : Seam₁ ≃ Seam₂)
    (chirality₁ : Vertex₁ → Bool)
    (seamEnds₁ : (Vertex₁ × Fin 4) ⊕ W₁.Vertex ≃ Seam₁ × Bool)
    (c : (Vertex₁ × Fin 6) ⊕ (W₁.Vertex × Fin 3)) :
    cornerOutgoingFun (chirality₁ ∘ eV.symm)
        ((((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans seamEnds₁).trans
          (eS.prodCongr (Equiv.refl Bool)))
        (((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
          (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) c) =
      ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge)
        (cornerOutgoingFun chirality₁ seamEnds₁ c) := by
  rcases c with ⟨v, e⟩ | ⟨w, i⟩
  · have hc : ((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
        (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) (Sum.inl (v, e)) = Sum.inl (eV v, e) := rfl
    rw [hc]
    dsimp only [cornerOutgoingFun, Equiv.trans_apply, Function.comp_apply]
    rw [eV.symm_apply_apply]
    have hs : (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm)
        (Sum.inl (eV v, ((ClosedWeb.tetWeb (chirality₁ v)).ends.symm (e, false)).1))) =
        Sum.inl (v, ((ClosedWeb.tetWeb (chirality₁ v)).ends.symm (e, false)).1) := by simp
    rw [hs]
    rfl
  · have hc : ((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
        (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) (Sum.inr (w, i)) =
        Sum.inr (φ.vertex w, i) := rfl
    rw [hc]
    dsimp only [cornerOutgoingFun, Equiv.trans_apply]
    rw [φ.map_ends_apply w i]
    have hs : (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm)
        (Sum.inr (φ.vertex w))) = Sum.inr w := by simp
    rw [hs]
    cases (W₁.ends (w, i)).2 <;> rfl

private theorem transport_nextSidePerm {Vertex₁ Seam₁ : Type u} {W₁ : ClosedWeb.{u}}
    {Vertex₂ Seam₂ : Type v} {W₂ : ClosedWeb.{v}}
    (φ : W₁.Iso W₂) (eV : Vertex₁ ≃ Vertex₂) (eS : Seam₁ ≃ Seam₂)
    (chirality₁ : Vertex₁ → Bool)
    (seamEnds₁ : (Vertex₁ × Fin 4) ⊕ W₁.Vertex ≃ Seam₁ × Bool)
    (h_inl₁ : ∀ v k,
      (seamEnds₁ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₁ v)).ends (k, 0)).2)
    (h_inr₁ : ∀ w, (seamEnds₁ (Sum.inr w)).2 = (W₁.ends (w, 0)).2) :
    let chirality₂ := chirality₁ ∘ eV.symm
    let seamEnds₂ := (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans
      seamEnds₁).trans (eS.prodCongr (Equiv.refl Bool))
    have h_inl₂ : ∀ v k,
        (seamEnds₂ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₂ v)).ends (k, 0)).2 :=
      fun v k ↦ h_inl₁ (eV.symm v) k
    have h_inr₂ : ∀ w, (seamEnds₂ (Sum.inr w)).2 = (W₂.ends (w, 0)).2 := fun w ↦ by
      have hw := congrArg Prod.snd (φ.map_ends_apply (φ.vertex.symm w) 0)
      rw [φ.vertex.apply_symm_apply] at hw
      exact (h_inr₁ (φ.vertex.symm w)).trans hw.symm
    nextSidePerm chirality₂ seamEnds₂ h_inl₂ h_inr₂ =
      ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge).permCongr
        (nextSidePerm chirality₁ seamEnds₁ h_inl₁ h_inr₁) := by
  intro chirality₂ seamEnds₂ h_inl₂ h_inr₂
  set eSide := (eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge
  ext y
  obtain ⟨x, rfl⟩ := eSide.surjective y
  obtain ⟨c, rfl⟩ := (cornerIncomingEquiv chirality₁ seamEnds₁ h_inl₁ h_inr₁).surjective x
  have hInc : cornerIncomingEquiv chirality₂ seamEnds₂ h_inl₂ h_inr₂
      (((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) c) =
      eSide (cornerIncomingEquiv chirality₁ seamEnds₁ h_inl₁ h_inr₁ c) :=
    transport_cornerIncomingFun φ eV eS chirality₁ seamEnds₁ c
  have hOut : cornerOutgoingEquiv chirality₂ seamEnds₂ h_inl₂ h_inr₂
      (((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) c) =
      eSide (cornerOutgoingEquiv chirality₁ seamEnds₁ h_inl₁ h_inr₁ c) :=
    transport_cornerOutgoingFun φ eV eS chirality₁ seamEnds₁ c
  rw [Equiv.permCongr_apply, eSide.symm_apply_apply, ← hInc]
  dsimp only [nextSidePerm, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hOut]

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
  seamEnds_inl_snd v k := F.seamEnds_inl_snd (eV.symm v) k
  seamEnds_inr_snd w := by
    have hw := congrArg Prod.snd (φ.map_ends_apply (φ.vertex.symm w) 0)
    rw [φ.vertex.apply_symm_apply] at hw
    exact (F.seamEnds_inr_snd (φ.vertex.symm w)).trans hw.symm
  genus := F.genus ∘ eF.symm
  boundaryFacet := eF ∘ F.boundaryFacet ∘ eB.symm
  sideBoundary :=
    eB ∘ F.sideBoundary ∘ ((eS.symm.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge.symm)
  circleBoundary :=
    eB ∘ F.circleBoundary ∘ ((eSC.symm.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle.symm)
  sideBoundary_eq_iff x y := by
    rw [transport_nextSidePerm φ eV eS F.chirality F.seamEnds
      F.seamEnds_inl_snd F.seamEnds_inr_snd]
    set eSide := (eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge
    have hx : ((eS.symm.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge.symm) x = eSide.symm x :=
      rfl
    have hy : ((eS.symm.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge.symm) y = eSide.symm y :=
      rfl
    dsimp only [Function.comp_apply]
    rw [hx, hy, eB.apply_eq_iff_eq, F.sideBoundary_eq_iff]
    exact (Equiv.Perm.sameCycle_permCongr_iff (σ := F.nextSide) eSide).symm
  circleBoundary_injective := eB.injective.comp
    (F.circleBoundary_injective.comp
      ((eSC.symm.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle.symm).injective)
  sideBoundary_ne_circleBoundary x z h :=
    F.sideBoundary_ne_circleBoundary _ _ (eB.injective h)
  boundary_surjective b := by
    rcases F.boundary_surjective (eB.symm b) with ⟨x, hx⟩ | ⟨z, hz⟩
    · left
      set eSide := (eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge
      refine ⟨eSide x, ?_⟩
      change eB (F.sideBoundary (eSide.symm (eSide x))) = b
      rw [eSide.symm_apply_apply, hx, eB.apply_symm_apply]
    · right
      set eCSide := (eSC.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle
      refine ⟨eCSide z, ?_⟩
      change eB (F.circleBoundary (eCSide.symm (eCSide z))) = b
      rw [eCSide.symm_apply_apply, hz, eB.apply_symm_apply]

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
  map_seamEnds x := by
    rcases x with ⟨v, k⟩ | w
    · have hs : (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm)
          (Sum.inl (eV v, k))) = Sum.inl (v, k) := by simp
      dsimp only [relabelOver, Sum.map_inl, Prod.map_apply, id_eq, Equiv.trans_apply]
      rw [hs]
      rcases F.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · have hs : (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm)
          (Sum.inr (φ.vertex w))) = Sum.inr w := by simp
      dsimp only [relabelOver, Sum.map_inr, Equiv.trans_apply]
      rw [hs]
      rcases F.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
  map_genus f := by simp [relabelOver]
  map_boundaryFacet b := by simp [relabelOver]
  map_sideBoundary x := by
    rcases x with ⟨s, i⟩ | e <;> simp [relabelOver]
  map_circleBoundary z := by
    rcases z with ⟨c, i⟩ | c <;> simp [relabelOver]

/-- Transport a prefoam `F : FoamWithBoundary W` along a boundary web isomorphism `φ : W.Iso V`
within the same universe. -/
abbrev mapBoundary {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V) :
    FoamWithBoundary V :=
  F.relabelOver φ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

/-- Canonical isomorphism `F.IsoOver φ (F.mapBoundary φ)`. -/
def mapBoundaryIso {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V) :
    F.IsoOver φ (F.mapBoundary φ) :=
  F.relabelOverIso φ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

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

theorem isNilvalent_empty : (empty.{u}).IsNilvalent :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end FoamWithBoundary

end TauCeti
