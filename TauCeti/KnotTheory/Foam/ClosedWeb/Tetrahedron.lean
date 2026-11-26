/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import TauCeti.KnotTheory.Foam.ClosedWeb.Basic
import Mathlib.Tactic.FinCases

/-!
# Oriented tetrahedral closed webs

At an interior singular vertex of a foam, a small linking sphere meets the four incident seams
and six local facet sectors in an oriented tetrahedral web on `K₄`. Up to web isomorphism there
are two chiralities, related by reversing all local cyclic orders (`ClosedWeb.mirror`) and also
by reversing all edge orientations (`ClosedWeb.reverse`).

`ClosedWeb.tetWeb` packages both chiralities on the common vertex carrier `Fin 4` (two merges
`0, 1` and two splits `2, 3`) and edge carrier `Fin 6`, with `ClosedWeb.tetrahedronPos` (`true`)
and `ClosedWeb.tetrahedronNeg` (`false`) as the two specializations:

* Edge `0` runs `1 → 2` (the thick edge of total weight `(a + b) + c = a + (b + c)`).
* Edge `1` runs `2 → 3` and edge `2` runs `0 → 1` (the two intermediate edges).
* Edges `3`, `4`, `5` run `2 → 0`, `3 → 0`, `3 → 1` (the three thin edges).

Each chirality has trivial automorphism group (`ClosedWeb.instUniqueIsoTetWeb`), the two
chiralities are not isomorphic (`ClosedWeb.isEmpty_iso_tetWeb_not`), and reversing edge
orientations exchanges them (`ClosedWeb.tetWebReverseIso`). Finally, we verify the two local-link
properties of `tetWeb`: ordered noncommutative semigroup flows (`ClosedWeb.IsAdditiveFlow`) on the
two chiralities express semigroup associativity in the two opposite multiplication orders
(Goertz–Marino–Wedrich), and every nonempty single-pigment interval-edge selection
(`ClosedWeb.IsMonochromeEdgeSelection`, which determines the full monochrome subweb since
`tetWeb c` has no vertex-free circles) on `tetWeb c` is one of three simple directed cycles of
lengths `3`, `4`, and `3` (Robert–Wagner), ensuring that coning a monochrome subweb at a singular
foam vertex produces at most one disk rather than a pinched cone.

## References

* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1, Remark 2.2, and Lemma 2.5.
* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definitions 2.1, 2.4–2.5, and 3.12.
-/

public section

namespace TauCeti.ClosedWeb

/-- Explicit local-slot map of the positive oriented tetrahedral web on `Fin 4` and `Fin 6`. -/
@[expose] def tetrahedronPosEndsFun : Fin 4 × Fin 3 → Fin 6 × Bool
  | (0, 0) => (2, false)
  | (0, 1) => (3, true)
  | (0, 2) => (4, true)
  | (1, 0) => (0, false)
  | (1, 1) => (2, true)
  | (1, 2) => (5, true)
  | (2, 0) => (0, true)
  | (2, 1) => (3, false)
  | (2, 2) => (1, false)
  | (3, 0) => (1, true)
  | (3, 1) => (4, false)
  | (3, 2) => (5, false)

/-- Explicit inverse of `tetrahedronPosEndsFun`, sending each directed edge end to its vertex
and local slot. -/
@[expose] def tetrahedronPosEndsInv : Fin 6 × Bool → Fin 4 × Fin 3
  | (0, false) => (1, 0)
  | (0, true) => (2, 0)
  | (1, false) => (2, 2)
  | (1, true) => (3, 0)
  | (2, false) => (0, 0)
  | (2, true) => (1, 1)
  | (3, false) => (2, 1)
  | (3, true) => (0, 1)
  | (4, false) => (3, 1)
  | (4, true) => (0, 2)
  | (5, false) => (3, 2)
  | (5, true) => (1, 2)

/-- The incidence equivalence `Fin 4 × Fin 3 ≃ Fin 6 × Bool` of the positive tetrahedral web. -/
@[expose] def tetrahedronPosEnds : Fin 4 × Fin 3 ≃ Fin 6 × Bool where
  toFun := tetrahedronPosEndsFun
  invFun := tetrahedronPosEndsInv
  left_inv := by rintro ⟨v, i⟩; fin_cases v <;> fin_cases i <;> rfl
  right_inv := by rintro ⟨e, b⟩; fin_cases e <;> cases b <;> rfl

@[simp] theorem tetrahedronPosEnds_apply (x : Fin 4 × Fin 3) :
    tetrahedronPosEnds x = tetrahedronPosEndsFun x := (rfl)

@[simp] theorem tetrahedronPosEnds_symm_apply (d : Fin 6 × Bool) :
    tetrahedronPosEnds.symm d = tetrahedronPosEndsInv d := (rfl)

/-- The oriented tetrahedral closed web of chirality `c` (`true` for positive, `false` for
negative). Defining both chiralities on the common carriers `Fin 4`, `Fin 6`, and `PEmpty` allows
seam and corner incidences at interior foam vertices to be indexed without dependent type casts. -/
abbrev tetWeb (c : Bool) : ClosedWeb where
  Vertex := Fin 4
  Edge := Fin 6
  Circle := PEmpty
  ends := (Equiv.prodCongr (Equiv.refl _)
    (if c then Equiv.refl (Fin 3) else Equiv.swap (1 : Fin 3) 2)).trans tetrahedronPosEnds
  orientation_one v := by fin_cases v <;> cases c <;> rfl
  orientation_two v := by fin_cases v <;> cases c <;> rfl

/-- The positive oriented tetrahedral closed web. -/
abbrev tetrahedronPos : ClosedWeb := tetWeb true

/-- The negative oriented tetrahedral closed web, obtained by mirroring cyclic orders. -/
abbrev tetrahedronNeg : ClosedWeb := tetWeb false

theorem tetWeb_ends_apply (c : Bool) (v : Fin 4) (i : Fin 3) :
    (tetWeb c).ends (v, i) =
      tetrahedronPosEndsFun (v, if c then i else Equiv.swap (1 : Fin 3) 2 i) := by
  cases c <;> rfl

/-- The odd end at each vertex of `tetWeb c` is independent of chirality. -/
theorem tetWeb_ends_zero (c : Bool) (v : Fin 4) :
    (tetWeb c).ends (v, 0) = tetrahedronPosEndsFun (v, 0) := by
  cases c <;> rfl

/-- Vertices `0, 1` have source odd ends and vertices `2, 3` have target odd ends. -/
theorem tetWeb_ends_zero_snd (c : Bool) (v : Fin 4) :
    ((tetWeb c).ends (v, 0)).2 = decide (2 ≤ v.val) := by
  fin_cases v <;> cases c <;> rfl

/-- Mirroring reverses the chirality of `tetWeb`. -/
@[simp] theorem mirror_tetWeb (c : Bool) : (tetWeb c).mirror = tetWeb (!c) := by
  have h : (tetWeb c).mirror.ends = (tetWeb (!c)).ends := by
    apply Equiv.ext
    rintro ⟨v, i⟩
    cases c <;> fin_cases v <;> fin_cases i <;> rfl
  simp only [mirror, tetWeb]
  congr 1

theorem mirror_tetrahedronPos : tetrahedronPos.mirror = tetrahedronNeg :=
  mirror_tetWeb true

theorem mirror_tetrahedronNeg : tetrahedronNeg.mirror = tetrahedronPos :=
  mirror_tetWeb false

/-- Incidence on `tetWeb c` is independent of chirality. -/
@[simp] theorem incident_tetWeb (c : Bool) (d : (tetWeb c).End) :
    (tetWeb c).incident d = (tetrahedronPosEndsInv d).1 := by
  rw [incident_def]
  rcases d with ⟨e, b⟩
  cases c <;> fin_cases e <;> cases b <;> rfl

/-- Source vertices on `tetWeb c` are independent of chirality. -/
@[simp] theorem source_tetWeb (c : Bool) (e : Fin 6) :
    (tetWeb c).source e = (tetrahedronPosEndsInv (e, false)).1 := by
  rw [source_def, incident_tetWeb]

/-- Target vertices on `tetWeb c` are independent of chirality. -/
@[simp] theorem target_tetWeb (c : Bool) (e : Fin 6) :
    (tetWeb c).target e = (tetrahedronPosEndsInv (e, true)).1 := by
  rw [target_def, incident_tetWeb]

/-- Vertices `0` and `1` are the two merges of `tetWeb c`. -/
@[simp] theorem isMerge_tetWeb (c : Bool) (v : Fin 4) :
    (tetWeb c).IsMerge v ↔ v.val < 2 := by
  rw [isMerge_def, tetWeb_ends_zero_snd]
  simp

/-- Vertices `2` and `3` are the two splits of `tetWeb c`. -/
@[simp] theorem isSplit_tetWeb (c : Bool) (v : Fin 4) :
    (tetWeb c).IsSplit v ↔ 2 ≤ v.val := by
  rw [isSplit_def, tetWeb_ends_zero_snd]
  simp

/-- Every edge of `tetWeb c` connects two distinct vertices (no self-loops). -/
theorem source_ne_target_tetWeb (c : Bool) (e : Fin 6) :
    (tetWeb c).source e ≠ (tetWeb c).target e := by
  cases c <;> fin_cases e <;> simp [source_def, incident_def, tetrahedronPosEndsInv]

/-- Underlying `K₄` completeness: every pair of distinct vertices in `tetWeb c` is joined by a
unique edge in one of the two directions. -/
theorem existsUnique_edge_tetWeb (c : Bool) {u v : Fin 4} (huv : u ≠ v) :
    ∃! e : Fin 6,
      ((tetWeb c).source e = u ∧ (tetWeb c).target e = v) ∨
        ((tetWeb c).source e = v ∧ (tetWeb c).target e = u) := by
  unfold ExistsUnique
  simp only [source_tetWeb, target_tetWeb]
  revert huv u v
  decide

private theorem iso_tetWeb_vertex_eq {c₁ c₂ : Bool} (f : (tetWeb c₁).Iso (tetWeb c₂))
    (v : Fin 4) : f.vertex v = v := by
  have hm : (tetWeb c₂).IsMerge (f.vertex v) ↔ (tetWeb c₁).IsMerge v := f.isMerge_vertex v
  have hi : (tetWeb c₂).incident
      (((tetWeb c₂).ends (f.vertex v, 0)).1, !((tetWeb c₂).ends (f.vertex v, 0)).2) =
      f.vertex ((tetWeb c₁).incident
        (((tetWeb c₁).ends (v, 0)).1, !((tetWeb c₁).ends (v, 0)).2)) := by
    rw [f.map_ends_apply v 0, f.map_incident]
  have hopp : (tetWeb c₂).IsMerge ((tetWeb c₂).incident
      (((tetWeb c₂).ends (f.vertex v, 0)).1, !((tetWeb c₂).ends (f.vertex v, 0)).2)) ↔
      (tetWeb c₁).IsMerge ((tetWeb c₁).incident
        (((tetWeb c₁).ends (v, 0)).1, !((tetWeb c₁).ends (v, 0)).2)) := by
    rw [hi, f.isMerge_vertex]
  rw [isMerge_tetWeb, isMerge_tetWeb] at hm
  rw [tetWeb_ends_zero, tetWeb_ends_zero, incident_tetWeb, incident_tetWeb,
    isMerge_tetWeb, isMerge_tetWeb] at hopp
  generalize f.vertex v = w at hm hopp ⊢
  fin_cases v <;> fin_cases w <;> simp [tetrahedronPosEndsFun, tetrahedronPosEndsInv] at hm hopp ⊢

/-- Each oriented tetrahedral web is rigid: its only self-isomorphism is the identity. -/
instance instUniqueIsoTetWeb (c : Bool) : Unique ((tetWeb c).Iso (tetWeb c)) where
  default := Iso.refl (tetWeb c)
  uniq f := by
    have hv := iso_tetWeb_vertex_eq f
    refine Iso.ext (Equiv.ext fun x ↦ ?_) (Equiv.ext fun x ↦ ?_) (Equiv.ext fun x ↦ x.elim)
    · simp only [Iso.refl_vertex, Equiv.refl_apply, hv x]
    · obtain ⟨⟨v, i⟩, hvi⟩ := (tetWeb c).ends.surjective (x, false)
      have hm : ((tetWeb c).ends (f.vertex v, i)).1 = f.edge ((tetWeb c).ends (v, i)).1 :=
        congrArg Prod.fst (f.map_ends_apply v i)
      rw [hv v, hvi] at hm
      simp only [Iso.refl_edge, Equiv.refl_apply, ← hm]

/-- Positive and negative oriented tetrahedral webs are not isomorphic. -/
instance isEmpty_iso_tetWeb_not (c : Bool) : IsEmpty ((tetWeb c).Iso (tetWeb (!c))) :=
  ⟨fun f ↦ by
    have hv := iso_tetWeb_vertex_eq f
    have hs := f.map_source ((tetWeb c).ends (1, 1)).1
    have hm : ((tetWeb (!c)).ends (f.vertex 1, 1)).1 = f.edge ((tetWeb c).ends (1, 1)).1 :=
      congrArg Prod.fst (f.map_ends_apply 1 1)
    rw [← hm, hv 1] at hs
    cases c <;>
      simp [tetrahedronPosEndsFun, tetrahedronPosEndsInv, hv] at hs⟩

/-- The two chiral tetrahedral models `tetrahedronPos` and `tetrahedronNeg` are not isomorphic. -/
theorem not_nonempty_iso_tetrahedronPos_tetrahedronNeg :
    ¬Nonempty (tetrahedronPos.Iso tetrahedronNeg) :=
  not_nonempty_iff.mpr (isEmpty_iso_tetWeb_not true)

/-- Edge involution carrying `(tetWeb c).reverse` to `tetWeb (!c)`, swapping edges `1 ↔ 2` and
`3 ↔ 5` while fixing `0` and `4`. -/
def tetRevEdgeEquiv : Fin 6 ≃ Fin 6 :=
  (Equiv.swap (1 : Fin 6) 2).trans (Equiv.swap 3 5)

theorem tetRevEdgeEquiv_def :
    tetRevEdgeEquiv = (Equiv.swap (1 : Fin 6) 2).trans (Equiv.swap 3 5) := (rfl)

@[simp] theorem tetRevEdgeEquiv_symm : tetRevEdgeEquiv.symm = tetRevEdgeEquiv := by
  ext e
  fin_cases e <;> simp [tetRevEdgeEquiv, Equiv.swap_apply_def]

@[simp] theorem tetRevEdgeEquiv_tetRevEdgeEquiv (e : Fin 6) :
    tetRevEdgeEquiv (tetRevEdgeEquiv e) = e := by
  have h := tetRevEdgeEquiv.apply_symm_apply e
  rwa [tetRevEdgeEquiv_symm] at h

@[simp] theorem tetRevEdgeEquiv_zero : tetRevEdgeEquiv 0 = 0 := by
  simp [tetRevEdgeEquiv, Equiv.swap_apply_def]

@[simp] theorem tetRevEdgeEquiv_one : tetRevEdgeEquiv 1 = 2 := by
  simp [tetRevEdgeEquiv, Equiv.swap_apply_def]

@[simp] theorem tetRevEdgeEquiv_two : tetRevEdgeEquiv 2 = 1 := by
  simp [tetRevEdgeEquiv, Equiv.swap_apply_def]

@[simp] theorem tetRevEdgeEquiv_three : tetRevEdgeEquiv 3 = 5 := by
  simp [tetRevEdgeEquiv, Equiv.swap_apply_def]

@[simp] theorem tetRevEdgeEquiv_four : tetRevEdgeEquiv 4 = 4 := by
  simp [tetRevEdgeEquiv, Equiv.swap_apply_def]

@[simp] theorem tetRevEdgeEquiv_five : tetRevEdgeEquiv 5 = 3 := by
  simp [tetRevEdgeEquiv, Equiv.swap_apply_def]

/-- Reversing all edge orientations of `tetWeb c` produces a web isomorphic to `tetWeb (!c)`. -/
def tetWebReverseIso (c : Bool) : (tetWeb c).reverse.Iso (tetWeb (!c)) where
  vertex := Fin.revPerm
  edge := tetRevEdgeEquiv
  circle := Equiv.refl PEmpty
  map_ends := by
    rintro ⟨v, i⟩
    cases c <;> fin_cases v <;> fin_cases i <;> rfl

@[simp] theorem tetWebReverseIso_vertex (c : Bool) :
    (tetWebReverseIso c).vertex = Fin.revPerm := (rfl)

@[simp] theorem tetWebReverseIso_edge (c : Bool) :
    (tetWebReverseIso c).edge = tetRevEdgeEquiv := (rfl)

@[simp] theorem tetWebReverseIso_circle (c : Bool) :
    (tetWebReverseIso c).circle = Equiv.refl PEmpty := (rfl)

/-! ### Semigroup flows and monochrome local cycles -/

/-- Additive flows on `tetrahedronPos` express the four merge/split equations linking thin weights
`(w 3, w 4, w 5)` through `(w 3 + w 4) + w 5` and `w 3 + (w 4 + w 5)`. -/
theorem isAdditiveFlow_tetrahedronPos_iff {S : Type*} [Add S] (w : Fin 6 → S) :
    tetrahedronPos.IsAdditiveFlow w ↔
      w 2 = w 3 + w 4 ∧ w 0 = w 2 + w 5 ∧ w 0 = w 3 + w 1 ∧ w 1 = w 4 + w 5 := by
  rw [isAdditiveFlow_def]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2, h 3⟩, fun ⟨h0, h1, h2, h3⟩ v ↦ by fin_cases v <;> assumption⟩

/-- Any additive flow on `tetrahedronPos` witnesses `(w 3 + w 4) + w 5 = w 3 + (w 4 + w 5)`. -/
theorem assoc_of_isAdditiveFlow_tetrahedronPos {S : Type*} [Add S] {w : Fin 6 → S}
    (hw : tetrahedronPos.IsAdditiveFlow w) :
    (w 3 + w 4) + w 5 = w 3 + (w 4 + w 5) := by
  obtain ⟨h2, h0, h0', h1⟩ := (isAdditiveFlow_tetrahedronPos_iff w).mp hw
  rw [← h2, ← h0, h0', h1]

/-- Additive flows on `tetrahedronNeg` express the opposite multiplication order
`(w 5 + w 4) + w 3 = w 5 + (w 4 + w 3)`. -/
theorem isAdditiveFlow_tetrahedronNeg_iff {S : Type*} [Add S] (w : Fin 6 → S) :
    tetrahedronNeg.IsAdditiveFlow w ↔
      w 2 = w 4 + w 3 ∧ w 0 = w 5 + w 2 ∧ w 0 = w 1 + w 3 ∧ w 1 = w 5 + w 4 := by
  rw [isAdditiveFlow_def]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2, h 3⟩, fun ⟨h0, h1, h2, h3⟩ v ↦ by fin_cases v <;> assumption⟩

/-- Any additive flow on `tetrahedronNeg` witnesses `(w 5 + w 4) + w 3 = w 5 + (w 4 + w 3)`. -/
theorem assoc_of_isAdditiveFlow_tetrahedronNeg {S : Type*} [Add S] {w : Fin 6 → S}
    (hw : tetrahedronNeg.IsAdditiveFlow w) :
    (w 5 + w 4) + w 3 = w 5 + (w 4 + w 3) := by
  obtain ⟨h2, h0, h0', h1⟩ := (isAdditiveFlow_tetrahedronNeg_iff w).mp hw
  rw [← h2, ← h0, h0', h1]

/-- The three elementary nonempty single-pigment simple cycles on `tetWeb c`, determined by which
thin edge among `3, 4, 5` carries the pigment: `{0, 2, 3}`, `{0, 1, 2, 4}`, and `{0, 1, 5}`. -/
def tetPigmentCycle : Fin 3 → Fin 6 → Bool
  | 0 => ![true, false, true, true, false, false]
  | 1 => ![true, true, true, false, true, false]
  | 2 => ![true, true, false, false, false, true]

@[simp] theorem tetPigmentCycle_zero :
    tetPigmentCycle 0 = ![true, false, true, true, false, false] := (rfl)

@[simp] theorem tetPigmentCycle_one :
    tetPigmentCycle 1 = ![true, true, true, false, true, false] := (rfl)

@[simp] theorem tetPigmentCycle_two :
    tetPigmentCycle 2 = ![true, true, false, false, false, true] := (rfl)

/-- Every elementary pigment cycle is a valid monochrome interval-edge selection on both
chiralities of `tetWeb`. -/
theorem isMonochromeEdgeSelection_tetPigmentCycle (c : Bool) (i : Fin 3) :
    (tetWeb c).IsMonochromeEdgeSelection (tetPigmentCycle i) := by
  rw [isMonochromeEdgeSelection_def]
  intro v
  cases c <;> fin_cases i <;> fin_cases v <;> decide

private theorem isMonochromeEdgeSelection_tetrahedronPos_iff (p : Fin 6 → Bool) :
    tetrahedronPos.IsMonochromeEdgeSelection p ↔
      p = (fun _ ↦ false) ∨ ∃ i : Fin 3, p = tetPigmentCycle i := by
  constructor
  · rw [isMonochromeEdgeSelection_def]
    intro hp
    have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
    rw [tetWeb_ends_apply, tetWeb_ends_apply, tetWeb_ends_apply] at h0 h1 h2 h3
    dsimp [tetrahedronPosEndsFun] at h0 h1 h2 h3
    cases hp3 : p 3 <;> cases hp4 : p 4 <;> cases hp5 : p 5 <;>
      first
      | (solve | simp_all)
      | (solve | left; funext e; fin_cases e <;> simp_all)
      | (solve | right; refine ⟨0, funext fun e ↦ ?_⟩; fin_cases e <;> simp_all)
      | (solve | right; refine ⟨1, funext fun e ↦ ?_⟩; fin_cases e <;> simp_all)
      | (solve | right; refine ⟨2, funext fun e ↦ ?_⟩; fin_cases e <;> simp_all)
  · rintro (rfl | ⟨i, rfl⟩)
    · rw [isMonochromeEdgeSelection_def]
      intro v; fin_cases v <;> decide
    · exact isMonochromeEdgeSelection_tetPigmentCycle true i

/-- Complete classification of monochrome interval-edge selections (hence of monochrome subwebs,
as `tetWeb c` has no vertex-free circles) on `tetWeb c` (Robert–Wagner Lemma 2.5 at a singular
vertex): `p` is either identically `false` or one of the three single simple cycles
`tetPigmentCycle 0`, `tetPigmentCycle 1`, `tetPigmentCycle 2`. -/
theorem isMonochromeEdgeSelection_tetWeb_iff (c : Bool) (p : Fin 6 → Bool) :
    (tetWeb c).IsMonochromeEdgeSelection p ↔
      p = (fun _ ↦ false) ∨ ∃ i : Fin 3, p = tetPigmentCycle i := by
  cases c
  · have hm : tetrahedronPos.mirror.IsMonochromeEdgeSelection p ↔
        tetrahedronNeg.IsMonochromeEdgeSelection p :=
      iff_of_eq (by congr! (config := { closePost := false }) 1; exact mirror_tetrahedronPos)
    exact hm.symm.trans ((tetrahedronPos.isMonochromeEdgeSelection_mirror p).trans
      (isMonochromeEdgeSelection_tetrahedronPos_iff p))
  · exact isMonochromeEdgeSelection_tetrahedronPos_iff p

/-- The three elementary pigment cycles on `tetWeb c` have edge counts `3`, `4`, and `3`. -/
theorem card_tetPigmentCycle (i : Fin 3) :
    Nat.card {e : Fin 6 // tetPigmentCycle i e = true} = ![3, 4, 3] i := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases i <;> decide

end TauCeti.ClosedWeb
