/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
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
orientations exchanges them (`ClosedWeb.tetWebReverseIso`). Finally, we establish the local-link
properties used by Robert–Wagner's foam evaluation: additive flows on the two chiralities express
the two sides of semigroup associativity, and every nonempty single-pigment subweb
(`IsMonochromeSubweb`) on `tetWeb c` is one of three simple directed cycles of lengths `3`, `4`,
and `3`, ensuring that coning a monochrome subweb at a singular foam vertex produces at most one
disk rather than a pinched cone.

## References

* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1, Remark 2.2, and Lemma 2.5.
* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definition 2.1.
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
  fin_cases u <;> fin_cases v <;> dsimp only at huv ⊢ <;>
    [exact (huv rfl).elim; decide; decide; decide;
     decide; exact (huv rfl).elim; decide; decide;
     decide; decide; exact (huv rfl).elim; decide;
     decide; decide; decide; exact (huv rfl).elim]

private theorem iso_tetWeb_vertex_zero {c₁ c₂ : Bool} (f : (tetWeb c₁).Iso (tetWeb c₂)) :
    f.vertex 0 = 0 := by
  have hm0 : (f.vertex 0).val < 2 :=
    (isMerge_tetWeb c₂ _).mp ((f.isMerge_vertex 0).mpr (by simp))
  have ht := f.map_target ((tetWeb c₁).ends (0, 0)).1
  have he : ((tetWeb c₂).ends (f.vertex 0, 0)).1 = f.edge ((tetWeb c₁).ends (0, 0)).1 :=
    congrArg Prod.fst (f.map_ends_apply 0 0)
  rw [← he] at ht
  have hmerge : (tetWeb c₂).IsMerge ((tetWeb c₂).target ((tetWeb c₂).ends (f.vertex 0, 0)).1) :=
    ht ▸ (f.isMerge_vertex _).mpr (by
      rw [tetWeb_ends_zero, target_tetWeb, isMerge_tetWeb]
      simp [tetrahedronPosEndsFun, tetrahedronPosEndsInv])
  obtain ⟨v0, hv0⟩ : ∃ v0, f.vertex 0 = v0 := ⟨_, rfl⟩
  rw [hv0] at hm0 hmerge ⊢
  fin_cases v0 <;> dsimp only at hm0 hmerge ⊢
  · rfl
  · rw [tetWeb_ends_zero, target_tetWeb, isMerge_tetWeb] at hmerge
    simp [tetrahedronPosEndsFun, tetrahedronPosEndsInv] at hmerge
  · omega
  · omega

private theorem iso_tetWeb_vertex_two {c₁ c₂ : Bool} (f : (tetWeb c₁).Iso (tetWeb c₂)) :
    f.vertex 2 = 2 := by
  have hs2 : 2 ≤ (f.vertex 2).val :=
    (isSplit_tetWeb c₂ _).mp ((f.isSplit_vertex 2).mpr (by simp))
  have hs := f.map_source ((tetWeb c₁).ends (2, 0)).1
  have he : ((tetWeb c₂).ends (f.vertex 2, 0)).1 = f.edge ((tetWeb c₁).ends (2, 0)).1 :=
    congrArg Prod.fst (f.map_ends_apply 2 0)
  rw [← he] at hs
  have hmerge : (tetWeb c₂).IsMerge ((tetWeb c₂).source ((tetWeb c₂).ends (f.vertex 2, 0)).1) :=
    hs ▸ (f.isMerge_vertex _).mpr (by
      rw [tetWeb_ends_zero, source_tetWeb, isMerge_tetWeb]
      simp [tetrahedronPosEndsFun, tetrahedronPosEndsInv])
  obtain ⟨v2, hv2⟩ : ∃ v2, f.vertex 2 = v2 := ⟨_, rfl⟩
  rw [hv2] at hs2 hmerge ⊢
  fin_cases v2 <;> dsimp only at hs2 hmerge ⊢
  · omega
  · omega
  · rfl
  · rw [tetWeb_ends_zero, source_tetWeb, isMerge_tetWeb] at hmerge
    simp [tetrahedronPosEndsFun, tetrahedronPosEndsInv] at hmerge

private theorem iso_tetWeb_vertex_eq {c₁ c₂ : Bool} (f : (tetWeb c₁).Iso (tetWeb c₂)) :
    ∀ v : Fin 4, f.vertex v = v := by
  have h0 := iso_tetWeb_vertex_zero f
  have h2 := iso_tetWeb_vertex_two f
  have hm1 : (f.vertex 1).val < 2 :=
    (isMerge_tetWeb c₂ _).mp ((f.isMerge_vertex 1).mpr (by simp))
  have hs3 : 2 ≤ (f.vertex 3).val :=
    (isSplit_tetWeb c₂ _).mp ((f.isSplit_vertex 3).mpr (by simp))
  have h1 : f.vertex 1 = 1 := by
    have hne : f.vertex 1 ≠ 0 := h0 ▸ f.vertex.injective.ne (by simp)
    obtain ⟨v1, hv1⟩ : ∃ v1, f.vertex 1 = v1 := ⟨_, rfl⟩
    rw [hv1] at hm1 hne ⊢
    fin_cases v1 <;> dsimp only at hm1 hne ⊢ <;> [exact (hne rfl).elim; rfl; omega; omega]
  have h3 : f.vertex 3 = 3 := by
    have hne : f.vertex 3 ≠ 2 := h2 ▸ f.vertex.injective.ne (by simp)
    obtain ⟨v3, hv3⟩ : ∃ v3, f.vertex 3 = v3 := ⟨_, rfl⟩
    rw [hv3] at hs3 hne ⊢
    fin_cases v3 <;> dsimp only at hs3 hne ⊢ <;> [omega; omega; exact (hne rfl).elim; rfl]
  intro v
  fin_cases v <;> assumption

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

/-- Vertex involution `v ↦ 3 - v` carrying `(tetWeb c).reverse` to `tetWeb (!c)`. -/
@[expose] def tetRevVertexEquiv : Fin 4 ≃ Fin 4 where
  toFun | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0
  invFun | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0
  left_inv v := by fin_cases v <;> rfl
  right_inv v := by fin_cases v <;> rfl

/-- Edge involution carrying `(tetWeb c).reverse` to `tetWeb (!c)`. -/
@[expose] def tetRevEdgeEquiv : Fin 6 ≃ Fin 6 where
  toFun | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3
  invFun | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 5 | 4 => 4 | 5 => 3
  left_inv e := by fin_cases e <;> rfl
  right_inv e := by fin_cases e <;> rfl

/-- Reversing all edge orientations of `tetWeb c` produces a web isomorphic to `tetWeb (!c)`. -/
def tetWebReverseIso (c : Bool) : (tetWeb c).reverse.Iso (tetWeb (!c)) where
  vertex := tetRevVertexEquiv
  edge := tetRevEdgeEquiv
  circle := Equiv.refl PEmpty
  map_ends := by
    rintro ⟨v, i⟩
    cases c <;> fin_cases v <;> fin_cases i <;> rfl

/-! ### Semigroup flows and monochrome local cycles -/

/-- An additive flow on a closed web assigns weights to interval edges so that at every vertex,
the weight on the odd slot `0` equals the weight on slot `1` plus the weight on slot `2` in that
order. No commutativity is assumed on `S`. -/
def IsAdditiveFlow {S : Type*} [Add S] (W : ClosedWeb) (w : W.Edge → S) : Prop :=
  ∀ v, w (W.ends (v, 0)).1 = w (W.ends (v, 1)).1 + w (W.ends (v, 2)).1

/-- Additive flows on `tetrahedronPos` express the four merge/split equations linking thin weights
`(w 3, w 4, w 5)` through `(w 3 + w 4) + w 5` and `w 3 + (w 4 + w 5)`. -/
theorem isAdditiveFlow_tetrahedronPos_iff {S : Type*} [Add S] (w : Fin 6 → S) :
    tetrahedronPos.IsAdditiveFlow w ↔
      w 2 = w 3 + w 4 ∧ w 0 = w 2 + w 5 ∧ w 0 = w 3 + w 1 ∧ w 1 = w 4 + w 5 :=
  ⟨fun h ↦ ⟨h 0, h 1, h 2, h 3⟩, fun ⟨h0, h1, h2, h3⟩ v ↦ by fin_cases v <;> assumption⟩

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
      w 2 = w 4 + w 3 ∧ w 0 = w 5 + w 2 ∧ w 0 = w 1 + w 3 ∧ w 1 = w 5 + w 4 :=
  ⟨fun h ↦ ⟨h 0, h 1, h 2, h 3⟩, fun ⟨h0, h1, h2, h3⟩ v ↦ by fin_cases v <;> assumption⟩

/-- Any additive flow on `tetrahedronNeg` witnesses `(w 5 + w 4) + w 3 = w 5 + (w 4 + w 3)`. -/
theorem assoc_of_isAdditiveFlow_tetrahedronNeg {S : Type*} [Add S] {w : Fin 6 → S}
    (hw : tetrahedronNeg.IsAdditiveFlow w) :
    (w 5 + w 4) + w 3 = w 5 + (w 4 + w 3) := by
  obtain ⟨h2, h0, h0', h1⟩ := (isAdditiveFlow_tetrahedronNeg_iff w).mp hw
  rw [← h2, ← h0, h0', h1]

/-- A single-pigment indicator `p : W.Edge → Bool` satisfies the Robert–Wagner disjoint-union
condition when at every vertex `v`, the pigment appears on the odd edge `(v, 0)` if and only if
it appears on at least one of the thin edges `(v, 1)` and `(v, 2)`, and never on both thin edges
simultaneously. -/
def IsMonochromeSubweb (W : ClosedWeb.{u}) (p : W.Edge → Bool) : Prop :=
  ∀ v, p (W.ends (v, 0)).1 = (p (W.ends (v, 1)).1 || p (W.ends (v, 2)).1) ∧
    ¬(p (W.ends (v, 1)).1 && p (W.ends (v, 2)).1)

/-- Mirroring a closed web preserves single-pigment subwebs, since disjoint union of a single
pigment is symmetric in the two thin slots. -/
@[simp] theorem isMonochromeSubweb_mirror (W : ClosedWeb.{u}) (p : W.Edge → Bool) :
    W.mirror.IsMonochromeSubweb p ↔ W.IsMonochromeSubweb p := by
  refine forall_congr' fun v ↦ ?_
  rw [mirror_ends_apply, mirror_ends_apply, mirror_ends_apply]
  dsimp only [Equiv.swap_apply_def]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  rw [Bool.or_comm, Bool.and_comm]

private theorem card_fin_three_subtype (q : Fin 3 → Bool) :
    Nat.card {i : Fin 3 // q i = true} =
      (if q 0 then 1 else 0) + (if q 1 then 1 else 0) + (if q 2 then 1 else 0) := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  cases h0 : q 0 <;> cases h1 : q 1 <;> cases h2 : q 2 <;>
    decide +revert

/-- At every vertex of any closed web, a single-pigment subweb has equal numbers of active
incoming and outgoing ends, and at most one of each. -/
theorem card_active_ends_of_isMonochromeSubweb {W : ClosedWeb.{u}} {p : W.Edge → Bool}
    (hp : W.IsMonochromeSubweb p) (v : W.Vertex) :
    Nat.card {i : Fin 3 // (p (W.ends (v, i)).1 && !(W.ends (v, i)).2) = true} =
      Nat.card {i : Fin 3 // (p (W.ends (v, i)).1 && (W.ends (v, i)).2) = true} ∧
    Nat.card {i : Fin 3 // (p (W.ends (v, i)).1 && !(W.ends (v, i)).2) = true} ≤ 1 := by
  obtain ⟨h0, h12⟩ := hp v
  rw [card_fin_three_subtype (fun i ↦ p (W.ends (v, i)).1 && !(W.ends (v, i)).2),
    card_fin_three_subtype (fun i ↦ p (W.ends (v, i)).1 && (W.ends (v, i)).2)]
  simp only [W.orientation_one v, W.orientation_two v, Bool.not_not]
  cases hb0 : (W.ends (v, 0)).2 <;>
    cases hp1 : p (W.ends (v, 1)).1 <;>
    cases hp2 : p (W.ends (v, 2)).1 <;>
    simp_all

/-- The three elementary nonempty single-pigment simple cycles on `tetWeb c`, determined by which
thin edge among `3, 4, 5` carries the pigment: `{0, 2, 3}`, `{0, 1, 2, 4}`, and `{0, 1, 5}`. -/
def tetPigmentCycle : Fin 3 → Fin 6 → Bool
  | 0 => ![true, false, true, true, false, false]
  | 1 => ![true, true, true, false, true, false]
  | 2 => ![true, true, false, false, false, true]

/-- Every elementary pigment cycle is a valid monochrome subweb on both chiralities of `tetWeb`. -/
theorem isMonochromeSubweb_tetPigmentCycle (c : Bool) (i : Fin 3) :
    (tetWeb c).IsMonochromeSubweb (tetPigmentCycle i) := by
  intro v
  cases c <;> fin_cases i <;> fin_cases v <;> decide

private theorem isMonochromeSubweb_tetrahedronPos_iff (p : Fin 6 → Bool) :
    tetrahedronPos.IsMonochromeSubweb p ↔
      p = (fun _ ↦ false) ∨ ∃ i : Fin 3, p = tetPigmentCycle i := by
  constructor
  · intro hp
    have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
    rw [tetWeb_ends_apply, tetWeb_ends_apply, tetWeb_ends_apply] at h0 h1 h2 h3
    dsimp [tetrahedronPosEndsFun] at h0 h1 h2 h3
    cases hp3 : p 3 <;> cases hp4 : p 4 <;> cases hp5 : p 5 <;>
      rw [hp3] at h0 h2 <;> rw [hp4] at h0 h3 <;> rw [hp5] at h1 h3
    · have hp2 : p 2 = false := h0.1; have hp1 : p 1 = false := h3.1
      rw [hp2] at h1; have hp0 : p 0 = false := h1.1
      left; funext e; fin_cases e <;> assumption
    · have hp2 : p 2 = false := h0.1; have hp1 : p 1 = true := h3.1
      rw [hp2] at h1; have hp0 : p 0 = true := h1.1
      right; refine ⟨2, funext fun e ↦ ?_⟩; fin_cases e <;> assumption
    · have hp2 : p 2 = true := h0.1; have hp1 : p 1 = true := h3.1
      rw [hp2] at h1; have hp0 : p 0 = true := h1.1
      right; refine ⟨1, funext fun e ↦ ?_⟩; fin_cases e <;> assumption
    · exact absurd rfl h3.2
    · have hp2 : p 2 = true := h0.1; have hp1 : p 1 = false := h3.1
      rw [hp2] at h1; have hp0 : p 0 = true := h1.1
      right; refine ⟨0, funext fun e ↦ ?_⟩; fin_cases e <;> assumption
    · have hp1 : p 1 = true := h3.1
      rw [hp1] at h2; exact absurd rfl h2.2
    · exact absurd rfl h0.2
    · exact absurd rfl h0.2
  · rintro (rfl | ⟨i, rfl⟩)
    · intro v; fin_cases v <;> decide
    · exact isMonochromeSubweb_tetPigmentCycle true i

/-- Complete classification of monochrome subwebs on `tetWeb c` (Robert–Wagner Lemma 2.5 at a
singular vertex): `p` is either identically `false` or one of the three single simple cycles
`tetPigmentCycle 0`, `tetPigmentCycle 1`, `tetPigmentCycle 2`. -/
theorem isMonochromeSubweb_tetWeb_iff (c : Bool) (p : Fin 6 → Bool) :
    (tetWeb c).IsMonochromeSubweb p ↔
      p = (fun _ ↦ false) ∨ ∃ i : Fin 3, p = tetPigmentCycle i := by
  cases c
  · refine (forall_congr' fun v ↦ ?_).trans (isMonochromeSubweb_tetrahedronPos_iff p)
    change (p ((tetWeb true).ends (v, 0)).1 =
        (p ((tetWeb true).ends (v, 2)).1 || p ((tetWeb true).ends (v, 1)).1) ∧
      ¬(p ((tetWeb true).ends (v, 2)).1 && p ((tetWeb true).ends (v, 1)).1)) ↔ _
    rw [Bool.or_comm, Bool.and_comm]
  · exact isMonochromeSubweb_tetrahedronPos_iff p

/-- The three elementary pigment cycles on `tetWeb c` have edge counts `3`, `4`, and `3`. -/
theorem card_tetPigmentCycle (i : Fin 3) :
    Nat.card {e : Fin 6 // tetPigmentCycle i e = true} = ![3, 4, 3] i := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases i <;> decide

end TauCeti.ClosedWeb
