/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Equidecomp
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Order.Partition.Finpartition

/-!
# Equipartitions: equidecompositions as finite partitions

Mathlib defines an equidecomposition `f : Equidecomp X G` as a partial bijection of `X` moving each
point of its source by an element of a fixed finite subset of `G`. The more familiar definition
partitions the source `A` into finitely many pieces `Aᵢ` and moves each piece by one group element
`gᵢ`, so that the translates `gᵢ • Aᵢ` partition the target `B`. This file proves that the two
definitions agree.

An *equipartition* `E : Equidecomp.Equipartition X G` is a finite set of pairs `(Aᵢ, gᵢ)` of a
source piece and a group element, whose source pieces `Aᵢ` are pairwise disjoint and whose target
pieces `gᵢ • Aᵢ` are pairwise disjoint. Its source and target are the unions of these pieces.

## Main definitions

* `Equidecomp.Equipartition X G`: finitely many source pieces with group elements, with pairwise
  disjoint sources and pairwise disjoint targets.
* `Equidecomp.Equipartition.toEquidecomp`: the equidecomposition of an equipartition, moving each
  source piece `Aᵢ` by its element `gᵢ`.
* `Equidecomp.toEquipartition`: an equipartition of an equidecomposition, with the same source and
  target, whose pieces move points as the equidecomposition does.
* `Equidecomp.Equipartition.sourceFinpartition`, `Equidecomp.Equipartition.targetFinpartition`:
  the finite partitions of the source and of the target into the nonempty pieces.
* `Equidecomp.Equipartition.ofFinpartition`: the equipartition moving each part `s` of a finite
  partition by a group element `γ s`, when the translates `γ s • s` are pairwise disjoint.

## Main results

* `Equidecomp.Equipartition.toEquidecomp_apply`,
  `Equidecomp.Equipartition.toEquidecomp_symm_apply`: the equidecomposition of an equipartition
  moves the piece `Aᵢ` by `gᵢ`, and its inverse moves `gᵢ • Aᵢ` by `gᵢ⁻¹`.
* `Equidecomp.toEquidecomp_toEquipartition`: converting an equidecomposition to an equipartition
  and back recovers it on its source.
* `Equidecomp.exists_iff_exists_equipartition`: two sets are related by an equidecomposition
  exactly when they are the source and target of an equipartition.
* `Equidecomp.exists_iff_exists_finpartition`: `A` and `B` are related by an equidecomposition
  exactly when some finite partition of `A`, with one group element for each part, has pairwise
  disjoint translates with union `B`.

## Implementation notes

The name of an equipartition, its description by pieces with independent disjointness conditions
on sources and targets, and the two conversions to and from `Equidecomp` are those proposed in
mathlib4 PR 30330; no code from that PR is used here. This notion is unrelated to
`Finpartition.IsEquipartition`, a partition into parts of almost equal size.

Distinct pieces may share an empty source piece, so the pieces of an equipartition are not
determined by its partition of the source; `sourceFinpartition` and `targetFinpartition` discard
the empty pieces.

## References

* G. Tomkowicz, S. Wagon, *The Banach–Tarski Paradox*, 2nd ed., Chapter 3.
* A. Garrido, *An introduction to amenable groups*, §1.
-/

public section

open Set Pointwise

variable {X G : Type*}

namespace Equidecomp

section SMul

variable [SMul G X]

variable (X G) in
/-- An *equipartition* of `X` for an action of `G`: a finite set of pairs `(Aᵢ, gᵢ)` of a source
piece `Aᵢ : Set X` and a group element `gᵢ : G`, such that the source pieces `Aᵢ` are pairwise
disjoint and the target pieces `gᵢ • Aᵢ` are pairwise disjoint. Moving each `Aᵢ` by `gᵢ` is then an
equidecomposition of the union of the `Aᵢ` with the union of the `gᵢ • Aᵢ`. -/
@[ext]
structure Equipartition where
  /-- The pieces, each a source piece together with the group element moving it. -/
  pieces : Finset (Set X × G)
  /-- Distinct pieces have disjoint source pieces. -/
  pairwiseDisjoint_fst : (pieces : Set (Set X × G)).PairwiseDisjoint Prod.fst
  /-- Distinct pieces have disjoint target pieces. -/
  pairwiseDisjoint_smul : (pieces : Set (Set X × G)).PairwiseDisjoint fun p ↦ p.2 • p.1

namespace Equipartition

variable (E : Equipartition X G) {p q : Set X × G} {x y : X}

/-- The source of an equipartition: the union of its source pieces. -/
def source : Set X :=
  ⋃ p ∈ E.pieces, p.1

/-- The target of an equipartition: the union of its target pieces `gᵢ • Aᵢ`. -/
def target : Set X :=
  ⋃ p ∈ E.pieces, p.2 • p.1

variable {E}

@[simp]
theorem mem_source : x ∈ E.source ↔ ∃ p ∈ E.pieces, x ∈ p.1 := by
  simp [source]

@[simp]
theorem mem_target : y ∈ E.target ↔ ∃ p ∈ E.pieces, y ∈ p.2 • p.1 := by
  simp [target]

theorem fst_subset_source (hp : p ∈ E.pieces) : p.1 ⊆ E.source :=
  fun _ hx ↦ mem_source.2 ⟨p, hp, hx⟩

theorem smul_subset_target (hp : p ∈ E.pieces) : p.2 • p.1 ⊆ E.target :=
  fun _ hy ↦ mem_target.2 ⟨p, hp, hy⟩

/-- A point of the source lies in only one source piece. -/
theorem eq_of_mem_fst (hp : p ∈ E.pieces) (hq : q ∈ E.pieces) (hxp : x ∈ p.1) (hxq : x ∈ q.1) :
    p = q :=
  E.pairwiseDisjoint_fst.elim hp hq <| not_disjoint_iff.2 ⟨x, hxp, hxq⟩

/-- A point of the target lies in only one target piece. -/
theorem eq_of_mem_smul (hp : p ∈ E.pieces) (hq : q ∈ E.pieces) (hyp : y ∈ p.2 • p.1)
    (hyq : y ∈ q.2 • q.1) : p = q :=
  E.pairwiseDisjoint_smul.elim hp hq <| not_disjoint_iff.2 ⟨y, hyp, hyq⟩

/-- If a map `F` sends distinct pieces to disjoint sets, then the images of the pieces under `F`
are pairwise disjoint sets. -/
private theorem pairwiseDisjoint_image [DecidableEq (Set X)] {F : Set X × G → Set X}
    (hF : (E.pieces : Set (Set X × G)).PairwiseDisjoint F) :
    ((E.pieces.image F : Finset (Set X)) : Set (Set X)).PairwiseDisjoint id := by
  rintro _ hs _ ht hst
  simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hs ht
  obtain ⟨p, hp, rfl⟩ := hs
  obtain ⟨q, hq, rfl⟩ := ht
  exact hF hp hq fun hpq ↦ hst (congrArg F hpq)

open scoped Classical in
/-- The finite partition of the source of an equipartition into its nonempty source pieces. -/
noncomputable def sourceFinpartition (E : Equipartition X G) : Finpartition E.source :=
  Finpartition.ofErase (E.pieces.image Prod.fst)
    (Finset.supIndep_iff_pairwiseDisjoint.2 (pairwiseDisjoint_image E.pairwiseDisjoint_fst))
    (by rw [Finset.sup_image, Finset.sup_set_eq_biUnion]; rfl)

open scoped Classical in
/-- The finite partition of the target of an equipartition into its nonempty target pieces. -/
noncomputable def targetFinpartition (E : Equipartition X G) : Finpartition E.target :=
  Finpartition.ofErase (E.pieces.image fun p ↦ p.2 • p.1)
    (Finset.supIndep_iff_pairwiseDisjoint.2 (pairwiseDisjoint_image E.pairwiseDisjoint_smul))
    (by rw [Finset.sup_image, Finset.sup_set_eq_biUnion]; rfl)

@[simp]
theorem mem_sourceFinpartition_parts {s : Set X} :
    s ∈ E.sourceFinpartition.parts ↔ s.Nonempty ∧ ∃ p ∈ E.pieces, p.1 = s := by
  classical
  simp [sourceFinpartition, nonempty_iff_ne_empty]

@[simp]
theorem mem_targetFinpartition_parts {s : Set X} :
    s ∈ E.targetFinpartition.parts ↔ s.Nonempty ∧ ∃ p ∈ E.pieces, p.2 • p.1 = s := by
  classical
  simp [targetFinpartition, nonempty_iff_ne_empty]

/-- Each nonempty part of `E.sourceFinpartition` can be assigned the group element of its piece,
so that the translated parts are pairwise disjoint with union the target of `E`. -/
theorem exists_pairwiseDisjoint_smul_sourceFinpartition [Nonempty G] (E : Equipartition X G) :
    ∃ γ : Set X → G,
      (E.sourceFinpartition.parts : Set (Set X)).PairwiseDisjoint (fun s ↦ γ s • s) ∧
        ⋃ s ∈ E.sourceFinpartition.parts, γ s • s = E.target := by
  classical
  set γ : Set X → G := fun s ↦
    if h : ∃ p ∈ E.pieces, p.1 = s then h.choose.2 else Classical.arbitrary G
  -- A nonempty source piece determines its piece, hence its group element.
  have hγ : ∀ p ∈ E.pieces, p.1.Nonempty → γ p.1 = p.2 := by
    rintro p hp ⟨x, hx⟩
    have h : ∃ q ∈ E.pieces, q.1 = p.1 := ⟨p, hp, rfl⟩
    simp only [γ]
    rw [dite_eq_left h]
    exact congrArg Prod.snd <| E.eq_of_mem_fst h.choose_spec.1 hp (by rwa [h.choose_spec.2]) hx
  refine ⟨γ, ?_, ?_⟩
  · rintro _ hs _ ht hst
    obtain ⟨hsne, p, hp, rfl⟩ := mem_sourceFinpartition_parts.1 hs
    obtain ⟨htne, q, hq, rfl⟩ := mem_sourceFinpartition_parts.1 ht
    simp only [Function.onFun, hγ p hp hsne, hγ q hq htne]
    exact E.pairwiseDisjoint_smul hp hq fun hpq ↦ hst (congrArg Prod.fst hpq)
  · ext y
    simp only [mem_iUnion, mem_sourceFinpartition_parts, mem_target]
    constructor
    · rintro ⟨_, ⟨hsne, p, hp, rfl⟩, hy⟩
      exact ⟨p, hp, hγ p hp hsne ▸ hy⟩
    · rintro ⟨p, hp, hy⟩
      have hne : p.1.Nonempty := by
        obtain ⟨x, hx, -⟩ := hy
        exact ⟨x, hx⟩
      exact ⟨p.1, ⟨hne, p, hp, rfl⟩, (hγ p hp hne).symm ▸ hy⟩

section ofFinpartition

variable {A : Set X} (P : Finpartition A) (γ : Set X → G)
  (hγ : (P.parts : Set (Set X)).PairwiseDisjoint fun s ↦ γ s • s)

open scoped Classical in
/-- The equipartition whose source pieces are the parts `s` of a finite partition `P`, each moved
by `γ s`, provided these translates are pairwise disjoint. -/
noncomputable def ofFinpartition : Equipartition X G where
  pieces := P.parts.image fun s ↦ (s, γ s)
  pairwiseDisjoint_fst := by
    rintro _ hp _ hq hpq
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hp hq
    obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨t, ht, rfl⟩ := hq
    exact P.disjoint hs ht fun hst ↦ hpq (by rw [hst])
  pairwiseDisjoint_smul := by
    rintro _ hp _ hq hpq
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hp hq
    obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨t, ht, rfl⟩ := hq
    exact hγ hs ht fun hst ↦ hpq (by rw [hst])

@[simp]
theorem mem_ofFinpartition_pieces {p : Set X × G} :
    p ∈ (ofFinpartition P γ hγ).pieces ↔ p.1 ∈ P.parts ∧ γ p.1 = p.2 := by
  classical
  obtain ⟨s, g⟩ := p
  simp [ofFinpartition, and_comm]

@[simp]
theorem ofFinpartition_source : (ofFinpartition P γ hγ).source = A := by
  classical
  refine Eq.trans ?_ ((Finset.sup_set_eq_biUnion _ _).symm.trans P.sup_parts)
  ext x
  simp [source, ofFinpartition]

@[simp]
theorem ofFinpartition_target : (ofFinpartition P γ hγ).target = ⋃ s ∈ P.parts, γ s • s := by
  classical
  ext y
  simp [target, ofFinpartition]

end ofFinpartition

end Equipartition

/-- The piece of an equidecomposition `f` attached to `g`: the points `a` of the source for which
`g` is the chosen witness of `f a ∈ f.witness • a`. -/
private def piece (f : Equidecomp X G) (g : G) : Set X :=
  {a | ∃ h : a ∈ f.source, (f.isDecompOn a h).choose = g}

private theorem eq_of_mem_piece {f : Equidecomp X G} {g g' : G} {a : X} (ha : a ∈ piece f g)
    (ha' : a ∈ piece f g') : g = g' := by
  obtain ⟨h, rfl⟩ := ha
  obtain ⟨_, rfl⟩ := ha'
  rfl

private theorem apply_eq_smul_of_mem_piece {f : Equidecomp X G} {g : G} {a : X}
    (ha : a ∈ piece f g) : f a = g • a := by
  obtain ⟨h, rfl⟩ := ha
  exact (f.isDecompOn a h).choose_spec.2

open scoped Classical in
/-- An equipartition of an equidecomposition `f`: for each element `g` of its witness set, the
points of the source that `f` moves by the chosen element `g` form a piece moved by `g`. -/
noncomputable def toEquipartition (f : Equidecomp X G) : Equipartition X G where
  pieces := f.witness.image fun g ↦ (piece f g, g)
  pairwiseDisjoint_fst := by
    rintro _ hp _ hq hpq
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hp hq
    obtain ⟨g, -, rfl⟩ := hp
    obtain ⟨g', -, rfl⟩ := hq
    refine Set.disjoint_left.2 fun a ha ha' ↦ hpq ?_
    rw [eq_of_mem_piece ha ha']
  pairwiseDisjoint_smul := by
    rintro _ hp _ hq hpq
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hp hq
    obtain ⟨g, -, rfl⟩ := hp
    obtain ⟨g', -, rfl⟩ := hq
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    obtain rfl : b = a := f.toPartialEquiv.injOn hb.1 ha.1 <|
      (apply_eq_smul_of_mem_piece hb).trans <| hba.trans (apply_eq_smul_of_mem_piece ha).symm
    exact hpq (by rw [eq_of_mem_piece ha hb])

private theorem mem_toEquipartition_pieces {f : Equidecomp X G} {p : Set X × G} :
    p ∈ f.toEquipartition.pieces ↔ ∃ g ∈ f.witness, (piece f g, g) = p := by
  classical
  simp [toEquipartition]

/-- Each piece of `f.toEquipartition` is moved by an element of the witness set of `f`. -/
theorem snd_mem_witness_of_mem_toEquipartition {f : Equidecomp X G} {p : Set X × G}
    (hp : p ∈ f.toEquipartition.pieces) : p.2 ∈ f.witness := by
  obtain ⟨g, hg, rfl⟩ := mem_toEquipartition_pieces.1 hp
  exact hg

/-- On each piece of `f.toEquipartition`, the equidecomposition `f` acts by the piece's group
element. -/
theorem apply_eq_smul_of_mem_toEquipartition {f : Equidecomp X G} {p : Set X × G} {x : X}
    (hp : p ∈ f.toEquipartition.pieces) (hx : x ∈ p.1) : f x = p.2 • x := by
  obtain ⟨g, -, rfl⟩ := mem_toEquipartition_pieces.1 hp
  exact apply_eq_smul_of_mem_piece hx

/-- A point of the source of `f` lies in the piece of the element chosen for it. -/
private theorem mem_piece_choose {f : Equidecomp X G} {a : X} (ha : a ∈ f.source) :
    a ∈ piece f (f.isDecompOn a ha).choose :=
  ⟨ha, rfl⟩

private theorem mk_piece_choose_mem {f : Equidecomp X G} {a : X} (ha : a ∈ f.source) :
    (piece f (f.isDecompOn a ha).choose, (f.isDecompOn a ha).choose) ∈
      f.toEquipartition.pieces :=
  mem_toEquipartition_pieces.2 ⟨_, (f.isDecompOn a ha).choose_spec.1, rfl⟩

@[simp]
theorem toEquipartition_source (f : Equidecomp X G) : f.toEquipartition.source = f.source := by
  ext a
  refine ⟨fun ha ↦ ?_, fun ha ↦ Equipartition.mem_source.2 ⟨_, mk_piece_choose_mem ha,
    mem_piece_choose ha⟩⟩
  obtain ⟨p, hp, hap⟩ := Equipartition.mem_source.1 ha
  obtain ⟨g, -, rfl⟩ := mem_toEquipartition_pieces.1 hp
  exact hap.1

@[simp]
theorem toEquipartition_target (f : Equidecomp X G) : f.toEquipartition.target = f.target := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · obtain ⟨p, hp, a, ha, rfl⟩ := Equipartition.mem_target.1 hy
    obtain ⟨g, -, rfl⟩ := mem_toEquipartition_pieces.1 hp
    beta_reduce
    rw [← apply_eq_smul_of_mem_piece ha]
    exact apply_mem_target ha.1
  · have ha := f.toPartialEquiv.map_target hy
    refine Equipartition.mem_target.2 ⟨_, mk_piece_choose_mem ha, _, mem_piece_choose ha, ?_⟩
    exact (apply_eq_smul_of_mem_piece (mem_piece_choose ha)).symm.trans
      (f.toPartialEquiv.right_inv hy)

end SMul

section Group

variable [Group G] [MulAction G X]

namespace Equipartition

variable {E : Equipartition X G} {p : Set X × G} {x y : X}

open scoped Classical in
private theorem dite_mem_fst (hp : p ∈ E.pieces) (hx : x ∈ p.1) :
    (if h : ∃ q ∈ E.pieces, x ∈ q.1 then h.choose.2 • x else x) = p.2 • x := by
  have h : ∃ q ∈ E.pieces, x ∈ q.1 := ⟨p, hp, hx⟩
  rw [dite_eq_left h, E.eq_of_mem_fst h.choose_spec.1 hp h.choose_spec.2 hx]

open scoped Classical in
private theorem dite_mem_smul (hp : p ∈ E.pieces) (hy : y ∈ p.2 • p.1) :
    (if h : ∃ q ∈ E.pieces, y ∈ q.2 • q.1 then h.choose.2⁻¹ • y else y) = p.2⁻¹ • y := by
  have h : ∃ q ∈ E.pieces, y ∈ q.2 • q.1 := ⟨p, hp, hy⟩
  rw [dite_eq_left h, E.eq_of_mem_smul h.choose_spec.1 hp h.choose_spec.2 hy]

open scoped Classical in
/-- The equidecomposition of an equipartition: each source piece `Aᵢ` is moved by its group
element `gᵢ`, giving a bijection from the source onto the target. Points outside the source are
fixed. -/
noncomputable def toEquidecomp (E : Equipartition X G) : Equidecomp X G where
  toFun x := if h : ∃ p ∈ E.pieces, x ∈ p.1 then h.choose.2 • x else x
  invFun y := if h : ∃ p ∈ E.pieces, y ∈ p.2 • p.1 then h.choose.2⁻¹ • y else y
  source := E.source
  target := E.target
  map_source' x hx := by
    obtain ⟨p, hp, hx⟩ := mem_source.1 hx
    rw [dite_mem_fst hp hx]
    exact smul_subset_target hp (smul_mem_smul_set hx)
  map_target' y hy := by
    obtain ⟨p, hp, hy⟩ := mem_target.1 hy
    rw [dite_mem_smul hp hy]
    exact fst_subset_source hp (mem_smul_set_iff_inv_smul_mem.1 hy)
  left_inv' x hx := by
    obtain ⟨p, hp, hx⟩ := mem_source.1 hx
    simp only [dite_mem_fst hp hx, dite_mem_smul hp (smul_mem_smul_set hx), inv_smul_smul]
  right_inv' y hy := by
    obtain ⟨p, hp, hy⟩ := mem_target.1 hy
    simp only [dite_mem_smul hp hy, dite_mem_fst hp (mem_smul_set_iff_inv_smul_mem.1 hy),
      smul_inv_smul]
  isDecompOn' := by
    refine ⟨E.pieces.image Prod.snd, fun x hx ↦ ?_⟩
    obtain ⟨p, hp, hx⟩ := mem_source.1 hx
    exact ⟨p.2, Finset.mem_image_of_mem _ hp, dite_mem_fst hp hx⟩

@[simp]
theorem toEquidecomp_source (E : Equipartition X G) : E.toEquidecomp.source = E.source :=
  (rfl)

@[simp]
theorem toEquidecomp_target (E : Equipartition X G) : E.toEquidecomp.target = E.target :=
  (rfl)

/-- The equidecomposition of an equipartition moves each source piece by its group element. -/
theorem toEquidecomp_apply (hp : p ∈ E.pieces) (hx : x ∈ p.1) : E.toEquidecomp x = p.2 • x :=
  dite_mem_fst hp hx

/-- The inverse of the equidecomposition of an equipartition moves each target piece `gᵢ • Aᵢ`
by `gᵢ⁻¹`. -/
theorem toEquidecomp_symm_apply (hp : p ∈ E.pieces) (hy : y ∈ p.2 • p.1) :
    E.toEquidecomp.symm y = p.2⁻¹ • y :=
  dite_mem_smul hp hy

/-- The equidecomposition of an equipartition only uses the group elements of its pieces. -/
theorem isDecompOn_toEquidecomp [DecidableEq G] (E : Equipartition X G) :
    IsDecompOn E.toEquidecomp E.source (E.pieces.image Prod.snd) := fun x hx ↦ by
  obtain ⟨p, hp, hx⟩ := mem_source.1 hx
  exact ⟨p.2, Finset.mem_image_of_mem _ hp, toEquidecomp_apply hp hx⟩

end Equipartition

/-- Converting an equidecomposition to an equipartition and back recovers it on its source. -/
theorem toEquidecomp_toEquipartition (f : Equidecomp X G) :
    f.toEquipartition.toEquidecomp.toPartialEquiv ≈ f.toPartialEquiv := by
  refine ⟨by simp, fun x hx ↦ ?_⟩
  obtain ⟨p, hp, hx⟩ := Equipartition.mem_source.1 hx
  exact (Equipartition.toEquidecomp_apply hp hx).trans
    (apply_eq_smul_of_mem_toEquipartition hp hx).symm

/-- Two sets are related by an equidecomposition exactly when they are the source and the target
of an equipartition. -/
theorem exists_iff_exists_equipartition {A B : Set X} :
    (∃ f : Equidecomp X G, f.source = A ∧ f.target = B) ↔
      ∃ E : Equipartition X G, E.source = A ∧ E.target = B :=
  ⟨fun ⟨f, hA, hB⟩ ↦ ⟨f.toEquipartition, f.toEquipartition_source.trans hA,
    f.toEquipartition_target.trans hB⟩, fun ⟨E, hA, hB⟩ ↦ ⟨E.toEquidecomp, hA, hB⟩⟩

/-- **Equidecompositions as partitions.** Two sets `A` and `B` are related by an
equidecomposition exactly when there are a finite partition of `A` and a group element `γ s` for
each part `s`, such that the translates `γ s • s` are pairwise disjoint with union `B`. -/
theorem exists_iff_exists_finpartition {A B : Set X} :
    (∃ f : Equidecomp X G, f.source = A ∧ f.target = B) ↔
      ∃ (P : Finpartition A) (γ : Set X → G),
        (P.parts : Set (Set X)).PairwiseDisjoint (fun s ↦ γ s • s) ∧
          ⋃ s ∈ P.parts, γ s • s = B := by
  rw [exists_iff_exists_equipartition]
  constructor
  · rintro ⟨E, rfl, rfl⟩
    exact ⟨E.sourceFinpartition, E.exists_pairwiseDisjoint_smul_sourceFinpartition⟩
  · rintro ⟨P, γ, hγ, rfl⟩
    exact ⟨.ofFinpartition P γ hγ, by simp, by simp⟩

end Group

end Equidecomp
