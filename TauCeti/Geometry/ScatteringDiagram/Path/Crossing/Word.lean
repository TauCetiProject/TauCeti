/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude Code, Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic
public import TauCeti.Geometry.ScatteringDiagram.Path.Product
public import TauCeti.Geometry.ScatteringDiagram.Path.Subdivision
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Signed crossing words through the walls of a polyhedral complex

The walls of a finite polyhedral complex are its cells of codimension one. Two distinct walls
meet only in a common proper face, so they share no relative interior point. An admissible
segment crosses walls only in their relative interiors, so it crosses at most one wall at each
time, even when several walls are coplanar. Its crossings therefore form a strictly
time-ordered list (`TauCeti.FinitePolyhedralComplex.orderedCrossings`).

Reading the signed wall generators along this list gives an element of the free group on the
walls. A wall cooriented by `ν` contributes its generator when the path crosses it against `ν`
and the inverse generator when it crosses along `ν`; the first crossing is the rightmost
factor, so wall labels acting on the left compose in traversal order. This is
`Quiver.Path.crossingWord`. It is the universal path product: for any group-valued labels
that commute along common affine spans, evaluating the crossing word by `FreeGroup.lift` gives
the transport `Quiver.Path.wallPathProduct` (`Quiver.Path.lift_crossingWord`). Unlike that
transport, the word imposes no relation between distinct walls, coplanar or not.

The crossing word is multiplicative under concatenation, is inverted by reversal when the
coorientations have the walls' directions as kernels, and is unchanged by positive rescaling of
the coorientations and by subdivision of the path (`Quiver.Path.IsSubdivision.crossingWord_eq`).
Passing to a complex with fewer walls keeps every admissible path admissible, and maps its
crossing word by the homomorphism `TauCeti.FinitePolyhedralComplex.wallDeletion` killing the
generators of the deleted walls (`Quiver.Path.crossingWord_restrictPrefunctor`).

## Attribution

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/CrossingWord.lean`,
`PathSubdivision.lean` and `WallDeletion.lean`, and the regular-wall uniqueness theorem of
`Strata.lean`, in [yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at commit
`f56836f6c1c87320bd0dfea701f6028b78830f91` (Apache 2.0).
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

noncomputable section

open Set

namespace TauCeti.FinitePolyhedralComplex

open TauCeti.WallComplement

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- An allowed endpoint for a finite polyhedral complex `C`: an ambient point lying on no wall of
`C`. -/
abbrev WallComplement (C : FinitePolyhedralComplex h) : Type _ :=
  TauCeti.WallComplement (fun P : C.walls => (P : Set V))

section Segment

variable (C : FinitePolyhedralComplex h)

/-- Two walls of a complex through a common point outside the singular support of the walls
are equal: the point lies in the relative interior of both. -/
theorem eq_of_mem_wall_of_notMem_singularSupport {P Q : C.walls} {x : V}
    (hxP : x ∈ (P : Set V)) (hxQ : x ∈ (Q : Set V))
    (hx : x ∉ singularSupport (fun W : C.walls => (W : Set V))) : P = Q :=
  Subtype.ext <| C.eq_of_mem_intrinsicInterior
    (mem_cellsOfCodimension.mp P.property).1 (mem_cellsOfCodimension.mp Q.property).1
    (mem_intrinsicInterior_of_notMem_singularSupport (W := fun W : C.walls => (W : Set V))
      hxP hx)
    (mem_intrinsicInterior_of_notMem_singularSupport (W := fun W : C.walls => (W : Set V))
      hxQ hx)

variable {x y z : C.WallComplement}

/-- On an admissible segment through the walls of a complex, the crossing time determines the
crossed wall. -/
theorem eq_of_mem_crossings (e : x ⟶ y) {P Q : C.walls} {t : ℝ}
    (hP : (P, t) ∈ crossings x y) (hQ : (Q, t) ∈ crossings x y) : P = Q :=
  C.eq_of_mem_wall_of_notMem_singularSupport ((mem_crossings x y P t).mp hP).2
    ((mem_crossings x y Q t).mp hQ).2 (e.down.regular t ((mem_crossings x y P t).mp hP).1)

/-- At a crossing of an admissible segment through a complex, the signed crossing event consists
of the crossed wall alone, with its crossing exponent. -/
theorem signedCrossingEvent_eq_singleton (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    {Q : C.walls} {t : ℝ} (hQ : (Q, t) ∈ crossings x y) :
    signedCrossingEvent ν x y t = {(Q, if 0 < ν Q (y.val - x.val) then -1 else 1)} := by
  ext ⟨Q', s⟩
  rw [mem_signedCrossingEvent, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hQ', hs⟩
    obtain rfl := C.eq_of_mem_crossings e hQ' hQ
    exact ⟨rfl, hs⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hQ, rfl⟩

/-- The crossings of an admissible segment through the walls of a complex, in strictly
increasing time order. -/
def orderedCrossings (e : x ⟶ y) : List (C.walls × ℝ) :=
  e.down.finite_crossings.toFinset.toList.mergeSort fun a b => decide (a.2 ≤ b.2)

/-- The ordered crossing list contains exactly the geometric crossings. -/
@[simp]
theorem mem_orderedCrossings (e : x ⟶ y) (a : C.walls × ℝ) :
    a ∈ C.orderedCrossings e ↔ a ∈ crossings x y := by
  simp [orderedCrossings]

/-- Crossing times strictly increase along the ordered crossing list. -/
theorem pairwise_orderedCrossings (e : x ⟶ y) :
    (C.orderedCrossings e).Pairwise (fun a b => a.2 < b.2) := by
  unfold orderedCrossings
  have hle := List.pairwise_mergeSort (le := fun a b : C.walls × ℝ => decide (a.2 ≤ b.2))
    (fun _ _ _ hab hbc => by simpa using le_trans (by simpa using hab) (by simpa using hbc))
    (fun a b => by simpa using le_total a.2 b.2) e.down.finite_crossings.toFinset.toList
  refine (hle.and <| List.nodup_iff_pairwise_ne.mp <| (List.mergeSort_perm _ _).nodup_iff.mpr
    (Finset.nodup_toList _)).imp_of_mem fun {a b} ha hb hab => ?_
  refine lt_of_le_of_ne (by simpa using hab.1) fun he => hab.2 (Prod.ext ?_ he)
  simp only [List.mem_mergeSort, Finset.mem_toList, Set.Finite.mem_toFinset] at ha hb
  exact C.eq_of_mem_crossings e ha (he ▸ hb)

/-- The ordered crossing list is the unique strictly time-ordered list of the geometric
crossings. -/
theorem orderedCrossings_eq_iff (e : x ⟶ y) (l : List (C.walls × ℝ)) :
    C.orderedCrossings e = l ↔
      l.Pairwise (fun a b => a.2 < b.2) ∧ ∀ a, a ∈ l ↔ a ∈ crossings x y := by
  constructor
  · rintro rfl
    exact ⟨C.pairwise_orderedCrossings e, C.mem_orderedCrossings e⟩
  · rintro ⟨hpair, hmem⟩
    have : Std.Antisymm (fun a b : C.walls × ℝ => a.2 < b.2) :=
      ⟨fun _ _ hab hba => (lt_asymm hab hba).elim⟩
    have : Std.Irrefl (fun a b : C.walls × ℝ => a.2 < b.2) := ⟨fun a => lt_irrefl a.2⟩
    exact (C.pairwise_orderedCrossings e).eq_of_mem_iff hpair
      fun a => (C.mem_orderedCrossings e a).trans (hmem a).symm

/-- A segment whose crossing set through `C` is a singleton `{(P, t)}` has ordered crossing list
`[(P, t)]`. -/
theorem orderedCrossings_of_crossings_eq_singleton (e : x ⟶ y) {P : C.walls} {t : ℝ}
    (hcr : crossings x y = {(P, t)}) :
    C.orderedCrossings e = [(P, t)] :=
  (C.orderedCrossings_eq_iff e [(P, t)]).mpr
    ⟨List.pairwise_singleton _ _, fun a => by simp [hcr]⟩

/-- The distinct crossing times of a segment through a complex are the times of its ordered
crossings. -/
theorem orderedCrossingTimes_eq_map_snd (e : x ⟶ y) :
    orderedCrossingTimes e = (C.orderedCrossings e).map Prod.snd := by
  refine (pairwise_orderedCrossingTimes e).eq_of_mem_iff
    (List.pairwise_map.mpr (C.pairwise_orderedCrossings e)) fun t => ?_
  simp only [mem_orderedCrossingTimes, List.mem_map, mem_orderedCrossings, Prod.exists,
    exists_eq_right]

/-- Reversing a segment reverses its crossing list and replaces each time `t` by `1 - t`. -/
theorem orderedCrossings_reverse (e : x ⟶ y) :
    C.orderedCrossings (Quiver.reverse e) =
      (C.orderedCrossings e).reverse.map fun a => (a.1, 1 - a.2) := by
  refine (C.orderedCrossings_eq_iff _ _).mpr ⟨?_, fun a => ?_⟩
  · exact List.pairwise_map.mpr <|
      (C.pairwise_orderedCrossings e).reverse.imp fun hab => by dsimp; linarith
  · rcases a with ⟨P, t⟩
    rw [mem_crossings_swap]
    simp only [List.mem_map, List.mem_reverse, mem_orderedCrossings]
    constructor
    · rintro ⟨⟨Q, s⟩, hs, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simpa only [sub_sub_cancel] using hs
    · exact fun ht => ⟨(P, 1 - t), ht, by simp⟩

/-- Inserting an allowed vertex at time `t ∈ (0, 1)` splits the crossing list of a segment into
those of the two subsegments, with their times rescaled to the original segment. -/
theorem orderedCrossings_subdivide (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    C.orderedCrossings e =
      (C.orderedCrossings e₁).map (fun a => (a.1, a.2 * t)) ++
        (C.orderedCrossings e₂).map (fun a => (a.1, 1 - (1 - a.2) * (1 - t))) := by
  refine (C.orderedCrossings_eq_iff e _).mpr ⟨?_, fun a => ?_⟩
  · refine List.pairwise_append.mpr ⟨List.pairwise_map.mpr <|
      (C.pairwise_orderedCrossings e₁).imp fun hab => mul_lt_mul_of_pos_right hab ht.1,
      List.pairwise_map.mpr <| (C.pairwise_orderedCrossings e₂).imp fun hab => ?_, ?_⟩
    · dsimp
      nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht.2)]
    · intro a ha b hb
      obtain ⟨a, ha₀, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, hb₀, rfl⟩ := List.mem_map.mp hb
      have ha' := mem_Ioo_of_mem_crossings ((C.mem_orderedCrossings e₁ a).mp ha₀)
      have hb' := mem_Ioo_of_mem_crossings ((C.mem_orderedCrossings e₂ b).mp hb₀)
      dsimp
      nlinarith [mul_pos (sub_pos.mpr ha'.2) ht.1, mul_pos hb'.1 (sub_pos.mpr ht.2)]
  · rw [crossings_subdivide hz ht]
    simp only [List.mem_append, List.mem_map, mem_orderedCrossings, mem_union, mem_image]

/-- The signed generator of a crossing of the wall `P` by the segment `[x, y]`: the inverse
generator when the velocity is positive on the coorientation, and the generator otherwise. -/
def crossingLetter (ν : C.walls → V →ₗ[ℝ] ℝ) (x y : C.WallComplement) (P : C.walls) :
    FreeGroup C.walls :=
  if 0 < ν P (y.val - x.val) then (FreeGroup.of P)⁻¹ else FreeGroup.of P

/-- The sign convention defining each crossing letter. -/
theorem crossingLetter_def (ν : C.walls → V →ₗ[ℝ] ℝ) (x y : C.WallComplement) (P : C.walls) :
    C.crossingLetter ν x y P =
      if 0 < ν P (y.val - x.val) then (FreeGroup.of P)⁻¹ else FreeGroup.of P := (rfl)

/-- A crossing letter is the generator raised to the crossing exponent of the signed crossing
events. -/
theorem crossingLetter_eq_zpow (ν : C.walls → V →ₗ[ℝ] ℝ) (x y : C.WallComplement) (P : C.walls) :
    C.crossingLetter ν x y P =
      FreeGroup.of P ^ (if 0 < ν P (y.val - x.val) then -1 else 1 : ℤ) := by
  rw [crossingLetter_def]
  split_ifs <;> simp

/-- Reversing a velocity on which the coorientation is nonzero inverts the crossing letter. -/
theorem crossingLetter_swap (ν : C.walls → V →ₗ[ℝ] ℝ) (P : C.walls)
    (hν : ν P (y.val - x.val) ≠ 0) :
    C.crossingLetter ν y x P = (C.crossingLetter ν x y P)⁻¹ := by
  have he : ν P (x.val - y.val) = -ν P (y.val - x.val) := by simp [map_sub]
  rw [crossingLetter_def, crossingLetter_def, he]
  rcases lt_or_gt_of_ne hν with hn | hn
  · simp only [neg_pos.mpr hn, not_lt_of_ge hn.le, ↓reduceIte]
  · simp only [not_lt_of_ge (neg_nonpos.mpr hn.le), hn, ↓reduceIte, inv_inv]

/-- Positive rescaling of the coorientations leaves every crossing letter unchanged. -/
@[simp]
theorem crossingLetter_smul (ν : C.walls → V →ₗ[ℝ] ℝ) (r : C.walls → ℝ) (hr : ∀ P, 0 < r P)
    (x y : C.WallComplement) (P : C.walls) :
    C.crossingLetter (fun Q => r Q • ν Q) x y P = C.crossingLetter ν x y P := by
  simp [crossingLetter_def, mul_pos_iff_of_pos_left (hr P)]

/-- Moving the end of a segment to an interior point at positive time preserves the crossing
letters. -/
theorem crossingLetter_subdivide_left (ν : C.walls → V →ₗ[ℝ] ℝ) {t : ℝ} (ht : 0 < t)
    (hz : z.val = AffineMap.lineMap x.val y.val t) (P : C.walls) :
    C.crossingLetter ν x z P = C.crossingLetter ν x y P := by
  rw [crossingLetter_def, crossingLetter_def, hz, AffineMap.lineMap_apply_module',
    add_sub_cancel_right, map_smul]
  simp only [smul_eq_mul, mul_pos_iff_of_pos_left ht]

/-- Moving the start of a segment to an interior point at time less than one preserves the
crossing letters. -/
theorem crossingLetter_subdivide_right (ν : C.walls → V →ₗ[ℝ] ℝ) {t : ℝ} (ht : t < 1)
    (hz : z.val = AffineMap.lineMap x.val y.val t) (P : C.walls) :
    C.crossingLetter ν z y P = C.crossingLetter ν x y P := by
  have hv : y.val - z.val = (1 - t) • (y.val - x.val) := by
    rw [hz]
    exact AffineMap.right_vsub_lineMap x.val y.val t
  rw [crossingLetter_def, crossingLetter_def, hv, map_smul]
  simp only [smul_eq_mul, mul_pos_iff_of_pos_left (sub_pos.mpr ht)]

/-- The crossing word of one admissible segment, with the first crossing rightmost. -/
def segmentCrossingWord (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) : FreeGroup C.walls :=
  ((C.orderedCrossings e).reverse.map fun a => C.crossingLetter ν x y a.1).prod

/-- A segment word is the product of the signed letters of its crossings in reverse time
order. -/
theorem segmentCrossingWord_def (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) :
    C.segmentCrossingWord ν e =
      ((C.orderedCrossings e).reverse.map fun a => C.crossingLetter ν x y a.1).prod := (rfl)

/-- A segment meeting no wall has trivial crossing word. -/
theorem segmentCrossingWord_eq_one_of_crossings_eq_empty (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    (he : crossings x y = ∅) : C.segmentCrossingWord ν e = 1 := by
  have hl : C.orderedCrossings e = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun a => by simp [he]
  simp [segmentCrossingWord_def, hl]

/-- A segment whose crossing set through `C` is a singleton `{(P, t)}` has segment crossing word
`C.crossingLetter ν x y P`. -/
theorem segmentCrossingWord_of_crossings_eq_singleton (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    {P : C.walls} {t : ℝ} (hcr : crossings x y = {(P, t)}) :
    C.segmentCrossingWord ν e = C.crossingLetter ν x y P := by
  simp [C.segmentCrossingWord_def, C.orderedCrossings_of_crossings_eq_singleton e hcr]

/-- A stationary segment has trivial crossing word. -/
@[simp]
theorem segmentCrossingWord_self (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ x) :
    C.segmentCrossingWord ν e = 1 :=
  C.segmentCrossingWord_eq_one_of_crossings_eq_empty ν e <|
    Set.eq_empty_iff_forall_notMem.mpr fun ⟨P, t⟩ hP =>
      x.notMem P (by simpa using ((mem_crossings x x P t).mp hP).2)

/-- Reversing a segment inverts its crossing word, for coorientations whose kernels are the
wall directions. -/
@[simp]
theorem segmentCrossingWord_reverse (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) (e : x ⟶ y) :
    C.segmentCrossingWord ν (Quiver.reverse e) = (C.segmentCrossingWord ν e)⁻¹ := by
  have hl : (C.orderedCrossings e).map (fun a => C.crossingLetter ν y x a.1) =
      (C.orderedCrossings e).map (fun a => (C.crossingLetter ν x y a.1)⁻¹) := by
    refine List.map_congr_left fun a ha => C.crossingLetter_swap ν a.1 fun hz => ?_
    have ha := (mem_crossings x y a.1 a.2).mp ((C.mem_orderedCrossings e a).mp ha)
    exact e.down.transverse a.1 ⟨a.2, ha.1, ha.2⟩ (hν a.1 ▸ hz)
  simp only [segmentCrossingWord_def, orderedCrossings_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map, Function.comp_def]
  rw [hl, List.prod_inv_reverse]
  simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def]

/-- Positive rescaling of the coorientations preserves a segment word. -/
@[simp]
theorem segmentCrossingWord_smul (ν : C.walls → V →ₗ[ℝ] ℝ) (r : C.walls → ℝ)
    (hr : ∀ P, 0 < r P) (e : x ⟶ y) :
    C.segmentCrossingWord (fun P => r P • ν P) e = C.segmentCrossingWord ν e := by
  simp only [segmentCrossingWord_def, crossingLetter_smul C ν r hr]

/-- Inserting an allowed vertex at a time in `[0, 1]` splits a segment word into the words of
the two subsegments, the later one on the left. -/
theorem segmentCrossingWord_subdivide (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) (e₁ : x ⟶ z)
    (e₂ : z ⟶ y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hz : z.val = AffineMap.lineMap x.val y.val t) :
    C.segmentCrossingWord ν e = C.segmentCrossingWord ν e₂ * C.segmentCrossingWord ν e₁ := by
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · obtain rfl : z = x := WallComplement.ext (by simpa [← ht0] using hz)
    rw [segmentCrossingWord_self, mul_one,
      Subsingleton.elim e e₂]
  rcases eq_or_lt_of_le ht.2 with ht1 | ht1
  · obtain rfl : z = y := WallComplement.ext (by simpa [ht1] using hz)
    rw [segmentCrossingWord_self, one_mul,
      Subsingleton.elim e e₁]
  simp only [segmentCrossingWord_def, C.orderedCrossings_subdivide e e₁ e₂ ⟨ht0, ht1⟩ hz,
    List.reverse_append, List.map_append, List.prod_append, List.map_reverse, List.map_map,
    Function.comp_def, C.crossingLetter_subdivide_left ν ht0 hz,
    C.crossingLetter_subdivide_right ν ht1 hz]

/-- Evaluating a segment word on wall labels that commute along common affine spans gives the
segment transport. -/
theorem lift_segmentCrossingWord {G : Type*} [Group G] (ν : C.walls → V →ₗ[ℝ] ℝ)
    (label : C.walls → G)
    (hcomm : ∀ P Q : C.walls, affineSpan ℝ (P : Set V) = affineSpan ℝ (Q : Set V) →
      Commute (label P) (label Q))
    (e : x ⟶ y) :
    FreeGroup.lift label (C.segmentCrossingWord ν e) = segmentPathProduct ν label hcomm e := by
  rw [segmentCrossingWord_def, segmentPathProduct_def, map_list_prod,
    C.orderedCrossingTimes_eq_map_snd e]
  simp only [List.map_reverse, List.map_map, Function.comp_def]
  congr 2
  refine List.map_congr_left fun a ha => ?_
  rw [crossingEventProduct_singleton ν label hcomm e a.2 _
    (C.signedCrossingEvent_eq_singleton ν e ((C.mem_orderedCrossings e a).mp ha)),
    crossingLetter_eq_zpow, map_zpow, FreeGroup.lift_apply_of]

end Segment

section Deletion

variable {C D : FinitePolyhedralComplex h}

variable (C D) in
/-- The homomorphism of free groups on walls retaining the walls of `D` and killing all
others. -/
def wallDeletion : FreeGroup C.walls →* FreeGroup D.walls :=
  FreeGroup.lift fun P => if hP : P.val ∈ D.walls then FreeGroup.of ⟨P.val, hP⟩ else 1

/-- Wall deletion sends a generator to the generator of the same wall, or to `1` when the wall
is deleted. -/
@[simp]
theorem wallDeletion_of (P : C.walls) :
    C.wallDeletion D (FreeGroup.of P) =
      if hP : P.val ∈ D.walls then FreeGroup.of ⟨P.val, hP⟩ else 1 := by
  simp [wallDeletion]

/-- Deleting no walls is the identity. -/
@[simp]
theorem wallDeletion_self (C : FinitePolyhedralComplex h) :
    C.wallDeletion C = MonoidHom.id _ :=
  FreeGroup.ext_hom _ _ fun P => by simp

/-- Successive wall deletions compose to the deletion of all walls absent from the last
complex, when the walls shrink. -/
theorem wallDeletion_comp {E : FinitePolyhedralComplex h} (hW : E.walls ⊆ D.walls) :
    (D.wallDeletion E).comp (C.wallDeletion D) = C.wallDeletion E := by
  refine FreeGroup.ext_hom _ _ fun P => ?_
  rw [MonoidHom.comp_apply, wallDeletion_of, wallDeletion_of]
  by_cases hD : P.val ∈ D.walls
  · rw [dite_eq_left hD, wallDeletion_of]
  · rw [dite_eq_right hD, dite_eq_right fun hE => hD (hW hE), map_one]

variable (hW : D.walls ⊆ C.walls) {x y : C.WallComplement}

/-- Deleting walls filters the crossing list of a segment, keeping the times of the retained
crossings. -/
theorem orderedCrossings_restrictPrefunctor (e : x ⟶ y) :
    D.orderedCrossings ((WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
        fun P : D.walls => (⟨P.val, hW P.property⟩ : C.walls)).map e) =
      (C.orderedCrossings e).filterMap
        fun a => if hP : a.1.val ∈ D.walls then some (⟨a.1.val, hP⟩, a.2) else none := by
  classical
  set f : C.walls × ℝ → Option (D.walls × ℝ) :=
    fun a => if hP : a.1.val ∈ D.walls then some (⟨a.1.val, hP⟩, a.2) else none
  have hsome (a : C.walls × ℝ) (b : D.walls × ℝ) :
      f a = some b ↔ a.1.val = b.1.val ∧ a.2 = b.2 := by
    rcases b with ⟨⟨Q, hQ⟩, t⟩
    by_cases ha : a.1.val ∈ D.walls
    · simp only [f, ha, dite_true, Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    · simp only [f, ha, dite_false, reduceCtorEq, false_iff, not_and]
      exact fun hab => (ha (hab ▸ hQ)).elim
  refine (D.orderedCrossings_eq_iff _ _).mpr ⟨?_, fun b => ?_⟩
  · refine (C.pairwise_orderedCrossings e).filterMap f fun a a' haa b hb b' hb' => ?_
    rw [hsome] at hb hb'
    simpa only [← hb.2, ← hb'.2] using haa
  · rcases b with ⟨P, t⟩
    have hmem := WallComplement.mem_crossings_restrictPrefunctor
      (W := fun P : C.walls => (P : Set V))
      (fun P : D.walls => (⟨P.val, hW P.property⟩ : C.walls)) x y P t
    simp only [List.mem_filterMap, mem_orderedCrossings, Prod.exists]
    constructor
    · rintro ⟨Q, s, ha, hf⟩
      obtain ⟨hab, rfl⟩ := (hsome (Q, s) (P, t)).mp hf
      obtain rfl : Q = ⟨P.val, hW P.property⟩ := Subtype.ext hab
      exact hmem.mpr ha
    · exact fun hb => ⟨⟨P.val, hW P.property⟩, t, hmem.mp hb, (hsome _ _).mpr ⟨rfl, rfl⟩⟩

/-- Wall deletion sends a crossing letter of a retained wall to the crossing letter of that wall
at the restricted endpoints, and the letter of a deleted wall to `1`. -/
theorem wallDeletion_crossingLetter (ν : C.walls → V →ₗ[ℝ] ℝ) (P : C.walls) :
    C.wallDeletion D (C.crossingLetter ν x y P) =
      if hP : P.val ∈ D.walls then
        D.crossingLetter (fun Q => ν ⟨Q.val, hW Q.property⟩)
          ((WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
            fun P : D.walls => (⟨P.val, hW P.property⟩ : C.walls)).obj x)
          ((WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
            fun P : D.walls => (⟨P.val, hW P.property⟩ : C.walls)).obj y) ⟨P.val, hP⟩
      else 1 := by
  rw [crossingLetter_eq_zpow, map_zpow, wallDeletion_of]
  by_cases hP : P.val ∈ D.walls
  · -- `simp` reduces the restricted endpoint values to `x.val` and `y.val` by projection
    -- reduction of the `abbrev` `restrictPrefunctor`; this is `restrictPrefunctor_obj_val`, which
    -- is `rfl`, so passing it to `simp only` is rejected as an unused argument.
    simp only [dite_eq_left hP, crossingLetter_eq_zpow]
  · simp only [dite_eq_right hP, one_zpow]

/-- Deleting walls maps a segment word by `wallDeletion`, the remaining walls keeping their
coorientations. -/
@[simp]
theorem segmentCrossingWord_restrictPrefunctor (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) :
    D.segmentCrossingWord (fun P => ν ⟨P.val, hW P.property⟩)
        ((WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
          fun P : D.walls => (⟨P.val, hW P.property⟩ : C.walls)).map e) =
      C.wallDeletion D (C.segmentCrossingWord ν e) := by
  rw [segmentCrossingWord_def, segmentCrossingWord_def, orderedCrossings_restrictPrefunctor hW e,
    ← List.filterMap_reverse]
  generalize (C.orderedCrossings e).reverse = l
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a.1.val ∈ D.walls <;>
      simp only [List.filterMap_cons, ha, ↓reduceDIte, List.map_cons, List.prod_cons, map_mul,
        ih, wallDeletion_crossingLetter hW, one_mul]

end Deletion

end TauCeti.FinitePolyhedralComplex

namespace Quiver.Path

open TauCeti TauCeti.WallComplement TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C D : FinitePolyhedralComplex h}
  {x y z : C.WallComplement}

/-- The signed crossing word of an admissible polygonal path through the walls of a complex,
with the first crossing rightmost. -/
def crossingWord (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ) : FreeGroup C.walls :=
  MulOpposite.unop (p.weight fun e => MulOpposite.op (C.segmentCrossingWord ν e))

/-- A constant path has trivial crossing word. -/
@[simp]
theorem crossingWord_nil (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (Quiver.Path.nil : AdmissiblePLPath x x).crossingWord ν = 1 := by
  simp only [crossingWord, weight_nil, MulOpposite.unop_one]

/-- Appending a segment multiplies the crossing word on the left by the segment word. -/
@[simp]
theorem crossingWord_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (p.cons e).crossingWord ν = C.segmentCrossingWord ν e * p.crossingWord ν := by
  simp only [crossingWord, weight_cons, MulOpposite.unop_mul, MulOpposite.unop_op]

/-- The crossing word of a single segment is its segment word. -/
@[simp]
theorem crossingWord_toPath (e : x ⟶ y) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    e.toPath.crossingWord ν = C.segmentCrossingWord ν e := by
  simp [Quiver.Hom.toPath]

/-- The crossing word of a concatenation is the product of the crossing words, the later path
on the left. -/
@[simp]
theorem crossingWord_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (p.comp q).crossingWord ν = q.crossingWord ν * p.crossingWord ν := by
  simp only [crossingWord, weight_comp, MulOpposite.unop_mul]

/-- Reversing a path inverts its crossing word, for coorientations whose kernels are the wall
directions. -/
@[simp]
theorem crossingWord_reverse (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) :
    p.reverse.crossingWord ν = (p.crossingWord ν)⁻¹ := by
  induction p with
  | nil => simp [Quiver.Path.reverse]
  | cons p e ih => simp [Quiver.Path.reverse, ih, C.segmentCrossingWord_reverse ν hν]

/-- Positive rescaling of the coorientations preserves the crossing word. -/
@[simp]
theorem crossingWord_smul (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) :
    p.crossingWord (fun P => r P • ν P) = p.crossingWord ν := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, C.segmentCrossingWord_smul ν r hr]

/-- Subdividing a path by allowed interior vertices preserves its crossing word. -/
theorem IsSubdivision.crossingWord_eq {p q : AdmissiblePLPath x y} (hpq : p.IsSubdivision q)
    (ν : C.walls → V →ₗ[ℝ] ℝ) : q.crossingWord ν = p.crossingWord ν := by
  induction hpq with
  | refl p => rfl
  | split e e₁ e₂ ht hz =>
    simpa only [crossingWord_comp, crossingWord_toPath] using
      (C.segmentCrossingWord_subdivide ν e e₁ e₂ ⟨ht.1.le, ht.2.le⟩ hz).symm
  | comp _ _ ihp ihq => simp only [crossingWord_comp, ihp, ihq]
  | trans _ _ ihpq ihqr => exact ihqr.trans ihpq

/-- Evaluating the crossing word on wall labels that commute along common affine spans gives
the wall transport of the path. -/
theorem lift_crossingWord {G : Type*} [Group G] (p : AdmissiblePLPath x y)
    (ν : C.walls → V →ₗ[ℝ] ℝ) (label : C.walls → G)
    (hcomm : ∀ P Q : C.walls, affineSpan ℝ (P : Set V) = affineSpan ℝ (Q : Set V) →
      Commute (label P) (label Q)) :
    FreeGroup.lift label (p.crossingWord ν) = p.wallPathProduct ν label hcomm := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, C.lift_segmentCrossingWord ν label hcomm e]

/-- Forgetting the walls absent from a complex with fewer walls maps the crossing word of a
path by `TauCeti.FinitePolyhedralComplex.wallDeletion`. -/
@[simp]
theorem crossingWord_restrictPrefunctor (p : AdmissiblePLPath x y) (hW : D.walls ⊆ C.walls)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    ((WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
        fun P : D.walls => (⟨P.val, hW P.property⟩ : C.walls)).mapPath p).crossingWord
          (fun P => ν ⟨P.val, hW P.property⟩) =
      C.wallDeletion D (p.crossingWord ν) := by
  induction p with
  | nil => simp only [Prefunctor.mapPath_nil, crossingWord_nil (C := D),
      crossingWord_nil (C := C), map_one]
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, crossingWord_cons (C := D), crossingWord_cons (C := C),
      map_mul, ih,
      segmentCrossingWord_restrictPrefunctor hW ν e]

end Quiver.Path
