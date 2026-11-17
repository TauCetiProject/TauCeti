/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Product
public import Mathlib.GroupTheory.FreeGroup.Basic
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Data.Finset.Sort

/-!
# Crossing words of admissible paths across interior-disjoint walls

When a finite family of walls `W : ι → Set V` has pairwise disjoint intrinsic interiors, an
admissible segment crosses every wall in its intrinsic interior and therefore meets at most one
wall at each crossing parameter (`AdmissibleSegment.eq_of_mem_crossings`,
`subsingleton_crossingWalls`). Each simultaneous signed crossing event is then a singleton, so
without any commutation hypothesis on parallel or collinear walls, an admissible polygonal path `p`
carries a well-defined `crossingWord` in `FreeGroup ι`. Following the left-action convention of
`WallComplement.signedCrossingEvent`, the first crossing stands rightmost and a positive normal
velocity contributes the inverse generator `(FreeGroup.of i)⁻¹`.

Every `wallPathProduct` with coplanar-commuting labels in a group `G` factors through
`crossingWord` via `FreeGroup.lift label` (`lift_crossingWord_eq_wallPathProduct`). The crossing
word is multiplicative in reverse order under concatenation, inverted by path reversal, invariant
under positive rescaling of coorientations and under path subdivision
(`IsSubdivision.crossingWord_eq`), mapped by `FreeGroup.lift` killing deleted walls when
restricting to an injectively indexed subfamily (`crossingWord_restrictPrefunctor`), and mapped by
`FreeGroup.map` along a wall-index equivalence under continuous affine coordinate transport
(`crossingWord_affineMapReindex`).

Specialization to the walls of a `FinitePolyhedralComplex` is developed in
`TauCeti.Geometry.ScatteringDiagram.Path.Polyhedral`, and worked examples are in
`TauCeti.Examples.Geometry.ScatteringDiagram.Path.Word`.

## References

* M. Kontsevich and Y. Soibelman, *Wall-crossing structures in Donaldson–Thomas invariants,
  integrable systems and Mirror Symmetry*, §2.1.
* M. Gross, *Tropical Geometry and Mirror Symmetry*, §6.2.
* T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §2.3.

## Attribution

The `crossingEventWord`, `segmentCrossingWord`, and `crossingWord` API closely adapts
`TauCeti/Geometry/ScatteringDiagram/Path/Product.lean`,
`TauCeti/Geometry/ScatteringDiagram/Path/Basic.lean`, and
`TauCeti/Geometry/ScatteringDiagram/Path/Affine.lean`, which were ported from
`Mei/Geometry/Convex/Polyhedron/Path/Product.lean`,
`Mei/Geometry/Convex/Polyhedron/AdmissiblePath.lean`, and
`Mei/Geometry/Convex/Polyhedron/AffinePath.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei) at commits
`9cf969cdee9748087aae45dbf4888a130890655c` and `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`
(Apache 2.0; original copyright (c) 2026 Mei contributors, original author Codex).
-/

public section

noncomputable section

open Set

namespace TauCeti.WallComplement

section IsolatedCrossings

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}
  {x y : WallComplement W}

/-- When walls have pairwise disjoint intrinsic interiors, an admissible segment meets at most one
wall at any affine parameter `t`. -/
theorem AdmissibleSegment.eq_of_mem_crossings (a : AdmissibleSegment x y)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {t : ℝ} {i j : ι} (hi : (i, t) ∈ crossings x y) (hj : (j, t) ∈ crossings x y) : i = j := by
  obtain ⟨ht, hi'⟩ := (mem_crossings x y i t).mp hi
  obtain ⟨_, hj'⟩ := (mem_crossings x y j t).mp hj
  by_contra hij
  exact Set.disjoint_left.mp (hdisj hij)
    (a.crossing_mem_intrinsicInterior ht hi').2
    (a.crossing_mem_intrinsicInterior ht hj').2

variable [Finite ι]

/-- At each affine parameter, at most one wall of an interior-disjoint family is crossed. -/
theorem subsingleton_crossingWalls (e : x ⟶ y)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (t : ℝ) : (crossingWalls x y t : Set ι).Subsingleton := fun _ hi _ hj =>
  e.down.eq_of_mem_crossings hdisj
    ((mem_crossingWalls x y t _).mp hi) ((mem_crossingWalls x y t _).mp hj)

/-- At most one wall of an interior-disjoint family is crossed at time `t`. -/
theorem card_crossingWalls_le_one (e : x ⟶ y)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (t : ℝ) : (crossingWalls x y t).card ≤ 1 :=
  Finset.card_le_one.mpr (subsingleton_crossingWalls e hdisj t)

/-- Every listed crossing time on an admissible segment crosses a unique wall when walls have
pairwise disjoint intrinsic interiors. -/
theorem card_crossingWalls_eq_one (e : x ⟶ y)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {t : ℝ} (ht : t ∈ orderedCrossingTimes e) : (crossingWalls x y t).card = 1 :=
  le_antisymm (card_crossingWalls_le_one e hdisj t)
    (Finset.one_le_card.mpr (crossingWalls_nonempty e ht))

/-- Each signed crossing event of an interior-disjoint wall family has at most one element. -/
theorem subsingleton_signedCrossingEvent (ν : ι → V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (t : ℝ) : (signedCrossingEvent ν x y t : Set (ι × ℤ)).Subsingleton := by
  rintro ⟨i, s₁⟩ hi ⟨j, s₂⟩ hj
  obtain ⟨hi', rfl⟩ := (mem_signedCrossingEvent ν x y t i s₁).mp hi
  obtain ⟨hj', rfl⟩ := (mem_signedCrossingEvent ν x y t j s₂).mp hj
  obtain rfl := e.down.eq_of_mem_crossings hdisj hi' hj'
  rfl

/-- Every signed crossing event at a listed crossing time is a singleton. -/
theorem card_signedCrossingEvent_eq_one (ν : ι → V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {t : ℝ} (ht : t ∈ orderedCrossingTimes e) : (signedCrossingEvent ν x y t).card = 1 :=
  le_antisymm (Finset.card_le_one.mpr (subsingleton_signedCrossingEvent ν e hdisj t))
    (Finset.one_le_card.mpr <| by
      obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes e t).mp ht
      exact ⟨(i, if 0 < ν i (y.val - x.val) then -1 else 1),
        (mem_signedCrossingEvent ν x y t i _).mpr ⟨hi, rfl⟩⟩)

/-- Pairwise commutation on a signed crossing event holds vacuously when walls have pairwise
disjoint intrinsic interiors. -/
theorem signedCrossingEvent_pairwise_of_disjoint {G : Type*} [Mul G] (ν : ι → V →ₗ[ℝ] ℝ)
    (e : x ⟶ y)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (f : ι × ℤ → G) (t : ℝ) :
    (signedCrossingEvent ν x y t : Set (ι × ℤ)).Pairwise
      (fun a b => Commute (f a) (f b)) :=
  (subsingleton_signedCrossingEvent ν e hdisj t).pairwise _

/-- The free-group generator (or inverse) contributed at affine parameter `t` on an admissible
segment across an interior-disjoint wall family. -/
def crossingEventWord (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) : FreeGroup ι :=
  (signedCrossingEvent ν x y t).noncommProd (fun a => FreeGroup.of a.1 ^ a.2)
    (signedCrossingEvent_pairwise_of_disjoint ν e hdisj _ t)

/-- `crossingEventWord` is the `Finset.noncommProd` of signed generators over
`signedCrossingEvent`. -/
theorem crossingEventWord_def (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) :
    crossingEventWord ν hdisj e t =
      (signedCrossingEvent ν x y t).noncommProd (fun a => FreeGroup.of a.1 ^ a.2)
        (signedCrossingEvent_pairwise_of_disjoint ν e hdisj _ t) := (rfl)

@[simp]
theorem crossingEventWord_empty (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) (ht : signedCrossingEvent ν x y t = ∅) :
    crossingEventWord ν hdisj e t = 1 := by
  unfold crossingEventWord
  exact (Finset.noncommProd_congr ht (fun _ _ => rfl) _).trans (Finset.noncommProd_empty _ _)

/-- If no wall is crossed at parameter `t`, `crossingEventWord` is `1`. -/
theorem crossingEventWord_eq_one_of_forall_notMem (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) (h : ∀ i, (i, t) ∉ crossings x y) :
    crossingEventWord ν hdisj e t = 1 := by
  refine crossingEventWord_empty ν hdisj e t (Finset.eq_empty_iff_forall_notMem.mpr ?_)
  rintro ⟨i, s⟩ his
  exact h i ((mem_signedCrossingEvent ν x y t i s).mp his).1

/-- A crossing `(i, t) ∈ crossings x y` contributes `(FreeGroup.of i)⁻¹` for positive normal
velocity and `FreeGroup.of i` otherwise. -/
theorem crossingEventWord_of_mem_crossings (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) {i : ι} {t : ℝ} (hi : (i, t) ∈ crossings x y) :
    crossingEventWord ν hdisj e t =
      FreeGroup.of i ^ (if 0 < ν i (y.val - x.val) then -1 else 1 : ℤ) := by
  set s : ℤ := if 0 < ν i (y.val - x.val) then -1 else 1
  have hmem : (i, s) ∈ signedCrossingEvent ν x y t :=
    (mem_signedCrossingEvent ν x y t i s).mpr ⟨hi, rfl⟩
  have hsing : signedCrossingEvent ν x y t = {(i, s)} := by
    ext a
    simp only [Finset.mem_singleton]
    exact ⟨fun ha => subsingleton_signedCrossingEvent ν e hdisj t ha hmem,
      fun ha => ha ▸ hmem⟩
  unfold crossingEventWord
  simp only [hsing, Finset.noncommProd_singleton]

/-- Every duplicate-free enumeration of the signed crossing event computes `crossingEventWord`. -/
theorem crossingEventWord_eq_prod (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) (l : List (ι × ℤ)) (hl : l.Nodup)
    (hm : ∀ a, a ∈ l ↔ a ∈ signedCrossingEvent ν x y t) :
    crossingEventWord ν hdisj e t = (l.map fun a => FreeGroup.of a.1 ^ a.2).prod := by
  classical
  have hs : l.toFinset = signedCrossingEvent ν x y t := by ext a; simpa using hm a
  unfold crossingEventWord
  exact (Finset.noncommProd_congr hs.symm (fun _ _ => rfl) _).trans
    (Finset.noncommProd_toFinset l _ _ hl)

/-- Reversing an admissible segment inverts the crossing-event word and reflects time in `1/2`. -/
theorem crossingEventWord_reverse (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) (t : ℝ) :
    crossingEventWord ν hdisj (Quiver.reverse e) t =
      (crossingEventWord ν hdisj e (1 - t))⁻¹ := by
  let S := signedCrossingEvent ν x y (1 - t)
  let f : ι × ℤ → FreeGroup ι := fun a => FreeGroup.of a.1 ^ a.2
  let emb := (Equiv.prodCongr (Equiv.refl ι) (Equiv.neg ℤ)).toEmbedding
  have hc := signedCrossingEvent_pairwise_of_disjoint ν e hdisj f (1 - t)
  have hc' : (S.map emb : Set (ι × ℤ)).Pairwise (fun a b => Commute (f a) (f b)) := by
    rw [← signedCrossingEvent_swap ν hν e t]
    exact signedCrossingEvent_pairwise_of_disjoint ν (Quiver.reverse e) hdisj f t
  calc
    _ = (S.map emb).noncommProd f hc' :=
      Finset.noncommProd_congr (signedCrossingEvent_swap ν hν e t) (fun _ _ => rfl) _
    _ = S.noncommProd (fun a => f (emb a)) _ := Finset.noncommProd_map S emb f hc'
    _ = _ := by
      simpa only [f, emb, Equiv.toEmbedding_apply, Equiv.prodCongr_apply, Prod.map_fst,
        Prod.map_snd, Equiv.refl_apply, Equiv.neg_apply, zpow_neg, crossingEventWord, S] using
        Finset.noncommProd_inv S f hc

/-- Lifting `crossingEventWord` along any coplanar-commuting label assignment recovers
`crossingEventProduct`. -/
theorem lift_crossingEventWord_eq_crossingEventProduct {G : Type*} [Group G] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (label : ι → G)
    (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (e : x ⟶ y) (t : ℝ) :
    FreeGroup.lift label (crossingEventWord ν hdisj e t) =
      crossingEventProduct ν label hcomm e t := by
  rw [crossingEventWord_def, Finset.map_noncommProd, crossingEventProduct_eq_noncommProd]
  exact Finset.noncommProd_congr rfl (fun a _ => by simp) _

/-- The free-group word of an admissible segment, with the first crossing rightmost. -/
def segmentCrossingWord (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) : FreeGroup ι :=
  ((orderedCrossingTimes e).reverse.map (crossingEventWord ν hdisj e)).prod

/-- `segmentCrossingWord` is the reverse-time list product of `crossingEventWord`. -/
theorem segmentCrossingWord_def (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) :
    segmentCrossingWord ν hdisj e =
      ((orderedCrossingTimes e).reverse.map (crossingEventWord ν hdisj e)).prod := (rfl)

/-- Any strictly increasing list covering `orderedCrossingTimes e` computes `segmentCrossingWord`,
since non-crossing parameters contribute `1`. -/
theorem segmentCrossingWord_eq_prod_of_crossingTimes (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (T : List ℝ) (hT : T.Pairwise (· < ·))
    (hcover : ∀ t ∈ orderedCrossingTimes e, t ∈ T) :
    segmentCrossingWord ν hdisj e =
      (T.reverse.map (crossingEventWord ν hdisj e)).prod := by
  classical
  let f := crossingEventWord ν hdisj e
  have hone (t : ℝ) (ht : t ∉ orderedCrossingTimes e) : f t = 1 :=
    crossingEventWord_eq_one_of_forall_notMem ν hdisj e t fun j hj =>
      ht ((mem_orderedCrossingTimes e t).mpr ⟨j, hj⟩)
  have hs : (orderedCrossingTimes e).toFinset ⊆ T.toFinset := fun t ht =>
    List.mem_toFinset.mpr (hcover t (List.mem_toFinset.mp ht))
  have hS : (orderedCrossingTimes e).toFinset.sort = orderedCrossingTimes e :=
    (Finset.sortedLT_sort _).pairwise.eq_of_mem_iff (pairwise_orderedCrossingTimes e) (by simp)
  have hTsort : T.toFinset.sort = T :=
    (Finset.sortedLT_sort _).pairwise.eq_of_mem_iff hT (by simp)
  rw [segmentCrossingWord_def]
  simp only [List.map_reverse, List.prod_reverse_noncomm, List.map_map, Function.comp_def]
  exact congrArg Inv.inv (by
    simpa only [hS, hTsort] using Finset.prod_map_sort_subset hs (fun t => (f t)⁻¹)
      (fun t _ ht => by rw [hone t (by simpa only [List.mem_toFinset] using ht), inv_one]))

/-- A segment with no wall crossings has trivial crossing word. -/
theorem segmentCrossingWord_eq_one_of_crossings_eq_empty (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (he : crossings x y = ∅) : segmentCrossingWord ν hdisj e = 1 := by
  have ht : orderedCrossingTimes e = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
      obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes e t).mp ht
      simp [he] at hi
  simp [segmentCrossingWord_def, ht]

@[simp]
theorem segmentCrossingWord_self (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ x) : segmentCrossingWord ν hdisj e = 1 := by
  refine segmentCrossingWord_eq_one_of_crossings_eq_empty ν hdisj e
    (Set.eq_empty_iff_forall_notMem.mpr ?_)
  rintro ⟨i, t⟩ hi
  exact x.notMem i (by simpa using ((mem_crossings x x i t).mp hi).2)

/-- A segment whose crossing set is a singleton `{(i, t)}` has crossing word
`FreeGroup.of i ^ (±1)`. -/
theorem segmentCrossingWord_of_crossings_eq_singleton (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) {i : ι} {t : ℝ} (hcr : crossings x y = {(i, t)}) :
    segmentCrossingWord ν hdisj e =
      FreeGroup.of i ^ (if 0 < ν i (y.val - x.val) then -1 else 1 : ℤ) := by
  have htimes : orderedCrossingTimes e = [t] := by
    refine (pairwise_orderedCrossingTimes e).eq_of_mem_iff (List.pairwise_singleton _ t) fun s => ?_
    simp only [mem_orderedCrossingTimes, hcr, Set.mem_singleton_iff, Prod.mk.injEq,
      List.mem_singleton]
    exact ⟨fun ⟨_, _, hs⟩ => hs, fun hs => ⟨i, rfl, hs⟩⟩
  rw [segmentCrossingWord_def, htimes, List.reverse_singleton, List.map_singleton,
    List.prod_singleton]
  exact crossingEventWord_of_mem_crossings ν hdisj e (hcr ▸ Set.mem_singleton (i, t))

/-- Reversing an admissible segment inverts its crossing word. -/
@[simp]
theorem segmentCrossingWord_reverse (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction) (e : x ⟶ y) :
    segmentCrossingWord ν hdisj (Quiver.reverse e) = (segmentCrossingWord ν hdisj e)⁻¹ := by
  simp only [segmentCrossingWord, orderedCrossingTimes_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map, Function.comp_def,
    crossingEventWord_reverse ν hdisj hν, sub_sub_cancel, List.prod_inv_reverse]

/-- Lifting `segmentCrossingWord` along any coplanar-commuting label assignment `label : ι → G`
recovers `segmentPathProduct`. -/
theorem lift_segmentCrossingWord_eq_segmentPathProduct {G : Type*} [Group G] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (label : ι → G)
    (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (e : x ⟶ y) :
    FreeGroup.lift label (segmentCrossingWord ν hdisj e) = segmentPathProduct ν label hcomm e := by
  simp only [segmentCrossingWord_def, segmentPathProduct_def, map_list_prod, List.map_map,
    Function.comp_def, lift_crossingEventWord_eq_crossingEventProduct ν hdisj label hcomm e]

end IsolatedCrossings

/-! ### Restricting wall families on segments -/

section WallRestriction

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}

/-- Restricting a segment along `WallComplement.restrictPrefunctor W f` maps its crossing word by
`FreeGroup.lift g` for any generator map `g : ι → FreeGroup κ` sending `f j` to `FreeGroup.of j`
and killing indices outside `Set.range f`. -/
theorem segmentCrossingWord_restrictPrefunctor_eq_lift [Finite ι] [Finite κ] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {f : κ → ι}
    {hdisj' : Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ ((W ∘ f) i)) (intrinsicInterior ℝ ((W ∘ f) j))}
    {g : ι → FreeGroup κ}
    (hg_mem : ∀ j, g (f j) = FreeGroup.of j) (hg_out : ∀ i, i ∉ Set.range f → g i = 1)
    {x y : WallComplement W} (e : x ⟶ y)
    (e' : (restrictPrefunctor W f).obj x ⟶ (restrictPrefunctor W f).obj y) :
    segmentCrossingWord (ν ∘ f) hdisj' e' =
      FreeGroup.lift g (segmentCrossingWord ν hdisj e) := by
  have hcover : ∀ t ∈ orderedCrossingTimes e', t ∈ orderedCrossingTimes e := by
    intro t ht
    obtain ⟨j, hj⟩ := (mem_orderedCrossingTimes e' t).mp ht
    exact (mem_orderedCrossingTimes e t).mpr
      ⟨f j, (mem_crossings_restrictPrefunctor W f x y j t).mp hj⟩
  rw [segmentCrossingWord_eq_prod_of_crossingTimes (ν ∘ f) hdisj' e'
    (orderedCrossingTimes e) (pairwise_orderedCrossingTimes e) hcover,
    segmentCrossingWord_def, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun t _ => ?_)
  rw [Function.comp_apply]
  by_cases hcr' : ∃ j, (j, t) ∈ crossings ((restrictPrefunctor W f).obj x)
      ((restrictPrefunctor W f).obj y)
  · obtain ⟨j, hj⟩ := hcr'
    have hjf : (f j, t) ∈ crossings x y := (mem_crossings_restrictPrefunctor W f x y j t).mp hj
    rw [crossingEventWord_of_mem_crossings (ν ∘ f) hdisj' e' hj,
      crossingEventWord_of_mem_crossings ν hdisj e hjf, map_zpow, FreeGroup.lift_apply_of,
      hg_mem j]
    rw [Function.comp_apply, restrictPrefunctor_obj_val W f y, restrictPrefunctor_obj_val W f x]
  · rw [crossingEventWord_eq_one_of_forall_notMem _ hdisj' e' t fun j hj => hcr' ⟨j, hj⟩]
    by_cases hcr : ∃ i, (i, t) ∈ crossings x y
    · obtain ⟨i, hi⟩ := hcr
      have hout : i ∉ Set.range f := fun ⟨j, hj⟩ =>
        hcr' ⟨j, (mem_crossings_restrictPrefunctor W f x y j t).mpr (hj ▸ hi)⟩
      rw [crossingEventWord_of_mem_crossings ν hdisj e hi, map_zpow,
        FreeGroup.lift_apply_of, hg_out i hout, one_zpow]
    · rw [crossingEventWord_eq_one_of_forall_notMem ν hdisj e t fun i hi => hcr ⟨i, hi⟩,
        map_one]

end WallRestriction

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti WallComplement

section CrossingWord

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Every signed crossing event along an admissible polygonal path across interior-disjoint walls
has cardinality `1`. -/
theorem card_eq_one_of_mem_signedCrossingEvents (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) {S : Finset (ι × ℤ)} (hS : S ∈ p.signedCrossingEvents ν) :
    S.card = 1 := by
  induction p with
  | nil => simp [signedCrossingEvents_nil] at hS
  | cons p e ih =>
    rw [signedCrossingEvents_cons] at hS
    rcases List.mem_append.mp hS with hp | he
    · exact ih hp
    · obtain ⟨t, ht, rfl⟩ := (mem_segmentCrossingEvents ν e S).mp he
      exact card_signedCrossingEvent_eq_one ν e hdisj ht

/-- The crossing word of an admissible polygonal path across an interior-disjoint wall family,
lying in `FreeGroup ι` with the first crossing rightmost and signs prescribed by left wall actions.
-/
def crossingWord (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) : FreeGroup ι :=
  MulOpposite.unop (p.weight (fun e => MulOpposite.op (segmentCrossingWord ν hdisj e)))

/-- `crossingWord` is the path weight in the opposite group, so later segments multiply on the
left. -/
theorem crossingWord_eq_unop_weight (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) :
    p.crossingWord ν hdisj =
      MulOpposite.unop (p.weight (fun e => MulOpposite.op (segmentCrossingWord ν hdisj e))) :=
  (rfl)

@[simp]
theorem crossingWord_nil (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j))) :
    (Quiver.Path.nil : AdmissiblePLPath x x).crossingWord ν hdisj = 1 := by
  simp only [crossingWord, weight_nil, MulOpposite.unop_one]

@[simp]
theorem crossingWord_cons (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    (p.cons e).crossingWord ν hdisj = segmentCrossingWord ν hdisj e * p.crossingWord ν hdisj := by
  simp only [crossingWord, weight_cons, MulOpposite.unop_mul, MulOpposite.unop_op]

@[simp]
theorem crossingWord_toPath (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) :
    e.toPath.crossingWord ν hdisj = segmentCrossingWord ν hdisj e := by
  simp [Quiver.Hom.toPath]

/-- Concatenating two admissible polygonal paths multiplies their crossing words in reverse order,
so the later path acts on the left. -/
@[simp]
theorem crossingWord_comp (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    (p.comp q).crossingWord ν hdisj = q.crossingWord ν hdisj * p.crossingWord ν hdisj := by
  simp only [crossingWord, weight_comp, MulOpposite.unop_mul]

/-- Express `crossingWord` directly from the ordered list of signed crossing events. -/
theorem crossingWord_eq_prod_signedCrossingEvents (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) :
    p.crossingWord ν hdisj =
      ((p.signedCrossingEvents ν).reverse.map
        (fun S => (S.toList.map (fun a => FreeGroup.of a.1 ^ a.2)).prod)).prod := by
  classical
  have he {u v : WallComplement W} (e : u ⟶ v) :
      segmentCrossingWord ν hdisj e =
        ((segmentCrossingEvents ν e).reverse.map
          (fun S => (S.toList.map (fun a => FreeGroup.of a.1 ^ a.2)).prod)).prod := by
    simp only [segmentCrossingWord_def, segmentCrossingEvents_def, List.map_reverse, List.map_map]
    congr 2
    exact List.map_congr_left fun t _ =>
      crossingEventWord_eq_prod ν hdisj e t _ (Finset.nodup_toList _) fun _ => Finset.mem_toList
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [crossingWord_cons, signedCrossingEvents_cons, List.reverse_append,
      List.map_append, List.prod_append, ih, he]

/-- Two admissible polygonal paths (possibly in different ambient spaces) with the same ordered
signed crossing events have equal crossing words. -/
theorem crossingWord_eq_of_signedCrossingEvents_eq
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {W' : ι → Set U}
    {x' y' : WallComplement W'} (ν : ι → V →ₗ[ℝ] ℝ) (ν' : ι → U →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hdisj' : Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ (W' i)) (intrinsicInterior ℝ (W' j)))
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.signedCrossingEvents ν = q.signedCrossingEvents ν') :
    p.crossingWord ν hdisj = q.crossingWord ν' hdisj' := by
  rw [crossingWord_eq_prod_signedCrossingEvents, crossingWord_eq_prod_signedCrossingEvents, hpq]

/-- Positive rescaling of coorientations leaves `crossingWord` unchanged. -/
@[simp]
theorem crossingWord_smul (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (p : AdmissiblePLPath x y) :
    p.crossingWord (fun i => r i • ν i) hdisj = p.crossingWord ν hdisj :=
  crossingWord_eq_of_signedCrossingEvents_eq _ _ hdisj hdisj p p
    (signedCrossingEvents_smul ν r hr p)

/-- Subdividing an admissible polygonal path by allowed interior vertices leaves its crossing word
unchanged. -/
theorem IsSubdivision.crossingWord_eq (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {p q : AdmissiblePLPath x y} (h : IsSubdivision p q) :
    p.crossingWord ν hdisj = q.crossingWord ν hdisj :=
  crossingWord_eq_of_signedCrossingEvents_eq ν ν hdisj hdisj p q (h.signedCrossingEvents_eq ν)

/-- Reversing an admissible polygonal path inverts its crossing word. -/
@[simp]
theorem crossingWord_reverse (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction) (p : AdmissiblePLPath x y) :
    p.reverse.crossingWord ν hdisj = (p.crossingWord ν hdisj)⁻¹ := by
  induction p with
  | nil => simp [Quiver.Path.reverse]
  | cons p e ih =>
    simp [Quiver.Path.reverse, ih, segmentCrossingWord_reverse ν hdisj hν, mul_inv_rev]

/-- Lifting `p.crossingWord` along any coplanar-commuting label assignment `label : ι → G` recovers
`p.wallPathProduct`. -/
theorem lift_crossingWord_eq_wallPathProduct {G : Type*} [Group G] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (label : ι → G)
    (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (p : AdmissiblePLPath x y) :
    FreeGroup.lift label (p.crossingWord ν hdisj) = p.wallPathProduct ν label hcomm := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp [ih, lift_segmentCrossingWord_eq_segmentPathProduct ν hdisj label hcomm e]

end CrossingWord

/-! ### Polygonal wall restriction and reindexed affine transport -/

section WallRestriction

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y : WallComplement W}

/-- Restricting a polygonal path along `WallComplement.restrictPrefunctor W f` maps `crossingWord`
by any `FreeGroup.lift g` sending `f j` to `FreeGroup.of j` and killing indices outside
`Set.range f`. -/
theorem crossingWord_restrictPrefunctor_eq_lift [Finite ι] [Finite κ] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {f : κ → ι}
    {hdisj' : Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ ((W ∘ f) i)) (intrinsicInterior ℝ ((W ∘ f) j))}
    {g : ι → FreeGroup κ}
    (hg_mem : ∀ j, g (f j) = FreeGroup.of j) (hg_out : ∀ i, i ∉ Set.range f → g i = 1)
    (p : AdmissiblePLPath x y) :
    ((WallComplement.restrictPrefunctor W f).mapPath p).crossingWord (ν ∘ f) hdisj' =
      FreeGroup.lift g (p.crossingWord ν hdisj) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, crossingWord_cons, map_mul, ih]
    exact congrArg (· * _) (segmentCrossingWord_restrictPrefunctor_eq_lift ν hdisj hg_mem hg_out
      e ((WallComplement.restrictPrefunctor W f).map e))

/-- Restricting to an injectively indexed subfamily of walls along
`WallComplement.restrictPrefunctor W f` maps `crossingWord` by
`FreeGroup.lift (Function.extend f FreeGroup.of 1)`, killing deleted walls. -/
@[simp]
theorem crossingWord_restrictPrefunctor [Finite ι] [Finite κ] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {f : κ → ι} (hf : Function.Injective f)
    {hdisj' : Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ ((W ∘ f) i)) (intrinsicInterior ℝ ((W ∘ f) j))}
    (p : AdmissiblePLPath x y) :
    ((WallComplement.restrictPrefunctor W f).mapPath p).crossingWord (ν ∘ f) hdisj' =
      FreeGroup.lift (Function.extend f FreeGroup.of 1) (p.crossingWord ν hdisj) :=
  crossingWord_restrictPrefunctor_eq_lift ν hdisj (hf.extend_apply _ _)
    (fun i hi => Function.extend_apply' _ _ i (by simpa using hi)) p

end WallRestriction

section AffineTransport

variable {V U ι ι' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V} {W' : ι' → Set U} {x y : WallComplement W}

/-- Continuous affine coordinate transport preserves `crossingWord` (for the image family with the
same index type `ι`) under pushed-forward coorientations. -/
@[simp]
theorem crossingWord_affineMap [Finite ι] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U)
    {hdisj' : Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ (e '' W i)) (intrinsicInterior ℝ (e '' W j))} :
    (p.affineMap e).crossingWord
        (fun i => (ν i).comp e.toAffineEquiv.linear.symm.toLinearMap) hdisj' =
      p.crossingWord ν hdisj :=
  crossingWord_eq_of_signedCrossingEvents_eq _ _ hdisj' hdisj (p.affineMap e) p
    (signedCrossingEvents_affineMap ν p e)

/-- Transporting an admissible polygonal path along `e : V ≃ᴬ[ℝ] U` and a wall bijection
`r : ι ≃ ι'` maps its crossing word by `FreeGroup.map r`. -/
@[simp]
theorem crossingWord_affineMapReindex [Finite ι] [Finite ι'] (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι') (hW : ∀ i, W' (r i) = e '' W i)
    {hdisj' : Pairwise fun i' j' =>
      Disjoint (intrinsicInterior ℝ (W' i')) (intrinsicInterior ℝ (W' j'))}
    (p : AdmissiblePLPath x y) :
    (p.affineMapReindex e r hW).crossingWord
        (fun i' => (ν (r.symm i')).comp e.toAffineEquiv.linear.symm.toLinearMap) hdisj' =
      FreeGroup.map r (p.crossingWord ν hdisj) := by
  obtain rfl := (r.eq_comp_symm W' _).mpr (funext hW)
  have hν :
      (fun i' => (ν (r.symm i')).comp e.toAffineEquiv.linear.symm.toLinearMap) =
        (fun i => (ν i).comp e.toAffineEquiv.linear.symm.toLinearMap) ∘ r.symm := rfl
  rw [affineMapReindex_eq_restrictPrefunctor_mapPath_affineMap, hν,
    crossingWord_restrictPrefunctor_eq_lift _ (e.pairwise_disjoint_intrinsicInterior_image hdisj)
      (g := FreeGroup.of ∘ r) (fun i' => by simp)
      (fun i hi => (hi ⟨r i, r.symm_apply_apply i⟩).elim) (p.affineMap e),
    ← FreeGroup.map_eq_lift,
    crossingWord_affineMap ν hdisj p e
      (hdisj' := e.pairwise_disjoint_intrinsicInterior_image hdisj)]

end AffineTransport

end Quiver.Path
