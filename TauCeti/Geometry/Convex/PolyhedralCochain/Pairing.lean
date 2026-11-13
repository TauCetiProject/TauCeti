/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralCochain.Basic
public import TauCeti.LinearAlgebra.AffineSpace.Transverse
public import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.LinearAlgebra.AffineSpace.Simplex.Conormal
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Intersection pairing with affine test simplices

An affine test simplex of dimension `k` is given by its vertices `v : Fin (k + 1) → V`. It is
the image `convexHull ℝ (range v)` of the standard simplex under the affine map sending the
standard vertices to `v`, and its linear part sends the positively oriented standard frame to the
edge frame `(v 1 - v 0, …, v k - v 0)`. The test is weakly transverse
(`OrientedCell.IsWeaklyTransverse`) to a codimension-`k` cell `σ` when its image avoids the relative
boundary of `σ` and, if it meets `σ`, its edge frame maps to a basis of the normal quotient by the
direction of `σ`. In that case the test
meets the affine span of `σ` in a single point in the relative interior of `σ`. Disjoint tests
may be degenerate.

The local intersection index is the sign of the conormal orientation of `σ` on the edge frame
when the test meets `σ`, and zero otherwise. For a weakly transverse test, it vanishes
exactly when the test misses `σ`. Extending linearly gives the intersection pairing with finite
formal sums of oriented cells, natural in the coefficients.

The cochain relations preserve the pairing whenever the test is weakly transverse to the cells
of both representatives (`PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq`).
The intersection point may lie on a parameter face of the test simplex.

`OrientedCell.IsTransverse` also requires every proper parameter face to avoid the cell. This
condition prevents counting the same intersection in multiple pieces of a test subdivision.

Adapted from `Mei/Geometry/Convex/PolyhedralCochain/Pairing.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commits `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` and
`20afa0bb23652286da5d0967710a055aca2736e1` (Apache 2.0).
-/

public section

open Set Topology

noncomputable section

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

namespace OrientedCell

/-- A test of dimension `k` is weakly transverse to a codimension-`k` cell if
it avoids the cell's relative frontier and, whenever it meets the cell, its
edge vectors project to a basis of the normal quotient. The test may meet the cell
on a proper parameter face. -/
structure IsWeaklyTransverse (σ : OrientedCell h k) (v : Fin (k + 1) → V) : Prop where
  /-- The test avoids the relative boundary of the cell. -/
  disjoint_intrinsicFrontier :
    Disjoint (convexHull ℝ (range v)) (intrinsicFrontier ℝ σ.carrier)
  /-- Where the test meets the cell, its edge frame is a basis of the normal quotient. -/
  linearIndependent : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty →
    LinearIndependent ℝ
      ((affineSpan ℝ σ.carrier).direction.mkQ ∘ fun j : Fin k => v j.succ - v 0)

variable {σ : OrientedCell h k} {v : Fin (k + 1) → V}

/-- A test missing a cell is weakly transverse, including when the test is degenerate. -/
theorem isWeaklyTransverse_of_disjoint (σ : OrientedCell h k) {v : Fin (k + 1) → V}
    (hv : Disjoint (convexHull ℝ (range v)) σ.carrier) : σ.IsWeaklyTransverse v :=
  ⟨hv.mono_right (intrinsicFrontier_subset σ.rational.isClosed),
    fun ⟨_, hx, hy⟩ => (Set.disjoint_left.mp hv hx hy).elim⟩

/-- A test whose vector span complements the cell direction is affinely independent. -/
theorem affineIndependent_of_isCompl (σ : OrientedCell h k) {v : Fin (k + 1) → V}
    (hc : IsCompl (affineSpan ℝ σ.carrier).direction (vectorSpan ℝ (range v))) :
    AffineIndependent ℝ v := by
  have := h.finiteDimensional
  exact (affineIndependent_iff_finrank_vectorSpan_eq ℝ v (Fintype.card_fin (k + 1))).mpr
    (((affineSpan ℝ σ.carrier).direction.quotientEquivOfIsCompl _ hc).symm.finrank_eq.trans
      σ.finrank_quotient_direction)

/-- A test whose vector span complements the cell direction is weakly transverse if it avoids
the cell's relative frontier. -/
theorem isWeaklyTransverse_of_isCompl (σ : OrientedCell h k) {v : Fin (k + 1) → V}
    (hc : IsCompl (affineSpan ℝ σ.carrier).direction (vectorSpan ℝ (range v)))
    (hf : Disjoint (convexHull ℝ (range v)) (intrinsicFrontier ℝ σ.carrier)) :
    σ.IsWeaklyTransverse v := by
  have := h.finiteDimensional
  let s : Affine.Simplex ℝ V k := ⟨v, σ.affineIndependent_of_isCompl hc⟩
  refine ⟨hf, fun _ => ?_⟩
  apply (σ.isConormal.evalSign_ne_zero_iff
    (σ.finrank_quotient_direction.trans (Fintype.card_fin k).symm) _).mp
  have he := Module.Ray.evalSign_rayOfNeZero σ.orientation.someVector_ne_zero
    (fun j : Fin k => v j.succ - v 0)
  rw [Module.Ray.someVector_ray] at he
  rw [he, sign_ne_zero]
  exact s.conormal_apply_ne_zero hc
    (Module.Ray.isConormal_iff.mp σ.isConormal) σ.orientation.someVector_ne_zero

/-- The vector span of a weakly transverse test meeting a cell complements the cell's
direction. -/
theorem IsWeaklyTransverse.isCompl {σ : OrientedCell h k} {v : Fin (k + 1) → V}
    (hv : σ.IsWeaklyTransverse v)
    (hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty) :
    IsCompl (affineSpan ℝ σ.carrier).direction (vectorSpan ℝ (range v)) := by
  have := h.finiteDimensional
  let W := (affineSpan ℝ σ.carrier).direction
  let e : Fin k → V := fun j => v j.succ - v 0
  have hlin : LinearIndependent ℝ (W.mkQ ∘ e) := hv.linearIndependent hmeet
  have hspan : Submodule.span ℝ (range (W.mkQ ∘ e)) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank'
      ((Fintype.card_fin k).trans σ.finrank_quotient_direction.symm)
  have hcompl : IsCompl W (Submodule.span ℝ (range e)) := by
    have hd : Disjoint (Submodule.span ℝ (range e)) W := by
      simpa only [Submodule.ker_mkQ] using Submodule.range_ker_disjoint hlin
    refine ⟨hd.symm, codisjoint_iff.mpr ?_⟩
    rw [← Submodule.map_mkQ_eq_top W (Submodule.span ℝ (range e)),
      LinearMap.map_span, ← Set.range_comp]
    exact hspan
  have hvec : Submodule.span ℝ (range e) = vectorSpan ℝ (range v) := by
    rw [vectorSpan_range_eq_span_range_vsub_right_ne ℝ v 0]
    congr 1
    simpa only [e, Function.comp_def, finSuccAboveEquiv_apply,
      Fin.succAbove_zero, vsub_eq_sub] using
      (finSuccAboveEquiv 0).surjective.range_comp
        (fun j : {j : Fin (k + 1) // j ≠ 0} => v j - v 0)
  rwa [hvec] at hcompl

/-- A weakly transverse test meeting a cell is affinely independent. -/
theorem IsWeaklyTransverse.affineIndependent {σ : OrientedCell h k} {v : Fin (k + 1) → V}
    (hv : σ.IsWeaklyTransverse v)
    (hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty) :
    AffineIndependent ℝ v :=
  σ.affineIndependent_of_isCompl (hv.isCompl hmeet)

/-- A test is weakly transverse exactly when it avoids the cell's relative frontier and its
vector span complements the cell's direction whenever the test meets the cell. -/
theorem isWeaklyTransverse_iff_isCompl (σ : OrientedCell h k) (v : Fin (k + 1) → V) :
    σ.IsWeaklyTransverse v ↔
      Disjoint (convexHull ℝ (range v)) (intrinsicFrontier ℝ σ.carrier) ∧
        ((convexHull ℝ (range v) ∩ σ.carrier).Nonempty →
          IsCompl (affineSpan ℝ σ.carrier).direction (vectorSpan ℝ (range v))) := by
  refine ⟨fun hv => ⟨hv.disjoint_intrinsicFrontier, hv.isCompl⟩, fun ⟨hf, hc⟩ => ?_⟩
  by_cases hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty
  · exact σ.isWeaklyTransverse_of_isCompl (hc hmeet) hf
  · exact σ.isWeaklyTransverse_of_disjoint
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))

/-- Weak transversality is preserved by re-indexing the vertices. -/
theorem IsWeaklyTransverse.comp_equiv (hv : σ.IsWeaklyTransverse v)
    (e : Fin (k + 1) ≃ Fin (k + 1)) : σ.IsWeaklyTransverse (v ∘ e) := by
  rwa [σ.isWeaklyTransverse_iff_isCompl (v ∘ e), e.surjective.range_comp v,
    ← σ.isWeaklyTransverse_iff_isCompl v]

/-- Weak transversality is independent of the vertex ordering. -/
@[simp]
theorem isWeaklyTransverse_comp_equiv_iff (σ : OrientedCell h k) (v : Fin (k + 1) → V)
    (e : Fin (k + 1) ≃ Fin (k + 1)) :
    σ.IsWeaklyTransverse (v ∘ e) ↔ σ.IsWeaklyTransverse v := by
  rw [σ.isWeaklyTransverse_iff_isCompl (v ∘ e), e.surjective.range_comp v,
    σ.isWeaklyTransverse_iff_isCompl v]

/-- Reversing a cell's orientation preserves weak transversality. -/
@[simp]
theorem isWeaklyTransverse_reverse_iff (σ : OrientedCell h k) (v : Fin (k + 1) → V) :
    σ.reverse.IsWeaklyTransverse v ↔ σ.IsWeaklyTransverse v := by
  constructor <;> intro hv <;>
    refine ⟨by simpa only [reverse_carrier] using hv.disjoint_intrinsicFrontier, ?_⟩
  · have hlin := hv.linearIndependent
    rw [reverse_carrier] at hlin
    exact hlin
  · rw [reverse_carrier]
    exact hv.linearIndependent

/-- A point test is weakly transverse exactly when it avoids the cell's relative frontier. -/
@[simp]
theorem isWeaklyTransverse_singleton_iff (σ : OrientedCell h 0) (x : V) :
    σ.IsWeaklyTransverse ![x] ↔ x ∉ intrinsicFrontier ℝ σ.carrier := by
  constructor
  · intro hv
    simpa [Matrix.range_cons, Set.disjoint_singleton_left] using
      hv.disjoint_intrinsicFrontier
  · intro hx
    refine ⟨?_, fun _ => linearIndependent_empty_type⟩
    simpa [Matrix.range_cons, Set.disjoint_singleton_left] using hx

/-- Weak transversality of a segment means avoiding the cell's relative frontier and having
its edge vector outside the cell's direction when the segment meets the cell. -/
theorem isWeaklyTransverse_pair_iff (σ : OrientedCell h 1) (a b : V) :
    σ.IsWeaklyTransverse ![a, b] ↔
      Disjoint (segment ℝ a b) (intrinsicFrontier ℝ σ.carrier) ∧
        ((segment ℝ a b ∩ σ.carrier).Nonempty →
          b - a ∉ (affineSpan ℝ σ.carrier).direction) := by
  rw [← (affineSpan ℝ σ.carrier).direction.ker_mkQ, LinearMap.mem_ker]
  have hhull : convexHull ℝ (range ![a, b]) = segment ℝ a b := by
    rw [Matrix.range_cons_cons_empty, convexHull_pair]
  constructor
  · intro hv
    refine ⟨?_, fun hmeet => ?_⟩
    · rw [← hhull]
      exact hv.disjoint_intrinsicFrontier
    · have hi := hv.linearIndependent (by rwa [hhull])
      rw [linearIndependent_unique_iff] at hi
      simpa only [Function.comp_apply, Fin.default_eq_zero, Fin.succ_zero_eq_one,
        Matrix.cons_val_one, Matrix.cons_val_zero] using hi
  · rintro ⟨hf, hi⟩
    refine ⟨?_, fun hmeet => ?_⟩
    · rw [hhull]
      exact hf
    · rw [linearIndependent_unique_iff]
      simp only [Function.comp_apply, Fin.default_eq_zero, Fin.succ_zero_eq_one,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      apply hi
      rwa [← hhull]

/-- Reversing a segment preserves weak transversality. -/
theorem isWeaklyTransverse_pair_swap_iff (σ : OrientedCell h 1) (a b : V) :
    σ.IsWeaklyTransverse ![b, a] ↔ σ.IsWeaklyTransverse ![a, b] := by
  simpa only [Matrix.cons_cons_comp_swap_zero_one] using
    σ.isWeaklyTransverse_comp_equiv_iff ![a, b] (Equiv.swap 0 1)

/-- An affinely independent subsimplex of a weakly transverse test is weakly transverse.
Affine independence is needed only when the subsimplex meets the cell. -/
theorem IsWeaklyTransverse.of_subset_convexHull {σ : OrientedCell h k}
    {v w : Fin (k + 1) → V} (hv : σ.IsWeaklyTransverse v)
    (hw : convexHull ℝ (range w) ⊆ convexHull ℝ (range v))
    (hi : (convexHull ℝ (range w) ∩ σ.carrier).Nonempty → AffineIndependent ℝ w) :
    σ.IsWeaklyTransverse w := by
  refine (σ.isWeaklyTransverse_iff_isCompl w).mpr
    ⟨hv.disjoint_intrinsicFrontier.mono_left hw, fun hm => ?_⟩
  have hc := hv.isCompl (hm.mono (inter_subset_inter_left _ hw))
  have hle : vectorSpan ℝ (range w) ≤ vectorSpan ℝ (range v) := by
    have hle' := AffineSubspace.direction_le (affineSpan_mono ℝ hw)
    rw [affineSpan_convexHull, direction_affineSpan,
      affineSpan_convexHull, direction_affineSpan] at hle'
    exact hle'
  have hdim : Module.finrank ℝ (vectorSpan ℝ (range w)) =
      Module.finrank ℝ (vectorSpan ℝ (range v)) := by
    rw [(hi hm).finrank_vectorSpan (Fintype.card_fin (k + 1)),
      (σ.affineIndependent_of_isCompl hc).finrank_vectorSpan (Fintype.card_fin (k + 1))]
  have heq := Submodule.eq_of_le_of_finrank_le hle hdim.ge
  rw [heq]
  exact hc

/-- A subsegment of a weakly transverse segment is weakly transverse whenever it is
nondegenerate where it meets the cell. -/
theorem IsWeaklyTransverse.of_mem_segment {σ : OrientedCell h 1} {x y a b : V}
    (hv : σ.IsWeaklyTransverse ![x, y]) (ha : a ∈ segment ℝ x y)
    (hb : b ∈ segment ℝ x y) (hab : (segment ℝ a b ∩ σ.carrier).Nonempty → a ≠ b) :
    σ.IsWeaklyTransverse ![a, b] := by
  apply hv.of_subset_convexHull
  · rw [Matrix.range_cons_cons_empty, Matrix.range_cons_cons_empty,
      convexHull_pair, convexHull_pair]
    exact (convex_segment x y).segment_subset ha hb
  · exact fun hm => affineIndependent_of_ne ℝ (hab (by rwa [← convexHull_pair,
      ← Matrix.range_cons_cons_empty]))

/-- Restricting a weakly transverse segment to a nontrivial parameter interval preserves
weak transversality, including when a new endpoint lies on the cell. The parameters
may occur in either order. -/
theorem IsWeaklyTransverse.subsegment {σ : OrientedCell h 1} {x y a b : V}
    (hv : σ.IsWeaklyTransverse ![x, y]) {s u : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (hsu : s ≠ u)
    (ha : a = AffineMap.lineMap x y s) (hb : b = AffineMap.lineMap x y u) :
    σ.IsWeaklyTransverse ![a, b] := by
  subst ha hb
  rcases eq_or_ne x y with rfl | hxy
  · rwa [AffineMap.lineMap_same_apply, AffineMap.lineMap_same_apply]
  · exact hv.of_mem_segment (lineMap_mem_segment ℝ x y hs) (lineMap_mem_segment ℝ x y hu)
      fun _ => (AffineMap.lineMap_injective ℝ hxy).ne hsu

/-- A weakly transverse test whose proper parameter faces all avoid the cell. -/
structure IsTransverse (σ : OrientedCell h k) (v : Fin (k + 1) → V) : Prop
    extends IsWeaklyTransverse σ v where
  /-- Every proper parameter face avoids the support. -/
  disjoint_faces : ∀ j : Fin (k + 1),
    Disjoint (convexHull ℝ (range (v ∘ j.succAbove))) σ.carrier

/-- A test missing a cell is transverse, including when the test is degenerate. -/
theorem isTransverse_of_disjoint (σ : OrientedCell h k) {v : Fin (k + 1) → V}
    (hv : Disjoint (convexHull ℝ (range v)) σ.carrier) : σ.IsTransverse v :=
  ⟨σ.isWeaklyTransverse_of_disjoint hv,
    fun _ => hv.mono_left (convexHull_mono (range_comp_subset_range _ _))⟩

/-- A test whose vector span complements the cell direction is transverse when it avoids the
cell's relative frontier and its proper parameter faces avoid the cell. -/
theorem isTransverse_of_isCompl (σ : OrientedCell h k) {v : Fin (k + 1) → V}
    (hc : IsCompl (affineSpan ℝ σ.carrier).direction (vectorSpan ℝ (range v)))
    (hf : Disjoint (convexHull ℝ (range v)) (intrinsicFrontier ℝ σ.carrier))
    (hb : ∀ j : Fin (k + 1),
      Disjoint (convexHull ℝ (range (v ∘ j.succAbove))) σ.carrier) :
    σ.IsTransverse v :=
  ⟨σ.isWeaklyTransverse_of_isCompl hc hf, hb⟩

/-- A test is transverse exactly when it avoids the cell's relative frontier, its vector span
complements the cell's direction whenever it meets the cell, and its proper faces avoid the cell. -/
theorem isTransverse_iff_isCompl (σ : OrientedCell h k) (v : Fin (k + 1) → V) :
    σ.IsTransverse v ↔
      Disjoint (convexHull ℝ (range v)) (intrinsicFrontier ℝ σ.carrier) ∧
      ((convexHull ℝ (range v) ∩ σ.carrier).Nonempty →
        IsCompl (affineSpan ℝ σ.carrier).direction (vectorSpan ℝ (range v))) ∧
      ∀ j : Fin (k + 1), Disjoint (convexHull ℝ (range (v ∘ j.succAbove))) σ.carrier := by
  constructor
  · intro hv
    have hw := (σ.isWeaklyTransverse_iff_isCompl v).mp hv.toIsWeaklyTransverse
    exact ⟨hw.1, hw.2, hv.disjoint_faces⟩
  · rintro ⟨hf, hc, hb⟩
    exact ⟨(σ.isWeaklyTransverse_iff_isCompl v).mpr ⟨hf, hc⟩, hb⟩

/-- Every vertex of a positive-dimensional transverse test avoids the cell. -/
theorem IsTransverse.notMem_carrier [NeZero k] {σ : OrientedCell h k} {v : Fin (k + 1) → V}
    (hv : σ.IsTransverse v) (j : Fin (k + 1)) : v j ∉ σ.carrier := by
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := j) (y := j.succAbove 0)
    (Fin.succAbove_ne j 0).symm
  apply (hv.disjoint_faces (j.succAbove 0)).notMem_of_mem_left
  apply subset_convexHull ℝ _
  exact ⟨l, by simpa only [Function.comp_apply] using congrArg v hl⟩

/-- Transversality is preserved by re-indexing the vertices. -/
theorem IsTransverse.comp_equiv (hv : σ.IsTransverse v)
    (e : Fin (k + 1) ≃ Fin (k + 1)) : σ.IsTransverse (v ∘ e) := by
  refine ⟨hv.toIsWeaklyTransverse.comp_equiv e, fun j => ?_⟩
  rw [Set.range_comp, Set.image_comp, Fin.range_succAbove, e.image_compl, Set.image_singleton,
    ← Fin.range_succAbove, ← Set.range_comp]
  exact hv.disjoint_faces (e j)

/-- Transversality is independent of the vertex ordering. -/
@[simp]
theorem isTransverse_comp_equiv_iff (σ : OrientedCell h k) (v : Fin (k + 1) → V)
    (e : Fin (k + 1) ≃ Fin (k + 1)) :
    σ.IsTransverse (v ∘ e) ↔ σ.IsTransverse v := by
  refine ⟨fun hv => ?_, fun hv => hv.comp_equiv e⟩
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using
    hv.comp_equiv e.symm

/-- A point test is transverse exactly when it avoids the cell's relative frontier. -/
@[simp]
theorem isTransverse_singleton_iff (σ : OrientedCell h 0) (x : V) :
    σ.IsTransverse ![x] ↔ x ∉ intrinsicFrontier ℝ σ.carrier := by
  rw [← isWeaklyTransverse_singleton_iff]
  refine ⟨fun hv => hv.toIsWeaklyTransverse, fun hv => ⟨hv, fun j => ?_⟩⟩
  simp

/-- A segment is transverse exactly when it is weakly transverse and both endpoints avoid
the cell. -/
theorem isTransverse_pair_iff (σ : OrientedCell h 1) (a b : V) :
    σ.IsTransverse ![a, b] ↔
      σ.IsWeaklyTransverse ![a, b] ∧ a ∉ σ.carrier ∧ b ∉ σ.carrier := by
  constructor
  · intro hv
    refine ⟨hv.toIsWeaklyTransverse, ?_, ?_⟩
    · simpa using hv.notMem_carrier 0
    · simpa using hv.notMem_carrier 1
  · rintro ⟨hv, ha, hb⟩
    refine ⟨hv, fun j => ?_⟩
    rw [Set.range_unique, convexHull_singleton, Set.disjoint_singleton_left]
    fin_cases j
    · simpa using hb
    · simpa using ha

/-- Reversing a segment preserves transversality. -/
theorem isTransverse_pair_swap_iff (σ : OrientedCell h 1) (a b : V) :
    σ.IsTransverse ![b, a] ↔ σ.IsTransverse ![a, b] := by
  simpa only [Matrix.cons_cons_comp_swap_zero_one] using
    σ.isTransverse_comp_equiv_iff ![a, b] (Equiv.swap 0 1)

/-- Reversing a cell's orientation preserves transversality of an affine test simplex. -/
@[simp]
theorem isTransverse_reverse_iff (σ : OrientedCell h k) (v : Fin (k + 1) → V) :
    σ.reverse.IsTransverse v ↔ σ.IsTransverse v := by
  constructor
  · intro hv
    exact ⟨(σ.isWeaklyTransverse_reverse_iff v).mp hv.toIsWeaklyTransverse,
      by simpa only [reverse_carrier] using hv.disjoint_faces⟩
  · intro hv
    exact ⟨(σ.isWeaklyTransverse_reverse_iff v).mpr hv.toIsWeaklyTransverse,
      by simpa only [reverse_carrier] using hv.disjoint_faces⟩

/-- An affinely independent subtest of a weakly transverse test is transverse when its proper
parameter faces avoid the cell. -/
theorem IsWeaklyTransverse.isTransverse_of_subset_convexHull {σ : OrientedCell h k}
    {v w : Fin (k + 1) → V} (hv : σ.IsWeaklyTransverse v)
    (hw : convexHull ℝ (range w) ⊆ convexHull ℝ (range v))
    (hi : (convexHull ℝ (range w) ∩ σ.carrier).Nonempty → AffineIndependent ℝ w)
    (hb : ∀ j : Fin (k + 1), Disjoint (convexHull ℝ (range (w ∘ j.succAbove))) σ.carrier) :
    σ.IsTransverse w :=
  ⟨hv.of_subset_convexHull hw hi, hb⟩

/-- Restricting a weakly transverse segment to a segment whose endpoints avoid the cell
gives a transverse segment. The new segment may be stationary. -/
theorem IsWeaklyTransverse.isTransverse_of_mem_segment {σ : OrientedCell h 1} {x y a b : V}
    (hv : σ.IsWeaklyTransverse ![x, y]) (ha : a ∈ segment ℝ x y) (hb : b ∈ segment ℝ x y)
    (haσ : a ∉ σ.carrier) (hbσ : b ∉ σ.carrier) :
    σ.IsTransverse ![a, b] := by
  refine (σ.isTransverse_pair_iff a b).mpr ⟨hv.of_mem_segment ha hb ?_, haσ, hbσ⟩
  rintro ⟨z, hz, hzσ⟩ rfl
  simp only [segment_same, mem_singleton_iff] at hz
  subst z
  exact haσ hzσ

/-- A weakly transverse test meets the affine span in at most one point if it meets
the cell. -/
theorem IsWeaklyTransverse.subsingleton_convexHull_inter_affineSpan
    (hv : σ.IsWeaklyTransverse v)
    (hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty) :
    (convexHull ℝ (range v) ∩ affineSpan ℝ σ.carrier).Subsingleton :=
  ((affineSpan ℝ σ.carrier).subsingleton_affineSpan_range_inter
    (hv.linearIndependent hmeet)).anti
    (inter_subset_inter_left _ (convexHull_subset_affineSpan _))

/-- A weakly transverse test meets the cell only at relative interior points. -/
theorem IsWeaklyTransverse.mem_intrinsicInterior (hv : σ.IsWeaklyTransverse v) {x : V}
    (hxv : x ∈ convexHull ℝ (range v)) (hxσ : x ∈ σ.carrier) :
    x ∈ intrinsicInterior ℝ σ.carrier := by
  rw [← intrinsicClosure_sdiff_intrinsicFrontier]
  exact ⟨subset_intrinsicClosure hxσ, hv.disjoint_intrinsicFrontier.notMem_of_mem_left hxv⟩

open Classical in
/-- The local intersection index of the affine test simplex with vertices `v` at the cell `σ`:
the sign of the conormal orientation of `σ` on the edge frame `(v 1 - v 0, …, v k - v 0)` if the
test meets `σ`, and zero otherwise. -/
def intersectionIndex (σ : OrientedCell h k) (v : Fin (k + 1) → V) : ℤ :=
  if (convexHull ℝ (range v) ∩ σ.carrier).Nonempty then
    σ.orientation.evalSign (fun j : Fin k => v j.succ - v 0)
  else 0

/-- A test meeting a cell has the orientation sign on its edge frame as intersection index. -/
theorem intersectionIndex_of_nonempty
    (hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty) :
    σ.intersectionIndex v = σ.orientation.evalSign (fun j : Fin k => v j.succ - v 0) := by
  rw [intersectionIndex, ite_eq_left hmeet]

/-- A test disjoint from a cell has intersection index zero. -/
theorem intersectionIndex_of_disjoint (hdisj : Disjoint (convexHull ℝ (range v)) σ.carrier) :
    σ.intersectionIndex v = 0 := by
  rw [intersectionIndex, ite_eq_right (not_nonempty_iff_eq_empty.mpr hdisj.inter_eq)]

open Classical in
/-- A point test on a full-dimensional cell reads its orientation sign when
the point belongs to the cell, and is zero otherwise. -/
@[simp]
theorem intersectionIndex_singleton (σ : OrientedCell h 0) (x : V) :
    σ.intersectionIndex ![x] =
      if x ∈ σ.carrier then (σ.orientation.evalSign ![] : ℤ) else 0 := by
  have he : (fun j : Fin 0 => (![x] : Fin 1 → V) j.succ - ![x] 0) = ![] :=
    funext fun j => Fin.elim0 j
  rw [intersectionIndex, he]
  simp [Matrix.range_cons]

open Classical in
/-- On a one-dimensional test the edge frame is its endpoint difference, and
the test image is the closed segment. -/
theorem intersectionIndex_pair (σ : OrientedCell h 1) (a b : V) :
    σ.intersectionIndex ![a, b] =
      if (segment ℝ a b ∩ σ.carrier).Nonempty then
        (σ.orientation.evalSign (fun _ : Fin 1 => b - a) : ℤ) else 0 := by
  have hframe : (fun j : Fin 1 => ![a, b] j.succ - ![a, b] 0) =
      fun _ : Fin 1 => b - a := by
    ext j
    fin_cases j
    rfl
  rw [intersectionIndex, Matrix.range_cons_cons_empty, convexHull_pair, hframe]

/-- Reversing the endpoints of a segment negates its intersection index,
including for a stationary segment or one disjoint from the cell. -/
theorem intersectionIndex_pair_swap (σ : OrientedCell h 1) (a b : V) :
    σ.intersectionIndex ![b, a] = -σ.intersectionIndex ![a, b] := by
  have hframe : (fun _ : Fin 1 => a - b) =
      fun j => (-1 : ℝ) • (fun _ : Fin 1 => b - a) j := by
    ext j
    simp
  rw [intersectionIndex_pair, intersectionIndex_pair, segment_symm ℝ b a, hframe,
    Module.Ray.evalSign_smul]
  split_ifs <;> simp

/-- Reversing the orientation of a cell negates its intersection index. -/
@[simp]
theorem intersectionIndex_reverse (σ : OrientedCell h k) (v : Fin (k + 1) → V) :
    σ.reverse.intersectionIndex v = -σ.intersectionIndex v := by
  by_cases hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty
  · rw [intersectionIndex_of_nonempty hmeet,
      intersectionIndex_of_nonempty (σ := σ.reverse) (by rwa [reverse_carrier]),
      reverse_orientation, Module.Ray.evalSign_neg, SignType.coe_neg]
  · have hdisj : Disjoint (convexHull ℝ (range v)) σ.carrier :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet)
    rw [intersectionIndex_of_disjoint hdisj,
      intersectionIndex_of_disjoint (σ := σ.reverse) (by rwa [reverse_carrier]), neg_zero]

/-- For a weakly transverse test, the intersection index vanishes exactly when the
test misses the cell. -/
theorem IsWeaklyTransverse.intersectionIndex_eq_zero_iff (hv : σ.IsWeaklyTransverse v) :
    σ.intersectionIndex v = 0 ↔ Disjoint (convexHull ℝ (range v)) σ.carrier := by
  have := h.finiteDimensional
  refine ⟨fun hzero => ?_, intersectionIndex_of_disjoint⟩
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hmeet
  have hne := (σ.isConormal.evalSign_ne_zero_iff
    (σ.finrank_quotient_direction.trans (Fintype.card_fin k).symm) _).mpr
    (hv.linearIndependent hmeet)
  rw [intersectionIndex_of_nonempty hmeet] at hzero
  generalize σ.orientation.evalSign _ = s at hzero hne
  cases s <;> simp_all

/-- A weakly transverse test that meets the cell has intersection index `1` or `-1`. -/
theorem IsWeaklyTransverse.intersectionIndex_eq_one_or_neg_one (hv : σ.IsWeaklyTransverse v)
    (hmeet : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty) :
    σ.intersectionIndex v = 1 ∨ σ.intersectionIndex v = -1 := by
  have hne : σ.intersectionIndex v ≠ 0 := by
    intro hzero
    exact hmeet.not_disjoint (hv.intersectionIndex_eq_zero_iff.mp hzero)
  rw [intersectionIndex_of_nonempty hmeet] at hne ⊢
  cases hs : σ.orientation.evalSign (fun j : Fin k => v j.succ - v 0) <;>
    simp [hs] at hne ⊢

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

/-- The intersection pairing of the affine test simplex with vertices `v` with finite formal sums
of oriented cells: the sum of the coefficients weighted by the local intersection indices. -/
def intersectionPairing (v : Fin (k + 1) → V) : (OrientedCell h k →₀ E) →ₗ[R] E :=
  Finsupp.lsum ℕ fun σ => σ.intersectionIndex v • LinearMap.id

/-- Pairing with one generator multiplies its coefficient by the intersection sign. -/
@[simp]
theorem intersectionPairing_single (v : Fin (k + 1) → V) (σ : OrientedCell h k) (c : E) :
    intersectionPairing (R := R) v (Finsupp.single σ c) = σ.intersectionIndex v • c := by
  simp [intersectionPairing]

/-- The pairing is the finite sum of coefficients weighted by their intersection signs. -/
theorem intersectionPairing_apply (v : Fin (k + 1) → V) (x : OrientedCell h k →₀ E) :
    intersectionPairing (R := R) v x = x.sum fun σ c => σ.intersectionIndex v • c := by
  rw [intersectionPairing, Finsupp.lsum_apply]
  exact Finsupp.sum_congr fun σ _ => by rw [LinearMap.smul_apply, LinearMap.id_apply]

/-- Reversing a segment negates its pairing with a finite wall presentation. -/
theorem intersectionPairing_pair_swap (a b : V) (f : OrientedCell h 1 →₀ E) :
    intersectionPairing (R := R) ![b, a] f = -intersectionPairing (R := R) ![a, b] f := by
  simp only [intersectionPairing_apply, Finsupp.sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [σ.intersectionIndex_pair_swap, neg_smul]

/-- The intersection pairing commutes with linear maps of coefficients. -/
theorem intersectionPairing_comp_mapRange {E' : Type*} [AddCommGroup E'] [Module R E']
    (f : E →ₗ[R] E') (v : Fin (k + 1) → V) :
    intersectionPairing v ∘ₗ Finsupp.mapRange.linearMap f =
      f ∘ₗ intersectionPairing (R := R) (h := h) v := by
  ext σ c
  simp

section relations

/-! ### Local coefficients and the cochain relations -/

open Classical in
/-- The coefficient of a formal sum at the point `q` along the affine subspace `A`, measured
against the frame `f`. -/
private def localCoeff (A : AffineSubspace ℝ V) (f : Fin k → V) (q : V) :
    (OrientedCell h k →₀ E) →ₗ[R] E :=
  Finsupp.lsum ℕ fun σ => if affineSpan ℝ σ.carrier = A ∧ q ∈ σ.carrier then
    (σ.orientation.evalSign f : ℤ) • LinearMap.id else 0

open Classical in
private theorem localCoeff_single (A : AffineSubspace ℝ V) (f : Fin k → V) (q : V)
    (σ : OrientedCell h k) (c : E) :
    localCoeff (R := R) A f q (Finsupp.single σ c) =
      if affineSpan ℝ σ.carrier = A ∧ q ∈ σ.carrier then (σ.orientation.evalSign f : ℤ) • c
      else 0 := by
  rw [localCoeff, Finsupp.lsum_single]
  split_ifs <;> simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]

open Classical in
private theorem localCoeff_apply (A : AffineSubspace ℝ V) (f : Fin k → V) (q : V)
    (x : OrientedCell h k →₀ E) :
    localCoeff (R := R) A f q x = ∑ σ ∈ x.support,
      if affineSpan ℝ σ.carrier = A ∧ q ∈ σ.carrier then (σ.orientation.evalSign f : ℤ) • x σ
      else 0 := by
  rw [localCoeff, Finsupp.lsum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]

/-- The formal sums whose local coefficient along `A` vanishes off a nowhere dense subset
of `A`. -/
private def locallyNull (A : AffineSubspace ℝ V) (f : Fin k → V) :
    Submodule R (OrientedCell h k →₀ E) where
  carrier := {z | ∃ S : Set A, IsNowhereDense S ∧ ∀ q : A, q ∉ S → localCoeff A f q z = 0}
  zero_mem' := ⟨∅, isNowhereDense_empty, fun _ _ => map_zero _⟩
  add_mem' := by
    rintro x y ⟨S, hS, hx⟩ ⟨T, hT, hy⟩
    refine ⟨S ∪ T, hS.union hT, fun q hq => ?_⟩
    rw [map_add, hx q fun h => hq (Or.inl h), hy q fun h => hq (Or.inr h), add_zero]
  smul_mem' := by
    rintro r x ⟨S, hS, hx⟩
    exact ⟨S, hS, fun q hq => by rw [map_smul, hx q hq, smul_zero]⟩

private theorem localCoeff_single_of_mem {A : AffineSubspace ℝ V} {f : Fin k → V} {q : V}
    {τ : OrientedCell h k} (hA : affineSpan ℝ τ.carrier = A) (hq : q ∈ τ.carrier) (c : E) :
    localCoeff (R := R) A f q (Finsupp.single τ c) = (τ.orientation.evalSign f : ℤ) • c := by
  rw [localCoeff_single, ite_eq_left ⟨hA, hq⟩]

private theorem localCoeff_single_of_not {A : AffineSubspace ℝ V} {f : Fin k → V} {q : V}
    {τ : OrientedCell h k} (hτ : ¬(affineSpan ℝ τ.carrier = A ∧ q ∈ τ.carrier)) (c : E) :
    localCoeff (R := R) A f q (Finsupp.single τ c) = 0 := by
  rw [localCoeff_single, ite_eq_right hτ]

/-- Every cochain relation has vanishing local coefficients off a nowhere dense set: a reversal
relation vanishes everywhere, and a subdivision relation vanishes off the relative boundaries of
the pieces. -/
private theorem cochainRelations_le_locallyNull (A : AffineSubspace ℝ V) (f : Fin k → V) :
    cochainRelations R h E k ≤ locallyNull (R := R) A f := by
  refine cochainRelations_le_iff.mpr ⟨fun σ c => ?_, fun σ Q c hQ => ?_⟩
  · refine ⟨∅, isNowhereDense_empty, fun q _ => ?_⟩
    rw [map_add]
    by_cases hc : affineSpan ℝ σ.carrier = A ∧ (q : V) ∈ σ.carrier
    · rw [localCoeff_single_of_mem (by rw [reverse_carrier]; exact hc.1)
          (by rw [reverse_carrier]; exact hc.2),
        localCoeff_single_of_mem hc.1 hc.2, reverse_orientation, Module.Ray.evalSign_neg,
        SignType.coe_neg, neg_smul, neg_add_cancel]
    · rw [localCoeff_single_of_not (by rwa [reverse_carrier]), localCoeff_single_of_not hc,
        add_zero]
  by_cases hσA : affineSpan ℝ σ.carrier = A
  · have hτA {τ : OrientedCell h k} (hτ : τ ∈ Q) : affineSpan ℝ τ.carrier = A :=
      (hQ.affineSpan_eq hτ).trans hσA
    have hS : IsNowhereDense (⋃ τ ∈ Q, ((↑) ⁻¹' intrinsicFrontier ℝ τ.carrier : Set A)) :=
      IsNowhereDense.biUnion fun τ hτ =>
        τ.rational.isClosed.isNowhereDense_preimage_intrinsicFrontier (hτA hτ)
    refine ⟨_, hS, fun q hq => ?_⟩
    simp only [mem_iUnion, mem_preimage, not_exists] at hq
    rw [map_sub, map_sum, sub_eq_zero]
    by_cases hqσ : (q : V) ∈ σ.carrier
    · -- Exactly one piece contains `q`, since `q` is off the relative boundaries of the pieces.
      have hqQ := hqσ
      rw [← hQ.biUnion_carrier, mem_iUnion₂] at hqQ
      obtain ⟨τ₀, hτ₀, hqτ₀⟩ := hqQ
      have hint {τ : OrientedCell h k} (hτ : τ ∈ Q) (hqτ : (q : V) ∈ τ.carrier) :
          (q : V) ∈ intrinsicInterior ℝ τ.carrier := by
        rw [← intrinsicClosure_sdiff_intrinsicFrontier]
        exact ⟨subset_intrinsicClosure hqτ, hq τ hτ⟩
      rw [Finset.sum_eq_single τ₀ (fun τ hτ hne => localCoeff_single_of_not (fun hc =>
          (hQ.pairwiseDisjoint hτ hτ₀ hne).ne_of_mem (hint hτ hc.2) (hint hτ₀ hqτ₀) rfl) c)
          (fun h => (h hτ₀).elim),
        localCoeff_single_of_mem hσA hqσ, localCoeff_single_of_mem (hτA hτ₀) hqτ₀,
        hQ.orientation_eq τ₀ hτ₀]
    · rw [localCoeff_single_of_not (fun hc => hqσ hc.2), eq_comm]
      exact Finset.sum_eq_zero fun τ hτ =>
        localCoeff_single_of_not (fun hc => hqσ (hQ.carrier_subset hτ hc.2)) c
  · refine ⟨∅, isNowhereDense_empty, fun q _ => ?_⟩
    rw [map_sub, map_sum, localCoeff_single_of_not fun hc => hσA hc.1, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun τ hτ =>
      localCoeff_single_of_not (fun hc => hσA ((hQ.affineSpan_eq hτ).symm.trans hc.1)) c

/-- A cochain relation has zero local coefficient at every point `q` of `A` off the relative
boundaries of its cells. -/
private theorem localCoeff_eq_zero {z : OrientedCell h k →₀ E}
    (hz : z ∈ cochainRelations R h E k) (A : AffineSubspace ℝ V) (f : Fin k → V) (q : A)
    (hq : ∀ σ ∈ z.support, (q : V) ∉ intrinsicFrontier ℝ σ.carrier) :
    localCoeff (R := R) A f q z = 0 := by
  classical
  -- The local coefficient is constant near `q` in `A` and vanishes off a nowhere dense subset.
  obtain ⟨S, hS, hzS⟩ := cochainRelations_le_locallyNull A f hz
  have hmem : ∀ᶠ y : A in 𝓝 q, ∀ σ ∈ z.support,
      affineSpan ℝ σ.carrier = A → ((y : V) ∈ σ.carrier ↔ (q : V) ∈ σ.carrier) := by
    rw [Filter.eventually_all_finset]
    intro σ hσ
    by_cases hσA : affineSpan ℝ σ.carrier = A
    · filter_upwards [eventually_mem_iff_of_notMem_intrinsicFrontier hσA
        (hq σ hσ)] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun y hA => absurd hA hσA
  have hev : ∀ᶠ y : A in 𝓝 q, localCoeff (R := R) A f y z = localCoeff (R := R) A f q z := by
    filter_upwards [hmem] with y hy
    rw [localCoeff_apply, localCoeff_apply]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    by_cases hσA : affineSpan ℝ σ.carrier = A
    · rw [hy σ hσ hσA]
    · simp [hσA]
  have hdense : Dense Sᶜ := (interior_eq_empty_iff_dense_compl.mp hS).mono
    (compl_subset_compl.mpr subset_closure)
  obtain ⟨y, hyS, hy⟩ := hdense.inter_nhds_nonempty hev
  rw [← hy, hzS y hyS]

end relations

/-- A cochain relation pairs to zero with every test weakly transverse to the cells
in its support. -/
theorem intersectionPairing_eq_zero_of_mem_cochainRelations {v : Fin (k + 1) → V}
    {z : OrientedCell h k →₀ E} (hz : z ∈ cochainRelations R h E k)
    (hv : ∀ σ ∈ z.support, σ.IsWeaklyTransverse v) :
    intersectionPairing (R := R) v z = 0 := by
  classical
  -- The test meets each relevant span in a single point. Near that point in the span, the
  -- local coefficient is constant, while every relation vanishes off a nowhere dense set.
  -- Group the cells by affine span.
  rw [intersectionPairing_apply, Finsupp.sum,
    ← Finset.sum_fiberwise_of_maps_to (g := fun σ => affineSpan ℝ σ.carrier)
      (t := z.support.image fun σ => affineSpan ℝ σ.carrier)
      fun σ hσ => Finset.mem_image_of_mem _ hσ]
  refine Finset.sum_eq_zero fun A _ => ?_
  by_cases hmeet : ∃ σ ∈ z.support, affineSpan ℝ σ.carrier = A ∧
      (convexHull ℝ (range v) ∩ σ.carrier).Nonempty
  · -- The test meets `A` in a single point `q`, so the group is the local coefficient at `q`.
    obtain ⟨σ₀, hσ₀, hσ₀A, q, hqv, hqσ₀⟩ := hmeet
    have hsub := (hv σ₀ hσ₀).subsingleton_convexHull_inter_affineSpan ⟨q, hqv, hqσ₀⟩
    rw [hσ₀A] at hsub
    have hqA : q ∈ A := hσ₀A ▸ subset_affineSpan ℝ _ hqσ₀
    have hgroup : ∑ σ ∈ z.support with affineSpan ℝ σ.carrier = A,
        σ.intersectionIndex v • z σ =
          localCoeff (R := R) A (fun j : Fin k => v j.succ - v 0) q z := by
      rw [localCoeff_apply, Finset.sum_filter]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases hσA : affineSpan ℝ σ.carrier = A
      · have hiff : (convexHull ℝ (range v) ∩ σ.carrier).Nonempty ↔ q ∈ σ.carrier := by
          refine ⟨fun ⟨p, hpv, hpσ⟩ => ?_, fun hq => ⟨q, hqv, hq⟩⟩
          rwa [hsub ⟨hpv, hσA ▸ subset_affineSpan ℝ _ hpσ⟩ ⟨hqv, hqA⟩] at hpσ
        rw [ite_eq_left hσA]
        by_cases hqσ : q ∈ σ.carrier
        · rw [ite_eq_left ⟨hσA, hqσ⟩, intersectionIndex_of_nonempty (hiff.mpr hqσ)]
        · rw [ite_eq_right fun hc => hqσ hc.2, intersectionIndex_of_disjoint
            (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp (hiff.not.mpr hqσ))),
            zero_smul]
      · rw [ite_eq_right hσA, ite_eq_right fun hc => hσA hc.1]
    rw [hgroup]
    exact localCoeff_eq_zero hz A _ ⟨q, hqA⟩ fun σ hσ =>
      (hv σ hσ).disjoint_intrinsicFrontier.notMem_of_mem_left hqv
  · -- The test misses every cell of the group.
    simp only [not_exists, not_and] at hmeet
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [intersectionIndex_of_disjoint (disjoint_iff_inter_eq_empty.mpr
      (not_nonempty_iff_eq_empty.mp (hmeet σ hσ.1 hσ.2))), zero_smul]

end OrientedCell

namespace PolyhedralCochain

open OrientedCell

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

/-- The intersection pairing is independent of the representative for tests weakly transverse
to all cells in the two representatives. -/
theorem intersectionPairing_eq_of_ofFinsupp_eq {v : Fin (k + 1) → V}
    {x y : OrientedCell h k →₀ E} (hxy : ofFinsupp (R := R) x = ofFinsupp y)
    (hx : ∀ σ ∈ x.support, σ.IsWeaklyTransverse v)
    (hy : ∀ σ ∈ y.support, σ.IsWeaklyTransverse v) :
    intersectionPairing (R := R) v x = intersectionPairing (R := R) v y := by
  classical
  rw [← sub_eq_zero, ← map_sub]
  refine intersectionPairing_eq_zero_of_mem_cochainRelations ?_ fun σ hσ => ?_
  · rw [← ofFinsupp_eq_zero_iff, map_sub, hxy, sub_self]
  · rcases Finset.mem_union.mp (Finsupp.support_sub hσ) with hσ | hσ
    exacts [hx σ hσ, hy σ hσ]

end PolyhedralCochain

end TauCeti
