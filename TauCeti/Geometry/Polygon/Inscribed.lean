/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import TauCeti.Analysis.Calculus.Deriv.ChordGraph
public import TauCeti.Analysis.Convex.CurveChord
public import TauCeti.Geometry.Polygon.DeltaMove
public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.Topology.Homotopy.Isotopy.Basic
public import TauCeti.Topology.Instances.Real.InjectiveModPeriod
import TauCeti.Topology.Homotopy.Isotopy.StraightenGraph

/-!
# Inscribed polygons of a `C¹` loop

A closed curve `γ : ℝ → P` of period `T` carries, for each `n`, the **inscribed polygon**
`Polygon.inscribed γ T n` whose `n` vertices are the points `γ (k * (T / n))`, `0 ≤ k < n`, in
order. This file proves that inscribed polygons approximate an embedded `C¹` loop without
self-intersections: if `γ` is a `C¹` map into a real normed space with nowhere vanishing derivative,
injective modulo its period, then its inscribed polygons are simple for all large `n`
(`Polygon.eventually_isSimple_inscribed`).

Fine inscribed polygons are moreover all the same polygonal knot: for all large `n` and `m` the
inscribed polygons with `n` and with `m` vertices are combinatorially equivalent
(`Polygon.exists_combinatoriallyEquivalent_inscribed`), that is, related by Δ-moves and
subdivisions of edges (`TauCeti.SimplePolygon.CombinatoriallyEquivalent`). So an embedded `C¹`
loop determines a polygonal knot up to combinatorial equivalence, independently of the number of
vertices used to inscribe it.

Fine inscribed polygons are also ambient isotopic to the loop: for all large `n` some ambient
isotopy of the ambient space carries the image of `γ` onto the inscribed polygon with `n` vertices
(`Polygon.eventually_exists_ambientIsotopy_image_inscribed`). So a knot of class `C¹` is tame, that
is, ambient isotopic to a polygonal knot.

The polygonal knot of the loop does not change along an isotopy. If `Γ t` is a family of such
loops, jointly `C¹` in the time `t` and the loop parameter, and each `Γ t` for `t ∈ [0, 1]` is an
embedded loop with nowhere vanishing derivative, then the fine inscribed polygons of `Γ 0` and
of `Γ 1` are combinatorially equivalent
(`Polygon.exists_combinatoriallyEquivalent_inscribed_of_isotopy`). The specialisations to smooth
embeddings of the circle, and to smooth isotopies between them, are in
`TauCeti.KnotTheory.InscribedPolygon`.

## Main definitions

* `Polygon.inscribed γ T n`: the polygon with vertices `γ (k * (T / n))`.

## Main results

* `Polygon.edgeSet_inscribed`: the edges of the polygon inscribed in a periodic curve.
* `Polygon.rotate_inscribed`: relabelling an inscribed polygon cyclically starts the loop one
  vertex later.
* `Polygon.eventually_isSimple_inscribed`: the inscribed polygons of a `C¹` loop with nowhere
  vanishing derivative, injective modulo its period, are eventually simple.
* `Polygon.exists_combinatoriallyEquivalent_inscribed`: any two such inscribed polygons with
  enough vertices are combinatorially equivalent.
* `Polygon.exists_combinatoriallyEquivalent_inscribed_of_isotopy`: fine inscribed polygons of the
  two ends of a `C¹` isotopy of such loops are combinatorially equivalent.
* `Polygon.eventually_exists_ambientIsotopy_image_inscribed`: an ambient isotopy carries such a loop
  onto each of its inscribed polygons with enough vertices.

## Implementation notes

The proof of `Polygon.eventually_isSimple_inscribed` compares two edges of the inscribed polygon
`γ (k * h)`, `h = T / n`, according to how far apart their parameters are.

* **Nearby edges.** There is `δ > 0` such that on every window `[a, a + 3δ]` some continuous
  linear functional `φ` makes `φ ∘ γ` strictly increasing. Two edges in one window are mapped by
  `φ` onto intervals between the values of `φ ∘ γ` at their ends, which are disjoint unless the
  edges are consecutive, and then meet only at the common vertex.
* **Distant edges.** By compactness and injectivity, `‖γ (a + d) - γ a‖` is bounded below by some
  `η > 0` when `δ ≤ d ≤ T - δ`, while every point of an edge lies within `K h` of its first vertex,
  `K` a Lipschitz constant of `γ` on `[0, T]`. So distant edges are disjoint once `2 K h < η`.

The proof of `Polygon.exists_combinatoriallyEquivalent_inscribed` works with polygons inscribed at
arbitrary parameters `0 = t₀ < t₁ < ⋯ < t_N < T` whose gaps, including the gap from `t_N` to `T`,
are at most a mesh `h` with `h ≤ δ` and `2 K h < η`. Inserting a parameter `s` between `tᵢ` and
the next parameter `t'` inserts the vertex `γ s`, and the same comparison of nearby and distant
parameters shows that the triangle `γ tᵢ, γ s, γ t'` meets every other edge only at `γ tᵢ` or
`γ t'`. So the insertion is a Δ-move, or a subdivision of the edge when the three points are
collinear, and it keeps the mesh at most `h`. Refining the uniform parameters of the polygons with
`n` and with `m` vertices, one parameter at a time, to the union of the two sets of parameters gives
the same polygon from both sides.

Along an isotopy `Γ`, the three constants `δ`, `K` and `η` are chosen uniformly, by compactness of
`[0, 1] × [0, 2T]`, for all the loops `s ↦ Γ (τ s) (s + c)` whose time `τ s ∈ [0, 1]` is periodic,
moves slowly in `s`, and varies little overall: the windows come from
`ContDiff.exists_strictMonoOn_dual_comp_uncurry` and the separation from
`TauCeti.exists_pos_le_dist_apply_add_uncurry`. For two close times `t` and `t'`, with `h = T / n`,
one such loop is the hybrid loop `α` whose time oscillates between `t` and `t'` with period `h`: it
passes through the `n` vertices of the polygon inscribed in `Γ t`, and halfway between them
through the points `Γ t' (k * h + h / 2)`. Refining in `α`, in the loop `α` started half a step
later, and in `Γ t'` started half a step later shows that the inscribed polygons of `Γ t` and
`Γ t'` with `n` vertices are combinatorially equivalent. Stepping from time `0` to time `1` in
steps small compared with `h` finishes the proof.

The proof of `Polygon.eventually_exists_ambientIsotopy_image_inscribed` straightens the arcs of `γ`
over the steps `[k h, k h + h]`, `h = T / n`, onto their chords one at a time
(`TauCeti.AmbientIsotopy.exists_final_image_eq_segment`). For step `k` it uses a functional `φ`
with `φ ∘ γ` strictly increasing on the window `[k h - 2 δ, k h + 2 δ]`, and the straightening
moves only points `x` with `φ x` strictly between the values of `φ` at the ends of the arc and
within `7 K h` of `γ (k h)`. The pieces over the other steps, arcs not yet straightened and chords
already straightened, avoid this region. After shifting their parameters by a multiple of the
period into `[k h - 2 δ, k h - 2 δ + T)`, either they lie in the window, entirely on one side of the
step `k`, or their parameters differ from `k h` by between `δ` and `T - δ`, so that they stay at
distance at least `η - K h ≥ 7 K h` from `γ (k h)`.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Appendix I, for
  inscribed polygons of a knot of class `C¹`.
* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1 §B, Definitions 1.6 and 1.7, for Δ-moves and combinatorial equivalence.
-/


public section

noncomputable section

open Filter Function Set Topology

namespace Polygon

/-- The polygon **inscribed** in a curve `γ : ℝ → P` with `n` vertices at the times
`k * (T / n)`, `0 ≤ k < n`. For a curve of period `T` its last edge returns to `γ 0`
(`Polygon.inscribed_finRotate`). -/
def inscribed {P : Type*} (γ : ℝ → P) (T : ℝ) (n : ℕ) : Polygon P n :=
  ⟨fun k ↦ γ (k * (T / n))⟩

@[simp]
theorem inscribed_apply {P : Type*} (γ : ℝ → P) (T : ℝ) (n : ℕ) (k : Fin n) :
    inscribed γ T n k = γ (k * (T / n)) :=
  (rfl)

/-- The vertex after vertex `k` of the polygon inscribed in a curve of period `T` is the point at
time `(k + 1) * (T / n)`, also for the last vertex. -/
theorem inscribed_finRotate {P : Type*} {γ : ℝ → P} {T : ℝ} (hper : Periodic γ T) {n : ℕ}
    (k : Fin n) : inscribed γ T n (finRotate n k) = γ ((k + 1) * (T / n)) := by
  obtain _ | n := n
  · exact k.elim0
  rw [inscribed_apply, coe_finRotate]
  split_ifs with hk
  · subst hk
    have : ((Fin.last n : ℕ) + 1 : ℝ) * (T / (n + 1 : ℕ)) = 0 + T := by
      rw [Fin.val_last]
      push_cast
      field_simp
      ring
    rw [this, hper, Nat.cast_zero, zero_mul]
  · rw [Nat.cast_add_one]

/-- The edge from vertex `k` of the polygon inscribed in a curve of period `T` is the segment from
`γ (k * (T / n))` to `γ ((k + 1) * (T / n))`. -/
theorem edgeSet_inscribed {R V : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    [AddCommGroup V] [Module R V] {γ : ℝ → V} {T : ℝ} (hper : Periodic γ T) {n : ℕ} (k : Fin n) :
    (inscribed γ T n).edgeSet R k = segment R (γ (k * (T / n))) (γ ((k + 1) * (T / n))) := by
  rw [edgeSet, affineSegment_eq_segment, inscribed_apply, inscribed_finRotate hper]

/-- Relabelling the polygon inscribed in a loop of period `T` cyclically gives the polygon
inscribed in the same loop started one vertex later. -/
theorem rotate_inscribed {P : Type*} {γ : ℝ → P} {T : ℝ} (hper : Periodic γ T) (n : ℕ) :
    (inscribed γ T n).rotate = inscribed (fun s ↦ γ (s + T / n)) T n := by
  have h (k : Fin n) : (inscribed γ T n).rotate k = inscribed (fun s ↦ γ (s + T / n)) T n k := by
    rw [rotate_apply, inscribed_finRotate hper, inscribed_apply, add_one_mul]
  exact congrArg Polygon.mk (funext h)

/-- Two loops which agree at the vertices of the polygon inscribed with `n` vertices have the same
inscribed polygon. -/
theorem inscribed_congr {P : Type*} {γ γ' : ℝ → P} {T : ℝ} {n : ℕ}
    (h : ∀ k : Fin n, γ (k * (T / n)) = γ' (k * (T / n))) : inscribed γ T n = inscribed γ' T n :=
  congrArg Polygon.mk (funext h)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {T : ℝ}

/-- Two edges of an inscribed polygon whose parameters lie in a window on which `φ ∘ γ` is strictly
increasing meet only if they are consecutive, and then only at their common vertex. -/
private theorem eq_of_mem_segment_of_mem_segment {φ : StrongDual ℝ E} {a δ h : ℝ} {r : ℕ}
    (hmono : StrictMonoOn (fun t ↦ φ (γ t)) (Icc a (a + 3 * δ))) (hh : 0 < h) (hr : 1 ≤ r)
    (hrh : r * h + h ≤ 3 * δ) {x : E} (hx : x ∈ segment ℝ (γ a) (γ (a + h)))
    (hx' : x ∈ segment ℝ (γ (a + r * h)) (γ (a + r * h + h))) :
    r = 1 ∧ x = γ (a + h) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have mem (s : ℝ) (hs₀ : 0 ≤ s) (hs : s ≤ r * h + h) : a + s ∈ Icc a (a + 3 * δ) :=
    ⟨by linarith, by linarith⟩
  have ha : a ∈ Icc a (a + 3 * δ) := by simpa using mem 0 le_rfl (by positivity)
  have hah := mem h hh.le (by nlinarith)
  -- The first edge lies below `φ (γ (a + h))`, where the second one starts.
  have hle : φ x ≤ φ (γ (a + h)) := (convex_halfSpace_le φ.toLinearMap.isLinear _).segment_subset
    (hmono.monotoneOn ha hah (by linarith)) le_rfl hx
  obtain ⟨e, rfl⟩ := hmono.eq_of_mem_segment_of_le hah (mem (r * h) (by positivity) (by linarith))
    (by simpa [add_assoc] using mem (r * h + h) (by positivity) le_rfl) (by nlinarith)
    (by linarith) hle hx'
  refine ⟨?_, by rw [e]⟩
  have : (r : ℝ) * h = 1 * h := by linarith
  exact_mod_cast mul_right_cancel₀ hh.ne' this

/-- Two edges of an inscribed polygon are disjoint when `γ` moves at least `η` between their first
vertices but less than `η / 2` along each edge. -/
private theorem not_mem_segment_of_mem_segment {K : NNReal} (hK : LipschitzOnWith K γ (Icc 0 T))
    {a d h η : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hh : 0 < h) (hT : a + d + h ≤ T)
    (hη : η ≤ ‖γ (a + d) - γ a‖) (hKh : 2 * K * h < η) {x : E}
    (hx : x ∈ segment ℝ (γ a) (γ (a + h))) (hx' : x ∈ segment ℝ (γ (a + d)) (γ (a + d + h))) :
    False := by
  have e₁ := (norm_sub_le_of_mem_segment hx).trans
    (hK.norm_sub_le ⟨by linarith, by linarith⟩ ⟨ha, by linarith⟩)
  have e₂ := (norm_sub_le_of_mem_segment hx').trans
    (hK.norm_sub_le ⟨by linarith, hT⟩ ⟨by linarith, by linarith⟩)
  rw [add_sub_cancel_left, Real.norm_of_nonneg hh.le] at e₁
  rw [add_sub_cancel_left, Real.norm_of_nonneg hh.le, norm_sub_rev] at e₂
  linarith [norm_sub_le_norm_sub_add_norm_sub (γ (a + d)) x (γ a)]

/-! ### Fine meshes -/

/-- The constants controlling the chords of a loop `γ` of period `T` at mesh `h`: on every window
`[a, a + 3δ]` some `φ ∘ γ` is strictly increasing, `γ` is `K`-Lipschitz on `[0, T]`, points of
`γ` whose parameters are between `δ` and `T - δ` apart are at distance at least `η`, and the mesh
`h` is at most `δ` with `2 K h < η`. -/
private structure FineMesh (γ : ℝ → E) (T δ η h : ℝ) (K : NNReal) : Prop where
  periodic : Periodic γ T
  le_delta : h ≤ δ
  mono : ∀ a ∈ Icc 0 T, ∃ φ : StrongDual ℝ E, StrictMonoOn (fun t ↦ φ (γ t)) (Icc a (a + 3 * δ))
  lipschitz : LipschitzOnWith K γ (Icc 0 T)
  sep : ∀ a ∈ Icc 0 T, ∀ d ∈ Icc δ (T - δ), η ≤ dist (γ (a + d)) (γ a)
  lt_sep : 2 * K * h < η

variable {δ η h : ℝ} {K : NNReal}

/-- Under `FineMesh`, the points of `γ` at parameters of `[0, T]` at most `h` apart are at most
`K * h` apart. -/
private theorem FineMesh.dist_le (hF : FineMesh γ T δ η h K) {u v : ℝ} (hu : u ∈ Icc 0 T)
    (hv : v ∈ Icc 0 T) (huv : |u - v| ≤ h) : dist (γ u) (γ v) ≤ K * h :=
  (hF.lipschitz.dist_le_mul u hu v hv).trans
    (mul_le_mul_of_nonneg_left (by rwa [Real.dist_eq]) K.2)

/-- Two edges `i < j` of an inscribed polygon which are consecutive across the end of the period
meet only at their common vertex: `i` is the successor of `j`, and `x` is the vertex `i`. -/
private theorem FineMesh.eq_finRotate_of_mem_edges_of_wrap {h₀ : ℝ}
    (hF : FineMesh γ T δ η h₀ K) {n : ℕ} [NeZero n] {h : ℝ} (hh : 0 < h)
    (hnh : (n : ℝ) * h = T) (hhδ : h ≤ δ)
    {i j : Fin n} {r : ℕ} (hr : (j : ℕ) = i + r + 1) (hrn : r + 1 ≤ n)
    (hB : ((n - (r + 1) : ℕ) : ℝ) * h ≤ 2 * δ) (hj : (j : ℝ) * h = i * h + (r + 1 : ℕ) * h)
    (hT' : ((n - (r + 1) : ℕ) : ℝ) * h = T - ((r + 1 : ℕ) : ℝ) * h)
    (hjv : (j : ℝ) * h ∈ Icc 0 T) {x : E} (hxi : x ∈ segment ℝ (γ (i * h)) (γ (i * h + h)))
    (hxj : x ∈ segment ℝ (γ (i * h + (r + 1 : ℕ) * h)) (γ (i * h + (r + 1 : ℕ) * h + h))) :
    i = finRotate n j ∧ x = (inscribed γ T n).vertices i := by
  have hper := hF.periodic
  have hjn : (j : ℕ) < n := j.is_lt
  obtain ⟨φ, hφ⟩ := hF.mono _ hjv
  -- Read edge `i` one period later, as the edge `n - (r + 1)` steps after edge `j`.
  have e (s : ℝ) : γ ((i : ℝ) * h + s) = γ ((j : ℝ) * h + ((n - (r + 1) : ℕ) : ℝ) * h + s) := by
    rw [← hper ((i : ℝ) * h + s), hT', hj]
    ring_nf
  have e₀ := e 0
  rw [add_zero, add_zero] at e₀
  rw [e₀, e h] at hxi
  rw [← hj] at hxj
  obtain ⟨hr1, rfl⟩ := eq_of_mem_segment_of_mem_segment hφ hh (by omega) (by linarith) hxj hxi
  have hi0 : (i : ℕ) = 0 := by omega
  have hjn1 : (j : ℕ) + 1 = n := by omega
  refine ⟨Fin.ext ?_, ?_⟩
  · simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rw [hjn1, Nat.mod_self, hi0]
  · have : ((j : ℝ) + 1) * h = 0 + T := by
      rw [zero_add, ← hnh]
      congr 1
      exact_mod_cast hjn1
    rw [inscribed_apply, hi0, Nat.cast_zero, zero_mul, ← add_one_mul, this, hper]

/-- **Fine inscribed polygons are simple.** If a loop satisfies `FineMesh` at mesh `h₀`, then its
inscribed polygon with `n` vertices is simple as soon as `T / n ≤ h₀`. -/
private theorem FineMesh.isSimple_inscribed {h₀ : ℝ} (hF : FineMesh γ T δ η h₀ K) (hT : 0 < T)
    {n : ℕ} [NeZero n] (hn : T / n ≤ h₀) : (inscribed γ T n).IsSimple ℝ := by
  have hper := hF.periodic
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  set h := T / n with hh_def
  have hh : 0 < h := div_pos hT (by exact_mod_cast hn1)
  have hnh : (n : ℝ) * h = T := by rw [hh_def]; field_simp
  have hhδ : h ≤ δ := hn.trans hF.le_delta
  have hδ : 0 ≤ δ := hh.le.trans hhδ
  have hhη : 2 * K * h < η := lt_of_le_of_lt (by gcongr) hF.lt_sep
  have hval (k : Fin n) : (k : ℝ) * h ∈ Icc 0 T :=
    ⟨by positivity, by rw [← hnh]; gcongr; exact_mod_cast k.is_lt.le⟩
  refine ⟨fun i ↦ ?_, fun i j x hij hxi hxj ↦ ?_⟩
  · -- Consecutive vertices are distinct, since `φ ∘ γ` increases along the edge.
    rw [inscribed_apply, inscribed_finRotate hper, add_one_mul]
    obtain ⟨φ, hφ⟩ := hF.mono _ (hval i)
    exact fun heq ↦ (hφ ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)).ne
      (congrArg φ heq)
  wlog hlt : (i : ℕ) < j generalizing i j x
  · exact (this j i x hij.symm hxj hxi (lt_of_le_of_ne (not_lt.1 hlt)
      fun h ↦ hij (Fin.ext h.symm))).symm
  rw [edgeSet_inscribed hper, add_one_mul] at hxi hxj
  -- Write `j = i + (r + 1)` and `a = i * h`, the first parameter of edge `i`. The two edges are
  -- nearby with `j` ahead, nearby with `i` ahead across the end of the period, or distant.
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_lt hlt
  have hjn : (j : ℕ) < n := j.is_lt
  have hj1 : ((j : ℝ) + 1) * h ≤ T := by rw [← hnh]; gcongr; exact_mod_cast hjn
  have hj : (j : ℝ) * h = i * h + (r + 1 : ℕ) * h := by rw [hr]; push_cast; ring
  rw [hj] at hxj
  by_cases hA : ((r + 1 : ℕ) : ℝ) * h ≤ 2 * δ
  · -- Nearby edges, `j` ahead of `i`: they are consecutive and meet at vertex `j`.
    obtain ⟨φ, hφ⟩ := hF.mono _ (hval i)
    obtain ⟨hr1, rfl⟩ := eq_of_mem_segment_of_mem_segment hφ hh (by omega) (by linarith) hxi hxj
    have hji : (j : ℕ) = i + 1 := by omega
    refine .inl ⟨Fin.ext ?_, ?_⟩
    · simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt (by omega), hji]
    · rw [inscribed_apply, hji, Nat.cast_add_one, add_one_mul]
  have hrn : r + 1 ≤ n := by omega
  have hT' : ((n - (r + 1) : ℕ) : ℝ) * h = T - ((r + 1 : ℕ) : ℝ) * h := by
    rw [Nat.cast_sub hrn, sub_mul, hnh]
  by_cases hB : ((n - (r + 1) : ℕ) : ℝ) * h ≤ 2 * δ
  · -- Nearby edges, `i` ahead of `j` across the end of the period: then `i = 0` and `j = n - 1`.
    exact .inr (hF.eq_finRotate_of_mem_edges_of_wrap hh hnh hhδ hr hrn hB hj hT'
      (hval j) hxi hxj)
  · -- Distant edges are disjoint.
    rw [not_le] at hA hB
    exact (not_mem_segment_of_mem_segment hF.lipschitz (hval i).1 (by positivity) hh
      (by linarith) ((hF.sep _ (hval i) _ ⟨by linarith, by linarith⟩).trans_eq
        (dist_eq_norm _ _)) hhη hxi hxj).elim

/-! ### Families of loops -/

/-- Constants which control, uniformly, the loops `s ↦ Γ (τ s) (s + c)` obtained from a family
`Γ t` of loops of period `T` by letting the time move slowly with the loop parameter: for every
time function `τ` of period `T` with values in `[0, 1]`, `lam`-Lipschitz and varying by at most
`ρ`, and every shift `c ∈ [0, T]`, such a loop satisfies `FineMesh` with the constants `δ`, `η`
and `K` at every mesh `h` with `h ≤ δ` and `2 K h < η`. -/
private structure FineFamily (Γ : ℝ → ℝ → E) (T δ η lam ρ : ℝ) (K : NNReal) : Prop where
  lam_nonneg : 0 ≤ lam
  rho_nonneg : 0 ≤ ρ
  fineMesh ⦃α : ℝ → E⦄ ⦃τ : ℝ → ℝ⦄ ⦃c h : ℝ⦄ (hα : ∀ s, α s = Γ (τ s) (s + c))
    (hc : c ∈ Icc 0 T) (hτ : Periodic τ T) (hτI : ∀ s, τ s ∈ Icc (0 : ℝ) 1)
    (hlip : ∀ x y, |τ x - τ y| ≤ lam * |x - y|) (hvar : ∀ x y, |τ x - τ y| ≤ ρ) (hδ : h ≤ δ)
    (hη : 2 * K * h < η) : FineMesh α T δ η h K

/-- **Uniform constants along a `C¹` isotopy of loops.** For a family `Γ t` of loops of period
`T`, jointly `C¹` in the time and the loop parameter, such that each `Γ t` with `t ∈ [0, 1]` is
injective modulo `T` with nowhere vanishing derivative, the constants of `FineFamily` exist. -/
private theorem exists_fineFamily {Γ : ℝ → ℝ → E} (hΓ : ContDiff ℝ 1 (uncurry Γ))
    (hper : ∀ t ∈ Icc (0 : ℝ) 1, Periodic (Γ t) T)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s s', Γ t s = Γ t s' → ∃ k : ℤ, s = s' + k * T)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s, deriv (Γ t) s ≠ 0) :
    ∃ (δ η lam ρ : ℝ) (K : NNReal), 0 < δ ∧ 0 < η ∧ 0 < lam ∧ 0 < ρ ∧
      FineFamily Γ T δ η lam ρ K := by
  -- The constants come from compactness of `[0, 1] × [0, 2T]`: a bound `B` on the derivative of
  -- `Γ`, uniform windows of width `δ₀` along which the loops increase, and the least distance
  -- `η₀` between points of one loop whose parameters are between `δ` and `T - δ` apart.
  obtain ⟨B, hlipΓ⟩ := hΓ.exists_norm_sub_le_mul_max_uncurry 0 1 0 (2 * T)
  obtain ⟨δ₀, hδ₀, lam₀, hlam₀, hmono⟩ :=
    hΓ.exists_strictMonoOn_dual_comp_uncurry hderiv 0 (2 * T)
  set δ := δ₀ / 3 with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨η₀, hη₀, hsep⟩ := TauCeti.exists_pos_le_dist_apply_add_uncurry hΓ.continuous
    isCompact_Icc hinj (isCompact_Icc (a := 0) (b := 2 * T)) hδ
  set lam := min 1 lam₀ with hlam_def
  have hlam : 0 < lam := lt_min one_pos hlam₀
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlam₀' : lam ≤ lam₀ := min_le_right _ _
  set ρ := η₀ / (2 * (B + 1)) with hρ_def
  have hBρ : B * ρ ≤ η₀ / 2 := by
    have h₁ : ρ * (2 * (B + 1)) = η₀ := by rw [hρ_def]; field_simp
    nlinarith [div_pos hη₀ (by positivity : (0 : ℝ) < 2 * (B + 1))]
  refine ⟨δ, η₀ / 2, lam, ρ, B, hδ, by positivity, hlam, by positivity,
    ⟨hlam.le, by positivity, ?_⟩⟩
  intro α τ c h hα hc hτ hτI hlip hvar hhδ hη
  have hτ1 (x y : ℝ) : |τ x - τ y| ≤ |x - y| :=
    (hlip x y).trans (mul_le_of_le_one_left (abs_nonneg _) hlam1)
  refine ⟨fun s ↦ ?_, hhδ, fun a ha ↦ ?_, ?_, fun a ha d hd ↦ ?_, hη⟩
  · rw [hα, hα, hτ s, add_right_comm s T c, hper _ (hτI s)]
  · -- The window `[a, a + 3δ]` of `α` is the window `[a + c, a + c + 3δ]` of `u ↦ Γ (τ' u) u`,
    -- with the time `τ' u = τ (u - c)`.
    obtain ⟨φ, hφ⟩ := hmono (fun u ↦ τ (u - c)) (fun u ↦ hτI _)
      (fun x y ↦ (hlip _ _).trans (by
        rw [sub_sub_sub_cancel_right]
        exact mul_le_mul_of_nonneg_right hlam₀' (abs_nonneg _)))
      (a + c) ⟨by linarith [ha.1, hc.1], by linarith [ha.2, hc.2]⟩
    refine ⟨φ, fun x hx y hy hxy ↦ ?_⟩
    have h := hφ (a := x + c) (b := y + c) ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
    simpa only [add_sub_cancel_right, ← hα] using h
  · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [dist_eq_norm, hα, hα, Real.dist_eq]
    refine (hlipΓ (hτI x) ⟨by linarith [hx.1, hc.1], by linarith [hx.2, hc.2]⟩ (hτI y)
      ⟨by linarith [hy.1, hc.1], by linarith [hy.2, hc.2]⟩).trans ?_
    rw [add_sub_add_right_eq_sub]
    exact mul_le_mul_of_nonneg_left (max_le (hτ1 x y) le_rfl) B.2
  · -- The time changes by at most `ρ`, which costs at most `B ρ ≤ η₀ / 2`.
    rw [dist_eq_norm, hα, hα]
    have h₁ := hsep (τ (a + d)) (hτI _) (a + c) ⟨by linarith [ha.1, hc.1], by linarith [ha.2, hc.2]⟩
      d hd
    rw [dist_eq_norm] at h₁
    have hac : a + c ∈ Icc 0 (2 * T) := ⟨by linarith [ha.1, hc.1], by linarith [ha.2, hc.2]⟩
    have h₂ := hlipΓ (hτI (a + d)) hac (hτI a) hac
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h₂
    have h₃ : B * |τ (a + d) - τ a| ≤ B * ρ := mul_le_mul_of_nonneg_left (hvar _ _) B.2
    rw [add_right_comm a d c]
    linarith [norm_sub_le_norm_sub_add_norm_sub (Γ (τ (a + d)) (a + c + d)) (Γ (τ a) (a + c))
      (Γ (τ (a + d)) (a + c)), norm_sub_rev (Γ (τ a) (a + c)) (Γ (τ (a + d)) (a + c))]

/-- A loop of the family at a fixed time `t ∈ [0, 1]`, shifted by `c ∈ [0, T]`, satisfies
`FineMesh`. -/
private theorem FineFamily.fineMesh_const {Γ : ℝ → ℝ → E} {lam ρ : ℝ}
    (hF : FineFamily Γ T δ η lam ρ K) {α : ℝ → E} {t c : ℝ} (hα : ∀ s, α s = Γ t (s + c))
    (ht : t ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc 0 T) (hδ : h ≤ δ) (hη : 2 * K * h < η) :
    FineMesh α T δ η h K :=
  hF.fineMesh (τ := fun _ ↦ t) hα hc (fun _ ↦ rfl) (fun _ ↦ ht)
    (fun _ _ ↦ by simpa using mul_nonneg hF.lam_nonneg (abs_nonneg _))
    (fun _ _ ↦ by simpa using hF.rho_nonneg) hδ hη

/-- The constants of `FineMesh` exist for a `C¹` loop with nowhere vanishing derivative, injective
modulo its period: they are those of the constant family. -/
private theorem exists_fineMesh (hT : 0 < T) (hγ : ContDiff ℝ 1 γ) (hper : Periodic γ T)
    (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T) (hderiv : ∀ t, deriv γ t ≠ 0) :
    ∃ (δ η h : ℝ) (K : NNReal), 0 < h ∧ FineMesh γ T δ η h K := by
  have hΓ : ContDiff ℝ 1 (uncurry fun _ : ℝ ↦ γ) := by
    have e : (uncurry fun _ : ℝ ↦ γ) = γ ∘ Prod.snd := by funext p; simp [uncurry_def]
    rw [e]
    exact hγ.comp contDiff_snd
  obtain ⟨δ, η, lam, ρ, K, hδ, hη, -, -, hF⟩ := exists_fineFamily hΓ (fun _ _ ↦ hper)
    (fun _ _ ↦ hinj) (fun _ _ ↦ hderiv)
  set h := min δ (η / (2 * K + 1))
  have hh : 0 < h := lt_min hδ (by positivity)
  refine ⟨δ, η, h, K, hh, hF.fineMesh_const (t := 0) (c := 0) (fun s ↦ by rw [add_zero])
    ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, hT.le⟩ (min_le_left _ _) ?_⟩
  have h₁ : h * (2 * K + 1) ≤ η := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have h₂ : h * (2 * K + 1) = 2 * K * h + h := by ring
  linarith

/-- **Inscribed polygons of a `C¹` loop are eventually simple.** Let `γ : ℝ → E` be a `C¹` curve
of period `T > 0` in a real normed space, with nowhere vanishing derivative, injective modulo `T`.
Then for all large `n` the polygon inscribed in `γ` with `n` vertices `γ (k * (T / n))` is
simple. -/
theorem eventually_isSimple_inscribed (hT : 0 < T) (hγ : ContDiff ℝ 1 γ) (hper : Periodic γ T)
    (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T) (hderiv : ∀ t, deriv γ t ≠ 0) :
    ∀ᶠ n in atTop, (inscribed γ T n).IsSimple ℝ := by
  obtain ⟨δ, η, h, K, hh, hF⟩ := exists_fineMesh hT hγ hper hinj hderiv
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat T).eventually (ge_mem_nhds hh),
    eventually_ge_atTop 1] with n hn hn1
  have : NeZero n := ⟨by omega⟩
  exact hF.isSimple_inscribed hT hn

/-! ### Refining an inscribed polygon by Δ-moves -/

section Refinement

/-- Under `FineMesh`, the points of `γ` at parameters in `[a, a']`, with `0 ≤ a`, `a' ≤ a + h` and
`a' ≤ T`, lie within `K * h` of `γ a`. -/
private theorem FineMesh.dist_le_of_mem_Icc (hF : FineMesh γ T δ η h K) {a a' u : ℝ} (ha : 0 ≤ a)
    (ha' : a' ≤ a + h) (haT : a' ≤ T) (hu : u ∈ Icc a a') : dist (γ u) (γ a) ≤ K * h :=
  hF.dist_le ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨ha, by linarith [hu.1, hu.2]⟩
    (abs_le.2 ⟨by linarith [hu.1, hu.2], by linarith [hu.2]⟩)

/-- Under `FineMesh`, the triangle on `γ a`, `γ s`, `γ a'` with `a ≤ s ≤ a' ≤ a + h` lies within
`K * h` of `γ a`. -/
private theorem FineMesh.dist_le_of_mem_convexHull (hF : FineMesh γ T δ η h K) {a s a' : ℝ}
    (ha : 0 ≤ a) (has : a ≤ s) (hsa' : s ≤ a') (ha' : a' ≤ a + h) (haT : a' ≤ T) {x : E}
    (hx : x ∈ convexHull ℝ {γ a, γ s, γ a'}) : dist x (γ a) ≤ K * h := by
  refine convexHull_min ?_ (convex_closedBall (γ a) (K * h)) hx
  rintro _ (rfl | rfl | rfl)
  exacts [hF.dist_le_of_mem_Icc ha ha' haT ⟨le_rfl, has.trans hsa'⟩,
    hF.dist_le_of_mem_Icc ha ha' haT ⟨has, hsa'⟩,
    hF.dist_le_of_mem_Icc ha ha' haT ⟨has.trans hsa', le_rfl⟩]

/-- Under `FineMesh`, the chord from `γ b` to `γ b'` with `b ≤ b' ≤ b + h` lies within `K * h` of
`γ b`. -/
private theorem FineMesh.dist_le_of_mem_segment (hF : FineMesh γ T δ η h K) {b b' : ℝ}
    (hb : 0 ≤ b) (hbb' : b ≤ b') (hb' : b' ≤ b + h) (hbT : b' ≤ T) {x : E}
    (hx : x ∈ segment ℝ (γ b) (γ b')) : dist x (γ b) ≤ K * h :=
  (convex_closedBall (γ b) (K * h)).segment_subset
    (hF.dist_le_of_mem_Icc hb hb' hbT ⟨le_rfl, hbb'⟩)
    (hF.dist_le_of_mem_Icc hb hb' hbT ⟨hbb', le_rfl⟩) hx

/-- Under `FineMesh`, a point within `K * h` of both `γ a` and `γ b` excludes any two parameters
`c ∈ [0, T]` and `c + d` with `d ∈ [δ, T - δ]` at which `γ` takes the values `γ a` and `γ b`. -/
private theorem FineMesh.false_of_dist_le_of_dist_le (hF : FineMesh γ T δ η h K) {a b : ℝ}
    {x : E} (hxa : dist x (γ a) ≤ K * h) (hxb : dist x (γ b) ≤ K * h) {c d : ℝ}
    (hc : c ∈ Icc 0 T) (hd : d ∈ Icc δ (T - δ))
    (hcd : γ (c + d) = γ b ∧ γ c = γ a ∨ γ (c + d) = γ a ∧ γ c = γ b) : False := by
  have := hF.sep c hc d hd
  rcases hcd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] at this <;>
    linarith [dist_triangle_left (γ b) (γ a) x, dist_comm (γ b) (γ a), hF.lt_sep]

/-- **Chords of a fine mesh meet only at their ends.** Let `[a, a']` and `[b, b']` be parameter
intervals in `[0, T]` of lengths at most `h`, with disjoint interiors, and `a ≤ s ≤ a'`. Then the
triangle with vertices `γ a`, `γ s`, `γ a'` meets the chord from `γ b` to `γ b'` at most in
`γ a` and `γ a'`. -/
private theorem FineMesh.eq_of_mem_convexHull_of_mem_segment (hF : FineMesh γ T δ η h K)
    {a s a' b b' : ℝ} (ha : 0 ≤ a) (has : a ≤ s) (hsa' : s ≤ a') (ha' : a' ≤ a + h)
    (haT : a' ≤ T) (hb : 0 ≤ b) (hbb' : b < b') (hb' : b' ≤ b + h) (hbT : b' ≤ T)
    (hdisj : a' ≤ b ∨ b' ≤ a) {x : E} (hx : x ∈ convexHull ℝ {γ a, γ s, γ a'})
    (hx' : x ∈ segment ℝ (γ b) (γ b')) : x = γ a ∨ x = γ a' := by
  have hh := hF.le_delta
  have hT (u : ℝ) : γ (u + T) = γ u := hF.periodic u
  have hxa := hF.dist_le_of_mem_convexHull ha has hsa' ha' haT hx
  have hxb := hF.dist_le_of_mem_segment hb hbb'.le hb' hbT hx'
  have far (c d : ℝ) (hc : c ∈ Icc 0 T) (hd : d ∈ Icc δ (T - δ))
      (hcd : γ (c + d) = γ b ∧ γ c = γ a ∨ γ (c + d) = γ a ∧ γ c = γ b) : False :=
    hF.false_of_dist_le_of_dist_le hxa hxb hc hd hcd
  rcases hdisj with hab | hba
  · -- The chord comes after the triangle.
    by_cases h₁ : b' ≤ a + 3 * δ
    · -- Both lie in the window `[a, a + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono a ⟨ha, by linarith⟩
      have hle := MonotoneOn.le_of_mem_convexHull
        (hφ.monotoneOn.mono (Icc_subset_Icc le_rfl (by linarith))) has hsa' hx
      obtain ⟨e, rfl⟩ := hφ.eq_of_mem_segment_of_le ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ ⟨by linarith, h₁⟩ hab hbb' hle hx'
      exact .inr (by rw [e])
    by_cases h₂ : a + T - b ≤ 2 * δ
    · -- The triangle, one period later, comes just after the chord: both lie in `[b, b + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono b ⟨hb, by linarith⟩
      rw [← hT a, ← hT s, ← hT a'] at hx
      have hge := MonotoneOn.ge_of_mem_convexHull (hφ.monotoneOn.mono (Icc_subset_Icc (by linarith)
        (by linarith))) (by linarith : a + T ≤ s + T) (by linarith : s + T ≤ a' + T) hx
      obtain ⟨e, rfl⟩ := hφ.eq_of_mem_segment_of_ge ⟨by linarith, by linarith⟩
        ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ hbb' (by linarith) hge hx'
      exact .inl (by rw [e, hT])
    · -- Distant: `γ a` and `γ b` are far apart.
      exact (far a (b - a) ⟨ha, by linarith⟩ ⟨by linarith, by linarith⟩
        (.inl ⟨by rw [add_sub_cancel], rfl⟩)).elim
  · -- The chord comes before the triangle.
    by_cases h₁ : a' ≤ b + 3 * δ
    · -- Both lie in the window `[b, b + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono b ⟨hb, by linarith⟩
      have hge := MonotoneOn.ge_of_mem_convexHull
        (hφ.monotoneOn.mono (Icc_subset_Icc (by linarith) h₁)) has hsa' hx
      obtain ⟨e, rfl⟩ := hφ.eq_of_mem_segment_of_ge ⟨by linarith, by linarith⟩
        ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ hbb' hba hge hx'
      exact .inl (by rw [e])
    by_cases h₂ : b + T - a ≤ 2 * δ
    · -- The chord, one period later, comes just after the triangle: both lie in `[a, a + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono a ⟨ha, by linarith⟩
      rw [← hT b, ← hT b'] at hx'
      have hle := MonotoneOn.le_of_mem_convexHull
        (hφ.monotoneOn.mono (Icc_subset_Icc le_rfl (by linarith))) has hsa' hx
      obtain ⟨e, rfl⟩ := hφ.eq_of_mem_segment_of_le ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith) (by linarith) hle hx'
      exact .inr (by rw [← e])
    · -- Distant: `γ b` and `γ a` are far apart.
      exact (far b (a - b) ⟨hb, by linarith⟩ ⟨by linarith, by linarith⟩
        (.inr ⟨by rw [add_sub_cancel], rfl⟩)).elim

/-- Parameters `0 = t 0 < t 1 < ⋯ < t N < T` of the vertices of a polygon inscribed in a loop of
period `T`, in which every parameter is followed, within `h`, by a later one or by `T`. -/
private structure IsMesh (T h : ℝ) {N : ℕ} (t : Fin (N + 1) → ℝ) : Prop where
  strictMono : StrictMono t
  zero : t 0 = 0
  last_lt : t (Fin.last N) < T
  exists_lt_le : ∀ x ∈ range t, ∃ y ∈ insert T (range t), x < y ∧ y ≤ x + h

/-- The polygon with vertices `γ (t k)`. -/
private def paramPolygon (γ : ℝ → E) {N : ℕ} (t : Fin (N + 1) → ℝ) : Polygon E (N + 1) :=
  ⟨fun k ↦ γ (t k)⟩

/-- The parameter at which the edge from vertex `k` ends: that of the next vertex, or `T` for the
last vertex. -/
private def nextParam (T : ℝ) {N : ℕ} (t : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : ℝ :=
  if k = Fin.last N then T else t (k + 1)

variable {N : ℕ} {t : Fin (N + 1) → ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem paramPolygon_apply (k : Fin (N + 1)) : paramPolygon γ t k = γ (t k) :=
  (rfl)

private theorem IsMesh.nonneg (ht : IsMesh T h t) (k : Fin (N + 1)) : 0 ≤ t k :=
  ht.zero ▸ ht.strictMono.monotone (Fin.zero_le k)

private theorem IsMesh.lt_nextParam (ht : IsMesh T h t) (k : Fin (N + 1)) :
    t k < nextParam T t k := by
  unfold nextParam
  split_ifs with hk
  · exact hk ▸ ht.last_lt
  · exact ht.strictMono (Fin.lt_add_one_iff.2 (Fin.lt_last_iff_ne_last.2 hk))

private theorem IsMesh.nextParam_le (ht : IsMesh T h t) (k : Fin (N + 1)) :
    nextParam T t k ≤ T := by
  unfold nextParam
  split_ifs
  · exact le_rfl
  · exact (ht.strictMono.monotone (Fin.le_last _)).trans ht.last_lt.le

private theorem IsMesh.nextParam_le_of_lt (ht : IsMesh T h t) {k j : Fin (N + 1)} (hkj : k < j) :
    nextParam T t k ≤ t j := by
  unfold nextParam
  split_ifs with hk
  · exact absurd hk (Fin.ne_last_of_lt hkj)
  · exact ht.strictMono.monotone (Fin.add_one_le_of_lt hkj)

private theorem nextParam_mem (k : Fin (N + 1)) : nextParam T t k ∈ insert T (range t) := by
  unfold nextParam
  split_ifs
  exacts [mem_insert _ _, mem_insert_of_mem _ (mem_range_self _)]

private theorem IsMesh.nextParam_le_add (ht : IsMesh T h t) (k : Fin (N + 1)) :
    nextParam T t k ≤ t k + h := by
  obtain ⟨y, hy, hky, hyh⟩ := ht.exists_lt_le _ (mem_range_self k)
  refine le_trans ?_ hyh
  rcases hy with rfl | ⟨j, rfl⟩
  · exact ht.nextParam_le k
  · exact ht.nextParam_le_of_lt (ht.strictMono.lt_iff_lt.1 hky)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem apply_nextParam (hper : Periodic γ T) (ht : IsMesh T h t) (k : Fin (N + 1)) :
    γ (nextParam T t k) = paramPolygon γ t (finRotate (N + 1) k) := by
  rw [paramPolygon_apply, finRotate_apply, nextParam]
  split_ifs with hk
  · rw [hk, Fin.last_add_one, ht.zero, ← zero_add T, hper]
  · rfl

private theorem edgeSet_paramPolygon (hper : Periodic γ T) (ht : IsMesh T h t) (k : Fin (N + 1)) :
    (paramPolygon γ t).edgeSet ℝ k = segment ℝ (γ (t k)) (γ (nextParam T t k)) := by
  rw [edgeSet, affineSegment_eq_segment, apply_nextParam hper ht, paramPolygon_apply]

/-- **Inserting a vertex into a fine inscribed polygon is an elementary move.** Inserting the
vertex `γ s`, for a parameter `s` strictly inside the edge from vertex `i`, is a Δ-move, or, when
`γ s` happens to lie on that edge, a subdivision. -/
private theorem FineMesh.exists_combinatoriallyEquivalent_insertVertex
    (hF : FineMesh γ T δ η h K) (ht : IsMesh T h t) (hp : (paramPolygon γ t).IsSimple ℝ)
    (i : Fin (N + 1)) {s : ℝ} (hs : s ∈ Ioo (t i) (nextParam T t i)) :
    ∃ hq : ((paramPolygon γ t).insertVertex i (γ s)).IsSimple ℝ,
      TauCeti.SimplePolygon.CombinatoriallyEquivalent ⟨N + 1, paramPolygon γ t, hp⟩
        ⟨N + 1 + 1, _, hq⟩ := by
  set poly := paramPolygon γ t
  have hi := ht.lt_nextParam i
  have hih := ht.nextParam_le_add i
  have hiT := ht.nextParam_le i
  have hi0 := ht.nonneg i
  have hvert : poly i = γ (t i) := paramPolygon_apply i
  have hnext : poly (finRotate (N + 1) i) = γ (nextParam T t i) :=
    (apply_nextParam hF.periodic ht i).symm
  by_cases hind : AffineIndependent ℝ ![poly i, poly (finRotate (N + 1) i), γ s]
  · -- A genuine triangle: every other edge meets it only at the ends of edge `i`.
    have hδ : poly.IsDeltaMove ℝ i (γ s) := by
      refine ⟨hind, fun k hk x ⟨hxk, hxT⟩ ↦ ?_⟩
      rw [← Affine.Simplex.convexHull_eq_closedInterior] at hxT
      rw [edgeSet_paramPolygon hF.periodic ht] at hxk
      rw [hvert, hnext]
      have hsub : range ![poly i, poly (finRotate (N + 1) i), γ s] ⊆
          {γ (t i), γ s, γ (nextParam T t i)} := by
        rintro _ ⟨j, rfl⟩
        fin_cases j
        exacts [.inl hvert, .inr (.inr hnext), .inr (.inl rfl)]
      exact hF.eq_of_mem_convexHull_of_mem_segment hi0 hs.1.le hs.2.le hih hiT (ht.nonneg k)
        (ht.lt_nextParam k) (ht.nextParam_le_add k) (ht.nextParam_le k)
        ((lt_or_gt_of_ne hk).symm.imp ht.nextParam_le_of_lt ht.nextParam_le_of_lt)
        (convexHull_mono hsub hxT) hxk
    exact ⟨hδ.isSimple_insertVertex hp,
      TauCeti.SimplePolygon.combinatoriallyEquivalent_deltaMove ⟨N + 1, poly, hp⟩ i (γ s) hδ⟩
  · -- A degenerate triangle: `γ s` lies on edge `i`, which it subdivides.
    have hne : poly i ≠ poly (finRotate (N + 1) i) := hp.hasNondegenerateEdges i
    rw [affineIndependent_iff_not_collinear_set, not_not] at hind
    obtain ⟨θ, hθ⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1
      (hind.mem_affineSpan_of_mem_of_ne (p₁ := poly i) (p₂ := poly (finRotate (N + 1) i))
        (p₃ := γ s) (by simp) (by simp) (by simp) hne)
    obtain ⟨φ, hφ⟩ := hF.mono (t i) ⟨hi0, by linarith⟩
    have mem (u : ℝ) (h₁ : t i ≤ u) (h₂ : u ≤ nextParam T t i) : u ∈ Icc (t i) (t i + 3 * δ) :=
      ⟨h₁, by linarith [hF.le_delta]⟩
    have h₁ := hφ (mem _ le_rfl hi.le) (mem _ hs.1.le hs.2.le) hs.1
    have h₂ := hφ (mem _ hs.1.le hs.2.le) (mem _ hi.le le_rfl) hs.2
    have hφθ := congrArg φ hθ
    rw [hvert, hnext, AffineMap.lineMap_apply_module] at hφθ
    simp only [map_add, map_smul, smul_eq_mul] at hφθ h₁ h₂
    have hθ' : θ ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
    have hc : poly.edgePath ℝ i θ = γ s := by rwa [edgePath]
    refine ⟨hc ▸ hp.insertVertex_edgePath i hθ', ?_⟩
    refine TauCeti.SimplePolygon.combinatoriallyEquivalent_subdivide ⟨N + 1, poly, hp⟩ i (γ s) ?_ _
    rw [edgeSet_eq_image_edgePath]
    exact ⟨θ, Ioo_subset_Icc_self hθ', hc⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Inserting the parameter `s` after `t i` inserts the vertex `γ s` after vertex `i`. -/
private theorem paramPolygon_insertNth (i : Fin (N + 1)) (s : ℝ) :
    paramPolygon γ (Fin.insertNth i.succ s t) = (paramPolygon γ t).insertVertex i (γ s) := by
  have : (paramPolygon γ (Fin.insertNth i.succ s t)).vertices =
      ((paramPolygon γ t).insertVertex i (γ s)).vertices := by
    rw [insertVertex_vertices]
    funext j
    induction j using Fin.succAboveCases i.succ <;> simp [paramPolygon]
  exact congrArg Polygon.mk this

/-- Inserting a parameter strictly inside a gap keeps a mesh. -/
private theorem IsMesh.insertNth (ht : IsMesh T h t) {i : Fin (N + 1)} {s : ℝ}
    (hs : s ∈ Ioo (t i) (nextParam T t i)) : IsMesh T h (Fin.insertNth i.succ s t) := by
  have hrange : range (Fin.insertNth i.succ s t) = insert s (range t) := Fin.range_insertNth _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_insertNth_iff]
    refine ⟨ht.strictMono, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
    · exact (ht.strictMono.monotone (Fin.castSucc_lt_succ_iff.1 hj)).trans_lt hs.1
    · exact hs.2.trans_le (ht.nextParam_le_of_lt (Fin.succ_le_castSucc_iff.1 hj))
  · rw [← Fin.succ_succAbove_zero i, Fin.insertNth_apply_succAbove, ht.zero]
  · have := hrange ▸ mem_range_self (Fin.last (N + 1))
    rcases this with e | ⟨k, e⟩
    · rw [e]
      exact hs.2.trans_le (ht.nextParam_le i)
    · rw [← e]
      exact (ht.strictMono.monotone (Fin.le_last k)).trans_lt ht.last_lt
  · rw [hrange]
    rintro x (rfl | hx)
    · exact ⟨_, insert_subset_insert (subset_insert _ _) (nextParam_mem i), hs.2,
        (ht.nextParam_le_add i).trans (by linarith [hs.1])⟩
    · obtain ⟨y, hy, hxy⟩ := ht.exists_lt_le x hx
      exact ⟨y, insert_subset_insert (subset_insert _ _) hy, hxy⟩

/-- A parameter in `[0, T)` which is not a parameter of the mesh lies strictly inside a gap. -/
private theorem IsMesh.exists_mem_Ioo (ht : IsMesh T h t) {a : ℝ} (ha : a ∈ Ico 0 T)
    (hat : a ∉ range t) : ∃ i, a ∈ Ioo (t i) (nextParam T t i) := by
  classical
  set S := Finset.univ.filter fun k ↦ t k ≤ a
  have hS : S.Nonempty := ⟨0, by simp [S, ht.zero, ha.1]⟩
  have hi := (Finset.mem_filter.1 (S.max'_mem hS)).2
  refine ⟨S.max' hS, hi.lt_of_ne fun e ↦ hat ⟨_, e⟩, ?_⟩
  unfold nextParam
  split_ifs with hl
  · exact ha.2
  · refine lt_of_not_ge fun hle ↦ ?_
    exact (S.le_max' _ (by simp [S, hle])).not_gt
      (Fin.lt_add_one_iff.2 (Fin.lt_last_iff_ne_last.2 hl))

/-- **Refining a fine inscribed polygon.** Adding finitely many parameters in `[0, T)` to a fine
mesh gives a fine mesh whose polygon is combinatorially equivalent to the original one. -/
private theorem FineMesh.exists_combinatoriallyEquivalent_union (hF : FineMesh γ T δ η h K)
    (A : Finset ℝ) (hA : ∀ a ∈ A, a ∈ Ico 0 T) (ht : IsMesh T h t)
    (hp : (paramPolygon γ t).IsSimple ℝ) :
    ∃ (N' : ℕ) (t' : Fin (N' + 1) → ℝ) (_ : IsMesh T h t') (hp' : (paramPolygon γ t').IsSimple ℝ),
      range t' = range t ∪ A ∧ TauCeti.SimplePolygon.CombinatoriallyEquivalent
        ⟨N + 1, paramPolygon γ t, hp⟩ ⟨N' + 1, paramPolygon γ t', hp'⟩ := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨N, t, ht, hp, by simp, .refl _⟩
  | insert a A haA ih =>
    obtain ⟨N', t', ht', hp', hr, he⟩ := ih fun b hb ↦ hA b (Finset.mem_insert_of_mem hb)
    have haT := hA a (Finset.mem_insert_self a A)
    rw [Finset.coe_insert, union_insert, ← hr]
    by_cases hat : a ∈ range t'
    · exact ⟨N', t', ht', hp', (insert_eq_of_mem hat).symm, he⟩
    obtain ⟨i, hi⟩ := ht'.exists_mem_Ioo haT hat
    obtain ⟨hq, he'⟩ := hF.exists_combinatoriallyEquivalent_insertVertex ht' hp' i hi
    refine ⟨N' + 1, Fin.insertNth i.succ a t', ht'.insertNth hi,
      (paramPolygon_insertNth i a).symm ▸ hq, Fin.range_insertNth _ _ _, he.trans ?_⟩
    convert he' using 2
    exact paramPolygon_insertNth i a

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The inscribed polygon with `N + 1` vertices is the polygon of the uniform mesh. -/
private theorem inscribed_eq_paramPolygon :
    inscribed γ T (N + 1) = paramPolygon γ fun k : Fin (N + 1) ↦ (k : ℝ) * (T / (N + 1 : ℕ)) :=
  (rfl)

/-- The uniform parameters `k * (T / (N + 1))` form a mesh of gap `T / (N + 1)`. -/
private theorem isMesh_uniform (hT : 0 < T) (hh : T / (N + 1 : ℕ) ≤ h) :
    IsMesh T h fun k : Fin (N + 1) ↦ (k : ℝ) * (T / (N + 1 : ℕ)) := by
  have hpos : 0 < T / (N + 1 : ℕ) := by positivity
  have hN : ((N + 1 : ℕ) : ℝ) * (T / (N + 1 : ℕ)) = T := by field_simp
  refine ⟨fun a b hab ↦ mul_lt_mul_of_pos_right (by exact_mod_cast hab) hpos, by simp, ?_, ?_⟩
  · have : ((Fin.last N : ℕ) : ℝ) * (T / (N + 1 : ℕ)) < ((N + 1 : ℕ) : ℝ) * (T / (N + 1 : ℕ)) :=
      mul_lt_mul_of_pos_right (by simp) hpos
    linarith
  · rintro _ ⟨k, rfl⟩
    refine ⟨((k : ℕ) + 1 : ℕ) * (T / (N + 1 : ℕ)), ?_, ?_, ?_⟩
    · by_cases hk : (k : ℕ) + 1 = N + 1
      · rw [hk, hN]
        exact mem_insert _ _
      · exact mem_insert_of_mem _ ⟨⟨k + 1, by omega⟩, by simp⟩
    · push_cast at hpos ⊢
      linarith
    · push_cast at hpos hh ⊢
      linarith


/-- **Fine inscribed polygons of one loop are combinatorially equivalent.** If a loop satisfies
`FineMesh` at mesh `h`, its inscribed polygons with `n` and with `m` vertices are combinatorially
equivalent as soon as `T / n ≤ h` and `T / m ≤ h`: both are refined, one vertex at a time, to the
polygon inscribed at the union of their parameters. -/
private theorem FineMesh.combinatoriallyEquivalent_inscribed (hF : FineMesh γ T δ η h K)
    (hT : 0 < T) {n m : ℕ} [NeZero n] [NeZero m] (hn : T / n ≤ h) (hm : T / m ≤ h)
    (hsn : (inscribed γ T n).IsSimple ℝ) (hsm : (inscribed γ T m).IsSimple ℝ) :
    TauCeti.SimplePolygon.CombinatoriallyEquivalent ⟨n, inscribed γ T n, hsn⟩
      ⟨m, inscribed γ T m, hsm⟩ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  have htn := isMesh_uniform hT hn
  have htm := isMesh_uniform hT hm
  generalize hPn : inscribed γ T (n + 1) = Pn at hsn ⊢
  generalize hPm : inscribed γ T (m + 1) = Pm at hsm ⊢
  rw [inscribed_eq_paramPolygon] at hPn hPm
  subst hPn hPm
  have mem {k : ℕ} {u : Fin (k + 1) → ℝ} (hu : IsMesh T h u) :
      ∀ a ∈ Finset.univ.image u, a ∈ Ico 0 T := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]
    exact fun j ↦ ⟨hu.nonneg j, (hu.strictMono.monotone (Fin.le_last j)).trans_lt hu.last_lt⟩
  -- Refine each mesh to the union of the two.
  obtain ⟨N₁, t₁, ht₁, hp₁, hr₁, he₁⟩ :=
    hF.exists_combinatoriallyEquivalent_union _ (mem htm) htn hsn
  obtain ⟨N₂, t₂, ht₂, hp₂, hr₂, he₂⟩ :=
    hF.exists_combinatoriallyEquivalent_union _ (mem htn) htm hsm
  simp only [Finset.coe_image, Finset.coe_univ, image_univ] at hr₁ hr₂
  have hr : range t₁ = range t₂ := by rw [hr₁, hr₂, union_comm]
  -- The two refinements have the same parameters, hence the same polygon.
  obtain rfl : N₁ = N₂ := by
    have := Nat.card_range_of_injective ht₁.strictMono.injective
    rw [hr, Nat.card_range_of_injective ht₂.strictMono.injective] at this
    simpa using this.symm
  obtain rfl := (ht₁.strictMono.range_inj_of_wellFoundedLT ht₂.strictMono).1 hr
  exact he₁.trans he₂.symm

/-- **Fine inscribed polygons of a `C¹` loop are combinatorially equivalent.** Let `γ : ℝ → E` be
a `C¹` curve of period `T > 0` in a real normed space, with nowhere vanishing derivative, injective
modulo `T`. Then for all large `n` and `m` the inscribed polygons with `n` and with `m` vertices,
which are simple by `Polygon.eventually_isSimple_inscribed`, are related by Δ-moves and
subdivisions of edges: both are refined, one vertex at a time, to the polygon inscribed at the
union of their parameters. -/
theorem exists_combinatoriallyEquivalent_inscribed (hT : 0 < T) (hγ : ContDiff ℝ 1 γ)
    (hper : Periodic γ T) (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T)
    (hderiv : ∀ t, deriv γ t ≠ 0) :
    ∃ N, ∀ n m : ℕ, ∀ [NeZero n] [NeZero m], N ≤ n → N ≤ m →
      ∀ (hn : (inscribed γ T n).IsSimple ℝ) (hm : (inscribed γ T m).IsSimple ℝ),
        TauCeti.SimplePolygon.CombinatoriallyEquivalent ⟨n, inscribed γ T n, hn⟩
          ⟨m, inscribed γ T m, hm⟩ := by
  obtain ⟨δ, η, h, K, hh, hF⟩ := exists_fineMesh hT hγ hper hinj hderiv
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_const_div_atTop_nhds_zero_nat T).eventually (ge_mem_nhds hh))
  exact ⟨N, fun n m _ _ hn hm ↦ hF.combinatoriallyEquivalent_inscribed hT (hN n hn) (hN m hm)⟩

end Refinement

/-! ### Inscribed polygons along an isotopy -/

section Isotopy

open TauCeti.SimplePolygon (CombinatoriallyEquivalent combinatoriallyEquivalent_rotate)

/-- The time `s ↦ t + (t' - t) (1 - cos (2π s / h)) / 2`, oscillating between `t` and `t'` with
period `h`: it is `t` at the multiples of `h` and `t'` halfway between them. -/
private def cosTime (t t' h s : ℝ) : ℝ :=
  t + (t' - t) * ((1 - Real.cos (2 * Real.pi * s / h)) / 2)

private theorem cosTime_natCast_mul (t t' : ℝ) {h : ℝ} (hh : h ≠ 0) (k : ℕ) :
    cosTime t t' h (k * h) = t := by
  have e : 2 * Real.pi * (k * h) / h = k * (2 * Real.pi) := by field_simp
  rw [cosTime, e, Real.cos_nat_mul_two_pi]
  ring

private theorem cosTime_natCast_mul_add_half (t t' : ℝ) {h : ℝ} (hh : h ≠ 0) (k : ℕ) :
    cosTime t t' h (k * h + h / 2) = t' := by
  have e : 2 * Real.pi * (k * h + h / 2) / h = k * (2 * Real.pi) + Real.pi := by
    field_simp
  rw [cosTime, e, Real.cos_nat_mul_two_pi_add_pi]
  ring

private theorem periodic_cosTime (t t' : ℝ) {h : ℝ} (hh : h ≠ 0) : Periodic (cosTime t t' h) h :=
  fun s ↦ by
    have e : 2 * Real.pi * (s + h) / h = 2 * Real.pi * s / h + 2 * Real.pi := by
      field_simp
    rw [cosTime, cosTime, e, Real.cos_add_two_pi]

private theorem cosTime_mem_Icc {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (h s : ℝ) : cosTime t t' h s ∈ Icc (0 : ℝ) 1 := by
  have h₁ := Real.neg_one_le_cos (2 * Real.pi * s / h)
  have h₂ := Real.cos_le_one (2 * Real.pi * s / h)
  have hw₀ : 0 ≤ (1 - Real.cos (2 * Real.pi * s / h)) / 2 := by linarith
  have hw₁ : (1 - Real.cos (2 * Real.pi * s / h)) / 2 ≤ 1 := by linarith
  rw [cosTime]
  constructor <;> nlinarith [ht.1, ht.2, ht'.1, ht'.2]

private theorem cosTime_sub_cosTime (t t' h x y : ℝ) :
    cosTime t t' h x - cosTime t t' h y =
      (t' - t) / 2 * (Real.cos (2 * Real.pi * y / h) - Real.cos (2 * Real.pi * x / h)) := by
  rw [cosTime, cosTime]
  ring

/-- The oscillating time is `|t' - t| π / h`-Lipschitz. -/
private theorem abs_cosTime_sub_le {t t' h : ℝ} (hh : 0 < h) (x y : ℝ) :
    |cosTime t t' h x - cosTime t t' h y| ≤ |t' - t| * Real.pi / h * |x - y| := by
  have hcos := Real.abs_cos_sub_cos_le (2 * Real.pi * y / h) (2 * Real.pi * x / h)
  have harg : 2 * Real.pi * y / h - 2 * Real.pi * x / h = 2 * Real.pi / h * (y - x) := by ring
  rw [harg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / h), abs_sub_comm y x] at hcos
  rw [cosTime_sub_cosTime, abs_mul, abs_div, abs_two]
  calc |t' - t| / 2 * |Real.cos (2 * Real.pi * y / h) - Real.cos (2 * Real.pi * x / h)|
      ≤ |t' - t| / 2 * (2 * Real.pi / h * |x - y|) := by gcongr
    _ = |t' - t| * Real.pi / h * |x - y| := by ring

/-- The oscillating time varies by at most `|t' - t|`. -/
private theorem abs_cosTime_sub_le_abs (t t' h x y : ℝ) :
    |cosTime t t' h x - cosTime t t' h y| ≤ |t' - t| := by
  have h₁ := Real.abs_cos_le_one (2 * Real.pi * y / h)
  have h₂ := Real.abs_cos_le_one (2 * Real.pi * x / h)
  have hcos : |Real.cos (2 * Real.pi * y / h) - Real.cos (2 * Real.pi * x / h)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  rw [cosTime_sub_cosTime, abs_mul, abs_div, abs_two]
  calc |t' - t| / 2 * |Real.cos (2 * Real.pi * y / h) - Real.cos (2 * Real.pi * x / h)|
      ≤ |t' - t| / 2 * 2 := by gcongr
    _ = |t' - t| := by ring

/-- **Half a step later.** If a loop `γ` and its shift `γ (· + T / n / 2)` by half a step satisfy
`FineMesh` at mesh `T / n`, their inscribed polygons with `n` vertices are combinatorially
equivalent: refine to `2 n` vertices, relabel by a rotation and coarsen. -/
private theorem FineMesh.combinatoriallyEquivalent_inscribed_shift {n : ℕ} [NeZero n]
    (hF : FineMesh γ T δ η (T / n) K)
    (hF₂ : FineMesh (fun s ↦ γ (s + T / n / 2)) T δ η (T / n) K) (hT : 0 < T)
    (hp : (inscribed γ T n).IsSimple ℝ)
    (hp₂ : (inscribed (fun s ↦ γ (s + T / n / 2)) T n).IsSimple ℝ) :
    CombinatoriallyEquivalent ⟨n, inscribed γ T n, hp⟩
      ⟨n, inscribed (fun s ↦ γ (s + T / n / 2)) T n, hp₂⟩ := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  have h2n : T / ((2 * n : ℕ) : ℝ) = T / n / 2 := by
    rw [Nat.cast_mul, Nat.cast_two]
    field_simp
  have h2nh : T / ((2 * n : ℕ) : ℝ) ≤ T / n := by
    rw [h2n]
    linarith [div_pos hT hn₀]
  have e : (inscribed γ T (2 * n)).rotate = inscribed (fun s ↦ γ (s + T / n / 2)) T (2 * n) := by
    rw [rotate_inscribed hF.periodic, h2n]
  have q : CombinatoriallyEquivalent ⟨2 * n, inscribed γ T (2 * n), hF.isSimple_inscribed hT h2nh⟩
      ⟨2 * n, inscribed (fun s ↦ γ (s + T / n / 2)) T (2 * n),
        hF₂.isSimple_inscribed hT h2nh⟩ := by
    simp only [← e]
    exact combinatoriallyEquivalent_rotate _
  exact (hF.combinatoriallyEquivalent_inscribed hT le_rfl h2nh _ _).trans
    (q.trans (hF₂.combinatoriallyEquivalent_inscribed hT h2nh le_rfl _ _))

/-- **One step of an isotopy.** For times `t, t' ∈ [0, 1]` close compared with the mesh
`h = T / n`, the inscribed polygons of `Γ t` and of `Γ t'` with `n` vertices are combinatorially
equivalent. -/
private theorem FineFamily.combinatoriallyEquivalent_inscribed {Γ : ℝ → ℝ → E} {lam ρ : ℝ}
    (hF : FineFamily Γ T δ η lam ρ K) (hT : 0 < T) {n : ℕ} [NeZero n] (hδ : T / n ≤ δ)
    (hη : 2 * K * (T / n) < η) {t t' : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1) (hρ : |t' - t| ≤ ρ)
    (hlam : |t' - t| * Real.pi / (T / n) ≤ lam) (hp : (inscribed (Γ t) T n).IsSimple ℝ)
    (hp' : (inscribed (Γ t') T n).IsSimple ℝ) :
    TauCeti.SimplePolygon.CombinatoriallyEquivalent ⟨n, inscribed (Γ t) T n, hp⟩
      ⟨n, inscribed (Γ t') T n, hp'⟩ := by
  -- The hybrid loop `α s = Γ (τ s) s`, whose time `τ` oscillates between `t` and `t'` with period
  -- `h`, passes through the vertices `Γ t (k h)` and, halfway between them, through the points
  -- `Γ t' (k h + h / 2)`. Refining in `α`, in `α` started half a step later, and in `Γ t'`
  -- started half a step later joins the two polygons.
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set h := T / n with hh_def
  have hh : 0 < h := div_pos hT hn₀
  have hnh : (n : ℝ) * h = T := by rw [hh_def]; field_simp
  have hhT : h ≤ T := div_le_self hT.le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
  have hc₀ : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hc₂ : h / 2 ∈ Icc 0 T := ⟨by positivity, by linarith⟩
  -- The oscillating time and its two loops `α` and `α₂ = α (· + h / 2)`.
  set τ := cosTime t t' h with hτ_def
  have hτper : Periodic τ T := hnh ▸ (periodic_cosTime t t' hh.ne').nat_mul n
  have hτI (s : ℝ) : τ s ∈ Icc (0 : ℝ) 1 := cosTime_mem_Icc ht ht' h s
  have hτlip (x y : ℝ) : |τ x - τ y| ≤ lam * |x - y| :=
    (abs_cosTime_sub_le hh x y).trans (by gcongr)
  have hτvar (x y : ℝ) : |τ x - τ y| ≤ ρ := (abs_cosTime_sub_le_abs t t' h x y).trans hρ
  have hFα : FineMesh (fun s ↦ Γ (τ s) s) T δ η h K :=
    hF.fineMesh (fun s ↦ by rw [add_zero]) hc₀ hτper hτI hτlip hτvar hδ hη
  have hFα₂ : FineMesh (fun s ↦ Γ (τ (s + h / 2)) (s + h / 2)) T δ η h K :=
    hF.fineMesh (τ := fun s ↦ τ (s + h / 2)) (fun s ↦ rfl) hc₂
      (fun s ↦ by dsimp only; rw [add_right_comm, hτper]) (fun s ↦ hτI _)
      (fun x y ↦ by simpa using hτlip (x + h / 2) (y + h / 2)) (fun x y ↦ hτvar _ _) hδ hη
  have hFβ₂ : FineMesh (fun s ↦ Γ t' (s + h / 2)) T δ η h K :=
    hF.fineMesh_const (fun s ↦ rfl) ht' hc₂ hδ hη
  have hFβ : FineMesh (Γ t') T δ η h K := hF.fineMesh_const (fun s ↦ by rw [add_zero]) ht' hc₀ hδ hη
  -- The polygons met along the way.
  have e₁ : inscribed (Γ t) T n = inscribed (fun s ↦ Γ (τ s) s) T n :=
    inscribed_congr fun k ↦ by simp only [← hh_def, hτ_def, cosTime_natCast_mul t t' hh.ne']
  have e₅ : inscribed (fun s ↦ Γ (τ (s + h / 2)) (s + h / 2)) T n =
      inscribed (fun s ↦ Γ t' (s + h / 2)) T n :=
    inscribed_congr fun k ↦ by
      simp only [← hh_def, hτ_def, cosTime_natCast_mul_add_half t t' hh.ne']
  -- The chain of equivalences, with explicit endpoints: `n`-gon of `Γ t` = `n`-gon of `α`,
  -- shifted by half a step to the `n`-gon of `α₂` = `n`-gon of `β₂ = Γ t' (· + h / 2)`, shifted
  -- back by half a step to the `n`-gon of `Γ t'`.
  have q₁ : CombinatoriallyEquivalent ⟨n, inscribed (Γ t) T n, hp⟩
      ⟨n, inscribed (fun s ↦ Γ (τ s) s) T n, hFα.isSimple_inscribed hT le_rfl⟩ := by
    simp only [e₁]
    exact .refl _
  have q₂ := hFα.combinatoriallyEquivalent_inscribed_shift hFα₂ hT
    (hFα.isSimple_inscribed hT le_rfl) (hFα₂.isSimple_inscribed hT le_rfl)
  have q₅ : CombinatoriallyEquivalent
      ⟨n, inscribed (fun s ↦ Γ (τ (s + h / 2)) (s + h / 2)) T n,
        hFα₂.isSimple_inscribed hT le_rfl⟩
      ⟨n, inscribed (fun s ↦ Γ t' (s + h / 2)) T n, hFβ₂.isSimple_inscribed hT le_rfl⟩ := by
    simp only [e₅]
    exact .refl _
  have q₆ := (hFβ.combinatoriallyEquivalent_inscribed_shift hFβ₂ hT hp'
    (hFβ₂.isSimple_inscribed hT le_rfl)).symm
  exact q₁.trans <| q₂.trans <| q₅.trans q₆

/-- **Fine inscribed polygons are invariant under isotopy.** Let `Γ : ℝ → ℝ → E` be a family of
loops of period `T > 0` in a real normed space, jointly `C¹` in the time `t` and the loop
parameter, such that each loop `Γ t` with `t ∈ [0, 1]` is periodic, injective modulo `T` and has
nowhere vanishing derivative. Then for all large `n` and `m` the inscribed polygons of `Γ 0` with
`n` vertices and of `Γ 1` with `m` vertices, which are simple by
`Polygon.eventually_isSimple_inscribed`, are related by Δ-moves and subdivisions of edges. So
isotopic embedded `C¹` loops determine the same polygonal knot up to combinatorial equivalence. -/
theorem exists_combinatoriallyEquivalent_inscribed_of_isotopy {Γ : ℝ → ℝ → E} (hT : 0 < T)
    (hΓ : ContDiff ℝ 1 (uncurry Γ)) (hper : ∀ t ∈ Icc (0 : ℝ) 1, Periodic (Γ t) T)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s s', Γ t s = Γ t s' → ∃ k : ℤ, s = s' + k * T)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s, deriv (Γ t) s ≠ 0) :
    ∃ N, ∀ n m : ℕ, ∀ [NeZero n] [NeZero m], N ≤ n → N ≤ m →
      ∀ (hn : (inscribed (Γ 0) T n).IsSimple ℝ) (hm : (inscribed (Γ 1) T m).IsSimple ℝ),
        TauCeti.SimplePolygon.CombinatoriallyEquivalent ⟨n, inscribed (Γ 0) T n, hn⟩
          ⟨m, inscribed (Γ 1) T m, hm⟩ := by
  obtain ⟨δ, η, lam, ρ, K, hδ, hη, hlam, hρ, hF⟩ := exists_fineFamily hΓ hper hinj hderiv
  -- A mesh `h₀` below which every loop of the family is fine.
  set h₀ := min δ (η / (2 * K + 1)) with hh₀_def
  have hh₀ : 0 < h₀ := lt_min hδ (by positivity)
  have hfine {h : ℝ} (hh : h ≤ h₀) : h ≤ δ ∧ 2 * K * h < η := by
    refine ⟨hh.trans (min_le_left _ _), ?_⟩
    have h₁ : h₀ * (2 * K + 1) ≤ η := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    have h₂ : 2 * K * h ≤ 2 * K * h₀ := by gcongr
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_const_div_atTop_nhds_zero_nat T).eventually (ge_mem_nhds hh₀))
  refine ⟨N, fun n m _ _ hn hm hsn hsm ↦ ?_⟩
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨hnδ, hnη⟩ := hfine (hN n hn)
  have hsimple (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (inscribed (Γ t) T n).IsSimple ℝ :=
    (hF.fineMesh_const (fun s ↦ by rw [add_zero]) ht ⟨le_rfl, hT.le⟩ hnδ hnη).isSimple_inscribed
      hT le_rfl
  -- Steps of length `1 / (M + 1)`, small compared with `T / n`.
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (lt_min hρ (by positivity :
    0 < lam * (T / n) / Real.pi))
  have hM₀ : (0 : ℝ) < M + 1 := by positivity
  have hmem {i : ℕ} (hi : i ≤ M + 1) : (i : ℝ) / (M + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hM₀).2 (by exact_mod_cast hi)⟩
  have hstep (i : ℕ) : |((i + 1 : ℕ) : ℝ) / (M + 1) - i / (M + 1)| = 1 / (M + 1) := by
    rw [Nat.cast_add_one, ← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
  have key (i : ℕ) (hi : i ≤ M + 1) :
      TauCeti.SimplePolygon.CombinatoriallyEquivalent ⟨n, inscribed (Γ 0) T n, hsn⟩
        ⟨n, inscribed (Γ ((i : ℝ) / (M + 1))) T n, hsimple _ (hmem hi)⟩ := by
    induction i with
    | zero => simp only [Nat.cast_zero, zero_div]; rfl
    | succ i ih =>
      refine (ih (by omega)).trans (hF.combinatoriallyEquivalent_inscribed hT hnδ hnη
        (hmem (by omega)) (hmem hi) ?_ ?_ _ _)
      · rw [hstep]
        exact hM.le.trans (min_le_left _ _)
      · rw [hstep, div_le_iff₀ (div_pos hT hn₀)]
        have := hM.trans_le (min_le_right _ _)
        rw [lt_div_iff₀ Real.pi_pos] at this
        exact this.le
  have hF₁ := hF.fineMesh_const (t := 1) (c := 0) (fun s ↦ by rw [add_zero]) ⟨zero_le_one, le_rfl⟩
    ⟨le_rfl, hT.le⟩ (hfine le_rfl).1 (hfine le_rfl).2
  -- The last step reaches time `((M + 1 : ℕ) : ℝ) / (M + 1) = 1`.
  have hlast : (((M + 1 : ℕ) : ℝ) / (M + 1)) = 1 := by
    rw [Nat.cast_add_one, div_self hM₀.ne']
  have q₁ := key (M + 1) le_rfl
  simp only [hlast] at q₁
  exact q₁.trans (hF₁.combinatoriallyEquivalent_inscribed hT (hN n hn) (hN m hm) _ hsm)

end Isotopy

/-! ### Straightening a `C¹` loop onto an inscribed polygon -/

section AmbientIsotopy

/-- Distinct steps `j ≠ k` of a uniform mesh `h = T / n` stay distinct modulo the period `n h`: the
interval `[j h + m n h, j h + m n h + h]` and `[k h, k h + h]` overlap at most at an endpoint. -/
private theorem add_mul_add_h_le_or_le_of_ne {n j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k)
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    j * h + m * (n * h) + h ≤ k * h ∨ k * h + h ≤ j * h + m * (n * h) := by
  have hne : (j : ℤ) + m * n ≠ k := fun he ↦ hjk <| by
    have h0 := Int.eq_zero_of_abs_lt_dvd (m := n) (x := k - j) ⟨m, by rw [← he]; ring⟩
      (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
    omega
  rcases hne.lt_or_gt with hlt | hlt
  · left
    have : ((j : ℝ) + m * n + 1) * h ≤ k * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hh.le
    linarith
  · right
    have : ((k : ℝ) + 1) * h ≤ (j + m * n) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hh.le
    linarith

/-- A piece of a curve over `[c, c + h]`, or its chord, lying in the window `[k h - 2 δ, k h + 2 δ]`
on which `φ ∘ γ` is strictly increasing and entirely on one side of `[k h, k h + h]`, does not meet
the region where `φ` is strictly between its values at `γ (k h)` and `γ (k h + h)`. -/
private theorem notMem_between_of_le_or_le {φ : StrongDual ℝ E} {k : ℕ} {h δ c : ℝ}
    (hφ : StrictMonoOn (fun t ↦ φ (γ t)) (Icc (k * h - 2 * δ) (k * h + 2 * δ))) (hh : 0 < h)
    (hhδ : h ≤ δ) (hc : k * h - 2 * δ ≤ c) (hnear : c ≤ k * h + δ)
    (hle : c + h ≤ k * h ∨ k * h + h ≤ c) {x : E}
    (hx : x ∈ γ '' Icc c (c + h) ∪ segment ℝ (γ c) (γ (c + h))) :
    ¬ (φ (γ (k * h)) < φ x ∧ φ x < φ (γ (k * h + h))) := by
  rintro ⟨h₁, h₂⟩
  have hW : Icc c (c + h) ⊆ Icc (k * h - 2 * δ) (k * h + 2 * δ) :=
    Icc_subset_Icc hc (by linarith)
  have hk₀ : k * h ∈ Icc (k * h - 2 * δ) (k * h + 2 * δ) := ⟨by linarith, by linarith⟩
  have hk₁ : k * h + h ∈ Icc (k * h - 2 * δ) (k * h + 2 * δ) := ⟨by linarith, by linarith⟩
  have hc₀ : c ∈ Icc c (c + h) := left_mem_Icc.2 (by linarith)
  have hc₁ : c + h ∈ Icc c (c + h) := right_mem_Icc.2 (by linarith)
  rcases hle with hle | hle
  · have hbelow : ∀ s ∈ Icc c (c + h), φ (γ s) ≤ φ (γ (k * h)) := fun s hs ↦
      hφ.monotoneOn (hW hs) hk₀ (by linarith [hs.2])
    have : φ x ≤ φ (γ (k * h)) := by
      rcases hx with ⟨s, hs, rfl⟩ | hx
      · exact hbelow s hs
      · exact (convex_halfSpace_le φ.toLinearMap.isLinear _).segment_subset
          (hbelow c hc₀) (hbelow (c + h) hc₁) hx
    linarith
  · have habove : ∀ s ∈ Icc c (c + h), φ (γ (k * h + h)) ≤ φ (γ s) := fun s hs ↦
      hφ.monotoneOn hk₁ (hW hs) (by linarith [hs.1])
    have : φ (γ (k * h + h)) ≤ φ x := by
      rcases hx with ⟨s, hs, rfl⟩ | hx
      · exact habove s hs
      · exact (convex_halfSpace_ge φ.toLinearMap.isLinear _).segment_subset
          (habove c hc₀) (habove (c + h) hc₁) hx
    linarith

/-- While the arc of `γ` over `[k h, k h + h]` is straightened, the other pieces stay put: for a
uniform mesh `h = T / n` of a `T`-periodic curve, fine compared with the window `4 δ` on which
`φ ∘ γ` is strictly increasing and with the separation constant `η` of `γ`, no point of the arc
or of the chord over another step `[j h, j h + h]` lies in the region moved by
`TauCeti.AmbientIsotopy.exists_final_image_eq_segment`. -/
private theorem notMem_straightenRegion {n j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k)
    (hT : 0 < T) (hper : Periodic γ T) {h δ η : ℝ} {K : NNReal} (hh : 0 < h) (hnh : n * h = T)
    (hhδ : h ≤ δ) (hKη : 8 * (K * h) ≤ η) (hK : LipschitzOnWith K γ (Icc 0 T))
    (hsep : ∀ a ∈ Icc 0 T, ∀ d ∈ Icc δ (T - δ), η ≤ dist (γ (a + d)) (γ a))
    {φ : StrongDual ℝ E}
    (hφ : StrictMonoOn (fun t ↦ φ (γ t)) (Icc (k * h - 2 * δ) (k * h + 2 * δ))) {x : E}
    (hx : x ∈ γ '' Icc (j * h) (j * h + h) ∪ segment ℝ (γ (j * h)) (γ (j * h + h))) :
    ¬ (φ (γ (k * h)) < φ x ∧ φ x < φ (γ (k * h + h)) ∧ ‖x - γ (k * h)‖ < 7 * (K * h)) := by
  rintro ⟨h₁, h₂, h₃⟩
  have hK0 : 0 ≤ (K : ℝ) * h := mul_nonneg K.2 hh.le
  have hjT : j * h + h ≤ T := by
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    nlinarith
  have hkT : k * h + h ≤ T := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    nlinarith
  -- Shift the parameters `[j h, j h + h]` of the piece by a period into
  -- `[k h - 2 δ, k h - 2 δ + T)`.
  set m : ℤ := -toIcoDiv hT (k * h - 2 * δ) (j * h) with hm
  set c := j * h + m * (n * h) with hc
  have hc_mem : c ∈ Ico (k * h - 2 * δ) (k * h - 2 * δ + T) := by
    have heq : toIcoMod hT (k * h - 2 * δ) (j * h) = c := by
      rw [toIcoMod, zsmul_eq_mul, hc, hnh, hm, Int.cast_neg]
      ring
    exact heq ▸ toIcoMod_mem_Ico hT (k * h - 2 * δ) (j * h)
  have hshift (s : ℝ) : γ (s + m * (n * h)) = γ s := by rw [hnh]; exact (hper.int_mul m) s
  have hx' : x ∈ γ '' Icc c (c + h) ∪ segment ℝ (γ c) (γ (c + h)) := by
    rcases hx with ⟨s, hs, rfl⟩ | hx
    · exact Or.inl ⟨s + m * (n * h), ⟨by linarith [hs.1], by linarith [hs.2]⟩, hshift s⟩
    · right
      rwa [hc, hshift, add_right_comm, hshift]
  rcases le_or_gt c (k * h + δ) with hnear | hfar
  · -- The piece lies in the window, entirely on one side of the arc being straightened.
    -- Distinct steps `j ≠ k < n` stay distinct modulo `n`, so the shifted parameter interval
    -- `[c, c + h]` and `[k h, k h + h]` overlap at most at an endpoint.
    exact notMem_between_of_le_or_le hφ hh hhδ hc_mem.1 hnear
      (add_mul_add_h_le_or_le_of_ne hj hk hjk hh m) hx' ⟨h₁, h₂⟩
  · -- The piece is far from the arc being straightened.
    have hfar' : ∀ s ∈ Icc c (c + h), η ≤ ‖γ s - γ (k * h)‖ := fun s hs ↦ by
      have := hsep (k * h) ⟨by positivity, by linarith⟩ (s - k * h)
        ⟨by linarith [hs.1], by linarith [hs.2, hc_mem.2]⟩
      rwa [add_sub_cancel, dist_eq_norm] at this
    rcases hx' with ⟨s, hs, rfl⟩ | hx'
    · linarith [hfar' s hs]
    · have hxc : ‖x - γ c‖ ≤ K * h := by
        have h1 := segment_subset_closedBall_left (γ c) (γ (c + h)) hx'
        rw [Metric.mem_closedBall, dist_eq_norm, dist_comm, dist_eq_norm, hc, hshift,
          add_right_comm, hshift] at h1
        have h2 := hK.dist_le_mul (j * h + h) ⟨by positivity, hjT⟩ (j * h)
          ⟨by positivity, by linarith⟩
        rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, Real.norm_of_nonneg hh.le] at h2
        rw [hc, hshift]
        linarith
      have := hfar' c (left_mem_Icc.2 (by linarith))
      have := norm_sub_le_norm_sub_add_norm_sub (γ c) x (γ (k * h))
      rw [norm_sub_rev (γ c) x] at this
      linarith

/-- Straightening the arc of a `T`-periodic curve `γ` over the step `[k h, k h + h]` of a uniform
mesh `h = T / n` carries the curve made of the chords over the first `k` steps and of the arcs over
the remaining ones onto the one with `k + 1` chords. -/
private theorem exists_ambientIsotopy_final_image_step {n k : ℕ} (hk : k < n) (hT : 0 < T)
    (hγ : Continuous γ) (hper : Periodic γ T) {h δ η : ℝ} {K : NNReal} (hh : 0 < h)
    (hnh : n * h = T) (hhδ : h ≤ δ) (hδT : 2 * δ ≤ T) (hKη : 8 * (K * h) ≤ η)
    (hmono : ∀ a ∈ Icc (-T) T, ∃ φ : StrongDual ℝ E,
      StrictMonoOn (fun t ↦ φ (γ t)) (Icc a (a + 4 * δ)))
    (hK : LipschitzOnWith K γ (Icc 0 T))
    (hsep : ∀ a ∈ Icc 0 T, ∀ d ∈ Icc δ (T - δ), η ≤ dist (γ (a + d)) (γ a)) :
    ∃ Ψ : TauCeti.AmbientIsotopy E,
      Ψ.final '' {x | ∃ j < n, (j < k ∧ x ∈ segment ℝ (γ (j * h)) (γ (j * h + h))) ∨
        (k ≤ j ∧ x ∈ γ '' Icc (j * h) (j * h + h))} =
      {x | ∃ j < n, (j < k + 1 ∧ x ∈ segment ℝ (γ (j * h)) (γ (j * h + h))) ∨
        (k + 1 ≤ j ∧ x ∈ γ '' Icc (j * h) (j * h + h))} := by
  have hkT : k * h + h ≤ T := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    nlinarith
  have hk0 : 0 ≤ k * h := by positivity
  obtain ⟨φ, hφ⟩ := hmono (k * h - 2 * δ) ⟨by linarith, by linarith⟩
  have hφ' : StrictMonoOn (fun t ↦ φ (γ t)) (Icc (k * h - 2 * δ) (k * h + 2 * δ)) :=
    hφ.mono (Icc_subset_Icc le_rfl (by linarith))
  obtain ⟨Ψ, himg, hsupp⟩ := TauCeti.AmbientIsotopy.exists_final_image_eq_segment
    (by linarith : k * h < k * h + h) hγ.continuousOn
    (hφ'.mono (Icc_subset_Icc (by linarith) (by linarith))) (D := K * h) fun s hs ↦ by
      have := hK.dist_le_mul s ⟨by linarith [hs.1], by linarith [hs.2]⟩ (k * h) ⟨hk0, by linarith⟩
      rw [dist_eq_norm, dist_eq_norm, Real.norm_of_nonneg (by linarith [hs.1])] at this
      exact this.trans (by gcongr; linarith [hs.2])
  have hfix (j : ℕ) (hj : j < n) (hjk : j ≠ k) (x : E)
      (hx : x ∈ γ '' Icc (j * h) (j * h + h) ∪ segment ℝ (γ (j * h)) (γ (j * h + h))) :
      Ψ.final x = x := by
    by_contra hne
    exact notMem_straightenRegion hj hk hjk hT hper hh hnh hhδ hKη hK hsep hφ' hx
      (hsupp 1 x (by rwa [← TauCeti.AmbientIsotopy.final_apply]))
  refine ⟨Ψ, ?_⟩
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨x, ⟨j, hj, hx⟩, rfl⟩
    rcases eq_or_ne j k with rfl | hjk
    · rcases hx with ⟨hjj, -⟩ | ⟨-, hx⟩
      · exact absurd hjj (lt_irrefl j)
      · exact ⟨j, hj, Or.inl ⟨j.lt_succ_self, himg ▸ mem_image_of_mem _ hx⟩⟩
    · rcases hx with ⟨hjk', hx⟩ | ⟨hjk', hx⟩
      · rw [hfix j hj hjk x (Or.inr hx)]
        exact ⟨j, hj, Or.inl ⟨by omega, hx⟩⟩
      · rw [hfix j hj hjk x (Or.inl hx)]
        exact ⟨j, hj, Or.inr ⟨by omega, hx⟩⟩
  · rintro ⟨j, hj, hy⟩
    rcases eq_or_ne j k with rfl | hjk
    · rcases hy with ⟨-, hy⟩ | ⟨hjj, -⟩
      · rw [← himg] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨x, ⟨j, hj, Or.inr ⟨le_rfl, hx⟩⟩, rfl⟩
      · omega
    · rcases hy with ⟨hjk', hy⟩ | ⟨hjk', hy⟩
      · exact ⟨y, ⟨j, hj, Or.inl ⟨by omega, hy⟩⟩, hfix j hj hjk y (Or.inr hy)⟩
      · exact ⟨y, ⟨j, hj, Or.inr ⟨by omega, hy⟩⟩, hfix j hj hjk y (Or.inl hy)⟩

/-- The inscribed polygon with `n` vertices of a continuous `T`-periodic curve `γ` is ambient
isotopic to `γ`, provided the mesh `T / n` is fine compared with the window `4 δ` on which some
`φ ∘ γ` is strictly increasing, with the separation constant `η` of `γ` and with a Lipschitz
constant `K` of `γ`. The arcs of `γ` over the steps of the mesh are straightened onto their chords
one at a time. -/
private theorem exists_ambientIsotopy_image_inscribed_of_mesh {n : ℕ} (hn : 0 < n) (hT : 0 < T)
    (hγ : Continuous γ) (hper : Periodic γ T) {δ η : ℝ} {K : NNReal} (hhδ : T / n ≤ δ)
    (hδT : 2 * δ ≤ T) (hKη : 8 * (K * (T / n)) ≤ η)
    (hmono : ∀ a ∈ Icc (-T) T, ∃ φ : StrongDual ℝ E,
      StrictMonoOn (fun t ↦ φ (γ t)) (Icc a (a + 4 * δ)))
    (hK : LipschitzOnWith K γ (Icc 0 T))
    (hsep : ∀ a ∈ Icc 0 T, ∀ d ∈ Icc δ (T - δ), η ≤ dist (γ (a + d)) (γ a)) :
    ∃ Φ : TauCeti.AmbientIsotopy E, Φ.final '' range γ = (inscribed γ T n).boundary ℝ := by
  set h := T / n with hh_def
  have hh : 0 < h := by positivity
  have hnh : n * h = T := by rw [hh_def]; field_simp
  -- After straightening the arcs over the first `k` steps, the curve consists of the chords over
  -- these steps and of the arcs over the remaining ones.
  let C (k : ℕ) : Set E := {x | ∃ j < n, (j < k ∧ x ∈ segment ℝ (γ (j * h)) (γ (j * h + h))) ∨
    (k ≤ j ∧ x ∈ γ '' Icc (j * h) (j * h + h))}
  have hC0 : range γ = C 0 := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨t, rfl⟩
      have hs := toIcoMod_mem_Ico hT 0 t
      rw [zero_add] at hs
      have hγs : γ (toIcoMod hT 0 t) = γ t := by
        rw [toIcoMod]; exact hper.sub_zsmul_eq _
      set s := toIcoMod hT 0 t
      have hs₀ : 0 ≤ s / h := div_nonneg hs.1 hh.le
      refine ⟨⌊s / h⌋₊, (Nat.floor_lt hs₀).2 ?_, Or.inr ⟨Nat.zero_le _, s, ⟨?_, ?_⟩, hγs⟩⟩
      · rw [div_lt_iff₀ hh, hnh]; exact hs.2
      · exact (le_div_iff₀ hh).1 (Nat.floor_le hs₀)
      · have := Nat.lt_floor_add_one (s / h)
        rw [div_lt_iff₀ hh] at this
        linarith
    · rintro ⟨j, -, ⟨hj, -⟩ | ⟨-, s, -, rfl⟩⟩
      · exact absurd hj (Nat.not_lt_zero j)
      · exact mem_range_self s
  have hCn : C n = (inscribed γ T n).boundary ℝ := by
    ext x
    simp only [C, boundary, mem_iUnion, edgeSet_inscribed hper, mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨j, hj, ⟨-, hx⟩ | ⟨hj', -⟩⟩
      · exact ⟨⟨j, hj⟩, by rwa [add_mul, one_mul]⟩
      · omega
    · rintro ⟨i, hx⟩
      exact ⟨i, i.2, Or.inl ⟨i.2, by rwa [add_mul, one_mul] at hx⟩⟩
  -- Straightening the arc over the step `k` carries `C k` onto `C (k + 1)`.
  have step (k : ℕ) (hk : k < n) : ∃ Ψ : TauCeti.AmbientIsotopy E, Ψ.final '' C k = C (k + 1) :=
    exists_ambientIsotopy_final_image_step hk hT hγ hper hh hnh hhδ hδT hKη hmono hK hsep
  -- Compose the straightenings of the arcs over all `n` steps.
  have hstage (k : ℕ) (hk : k ≤ n) : ∃ Φ : TauCeti.AmbientIsotopy E, Φ.final '' range γ = C k := by
    induction k with
    | zero => exact ⟨TauCeti.AmbientIsotopy.refl E, by simpa using hC0⟩
    | succ k ih =>
      obtain ⟨Φ, hΦ⟩ := ih (by omega)
      obtain ⟨Ψ, hΨ⟩ := step k (by omega)
      refine ⟨Φ.trans Ψ, ?_⟩
      rw [← hΨ, ← hΦ, image_image]
      simp
  obtain ⟨Φ, hΦ⟩ := hstage n le_rfl
  exact ⟨Φ, hΦ.trans hCn⟩

/-- **Fine inscribed polygons of a `C¹` loop are ambient isotopic to it.** Let `γ : ℝ → E` be a
`C¹` curve of period `T > 0` in a real normed space, with nowhere vanishing derivative, injective
modulo `T`. Then for all large `n` some ambient isotopy of `E` carries the image of `γ` onto the
inscribed polygon with `n` vertices, which is simple by `Polygon.eventually_isSimple_inscribed`.
So a knot of class `C¹` is tame: it is ambient isotopic to a polygonal knot. -/
theorem eventually_exists_ambientIsotopy_image_inscribed (hT : 0 < T) (hγ : ContDiff ℝ 1 γ)
    (hper : Periodic γ T) (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T)
    (hderiv : ∀ t, deriv γ t ≠ 0) :
    ∀ᶠ n in atTop, ∃ Φ : TauCeti.AmbientIsotopy E,
      Φ.final '' range γ = (inscribed γ T n).boundary ℝ := by
  obtain ⟨δ₀, hδ₀, hmono⟩ := hγ.exists_strictMonoOn_dual_comp hderiv (-T) T
  set δ := min (δ₀ / 4) (T / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨K, hK⟩ := (hγ.contDiffOn (s := Icc 0 T)).exists_lipschitzOnWith one_ne_zero
    (convex_Icc 0 T) isCompact_Icc
  obtain ⟨η, hη, hsep⟩ := TauCeti.exists_pos_le_dist_apply_add hγ.continuous hinj
    (isCompact_Icc (a := 0) (b := T)) hδ
  have hc : 0 < min δ (η / (8 * K + 1)) := lt_min hδ (by positivity)
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_const_div_atTop_nhds_zero_nat T).eventually (gt_mem_nhds hc)] with n hn hTn
  have h₁ : T / n < η / (8 * K + 1) := hTn.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at h₁
  have h₂ : 0 ≤ T / n := by positivity
  refine exists_ambientIsotopy_image_inscribed_of_mesh hn hT hγ.continuous hper
    (hTn.trans_le (min_le_left _ _)).le (by linarith [min_le_right (δ₀ / 4) (T / 2)])
    (by nlinarith) (fun a ha ↦ (hmono a ha).imp fun φ hφ ↦ hφ.mono
      (Icc_subset_Icc le_rfl (by linarith [min_le_left (δ₀ / 4) (T / 2)]))) hK hsep

end AmbientIsotopy

end Polygon
