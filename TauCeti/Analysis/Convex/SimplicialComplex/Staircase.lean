/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import TauCeti.Analysis.Convex.SimplicialComplex.Glue
public import TauCeti.Topology.Order.RegionBetween
import TauCeti.Analysis.Convex.RegionBetween

/-!
# The staircase triangulation of a band over a simplex

Let `v : ι → E` be the vertices of a simplex, indexed by a finite linear order `ι`, and let
`a b : E → ℝ` be two height functions with `a (v i) ≤ b (v i)` at every vertex. Over the simplex,
the band between the affine interpolations of these heights has the *lower vertices*
`(v i, a (v i))` and the *upper vertices* `(v i, b (v i))`. This file triangulates the band without
adding any vertex. For each `k : ι`, the *staircase simplex* `TauCeti.staircaseSimplex v a b k`
has the lower vertices over `v i` with `i ≤ k` and the upper vertices over `v i` with `k ≤ i`: it
climbs from the lower to the upper boundary at the vertex `v k`. Where the heights agree at `v k`,
the two vertices over `v k` coincide and the staircase simplex has one vertex fewer.

The staircase simplices and their faces form a geometric simplicial complex
`TauCeti.staircaseComplex v a b hv hab` in `E × ℝ`
(`hv : AffineIndependent ℝ v`, `hab : ∀ i, a (v i) ≤ b (v i)`):

* each staircase simplex is affinely independent
  (`TauCeti.affineIndependent_staircaseSimplex`);
* writing a base point as `∑ i, w i • v i` with barycentric weights `w`, a point `(x, t)` lies in
  the `k`-th staircase simplex exactly when the excess `t - ∑ i, w i * a (v i)` lies between the
  sums of `w i * (b (v i) - a (v i))` over `k < i` and over `k ≤ i`
  (`TauCeti.mem_convexHull_staircaseSimplex_iff`). These intervals tile the vertical fibre of the
  band (`TauCeti.exists_mem_convexHull_staircaseSimplex`), and two staircase simplices meet in the
  convex hull of their common vertices
  (`TauCeti.convexHull_inter_convexHull_staircaseSimplex_subset`);
* for affine `a` and `b` the complex triangulates the closed band
  `TauCeti.closedRegionBetween a b (convexHull ℝ (range v))`
  (`TauCeti.space_staircaseComplex`), and its vertices are exactly the lower and upper vertices
  (`TauCeti.vertices_staircaseComplex`);
* the construction is compatible with the faces of the base simplex: for an order embedding
  `e : κ ↪o ι`, the faces lying over the face `v ∘ e` of the base are the faces of the staircase
  complex of `v ∘ e` with the restricted order (`TauCeti.restrict_staircaseComplex`);
* every staircase simplex is the cone from the lower vertex over the least base vertex to either
  the upper graph or a staircase simplex of the band over the opposite facet
  (`TauCeti.coe_staircaseSimplex_eq_insert_range`, `TauCeti.coe_staircaseSimplex_eq_insert`). So,
  where the heights differ, the staircase triangulation is the *pulling triangulation* of the band
  for the vertex order in which the lower vertices precede the upper ones and are ordered as their
  base vertices: the least vertex is coned over the triangulations of the facets not containing it.

The heights need no relation beyond `a (v i) ≤ b (v i)`; this inequality is necessary, since for
crossing heights two staircase simplices of an interval overlap in an open set. Since every vertex
lies over a base vertex, every simplex of the complex projects onto a face of the base simplex, and
a single linear order on the base vertices fixes the triangulation of the band and of all its faces
at once. The combinatorial counterpart, for heights that differ at every vertex, is the ordered
cylinder `AbstractSimplicialComplex.orderedCylinder`; collapsed heights identify the two vertices
over a base vertex, so the construction here is made directly in `E × ℝ`. These are the properties
needed to triangulate the bands and graphs of a cylindrical decomposition over a simplicial base
without adding vertices, compatibly with the projection to the base. For an interval the staircase
simplices of a square with lower vertices `(0, 0), (1, 0)` and upper vertices `(0, 1), (1, 1)` are
the triangles with vertex sets `{(0, 0), (0, 1), (1, 1)}` and `{(0, 0), (1, 0), (1, 1)}`, which
meet along the diagonal.

## References

* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Springer (1998), §9.2.
* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2, for the staircase triangulation of a prism.
-/

public section

open Finset Set

namespace TauCeti

variable {ι κ E : Type*} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]

section Simplex

variable (v : ι → E) (a b : E → ℝ)

/-- The `k`-th staircase simplex of the band between the heights `a` and `b` over the simplex with
ordered vertices `v`: the lower vertices `(v i, a (v i))` with `i ≤ k` together with the upper
vertices `(v i, b (v i))` with `k ≤ i`. -/
noncomputable def staircaseSimplex (k : ι) : Finset (E × ℝ) := by
  classical
  exact (univ.filter (· ≤ k)).image (fun i ↦ (v i, a (v i))) ∪
    (univ.filter (k ≤ ·)).image fun i ↦ (v i, b (v i))

variable {v a b}

@[simp]
theorem mem_staircaseSimplex {k : ι} {p : E × ℝ} :
    p ∈ staircaseSimplex v a b k ↔
      (∃ i ≤ k, (v i, a (v i)) = p) ∨ ∃ i, k ≤ i ∧ (v i, b (v i)) = p := by
  classical
  simp [staircaseSimplex]

theorem coe_staircaseSimplex (k : ι) :
    (staircaseSimplex v a b k : Set (E × ℝ)) =
      (fun i ↦ (v i, a (v i))) '' Iic k ∪ (fun i ↦ (v i, b (v i))) '' Ici k := by
  ext p
  simp

theorem lower_mem_staircaseSimplex {i k : ι} (h : i ≤ k) :
    (v i, a (v i)) ∈ staircaseSimplex v a b k :=
  mem_staircaseSimplex.2 (.inl ⟨i, h, rfl⟩)

theorem upper_mem_staircaseSimplex {i k : ι} (h : k ≤ i) :
    (v i, b (v i)) ∈ staircaseSimplex v a b k :=
  mem_staircaseSimplex.2 (.inr ⟨i, h, rfl⟩)

/-- **Pulling the least lower vertex, first step.** Over the least base vertex `v i₀`, the
staircase simplex is the cone from the lower vertex over `v i₀` to the upper graph. -/
theorem coe_staircaseSimplex_eq_insert_range {i₀ : ι} (h₀ : IsBot i₀) :
    (staircaseSimplex v a b i₀ : Set (E × ℝ)) =
      insert (v i₀, a (v i₀)) (range fun i ↦ (v i, b (v i))) := by
  ext p
  simp only [mem_coe, mem_staircaseSimplex, Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, -, rfl⟩)
    exacts [.inl (by rw [le_antisymm hi (h₀ i)]), .inr ⟨i, rfl⟩]
  · rintro (rfl | ⟨i, rfl⟩)
    exacts [.inl ⟨i₀, le_rfl, rfl⟩, .inr ⟨i, h₀ i, rfl⟩]

/-- **Pulling the least lower vertex.** Over a base vertex `v k` other than the least one `v i₀`,
the staircase simplex is the cone from the lower vertex over `v i₀` to the staircase simplex of
the band over the facet opposite `v i₀`, for the restricted order. Together with
`TauCeti.coe_staircaseSimplex_eq_insert_range`, this exhibits the staircase triangulation as the
cone from the least lower vertex over the upper graph and over the staircase triangulation of the
band over the opposite facet. When the heights differ at `v i₀`, these are the facets of the band
not containing that vertex, so this is the pulling triangulation of the band for the vertex order
in which the lower vertices precede the upper ones and are ordered as their base vertices. -/
theorem coe_staircaseSimplex_eq_insert {i₀ k : ι} (h₀ : IsBot i₀) (hk : i₀ < k) :
    (staircaseSimplex v a b k : Set (E × ℝ)) =
      insert (v i₀, a (v i₀))
        (staircaseSimplex (fun i : {i // i₀ < i} ↦ v i) a b ⟨k, hk⟩ : Set (E × ℝ)) := by
  ext p
  simp only [mem_coe, mem_staircaseSimplex, Set.mem_insert_iff, Subtype.exists,
    Subtype.mk_le_mk, exists_prop]
  constructor
  · rintro (⟨i, hik, rfl⟩ | ⟨i, hki, rfl⟩)
    · rcases (h₀ i).lt_or_eq with hi | rfl
      exacts [.inr (.inl ⟨i, hi, hik, rfl⟩), .inl rfl]
    · exact .inr (.inr ⟨i, hk.trans_le hki, hki, rfl⟩)
  · rintro (rfl | ⟨i, -, hik, rfl⟩ | ⟨i, -, hki, rfl⟩)
    exacts [.inl ⟨i₀, hk.le, rfl⟩, .inl ⟨i, hik, rfl⟩, .inr ⟨i, hki, rfl⟩]

variable [AddCommGroup E] [Module ℝ E]

/-- A staircase simplex over an affinely independent family of base vertices is affinely
independent. -/
theorem affineIndependent_staircaseSimplex (hv : AffineIndependent ℝ v) (k : ι) :
    AffineIndependent ℝ ((↑) : staircaseSimplex v a b k → E × ℝ) := by
  classical
  -- the graph points, lower up to `k` and upper beyond it, project onto `v`
  set g : ι → E × ℝ := fun i ↦ if i ≤ k then (v i, a (v i)) else (v i, b (v i))
  have hg : AffineIndependent ℝ g := by
    refine AffineIndependent.of_comp (AffineMap.fst : E × ℝ →ᵃ[ℝ] E) ?_
    convert hv using 1
    ext i
    simp only [Function.comp_apply, AffineMap.coe_fst, g]
    split_ifs <;> rfl
  have hsub : (staircaseSimplex v a b k : Set (E × ℝ)) ⊆ insert (v k, b (v k)) (range g) := by
    intro p hp
    rcases mem_staircaseSimplex.1 hp with ⟨i, hik, rfl⟩ | ⟨i, hki, rfl⟩
    · exact .inr ⟨i, by simp [g, hik]⟩
    · rcases hki.lt_or_eq with hki | rfl
      · exact .inr ⟨i, by simp [g, not_le.2 hki]⟩
      · exact .inl rfl
  refine AffineIndependent.mono ?_ hsub
  by_cases hk : (v k, b (v k)) ∈ range g
  · rw [Set.insert_eq_of_mem hk]
    exact hg.range
  refine AffineIndepOn.id_insert hg.range fun hmem ↦ hk ⟨k, ?_⟩
  -- an affine combination of the graph points over `v k` has the weights of `g k`
  obtain ⟨w, hw1, hw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hmem
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at hw
  have hwk : ∀ i, w i = (Pi.single k 1 : ι → ℝ) i := by
    refine fun i ↦ hv.eq_of_sum_eq_sum (s := univ) (by simp [hw1]) ?_ i (mem_univ i)
    have := congrArg Prod.fst hw
    simp only [Prod.fst_sum, Prod.smul_fst, g, apply_ite Prod.fst, ite_self] at this
    simp [Pi.single_apply, ← this]
  have := congrArg Prod.snd hw
  simp only [hwk, Pi.single_apply, ite_smul, one_smul, zero_smul, sum_ite_eq'] at this
  simp [g, this]

omit [LinearOrder ι] in
/-- Barycentric weights `w` combine the vertices `(v i, b (v i))` for `P i` and `(v i, a (v i))`
otherwise to the point over `∑ i, w i • v i` at height `∑ i, w i * a (v i)` plus the weighted
excesses `w i * (b (v i) - a (v i))` with `P i`. -/
private theorem sum_smul_mk_ite (P : ι → Prop) [DecidablePred P] (w : ι → ℝ) :
    ∑ i, w i • (v i, if P i then b (v i) else a (v i)) =
      (∑ i, w i • v i, ∑ i, w i * a (v i) + ∑ i with P i, w i * (b (v i) - a (v i))) := by
  refine Prod.ext (by simp [Prod.fst_sum]) ?_
  simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  split_ifs <;> ring

omit [LinearOrder ι] in
/-- The points described by barycentric weights with excess between two partial sums of the
weighted height differences form a convex set. -/
private theorem convex_setOf_exists_weights (P Q : ι → Prop) [DecidablePred P]
    [DecidablePred Q] :
    Convex ℝ {p : E × ℝ | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • v i = p.1 ∧
      ∑ i with P i, w i * (b (v i) - a (v i)) ≤ p.2 - ∑ i, w i * a (v i) ∧
      p.2 - ∑ i, w i * a (v i) ≤ ∑ i with Q i, w i * (b (v i) - a (v i))} := by
  rintro p ⟨w, hw0, hw1, hwv, hlo, hhi⟩ q ⟨w', hw0', hw1', hwv', hlo', hhi'⟩ θ θ' hθ hθ' hθθ'
  have hlin : ∀ (s : Finset ι) (f : ι → ℝ),
      ∑ i ∈ s, (θ • w + θ' • w') i * f i = θ * ∑ i ∈ s, w i * f i + θ' * ∑ i ∈ s, w' i * f i :=
    fun s f ↦ by simp [add_mul, sum_add_distrib, mul_sum, mul_assoc]
  refine ⟨θ • w + θ' • w', fun i ↦ ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hw0 i, hw0' i]
  · simp [sum_add_distrib, ← mul_sum, hw1, hw1', hθθ']
  · simp [add_smul, mul_smul, sum_add_distrib, ← smul_sum, hwv, hwv']
  all_goals
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hlin]
    nlinarith [mul_le_mul_of_nonneg_left hlo hθ, mul_le_mul_of_nonneg_left hhi hθ,
      mul_le_mul_of_nonneg_left hlo' hθ', mul_le_mul_of_nonneg_left hhi' hθ']

omit [LinearOrder ι] in
/-- A point `(v i, t)` over a base vertex lies in the convex set of
`convex_setOf_exists_weights`, with the weights `Pi.single i 1`, when its height lies between the
two graphs that `P i` and `Q i` select. -/
private theorem exists_weights_single (P Q : ι → Prop) [DecidablePred P]
    [DecidablePred Q] (i : ι) {t : ℝ} (hP : P i → b (v i) ≤ t) (hP' : ¬ P i → a (v i) ≤ t)
    (hQ : Q i → t ≤ b (v i)) (hQ' : ¬ Q i → t ≤ a (v i)) :
    ∃ w : ι → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ ∑ j, w j • v j = v i ∧
      ∑ j with P j, w j * (b (v j) - a (v j)) ≤ t - ∑ j, w j * a (v j) ∧
      t - ∑ j, w j * a (v j) ≤ ∑ j with Q j, w j * (b (v j) - a (v j)) := by
  classical
  refine ⟨Pi.single i 1, Pi.single_nonneg.2 zero_le_one, by simp, by simp, ?_, ?_⟩ <;>
    by_cases P i <;> by_cases Q i <;> simp [Pi.single_apply, *]

/-- A point over `∑ i, w i • v i`, for barycentric weights `w`, whose excess
`p.2 - ∑ i, w i * a (v i)` over the lower boundary lies between the sums of the weighted height
differences `w i * (b (v i) - a (v i))` over `k < i` and over `k ≤ i`, lies in the `k`-th staircase
simplex. -/
theorem mem_convexHull_staircaseSimplex {k : ι} {p : E × ℝ} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hwv : ∑ i, w i • v i = p.1)
    (hlo : ∑ i with k < i, w i * (b (v i) - a (v i)) ≤ p.2 - ∑ i, w i * a (v i))
    (hhi : p.2 - ∑ i, w i * a (v i) ≤ ∑ i with k ≤ i, w i * (b (v i) - a (v i))) :
    p ∈ convexHull ℝ (staircaseSimplex v a b k : Set (E × ℝ)) := by
  classical
  -- `p` lies on the vertical segment between the two points with weights `w` on the graphs
  -- through the vertices of the `k`-th staircase simplex
  have hmem (P : ι → Prop) [DecidablePred P] (hP : ∀ i, P i → k ≤ i)
      (hP' : ∀ i, ¬ P i → i ≤ k) :
      (p.1, ∑ i, w i * a (v i) + ∑ i with P i, w i * (b (v i) - a (v i))) ∈
        convexHull ℝ (staircaseSimplex v a b k : Set (E × ℝ)) := by
    rw [← hwv, ← sum_smul_mk_ite]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ ↦ hw0 i) hw1 fun i _ ↦
      subset_convexHull ℝ _ ?_
    split_ifs with hi
    · exact upper_mem_staircaseSimplex (hP i hi)
    · exact lower_mem_staircaseSimplex (hP' i hi)
  have h₀ := hmem (k < ·) (fun _ ↦ le_of_lt) fun _ ↦ le_of_not_gt
  have h₁ := hmem (k ≤ ·) (fun _ ↦ id) fun _ h ↦ (lt_of_not_ge h).le
  refine (convex_convexHull ℝ _).segment_subset h₀ h₁ ?_
  rw [← Prod.image_mk_segment_right, segment_eq_Icc (by linarith)]
  exact ⟨p.2, ⟨by linarith, by linarith⟩, rfl⟩

/-- **Barycentric description of a staircase simplex.** A point `p` lies in the `k`-th staircase
simplex exactly when its base point is `∑ i, w i • v i` for barycentric weights `w` and its excess
`p.2 - ∑ i, w i * a (v i)` over the lower boundary lies between the sums of the weighted height
differences `w i * (b (v i) - a (v i))` over `k < i` and over `k ≤ i`. -/
theorem mem_convexHull_staircaseSimplex_iff (hab : ∀ i, a (v i) ≤ b (v i)) {k : ι}
    {p : E × ℝ} :
    p ∈ convexHull ℝ (staircaseSimplex v a b k : Set (E × ℝ)) ↔
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • v i = p.1 ∧
        ∑ i with k < i, w i * (b (v i) - a (v i)) ≤ p.2 - ∑ i, w i * a (v i) ∧
        p.2 - ∑ i, w i * a (v i) ≤ ∑ i with k ≤ i, w i * (b (v i) - a (v i)) := by
  classical
  refine ⟨fun hp ↦ convexHull_min (fun q hq ↦ ?_) (convex_setOf_exists_weights _ _) hp,
    fun ⟨w, hw0, hw1, hwv, hlo, hhi⟩ ↦ mem_convexHull_staircaseSimplex hw0 hw1 hwv hlo hhi⟩
  rcases mem_staircaseSimplex.1 hq with ⟨i, hik, rfl⟩ | ⟨i, hki, rfl⟩
  · exact exists_weights_single _ _ i (fun h ↦ absurd hik (not_le.2 h))
      (fun _ ↦ le_rfl) (fun _ ↦ hab i) fun _ ↦ le_rfl
  · exact exists_weights_single _ _ i (fun _ ↦ le_rfl) (fun _ ↦ hab i)
      (fun _ ↦ le_rfl) (absurd hki)

/-- **The staircase simplices cover the band.** A point over `∑ i, w i • v i`, for barycentric
weights `w`, whose excess `p.2 - ∑ i, w i * a (v i)` over the lower boundary lies between `0` and
`∑ i, w i * (b (v i) - a (v i))` lies in some staircase simplex: the intervals of
`TauCeti.mem_convexHull_staircaseSimplex` tile this range. -/
theorem exists_mem_convexHull_staircaseSimplex {p : E × ℝ} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hwv : ∑ i, w i • v i = p.1) (h₀ : 0 ≤ p.2 - ∑ i, w i * a (v i))
    (h₁ : p.2 - ∑ i, w i * a (v i) ≤ ∑ i, w i * (b (v i) - a (v i))) :
    ∃ k, p ∈ convexHull ℝ (staircaseSimplex v a b k : Set (E × ℝ)) := by
  classical
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  set f : ι → ℝ := fun i ↦ w i * (b (v i) - a (v i))
  set s := p.2 - ∑ i, w i * a (v i)
  -- take the least `k` whose lower bound is at most `s`; the greatest index has lower bound `0`
  set S := univ.filter fun k ↦ ∑ i with k < i, f i ≤ s
  have hS : S.Nonempty := by
    refine ⟨univ.max' univ_nonempty, mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    rwa [sum_eq_zero fun i hi ↦
      absurd (mem_filter.1 hi).2 (not_lt.2 (le_max' _ i (Finset.mem_univ i)))]
  refine ⟨S.min' hS, mem_convexHull_staircaseSimplex hw0 hw1 hwv (mem_filter.1 (min'_mem S hS)).2
    (not_lt.1 fun hlt ↦ ?_)⟩
  by_cases hex : (univ.filter (· < S.min' hS)).Nonempty
  · -- the greatest index below `S.min' hS` would have the same lower bound and lie in `S`
    set j := (univ.filter (· < S.min' hS)).max' hex
    have hj : j < S.min' hS := (mem_filter.1 (max'_mem _ hex)).2
    have hfilter : univ.filter (j < ·) = univ.filter (S.min' hS ≤ ·) := by
      ext i
      simp only [mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hji ↦ not_lt.1 fun hik ↦ (le_max' _ i (by simpa using hik)).not_gt hji,
        hj.trans_le⟩
    have hjS : j ∈ S := by simpa [S, hfilter] using hlt.le
    exact (min'_le S j hjS).not_gt hj
  · -- otherwise `S.min' hS` is the least index and its upper bound is the whole sum
    rw [Finset.not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hex
    have : Finset.univ.filter (S.min' hS ≤ ·) = Finset.univ :=
      filter_true_of_mem fun i _ ↦ not_lt.1 (hex (Finset.mem_univ i))
    rw [this] at hlt
    exact hlt.not_ge h₁

/-- Two staircase simplices meet in the convex hull of their common vertices. -/
theorem convexHull_inter_convexHull_staircaseSimplex_subset (hv : AffineIndependent ℝ v)
    (hab : ∀ i, a (v i) ≤ b (v i)) (k l : ι) :
    convexHull ℝ (staircaseSimplex v a b k : Set (E × ℝ)) ∩
        convexHull ℝ (staircaseSimplex v a b l : Set (E × ℝ)) ⊆
      convexHull ℝ ((staircaseSimplex v a b k : Set (E × ℝ)) ∩ staircaseSimplex v a b l) := by
  classical
  wlog hkl : k ≤ l generalizing k l
  · rw [Set.inter_comm, Set.inter_comm (staircaseSimplex v a b k : Set (E × ℝ))]
    exact this l k (le_of_not_ge hkl)
  rcases hkl.lt_or_eq with hkl | rfl
  swap
  · simp
  rintro p ⟨hpk, hpl⟩
  obtain ⟨w, hw0, hw1, hwv, hlo, -⟩ := (mem_convexHull_staircaseSimplex_iff hab).1 hpk
  obtain ⟨w', -, hw1', hwv', -, hhi⟩ := (mem_convexHull_staircaseSimplex_iff hab).1 hpl
  obtain rfl : w' = w := funext fun i ↦
    hv.eq_of_sum_eq_sum (s := univ) (by rw [hw1, hw1']) (by rw [hwv, hwv']) i (mem_univ i)
  have hnn : ∀ i, 0 ≤ w' i * (b (v i) - a (v i)) := fun i ↦
    mul_nonneg (hw0 i) (sub_nonneg.2 (hab i))
  -- the excess of `p` over the lower boundary is both the sum over `k < i` and over `l ≤ i`
  have hle : ∑ i with l ≤ i, w' i * (b (v i) - a (v i)) ≤
      ∑ i with k < i, w' i * (b (v i) - a (v i)) :=
    sum_le_sum_of_subset_of_nonneg (fun i ↦ by simpa using hkl.trans_le)
      fun i _ _ ↦ hnn i
  have hzero : ∀ i, k < i → i < l → w' i * (b (v i) - a (v i)) = 0 := by
    intro i hki hil
    have hins : insert i (univ.filter (l ≤ ·)) ⊆ univ.filter (k < ·) := by
      intro j hj
      rcases mem_insert.1 hj with rfl | hj
      · simpa using hki
      · simpa using hkl.trans_le (mem_filter.1 hj).2
    have := sum_le_sum_of_subset_of_nonneg hins fun j _ _ ↦ hnn j
    rw [sum_insert (by simpa using hil)] at this
    linarith [hnn i]
  have hp : p = ∑ i, w' i • (v i, if k < i then b (v i) else a (v i)) := by
    rw [sum_smul_mk_ite]
    exact Prod.ext hwv.symm (by linarith)
  rw [hp, ← centerMass_eq_of_sum_1 _ _ hw1, ← centerMass_filter_ne_zero]
  refine centerMass_mem_convexHull _ (fun i _ ↦ hw0 i)
    (by rw [sum_filter_ne_zero, hw1]; exact one_pos) fun i hi ↦ ?_
  have hwi : w' i ≠ 0 := (mem_filter.1 hi).2
  split_ifs with hki
  · refine ⟨upper_mem_staircaseSimplex hki.le, ?_⟩
    rcases le_or_gt l i with hli | hil
    · exact upper_mem_staircaseSimplex hli
    · have hab' : b (v i) = a (v i) := by
        have := hzero i hki hil
        rcases mul_eq_zero.1 this with h | h
        · exact (hwi h).elim
        · linarith
      simp only [mem_coe, hab']
      exact lower_mem_staircaseSimplex hil.le
  · exact ⟨lower_mem_staircaseSimplex (le_of_not_gt hki),
      lower_mem_staircaseSimplex ((le_of_not_gt hki).trans hkl.le)⟩

end Simplex

section Complex

variable [AddCommGroup E] [Module ℝ E] {v : ι → E} {a b : E → ℝ}

variable (v a b) in
/-- The **staircase triangulation** over the simplex with ordered affinely independent vertices
`v`: its faces are the nonempty subsets of the staircase simplices. It triangulates the band
between the affine interpolations of the vertex heights `a (v i) ≤ b (v i)`; for affine `a` and
`b` this is `TauCeti.closedRegionBetween a b (convexHull ℝ (range v))`
(`TauCeti.space_staircaseComplex`). -/
noncomputable def staircaseComplex (hv : AffineIndependent ℝ v) (hab : ∀ i, a (v i) ≤ b (v i)) :
    Geometry.SimplicialComplex ℝ (E × ℝ) :=
  .ofSimplices (staircaseSimplex v a b) (affineIndependent_staircaseSimplex hv)
    (convexHull_inter_convexHull_staircaseSimplex_subset hv hab)

variable (hv : AffineIndependent ℝ v) (hab : ∀ i, a (v i) ≤ b (v i))

/-- The faces of the staircase triangulation are the nonempty subsets of staircase simplices. -/
@[simp]
theorem mem_staircaseComplex_faces {t : Finset (E × ℝ)} :
    t ∈ (staircaseComplex v a b hv hab).faces ↔
      t.Nonempty ∧ ∃ k, t ⊆ staircaseSimplex v a b k :=
  Geometry.SimplicialComplex.mem_ofSimplices_faces

/-- Every staircase simplex is a face of the staircase triangulation. -/
theorem staircaseSimplex_mem_staircaseComplex_faces (k : ι) :
    staircaseSimplex v a b k ∈ (staircaseComplex v a b hv hab).faces :=
  (mem_staircaseComplex_faces hv hab).2 ⟨⟨_, lower_mem_staircaseSimplex le_rfl⟩, k, subset_rfl⟩

/-- The vertices of the staircase triangulation are the lower and the upper vertices. -/
theorem vertices_staircaseComplex :
    (staircaseComplex v a b hv hab).vertices =
      range (fun i ↦ (v i, a (v i))) ∪ range fun i ↦ (v i, b (v i)) := by
  rw [staircaseComplex, Geometry.SimplicialComplex.vertices_ofSimplices]
  ext p
  simp only [Set.mem_iUnion, mem_coe, mem_staircaseSimplex, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨k, ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩⟩
    exacts [.inl ⟨i, rfl⟩, .inr ⟨i, rfl⟩]
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    exacts [⟨i, .inl ⟨i, le_rfl, rfl⟩⟩, ⟨i, .inr ⟨i, le_rfl, rfl⟩⟩]

/-- The staircase triangulation over a face `v ∘ e` of the base simplex, with the order restricted
along `e`, is a subcomplex of the staircase triangulation over the whole simplex. -/
theorem staircaseComplex_comp_le (e : κ ↪o ι) :
    staircaseComplex (v ∘ e) a b (hv.comp_embedding e.toEmbedding) (fun i ↦ hab (e i)) ≤
      staircaseComplex v a b hv hab := by
  intro t
  simp only [mem_staircaseComplex_faces]
  rintro ⟨ht, k, htk⟩
  refine ⟨ht, e k, fun p hp ↦ ?_⟩
  rcases mem_staircaseSimplex.1 (htk hp) with ⟨i, hik, rfl⟩ | ⟨i, hki, rfl⟩
  · exact lower_mem_staircaseSimplex (e.le_iff_le.2 hik)
  · exact upper_mem_staircaseSimplex (e.le_iff_le.2 hki)

/-- **Restriction to a face of the base.** The faces of the staircase triangulation lying over a
face `v ∘ e` of the base simplex are exactly the faces of the staircase triangulation of `v ∘ e`,
for the order restricted along `e`. -/
theorem restrict_staircaseComplex (e : κ ↪o ι) :
    (staircaseComplex v a b hv hab).restrict (Prod.fst ⁻¹' range (v ∘ e)) =
      staircaseComplex (v ∘ e) a b (hv.comp_embedding e.toEmbedding) (fun i ↦ hab (e i)) := by
  classical
  refine Geometry.SimplicialComplex.ext <| Set.ext fun t ↦ ?_
  rw [Geometry.SimplicialComplex.mem_restrict_faces]
  refine ⟨?_, fun ht ↦ ⟨staircaseComplex_comp_le hv hab e ht, fun p hp ↦ ?_⟩⟩
  swap
  · obtain ⟨-, k, htk⟩ := (mem_staircaseComplex_faces _ _).1 ht
    rcases mem_staircaseSimplex.1 (htk hp) with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩ <;> exact ⟨i, rfl⟩
  rw [mem_staircaseComplex_faces, mem_staircaseComplex_faces]
  rintro ⟨⟨hne, k, htk⟩, htB⟩
  -- every vertex of `t` is a lower vertex below `k` or an upper vertex above `k` over the face
  have key : ∀ p ∈ t, ∃ j, (e j ≤ k ∧ (v (e j), a (v (e j))) = p) ∨
      (k ≤ e j ∧ (v (e j), b (v (e j))) = p) := by
    intro p hp
    obtain ⟨j, hj⟩ := htB hp
    rcases mem_staircaseSimplex.1 (htk hp) with ⟨i, hik, rfl⟩ | ⟨i, hki, rfl⟩ <;>
      obtain rfl : e j = i := hv.injective hj
    exacts [⟨j, .inl ⟨hik, rfl⟩⟩, ⟨j, .inr ⟨hki, rfl⟩⟩]
  refine ⟨hne, ?_⟩
  by_cases hB : (univ.filter fun j ↦ k ≤ e j).Nonempty
  · -- climb at the least upper index over the face
    refine ⟨(univ.filter fun j ↦ k ≤ e j).min' hB, fun p hp ↦ ?_⟩
    have hmin := min'_mem _ hB
    rw [mem_filter] at hmin
    obtain ⟨j, ⟨hjk, rfl⟩ | ⟨hkj, rfl⟩⟩ := key p hp
    · exact lower_mem_staircaseSimplex (e.le_iff_le.1 (hjk.trans hmin.2))
    · exact upper_mem_staircaseSimplex (min'_le _ _ (by simpa using hkj))
  · -- there are only lower vertices: climb at the greatest lower index
    have hlow : ∀ p ∈ t, ∃ j, e j ≤ k ∧ (v (e j), a (v (e j))) = p := fun p hp ↦ by
      obtain ⟨j, h | ⟨hkj, -⟩⟩ := key p hp
      exacts [⟨j, h⟩, (hB ⟨j, by simpa using hkj⟩).elim]
    obtain ⟨p₀, hp₀⟩ := hne
    obtain ⟨j₀, hj₀, -⟩ := hlow p₀ hp₀
    have hA : (univ.filter fun j ↦ e j ≤ k).Nonempty := ⟨j₀, by simpa using hj₀⟩
    refine ⟨(univ.filter fun j ↦ e j ≤ k).max' hA, fun p hp ↦ ?_⟩
    obtain ⟨j, hjk, rfl⟩ := hlow p hp
    exact lower_mem_staircaseSimplex (le_max' _ _ (by simpa using hjk))

end Complex

section Space

variable [AddCommGroup E] [Module ℝ E] {v : ι → E} {a b : E →ᵃ[ℝ] ℝ}

/-- **The staircase triangulation triangulates the band.** For affine heights `a ≤ b` on the
vertices, the staircase triangulation of the simplex with vertices `v` has the closed band between
`a` and `b` over the simplex as its underlying space. -/
theorem space_staircaseComplex (hv : AffineIndependent ℝ v) (hab : ∀ i, a (v i) ≤ b (v i)) :
    (staircaseComplex v a b hv hab).space = closedRegionBetween a b (convexHull ℝ (range v)) := by
  classical
  have hband := closedRegionBetween_convexHull (a := a) (b := b) (s := range v)
    (by rintro _ ⟨i, rfl⟩; exact hab i)
  rw [staircaseComplex, Geometry.SimplicialComplex.space_ofSimplices, hband]
  refine Set.Subset.antisymm (Set.iUnion_subset fun k ↦ convexHull_mono fun q hq ↦ ?_) fun p hp ↦ ?_
  · rcases mem_staircaseSimplex.1 hq with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
    exacts [.inl (Set.mem_graphOn.2 ⟨⟨i, rfl⟩, rfl⟩), .inr (Set.mem_graphOn.2 ⟨⟨i, rfl⟩, rfl⟩)]
  -- the band consists of the points with excess between `0` and the weighted height difference
  obtain ⟨w, hw0, hw1, hwv, hlo, hhi⟩ := convexHull_min (fun q hq ↦ by
      rcases hq with ⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩
      · exact exists_weights_single _ _ i False.elim (fun _ ↦ le_rfl)
          (fun _ ↦ hab i) (absurd trivial)
      · exact exists_weights_single _ _ i False.elim (fun _ ↦ hab i)
          (fun _ ↦ le_rfl) (absurd trivial))
    (convex_setOf_exists_weights (v := v) (a := a) (b := b) (fun _ ↦ False) fun _ ↦ True) hp
  simp only [filter_false, sum_empty, filter_true] at hlo hhi
  exact Set.mem_iUnion.2 (exists_mem_convexHull_staircaseSimplex hw0 hw1 hwv hlo hhi)

end Space

end TauCeti
