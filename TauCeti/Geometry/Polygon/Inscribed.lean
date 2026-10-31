/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import TauCeti.Analysis.Calculus.Deriv.DualStrictMono
public import TauCeti.Geometry.Polygon.DeltaMove
public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.Topology.Instances.Real.InjectiveModPeriod

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
vertices used to inscribe it. The specialisations to smooth embeddings of the circle are
`TauCeti.SmoothEmbedding.eventually_isSimple_inscribed` and
`TauCeti.SmoothEmbedding.exists_combinatoriallyEquivalent_inscribed` in
`TauCeti.KnotTheory.InscribedPolygon`.

## Main definitions

* `Polygon.inscribed γ T n`: the polygon with vertices `γ (k * (T / n))`.

## Main results

* `Polygon.edgeSet_inscribed`: the edges of the polygon inscribed in a periodic curve.
* `Polygon.eventually_isSimple_inscribed`: the inscribed polygons of a `C¹` loop with nowhere
  vanishing derivative, injective modulo its period, are eventually simple.
* `Polygon.exists_combinatoriallyEquivalent_inscribed`: any two such inscribed polygons with
  enough vertices are combinatorially equivalent.

## Implementation notes

The proof of `Polygon.eventually_isSimple_inscribed` compares two edges of the inscribed polygon
`γ (k * h)`, `h = T / n`, according to how far apart their parameters are.

* **Nearby edges.** There is `δ > 0` such that on every window `[a, a + 3δ]` some continuous
  linear functional `φ` makes `φ ∘ γ` strictly increasing
  (`ContDiff.exists_strictMonoOn_dual_comp`). Two edges in one window are mapped by `φ` onto
  intervals between the values of `φ ∘ γ` at their ends, which are disjoint unless the edges are
  consecutive, and then meet only at the common vertex.
* **Distant edges.** By compactness and injectivity, `‖γ (a + d) - γ a‖` is bounded below by some
  `η > 0` when `δ ≤ d ≤ T - δ` (`TauCeti.exists_pos_le_dist_apply_add`), while every point of an
  edge lies within `K h` of its first vertex, `K` a Lipschitz constant of `γ` on `[0, T]`. So
  distant edges are disjoint once `2 K h < η`.

The proof of `Polygon.exists_combinatoriallyEquivalent_inscribed` works with polygons inscribed at
arbitrary parameters `0 = t₀ < t₁ < ⋯ < t_N < T` whose gaps, including the gap from `t_N` to `T`,
are at most a mesh `h` with `h ≤ δ` and `2 K h < η`. Inserting a parameter `s` between `tᵢ` and
the next parameter `t'` inserts the vertex `γ s`, and the same comparison of nearby and distant
parameters shows that the triangle `γ tᵢ, γ s, γ t'` meets every other edge only at `γ tᵢ` or
`γ t'`. So the insertion is a Δ-move, or a subdivision of the edge when the three points are
collinear, and it keeps the mesh at most `h`. Refining the uniform parameters of the polygons with
`n` and with `m` vertices, one parameter at a time, to the union of the two sets of parameters gives
the same polygon from both sides.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {T : ℝ}

/-- Let `φ ∘ γ` be strictly increasing on `I`, and `a ≤ b < b'` in `I`. A point `x` of the chord
from `γ b` to `γ b'` with `φ x ≤ φ (γ a)` is the start `γ b` of the chord, and `a = b`. -/
private theorem eq_of_mem_segment_of_le {φ : StrongDual ℝ E} {I : Set ℝ}
    (hmono : StrictMonoOn (fun t ↦ φ (γ t)) I) {a b b' : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hb' : b' ∈ I) (hab : a ≤ b) (hbb' : b < b') {x : E} (hx : φ x ≤ φ (γ a))
    (hx' : x ∈ segment ℝ (γ b) (γ b')) : a = b ∧ x = γ b := by
  rw [segment_eq_image'] at hx'
  obtain ⟨θ, ⟨hθ, -⟩, rfl⟩ := hx'
  have h₁ : φ (γ b) < φ (γ b') := hmono hb hb' hbb'
  have h₂ : φ (γ a) ≤ φ (γ b) := hmono.monotoneOn ha hb hab
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hx
  obtain rfl : θ = 0 := by nlinarith
  simp only [zero_smul, add_zero, zero_mul] at hx ⊢
  exact ⟨hmono.injOn ha hb (le_antisymm h₂ hx), trivial⟩

/-- Let `φ ∘ γ` be strictly increasing on `I`, and `b < b' ≤ a` in `I`. A point `x` of the chord
from `γ b` to `γ b'` with `φ (γ a) ≤ φ x` is the end `γ b'` of the chord, and `b' = a`. -/
private theorem eq_of_mem_segment_of_ge {φ : StrongDual ℝ E} {I : Set ℝ}
    (hmono : StrictMonoOn (fun t ↦ φ (γ t)) I) {a b b' : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hb' : b' ∈ I) (hbb' : b < b') (hb'a : b' ≤ a) {x : E} (hx : φ (γ a) ≤ φ x)
    (hx' : x ∈ segment ℝ (γ b) (γ b')) : b' = a ∧ x = γ b' := by
  rw [segment_symm, segment_eq_image'] at hx'
  obtain ⟨θ, ⟨hθ, -⟩, rfl⟩ := hx'
  have h₁ : φ (γ b) < φ (γ b') := hmono hb hb' hbb'
  have h₂ : φ (γ b') ≤ φ (γ a) := hmono.monotoneOn hb' ha hb'a
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hx
  obtain rfl : θ = 0 := by nlinarith
  simp only [zero_smul, add_zero, zero_mul] at hx ⊢
  exact ⟨hmono.injOn hb' ha (le_antisymm h₂ hx), trivial⟩

/-- If `φ ∘ γ` is monotone on `[c, c']` and `c ≤ u ≤ c'`, then `φ` is at most `φ (γ c')` on the
triangle with vertices `γ c`, `γ u`, `γ c'`. -/
private theorem le_of_mem_convexHull {φ : StrongDual ℝ E} {c c' u : ℝ} {y : E}
    (hφ : MonotoneOn (fun t ↦ φ (γ t)) (Icc c c')) (hcu : c ≤ u) (huc : u ≤ c')
    (hy : y ∈ convexHull ℝ {γ c, γ u, γ c'}) : φ y ≤ φ (γ c') := by
  refine convexHull_min ?_ (convex_halfSpace_le φ.toLinearMap.isLinear _) hy
  rintro _ (rfl | rfl | rfl)
  · exact hφ ⟨le_rfl, hcu.trans huc⟩ ⟨hcu.trans huc, le_rfl⟩ (hcu.trans huc)
  · exact hφ ⟨hcu, huc⟩ ⟨hcu.trans huc, le_rfl⟩ huc
  · exact le_rfl

/-- If `φ ∘ γ` is monotone on `[c, c']` and `c ≤ u ≤ c'`, then `φ` is at least `φ (γ c)` on the
triangle with vertices `γ c`, `γ u`, `γ c'`. -/
private theorem ge_of_mem_convexHull {φ : StrongDual ℝ E} {c c' u : ℝ} {y : E}
    (hφ : MonotoneOn (fun t ↦ φ (γ t)) (Icc c c')) (hcu : c ≤ u) (huc : u ≤ c')
    (hy : y ∈ convexHull ℝ {γ c, γ u, γ c'}) : φ (γ c) ≤ φ y := by
  refine convexHull_min ?_ (convex_halfSpace_ge φ.toLinearMap.isLinear _) hy
  rintro _ (rfl | rfl | rfl)
  · exact le_rfl
  · exact hφ ⟨le_rfl, hcu.trans huc⟩ ⟨hcu, huc⟩ hcu
  · exact hφ ⟨le_rfl, hcu.trans huc⟩ ⟨hcu.trans huc, le_rfl⟩ (hcu.trans huc)

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
  obtain ⟨e, rfl⟩ := eq_of_mem_segment_of_le hmono hah (mem (r * h) (by positivity) (by linarith))
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

/-- **Inscribed polygons of a `C¹` loop are eventually simple.** Let `γ : ℝ → E` be a `C¹` curve
of period `T > 0` in a real normed space, with nowhere vanishing derivative, injective modulo `T`.
Then for all large `n` the polygon inscribed in `γ` with `n` vertices `γ (k * (T / n))` is
simple. -/
theorem eventually_isSimple_inscribed (hT : 0 < T) (hγ : ContDiff ℝ 1 γ) (hper : Periodic γ T)
    (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T) (hderiv : ∀ t, deriv γ t ≠ 0) :
    ∀ᶠ n in atTop, (inscribed γ T n).IsSimple ℝ := by
  -- The window width `δ`, a Lipschitz constant `K` and the separation `η` of distant points.
  obtain ⟨δ₀, hδ₀, hmono₀⟩ := hγ.exists_strictMonoOn_dual_comp hderiv 0 T
  set δ := min (δ₀ / 3) (T / 3)
  have hδ : 0 < δ := by positivity
  have hδT : 3 * δ ≤ T := by linarith [min_le_right (δ₀ / 3) (T / 3)]
  have hmono (a : ℝ) (ha : a ∈ Icc 0 T) :
      ∃ φ : StrongDual ℝ E, StrictMonoOn (fun t ↦ φ (γ t)) (Icc a (a + 3 * δ)) :=
    (hmono₀ a ha).imp fun _ h ↦ h.mono <| Icc_subset_Icc_right <| by
      linarith [min_le_left (δ₀ / 3) (T / 3)]
  obtain ⟨K, hK⟩ := (hγ.contDiffOn (s := Icc 0 T)).exists_lipschitzOnWith one_ne_zero
    (convex_Icc 0 T) isCompact_Icc
  obtain ⟨η, hη, hsep⟩ := TauCeti.exists_pos_le_dist_apply_add hγ.continuous hinj isCompact_Icc hδ
  have hε : 0 < min δ (η / (2 * K + 1)) := lt_min hδ (by positivity)
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat T).eventually (gt_mem_nhds hε),
    eventually_ge_atTop 1] with n hn hn1
  have : NeZero n := ⟨by omega⟩
  set h := T / n with hh_def
  have hh : 0 < h := div_pos hT (by exact_mod_cast hn1)
  have hnh : (n : ℝ) * h = T := by rw [hh_def]; field_simp
  have hhδ : h < δ := hn.trans_le (min_le_left _ _)
  have hhη : 2 * K * h < η := by
    have := hn.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have hval (k : Fin n) : (k : ℝ) * h ∈ Icc 0 T :=
    ⟨by positivity, by rw [← hnh]; gcongr; exact_mod_cast k.is_lt.le⟩
  refine ⟨fun i ↦ ?_, fun i j x hij hxi hxj ↦ ?_⟩
  · rw [inscribed_apply, inscribed_finRotate hper, add_one_mul]
    exact TauCeti.apply_ne_apply_add hinj hh (by linarith)
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
    obtain ⟨φ, hφ⟩ := hmono _ (hval i)
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
    obtain ⟨φ, hφ⟩ := hmono _ (hval j)
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
    refine .inr ⟨Fin.ext ?_, ?_⟩
    · simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      rw [hjn1, Nat.mod_self, hi0]
    · have : ((j : ℝ) + 1) * h = 0 + T := by
        rw [zero_add, ← hnh]
        congr 1
        exact_mod_cast hjn1
      rw [inscribed_apply, hi0, Nat.cast_zero, zero_mul, ← add_one_mul, this, hper]
  · -- Distant edges are disjoint.
    rw [not_le] at hA hB
    exact (not_mem_segment_of_mem_segment hK (hval i).1 (by positivity) hh
      (by linarith) ((hsep _ (hval i) _ ⟨by linarith, by linarith⟩).trans_eq (dist_eq_norm _ _)) hhη
      hxi hxj).elim

/-! ### Refining an inscribed polygon by Δ-moves -/

section Refinement

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
  -- The triangle and the chord lie within `K * h` of their first vertices.
  have hxa : dist x (γ a) ≤ K * h := by
    have hd (u : ℝ) (hau : a ≤ u) (hu : u ≤ a') : γ u ∈ Metric.closedBall (γ a) (K * h) :=
      hF.dist_le ⟨by linarith, by linarith⟩ ⟨ha, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩)
    refine convexHull_min ?_ (convex_closedBall (γ a) (K * h)) hx
    rintro _ (rfl | rfl | rfl)
    exacts [hd a le_rfl (has.trans hsa'), hd s has hsa', hd a' (has.trans hsa') le_rfl]
  have hxb : dist x (γ b) ≤ K * h := by
    have hd (u : ℝ) (hbu : b ≤ u) (hu : u ≤ b') : γ u ∈ Metric.closedBall (γ b) (K * h) :=
      hF.dist_le ⟨by linarith, by linarith⟩ ⟨hb, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩)
    exact (convex_closedBall (γ b) (K * h)).segment_subset (hd b le_rfl hbb'.le)
      (hd b' hbb'.le le_rfl) hx'
  have far (c d : ℝ) (hc : c ∈ Icc 0 T) (hd : d ∈ Icc δ (T - δ))
      (hcd : γ (c + d) = γ b ∧ γ c = γ a ∨ γ (c + d) = γ a ∧ γ c = γ b) : False := by
    have := hF.sep c hc d hd
    rcases hcd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] at this <;>
      linarith [dist_triangle_left (γ b) (γ a) x, dist_comm (γ b) (γ a), hF.lt_sep]
  rcases hdisj with hab | hba
  · -- The chord comes after the triangle.
    by_cases h₁ : b' ≤ a + 3 * δ
    · -- Both lie in the window `[a, a + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono a ⟨ha, by linarith⟩
      have hle := le_of_mem_convexHull
        (hφ.monotoneOn.mono (Icc_subset_Icc le_rfl (by linarith))) has hsa' hx
      obtain ⟨e, rfl⟩ := eq_of_mem_segment_of_le hφ ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ ⟨by linarith, h₁⟩ hab hbb' hle hx'
      exact .inr (by rw [e])
    by_cases h₂ : a + T - b ≤ 2 * δ
    · -- The triangle, one period later, comes just after the chord: both lie in `[b, b + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono b ⟨hb, by linarith⟩
      rw [← hT a, ← hT s, ← hT a'] at hx
      have hge := ge_of_mem_convexHull (hφ.monotoneOn.mono (Icc_subset_Icc (by linarith)
        (by linarith))) (by linarith : a + T ≤ s + T) (by linarith : s + T ≤ a' + T) hx
      obtain ⟨e, rfl⟩ := eq_of_mem_segment_of_ge hφ ⟨by linarith, by linarith⟩
        ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ hbb' (by linarith) hge hx'
      exact .inl (by rw [e, hT])
    · -- Distant: `γ a` and `γ b` are far apart.
      exact (far a (b - a) ⟨ha, by linarith⟩ ⟨by linarith, by linarith⟩
        (.inl ⟨by rw [add_sub_cancel], rfl⟩)).elim
  · -- The chord comes before the triangle.
    by_cases h₁ : a' ≤ b + 3 * δ
    · -- Both lie in the window `[b, b + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono b ⟨hb, by linarith⟩
      have hge := ge_of_mem_convexHull
        (hφ.monotoneOn.mono (Icc_subset_Icc (by linarith) h₁)) has hsa' hx
      obtain ⟨e, rfl⟩ := eq_of_mem_segment_of_ge hφ ⟨by linarith, by linarith⟩
        ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ hbb' hba hge hx'
      exact .inl (by rw [e])
    by_cases h₂ : b + T - a ≤ 2 * δ
    · -- The chord, one period later, comes just after the triangle: both lie in `[a, a + 3δ]`.
      obtain ⟨φ, hφ⟩ := hF.mono a ⟨ha, by linarith⟩
      rw [← hT b, ← hT b'] at hx'
      have hle := le_of_mem_convexHull
        (hφ.monotoneOn.mono (Icc_subset_Icc le_rfl (by linarith))) has hsa' hx
      obtain ⟨e, rfl⟩ := eq_of_mem_segment_of_le hφ ⟨by linarith, by linarith⟩
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

/-- The constants of `FineMesh` exist for a `C¹` loop with nowhere vanishing derivative, injective
modulo its period; they are chosen as in `Polygon.eventually_isSimple_inscribed`. -/
private theorem exists_fineMesh (hγ : ContDiff ℝ 1 γ) (hper : Periodic γ T)
    (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T) (hderiv : ∀ t, deriv γ t ≠ 0) :
    ∃ (δ η h : ℝ) (K : NNReal), 0 < h ∧ FineMesh γ T δ η h K := by
  obtain ⟨δ₀, hδ₀, hmono⟩ := hγ.exists_strictMonoOn_dual_comp hderiv 0 T
  obtain ⟨K, hK⟩ := (hγ.contDiffOn (s := Icc 0 T)).exists_lipschitzOnWith one_ne_zero
    (convex_Icc 0 T) isCompact_Icc
  obtain ⟨η, hη, hsep⟩ := TauCeti.exists_pos_le_dist_apply_add hγ.continuous hinj
    isCompact_Icc (by positivity : 0 < δ₀ / 3)
  set h := min (δ₀ / 3) (η / (2 * K + 1))
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  refine ⟨δ₀ / 3, η, h, K, hh, hper, min_le_left _ _, fun a ha ↦ ?_, hK, hsep, ?_⟩
  · exact (hmono a ha).imp fun _ hφ ↦ hφ.mono (Icc_subset_Icc le_rfl (by linarith))
  · have h₁ : h * (2 * K + 1) ≤ η := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    have h₂ : h * (2 * K + 1) = 2 * K * h + h := by ring
    linarith

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
  obtain ⟨δ, η, h, K, hh, hF⟩ := exists_fineMesh hγ hper hinj hderiv
  obtain ⟨N, hN⟩ := exists_nat_ge (T / h)
  refine ⟨N + 1, fun n m _ _ hn hm hsn hsm ↦ ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  -- The uniform meshes with `n + 1` and with `m + 1` parameters have gaps at most `h`.
  have gap (k : ℕ) (hk : N + 1 ≤ k + 1) : T / (k + 1 : ℕ) ≤ h := by
    rw [div_le_iff₀ (by positivity)]
    have : (N : ℝ) ≤ k := by exact_mod_cast Nat.le_of_succ_le_succ hk
    rw [div_le_iff₀ hh] at hN
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right this hh.le]
  have htn := isMesh_uniform hT (gap n hn)
  have htm := isMesh_uniform hT (gap m hm)
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

end Refinement

end Polygon
