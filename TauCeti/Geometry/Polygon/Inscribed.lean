/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import TauCeti.Analysis.Calculus.Deriv.DualStrictMono
public import TauCeti.Geometry.Polygon.Simple
public import TauCeti.Topology.Instances.Real.InjectiveModPeriod

/-!
# Inscribed polygons of a `C¹` loop

A closed curve `γ : ℝ → P` of period `T` carries, for each `n`, the **inscribed polygon**
`Polygon.inscribed γ T n` whose `n` vertices are the points `γ (k * (T / n))`, `0 ≤ k < n`, in
order. This file proves that inscribed polygons approximate an embedded `C¹` loop without
self-intersections: if `γ` is a `C¹` map into a real normed space with nowhere vanishing derivative,
injective modulo its period, then its inscribed polygons are simple for all large `n`
(`Polygon.eventually_isSimple_inscribed`). The specialisation to smooth embeddings of the circle is
`TauCeti.SmoothEmbedding.eventually_isSimple_inscribed` in `TauCeti.KnotTheory.InscribedPolygon`.

## Main definitions

* `Polygon.inscribed γ T n`: the polygon with vertices `γ (k * (T / n))`.

## Main results

* `Polygon.edgeSet_inscribed`: the edges of the polygon inscribed in a periodic curve.
* `Polygon.eventually_isSimple_inscribed`: the inscribed polygons of a `C¹` loop with nowhere
  vanishing derivative, injective modulo its period, are eventually simple.

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

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Appendix I, for
  inscribed polygons of a knot of class `C¹`.
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
  have h₁ := hmono ha (mem h hh.le (by nlinarith)) (by linarith)
  have h₂ := hmono (mem (r * h) (by positivity) (by linarith))
    (mem (r * h + h) (by positivity) le_rfl) (by linarith)
  rw [← add_assoc] at h₂
  rw [segment_eq_image'] at hx hx'
  obtain ⟨θ, ⟨-, hθ₁⟩, rfl⟩ := hx
  obtain ⟨θ', ⟨hθ'₀, -⟩, hθ'⟩ := hx'
  dsimp only at hθ' h₁ h₂ ⊢
  -- Apply `φ` to the two descriptions of the common point.
  have hφ := congrArg φ hθ'
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hφ
  obtain rfl | hr2 := eq_or_lt_of_le hr
  · refine ⟨rfl, ?_⟩
    simp only [Nat.cast_one, one_mul] at hφ h₂
    -- `φ` of the common point is at most `φ (γ (a + h))` and at least it, so `θ = 1`.
    have hθ : θ = 1 := by nlinarith
    rw [hθ, one_smul, add_sub_cancel]
  · have h₃ := hmono (mem h hh.le (by nlinarith)) (mem (r * h) (by positivity) (by linarith))
      (by have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
          nlinarith)
    dsimp only at h₃
    nlinarith

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

end Polygon
