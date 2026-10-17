/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Order.Minimal
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Orientation
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.GaussBonnet

/-!
# Compact polygons cut out by finitely many half-planes

A bounded intersection of finitely many closed geodesic half-planes of `ℍ` with nonempty interior
is the carrier of a compact convex polygon
(`exists_compactConvexPolygon_carrier_eq_iInter_closure_leftHalfPlane`). Each side of the polygon
lies on the boundary line of one of the half-planes, with the polygon on the left, and is exactly
the face of the intersection along that line. This converts finite half-plane descriptions, such
as those of bounded Dirichlet domains, into polygons with enumerated vertices and sides.

## Proof

First discard redundant half-planes: in a minimal subfamily with the same intersection `K`, each
line `L` carries a point strictly inside all the other half-planes, found by crossing `L` on the
segment from an interior point to a point violating only the half-plane of `L`. The face `K ∩ L`
is then a nondegenerate compact segment, traversed with `K` on its left. Its terminal point lies
on some other line `L'`, as otherwise `K` would continue along `L`. It is not inside the face of
`L'`, since `L` would then cross into the open right side of `L'`. It is not the terminal point
of that face either, since the two faces would then reach it from opposite sides, which the
signs of the oriented angles there exclude. So it is the initial point of the face on `L'`, and
following faces from terminal to initial points is a permutation of the lines. One of its cycles
lists the vertices of a compact convex polygon, whose carrier contains `K` and, by the hull
property `CompactConvexPolygon.carrier_subset_closure_leftHalfPlane`, lies in `K`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4 (sides and vertices of convex polygons).
-/

public section

open Set UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-! ### Discarding redundant half-planes -/

section Essential

variable {ι : Type*} {t : Finset ι} {L : ι → PSL(2, ℝ)}

/-- A finite family of half-planes containing a common point in all its open half-planes has a
subfamily with the same closed intersection in which every line carries a point strictly inside
all the other half-planes. -/
private theorem exists_subset_iInter_eq_and_essential {p : ℍ}
    (hp : ∀ j ∈ t, p ∈ leftHalfPlane (L j)) :
    ∃ s ⊆ t, ⋂ j ∈ s, closure (leftHalfPlane (L j)) = ⋂ j ∈ t, closure (leftHalfPlane (L j)) ∧
      ∀ k ∈ s, ∃ u : ℝ, ∀ j ∈ s, j ≠ k → geodesicLine (L k) u ∈ leftHalfPlane (L j) := by
  classical
  obtain ⟨s, hst, hs, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun s : Finset ι ↦ ⋂ j ∈ s, closure (leftHalfPlane (L j)) =
      ⋂ j ∈ t, closure (leftHalfPlane (L j))) t rfl
  refine ⟨s, hst, hs, fun k hk ↦ ?_⟩
  -- removing `k` strictly enlarges the intersection, by minimality
  have hsub : ⋂ j ∈ s, closure (leftHalfPlane (L j)) ⊆
      ⋂ j ∈ s.erase k, closure (leftHalfPlane (L j)) :=
    biInter_mono (Finset.erase_subset k s) fun _ _ ↦ Subset.rfl
  obtain ⟨x, hx, hxs⟩ := exists_of_ssubset (hsub.ssubset_of_ne fun heq ↦
    Finset.notMem_erase k s (hmin (heq.symm.trans hs) (Finset.erase_subset k s) hk))
  refine exists_geodesicLine_mem_leftHalfPlane_of_notMem (t := s) (fun j hj ↦ hp j (hst hj)) hk
    (fun j hj hjk ↦ mem_iInter₂.1 hx j (Finset.mem_erase.2 ⟨hjk, hj⟩)) fun hxk ↦ hxs ?_
  refine mem_iInter₂.2 fun j hj ↦ ?_
  by_cases hjk : j = k
  · exact hjk ▸ hxk
  · exact mem_iInter₂.1 hx j (Finset.mem_erase.2 ⟨hjk, hj⟩)

end Essential

/-! ### The faces of an irredundant intersection

Throughout, `K` is the intersection of the closed left half-planes of finitely many geodesic lines
`L k`, each face `K ∩ L k` is the image of `[a k, b k]` with `a k < b k`, and distinct indices
have distinct lines. -/

section Faces

variable {κ : Type*} {L : κ → PSL(2, ℝ)} {K : Set ℍ} {a b : κ → ℝ}

/-- A point of `K` lies in each of the closed half-planes. -/
private theorem mem_closure_leftHalfPlane_of_mem (hK : K = ⋂ j, closure (leftHalfPlane (L j)))
    {z : ℍ} (hz : z ∈ K) (k : κ) : z ∈ closure (leftHalfPlane (L k)) := by
  rw [hK] at hz
  exact mem_iInter.1 hz k

/-- A point of the line of `L k` strictly inside all the other half-planes lies in `K`, and so
does a point a little further along the line. -/
private theorem exists_pos_geodesicLine_add_mem [Finite κ]
    (hK : K = ⋂ j, closure (leftHalfPlane (L j))) {k : κ} {u : ℝ}
    (hu : ∀ j, j ≠ k → geodesicLine (L k) u ∈ leftHalfPlane (L j)) :
    geodesicLine (L k) u ∈ K ∧ ∃ ε > 0, geodesicLine (L k) (u + ε) ∈ K := by
  have hU : IsOpen (geodesicLine (L k) ⁻¹' ⋂ j, ⋂ (_ : j ≠ k), leftHalfPlane (L j)) :=
    (isOpen_iInter_of_finite fun _ ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_leftHalfPlane _).preimage (isometry_geodesicLine _).continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU u (mem_iInter₂.2 hu)
  -- on the line, the half-plane of `L k` itself holds automatically
  have hmem (τ : ℝ) (hτ : τ ∈ Metric.ball u ε) : geodesicLine (L k) τ ∈ K := by
    rw [hK, mem_iInter]
    intro j
    by_cases hjk : j = k
    · rw [hjk, closure_leftHalfPlane]
      exact Or.inr (mem_range_self τ)
    · exact subset_closure (mem_iInter₂.1 (hball hτ) j hjk)
  refine ⟨hmem u (Metric.mem_ball_self hε), ε / 2, half_pos hε, hmem _ ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

/-- If a line carries a point strictly inside all the other half-planes, then its face is a
nondegenerate compact segment. -/
private theorem exists_lt_and_preimage_eq_Icc [Finite κ]
    (hK : K = ⋂ j, closure (leftHalfPlane (L j))) (hb : Bornology.IsBounded K) {k : κ} {u : ℝ}
    (hu : ∀ j, j ≠ k → geodesicLine (L k) u ∈ leftHalfPlane (L j)) :
    ∃ a b : ℝ, a < b ∧ geodesicLine (L k) ⁻¹' K = Icc a b := by
  set S := geodesicLine (L k) ⁻¹' K
  have hcl : IsClosed S := (hK ▸ isClosed_iInter fun _ ↦ isClosed_closure).preimage
    (isometry_geodesicLine _).continuous
  have hoc : S.OrdConnected := by
    simp only [S, hK, preimage_iInter]
    exact ordConnected_iInter fun j ↦ ordConnected_preimage_geodesicLine_closure_leftHalfPlane _ _
  have hc : IsCompact S := Metric.isCompact_of_isClosed_isBounded hcl
    ((isometry_geodesicLine _).antilipschitzWith.isBounded_preimage hb)
  obtain ⟨huS, ε, hε, huS'⟩ := exists_pos_geodesicLine_add_mem hK hu
  refine ⟨sInf S, sSup S, (csInf_le hc.bddBelow huS).trans_lt ((lt_add_of_pos_right u
    hε).trans_le (le_csSup hc.bddAbove huS')), ?_⟩
  exact eq_Icc_of_connected_compact ⟨⟨u, huS⟩, hoc.isPreconnected⟩ hc

variable (hK : K = ⋂ j, closure (leftHalfPlane (L j)))
  (hS : ∀ k, geodesicLine (L k) ⁻¹' K = Icc (a k) (b k)) (hab : ∀ k, a k < b k)
  (hne : ∀ j k, j ≠ k → range (geodesicLine (L j)) ≠ range (geodesicLine (L k)))

include hS in
/-- A point of a line lies in `K` exactly when its parameter lies in the face interval. -/
private theorem geodesicLine_mem_iff (k : κ) (τ : ℝ) :
    geodesicLine (L k) τ ∈ K ↔ τ ∈ Icc (a k) (b k) := by
  rw [← hS k, mem_preimage]

include hK hne in
/-- A point of `K` on the line `L j` lies strictly to the left of another line `L k` meeting `L j`
at a different point. -/
private theorem mem_leftHalfPlane_of_mem_of_ne {j k : κ} (hjk : j ≠ k) {z w : ℍ} (hz : z ∈ K)
    (hzj : z ∈ range (geodesicLine (L j))) (hwj : w ∈ range (geodesicLine (L j)))
    (hwk : w ∈ range (geodesicLine (L k))) (hzw : z ≠ w) : z ∈ leftHalfPlane (L k) := by
  have hz' := mem_closure_leftHalfPlane_of_mem hK hz k
  rw [closure_leftHalfPlane] at hz'
  exact hz'.resolve_right fun hzk ↦ hne j k hjk (range_geodesicLine_eq_of_mem hzw hzj hwj hzk hwk)

include hK hS hab hne in
/-- The relative interior of a face does not meet another line. -/
private theorem geodesicLine_notMem_range_of_mem_Ioo {j k : κ} (hjk : j ≠ k) {τ : ℝ}
    (hτ : τ ∈ Ioo (a j) (b j)) : geodesicLine (L j) τ ∉ range (geodesicLine (L k)) := by
  have hmem (σ : ℝ) (hσ : σ ∈ Icc (a j) (b j)) :
      geodesicLine (L j) σ ∈ closure (leftHalfPlane (L k)) :=
    mem_closure_leftHalfPlane_of_mem hK ((geodesicLine_mem_iff hS j σ).2 hσ) k
  exact notMem_range_geodesicLine_of_mem_leftHalfPlane
    (geodesicLine_mem_leftHalfPlane_of_mem_closure hτ.1 hτ.2
      (hmem _ (left_mem_Icc.2 (hab j).le)) (hmem _ (right_mem_Icc.2 (hab j).le)) (hne j k hjk))

include hK hS hab in
/-- The terminal point of a face lies on another line: otherwise `K` would continue along the
line beyond it. -/
private theorem exists_ne_geodesicLine_mem_range [Finite κ] (k : κ) :
    ∃ j, j ≠ k ∧ geodesicLine (L k) (b k) ∈ range (geodesicLine (L j)) := by
  by_contra! h
  -- otherwise the terminal point is strictly inside the other half-planes, so `K` continues
  have hv : ∀ j, j ≠ k → geodesicLine (L k) (b k) ∈ leftHalfPlane (L j) := fun j hjk ↦ by
    have h' := mem_closure_leftHalfPlane_of_mem hK
      ((geodesicLine_mem_iff hS k _).2 (right_mem_Icc.2 (hab k).le)) j
    rw [closure_leftHalfPlane] at h'
    exact h'.resolve_right (h j hjk)
  obtain ⟨-, ε, hε, hK'⟩ := exists_pos_geodesicLine_add_mem hK hv
  have := ((geodesicLine_mem_iff hS k _).1 hK').2
  linarith

include hab in
/-- The initial and terminal points of a face are distinct. -/
private theorem geodesicLine_left_ne_right (k : κ) :
    geodesicLine (L k) (a k) ≠ geodesicLine (L k) (b k) :=
  (geodesicLine_injective _).ne (hab k).ne

include hK hS hab hne in
/-- Two faces do not end at the same point. -/
private theorem geodesicLine_right_ne_right {j k : κ} (hjk : j ≠ k) :
    geodesicLine (L j) (b j) ≠ geodesicLine (L k) (b k) := by
  intro hv
  have hkab := geodesicLine_left_ne_right (L := L) hab k
  have hjab := geodesicLine_left_ne_right (L := L) hab j
  have hx := mem_leftHalfPlane_of_mem_of_ne hK hne hjk.symm
    ((geodesicLine_mem_iff hS k _).2 (left_mem_Icc.2 (hab k).le)) (mem_range_self _)
    (mem_range_self (b k)) ⟨b j, hv⟩ hkab
  have hy := mem_leftHalfPlane_of_mem_of_ne hK hne hjk
    ((geodesicLine_mem_iff hS j _).2 (left_mem_Icc.2 (hab j).le)) (mem_range_self _)
    (mem_range_self (b j)) ⟨b k, hv.symm⟩ hjab
  -- both faces arrive at the common point, so each is on the right of the other seen from it
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ (hab k),
    leftHalfPlane_geodesicBetween_swap hkab.symm] at hy
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ (hab j),
    leftHalfPlane_geodesicBetween_swap hjab.symm, hv] at hx
  exact notMem_rightHalfPlane_geodesicBetween_of_mem_rightHalfPlane hkab.symm (hv ▸ hjab.symm) hy
    hx

include hK hS hab hne in
/-- Two faces do not start at the same point. -/
private theorem geodesicLine_left_ne_left {j k : κ} (hjk : j ≠ k) :
    geodesicLine (L j) (a j) ≠ geodesicLine (L k) (a k) := by
  intro hv
  have hkab := geodesicLine_left_ne_right (L := L) hab k
  have hjab := geodesicLine_left_ne_right (L := L) hab j
  have hx := mem_leftHalfPlane_of_mem_of_ne hK hne hjk.symm
    ((geodesicLine_mem_iff hS k _).2 (right_mem_Icc.2 (hab k).le)) (mem_range_self _)
    (mem_range_self (a k)) ⟨a j, hv⟩ hkab.symm
  have hy := mem_leftHalfPlane_of_mem_of_ne hK hne hjk
    ((geodesicLine_mem_iff hS j _).2 (right_mem_Icc.2 (hab j).le)) (mem_range_self _)
    (mem_range_self (a j)) ⟨a k, hv.symm⟩ hjab.symm
  -- both faces leave the common point, so each is on the left of the other seen from it
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ (hab k)] at hy
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ (hab j), hv] at hx
  exact notMem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane hkab (hv ▸ hjab) hy hx

include hK hS hab hne in
/-- The terminal point of each face is the initial point of the face of another line. -/
private theorem exists_ne_geodesicLine_right_eq_left [Finite κ] (k : κ) :
    ∃ j, j ≠ k ∧ geodesicLine (L k) (b k) = geodesicLine (L j) (a j) := by
  obtain ⟨j, hjk, τ, hτ⟩ := exists_ne_geodesicLine_mem_range hK hS hab k
  have hτJ : τ ∈ Icc (a j) (b j) := (geodesicLine_mem_iff hS j τ).1
    (hτ ▸ (geodesicLine_mem_iff hS k _).2 (right_mem_Icc.2 (hab k).le))
  refine ⟨j, hjk, ?_⟩
  rcases hτJ.1.eq_or_lt with hτa | hτa
  · rw [← hτ, hτa]
  rcases hτJ.2.eq_or_lt with hτb | hτb
  · exact absurd (hτb ▸ hτ) (geodesicLine_right_ne_right hK hS hab hne hjk)
  · exact absurd ⟨b k, hτ.symm⟩
      (geodesicLine_notMem_range_of_mem_Ioo hK hS hab hne hjk ⟨hτa, hτb⟩)

include hK hS hab hne in
/-- A point of `K` which is the initial point of the face of `j` lies strictly to the left of the
line of a different index `k`, unless it is an endpoint of the face of `k`. -/
private theorem geodesicLine_left_mem_leftHalfPlane {j k : κ} (hjk : j ≠ k)
    (hb' : geodesicLine (L j) (a j) ≠ geodesicLine (L k) (b k))
    (ha' : geodesicLine (L j) (a j) ≠ geodesicLine (L k) (a k)) :
    geodesicLine (L j) (a j) ∈ leftHalfPlane (L k) := by
  have hz := (geodesicLine_mem_iff hS j _).2 (left_mem_Icc.2 (hab j).le)
  have hz' := mem_closure_leftHalfPlane_of_mem hK hz k
  rw [closure_leftHalfPlane] at hz'
  refine hz'.resolve_right ?_
  rintro ⟨τ, hτ⟩
  have hτK : τ ∈ Icc (a k) (b k) := (geodesicLine_mem_iff hS k τ).1 (hτ ▸ hz)
  rcases hτK.1.eq_or_lt with hτa | hτa
  · exact ha' (by rw [← hτ, hτa])
  rcases hτK.2.eq_or_lt with hτb | hτb
  · exact hb' (by rw [← hτ, hτb])
  · exact geodesicLine_notMem_range_of_mem_Ioo hK hS hab hne hjk.symm ⟨hτa, hτb⟩ ⟨a j, hτ.symm⟩

include hab hne in
/-- A cycle of the successor map on faces has at least three lines: one line would be its own
successor, and two lines would share both endpoints of a face. -/
private theorem three_le_minimalPeriod {f : κ → κ} (hfk : ∀ k, f k ≠ k)
    (hf : ∀ k, geodesicLine (L k) (b k) = geodesicLine (L (f k)) (a (f k)))
    (hinj : f.Injective) [Finite κ] (k₀ : κ) : 3 ≤ Function.minimalPeriod f k₀ := by
  have hn0 := Function.minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts k₀)
  have hiter (m : ℕ) (hm : Function.minimalPeriod f k₀ = m) : f^[m] k₀ = k₀ := by
    rw [← hm]
    exact Function.iterate_minimalPeriod
  have hn1 : Function.minimalPeriod f k₀ ≠ 1 := fun h ↦ hfk k₀ (hiter 1 h)
  have hn2 : Function.minimalPeriod f k₀ ≠ 2 := fun h ↦ by
    have h2 : f (f k₀) = k₀ := hiter 2 h
    refine hne (f k₀) k₀ (hfk k₀) (range_geodesicLine_eq_of_mem
      (geodesicLine_left_ne_right (L := L) hab k₀) ?_ ⟨a (f k₀), (hf k₀).symm⟩
      (mem_range_self _) (mem_range_self _))
    exact ⟨b (f k₀), by rw [hf (f k₀), h2]⟩
  omega

include hK hS hab hne in
/-- Following the faces from terminal to initial points, one cycle of lines gives a compact convex
polygon whose carrier is `K` and whose sides are faces. -/
private theorem exists_compactConvexPolygon_of_faces [Finite κ] [Nonempty κ] :
    ∃ (n : ℕ) (_ : NeZero n) (P : CompactConvexPolygon n), P.carrier = K ∧
      ∀ i, ∃ k, leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))) =
          leftHalfPlane (L k) ∧ P.side i = K ∩ range (geodesicLine (L k)) := by
  choose f hfk hf using exists_ne_geodesicLine_right_eq_left hK hS hab hne
  have hinj : f.Injective := fun k₁ k₂ h ↦ by
    by_contra h₁₂
    exact geodesicLine_right_ne_right hK hS hab hne h₁₂ (by rw [hf k₁, hf k₂, h])
  obtain ⟨k₀⟩ := ‹Nonempty κ›
  -- the cycle `c 0, c 1, …` of `k₀` under `f` has length `n`
  set n := Function.minimalPeriod f k₀
  let c : ℕ → κ := fun m ↦ f^[m] k₀
  have hcmod (m : ℕ) : c (m % n) = c m := Function.iterate_mod_minimalPeriod_eq
  have hcsucc (m : ℕ) : c (m + 1) = f (c m) := Function.iterate_succ_apply' f m k₀
  have hcinj {m m' : ℕ} (hm : m < n) (hm' : m' < n) (h : c m = c m') : m = m' :=
    Function.iterate_injOn_Iio_minimalPeriod hm hm' h
  have hn3 : 3 ≤ n := three_le_minimalPeriod hab hne hfk hf hinj k₀
  have : NeZero n := ⟨by omega⟩
  have hsucc (i : Fin n) : c ((i + 1 : Fin n) : ℕ) = f (c i) := by
    rw [← hcsucc, ← hcmod (i + 1), Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  let P : CompactConvexPolygon n :=
    { vertex := fun i ↦ geodesicLine (L (c i)) (a (c i))
      three_le := hn3
      vertex_mem_leftHalfPlane := fun i j hji hji' ↦ by
        rw [hsucc, ← hf, leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ (hab _)]
        have hji₀ : c j ≠ c i := fun h ↦ hji (Fin.ext (hcinj j.isLt i.isLt h))
        refine geodesicLine_left_mem_leftHalfPlane hK hS hab hne hji₀ ?_ ?_
        -- the vertex `j` is neither endpoint of the face of `c i`
        · exact fun h ↦ hji' (Fin.ext (hcinj j.isLt (i + 1).isLt (by
            by_contra h'
            exact geodesicLine_left_ne_left hK hS hab hne h' (by rw [h, hf, hsucc]))))
        · exact geodesicLine_left_ne_left hK hS hab hne hji₀ }
  have hPv (i : Fin n) : P.vertex i = geodesicLine (L (c i)) (a (c i)) := rfl
  have hPv' (i : Fin n) : P.vertex (i + 1) = geodesicLine (L (c i)) (b (c i)) := by
    rw [hPv, hsucc, ← hf]
  have hside (i : Fin n) : leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))) =
      leftHalfPlane (L (c i)) := by
    rw [hPv, hPv', leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ (hab _)]
  refine ⟨n, inferInstance, P, (subset_antisymm ?_ ?_), fun i ↦ ⟨c i, hside i, ?_⟩⟩
  · -- the hull property: every vertex lies in `K`
    rw [hK]
    exact subset_iInter fun k ↦ P.carrier_subset_closure_leftHalfPlane fun i ↦
      mem_closure_leftHalfPlane_of_mem hK
        ((geodesicLine_mem_iff hS (c i) _).2 (left_mem_Icc.2 (hab (c i)).le)) k
  · rw [CompactConvexPolygon.carrier_def]
    refine subset_iInter fun i ↦ ?_
    rw [hside, hK]
    exact iInter_subset _ _
  · rw [CompactConvexPolygon.side_def, hPv, hPv', geodesicSegment_geodesicLine,
      uIcc_of_le (hab (c i)).le]
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨(geodesicLine_mem_iff hS _ τ).2 hτ, mem_range_self τ⟩
    · rintro ⟨hz, τ, rfl⟩
      exact ⟨τ, (geodesicLine_mem_iff hS _ τ).1 hz, rfl⟩

end Faces

/-! ### The polygon -/

/-- **A bounded intersection of finitely many closed half-planes is a compact convex polygon.**
Let `K` be the intersection of the closed left half-planes of the geodesic lines `L k`, `k ∈ t`,
for a finite set `t`. If `K` is bounded with nonempty interior, it is the carrier of a compact
convex polygon. Each side of the polygon is the face `K ∩ L k` of `K` along the line of some
`k ∈ t`, and the polygon lies to the left of that line. -/
theorem exists_compactConvexPolygon_carrier_eq_iInter_closure_leftHalfPlane {ι : Type*}
    (t : Finset ι) (L : ι → PSL(2, ℝ))
    (hint : (interior (⋂ k ∈ t, closure (leftHalfPlane (L k)))).Nonempty)
    (hb : Bornology.IsBounded (⋂ k ∈ t, closure (leftHalfPlane (L k)))) :
    ∃ (n : ℕ) (_ : NeZero n) (P : CompactConvexPolygon n),
      P.carrier = ⋂ k ∈ t, closure (leftHalfPlane (L k)) ∧
      ∀ i, ∃ k ∈ t, leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))) =
          leftHalfPlane (L k) ∧
        P.side i = (⋂ k ∈ t, closure (leftHalfPlane (L k))) ∩ range (geodesicLine (L k)) := by
  obtain ⟨p, hp⟩ := hint
  simp only [Finset.interior_iInter, interior_closure_leftHalfPlane, mem_iInter₂] at hp
  obtain ⟨s, hst, hs, hess⟩ := exists_subset_iInter_eq_and_essential hp
  -- pass to the irredundant subfamily `s`, indexed by its elements
  let L' : s → PSL(2, ℝ) := fun k ↦ L k
  have hK : ⋂ k ∈ t, closure (leftHalfPlane (L k)) = ⋂ k : s, closure (leftHalfPlane (L' k)) := by
    rw [← hs]
    ext z
    simp [L']
  have hess' (k : s) :
      ∃ u : ℝ, ∀ j : s, j ≠ k → geodesicLine (L' k) u ∈ leftHalfPlane (L' j) := by
    obtain ⟨u, hu⟩ := hess k k.2
    exact ⟨u, fun j hj ↦ hu j j.2 (Subtype.coe_injective.ne hj)⟩
  choose u hu using hess'
  choose a b hab hS using fun k ↦ exists_lt_and_preimage_eq_Icc hK hb (hu k)
  have hne (j k : s) (hjk : j ≠ k) :
      range (geodesicLine (L' j)) ≠ range (geodesicLine (L' k)) := fun h ↦
    notMem_range_geodesicLine_of_mem_leftHalfPlane (hu k j hjk) (by rw [h]; exact mem_range_self _)
  -- an empty family would give the unbounded set `ℍ`
  have : Nonempty s := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [hK, iInter_of_empty] at hb
    have h' := (isometry_geodesicLine 1).antilipschitzWith.isBounded_preimage hb
    rw [preimage_univ] at h'
    exact not_bddAbove_univ h'.bddAbove
  obtain ⟨n, _, P, hPK, hPs⟩ := exists_compactConvexPolygon_of_faces hK hS hab hne
  refine ⟨n, inferInstance, P, hPK, fun i ↦ ?_⟩
  obtain ⟨k, h₁, h₂⟩ := hPs i
  exact ⟨k, hst k.2, h₁, h₂⟩

end TauCeti.UpperHalfPlane
