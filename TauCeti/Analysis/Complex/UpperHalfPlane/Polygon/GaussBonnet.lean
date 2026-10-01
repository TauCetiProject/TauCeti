/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic

import TauCeti.Analysis.Complex.UpperHalfPlane.IdealRegion
import TauCeti.Data.Fin.Basic

/-!
# The Gauss–Bonnet formula for compact convex hyperbolic polygons

The invariant area of a compact convex hyperbolic polygon (all vertices in `ℍ`) with `n` vertices
and interior angles `α₀, …, αₙ₋₁` is `(n - 2) π - (α₀ + ⋯ + αₙ₋₁)`
(`CompactConvexPolygon.volume_carrier`).

The file also provides the cut of a polygon along the diagonal from its penultimate vertex to
`vertex 0`, used to argue by induction on the number of vertices
(`CompactConvexPolygon.induction`): the first `n - 1` vertices form a convex polygon
(`CompactConvexPolygon.eraseLast`); seen from `vertex 0` the vertices are in increasing angular
order (`CompactConvexPolygon.toReal_orientedAngle_lt`); the diagonal has the last vertex strictly on
its right and the others strictly on its left
(`CompactConvexPolygon.last_mem_rightHalfPlane_diagonal`,
`CompactConvexPolygon.mem_leftHalfPlane_diagonal`); the carrier is the union of the carrier of
`eraseLast` and the triangle on the last three vertices
(`CompactConvexPolygon.carrier_eq_union_triangle`), which meet only on the line through the
diagonal (`CompactConvexPolygon.carrier_eraseLast_inter_triangle_subset`); and the angle sum
splits accordingly (`CompactConvexPolygon.sum_interiorAngle_eq`).

## Main results

* `CompactConvexPolygon.volume_carrier`: **Gauss–Bonnet for compact convex polygons** (all
  vertices in `ℍ`), the area is `(n - 2) π` minus the sum of the interior angles.
* `CompactConvexPolygon.sum_interiorAngle_le`: the sum of the interior angles is at most
  `(n - 2) π`.
* `CompactConvexPolygon.carrier_subset_closure_leftHalfPlane`: the carrier lies in every closed
  half-plane containing the vertices.
* `CompactConvexPolygon.isCompact_carrier`: the carrier is compact.
* `CompactConvexPolygon.induction`: induction on the number of vertices, cutting off the last
  one.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), Theorem 7.2.2 and
its proof ("Cut up P into triangles. Apply Theorem 7.2.1 to each triangle and then sum the
areas."). The bookkeeping of the cut is ours.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane

namespace CompactConvexPolygon

variable {n : ℕ} [NeZero n] (P : CompactConvexPolygon n)

/-! ### The angular order of the vertices seen from `vertex 0` -/

/-- The first two vertices are distinct. -/
private theorem vertex_zero_ne_vertex_one : P.vertex 0 ≠ P.vertex 1 := by
  simpa using P.vertex_ne_vertex_add_one 0

/-- Every vertex other than `vertex 0` and `vertex 1` lies to the left of the first edge. -/
private theorem vertex_mem_leftHalfPlane_zero {j : Fin n} (hj₀ : j ≠ 0) (hj₁ : j ≠ 1) :
    P.vertex j ∈ leftHalfPlane (geodesicBetween (P.vertex 0) (P.vertex 1)) := by
  have h := P.vertex_mem_leftHalfPlane 0 j hj₀ (by rwa [zero_add])
  rwa [zero_add] at h

/-- The convexity condition read cyclically: `vertex (k + 1)` lies to the left of the geodesic
from `vertex i` to `vertex k` whenever `i` is neither `k` nor `k + 1`. -/
theorem vertex_add_one_mem_leftHalfPlane {i k : Fin n} (hi : i ≠ k) (hi' : i ≠ k + 1) :
    P.vertex (k + 1) ∈ leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex k)) :=
  mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane (P.vertex_injective.ne hi'.symm)
    (mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane (P.vertex_ne_vertex_add_one k)
      (P.vertex_mem_leftHalfPlane k i hi hi'))

/-- Seen from `vertex 0`, every other vertex lies to the left of the first edge, so its oriented
angle from the first edge is positive. -/
theorem toReal_orientedAngle_pos {j : Fin n} (hj₀ : j ≠ 0) (hj₁ : j ≠ 1) :
    0 < (orientedAngle (P.vertex 0) (P.vertex 1) (P.vertex j)).toReal := by
  have hsign := (orientedAngle_sign_eq_one_iff (P.vertex_injective.ne hj₀.symm)).2
    (P.vertex_mem_leftHalfPlane_zero hj₀ hj₁)
  rwa [← sign_eq_one_iff, Real.Angle.sign_toReal fun h ↦ by simp [h] at hsign]

/-- Seen from `vertex 0`, consecutive vertices are in increasing angular order. -/
private theorem toReal_orientedAngle_lt_add_one {k : Fin n} (hk₀ : k ≠ 0) (hk₁ : k + 1 ≠ 0) :
    (orientedAngle (P.vertex 0) (P.vertex 1) (P.vertex k)).toReal <
      (orientedAngle (P.vertex 0) (P.vertex 1) (P.vertex (k + 1))).toReal := by
  have hk₁' : k + 1 ≠ 1 := fun h ↦ hk₀ (add_left_injective 1 (h.trans (zero_add 1).symm))
  by_cases hk : k = 1
  · subst hk
    rw [orientedAngle_self, Real.Angle.toReal_zero]
    exact P.toReal_orientedAngle_pos hk₁ hk₁'
  · exact (toReal_orientedAngle_lt_iff
      (P.vertex_mem_leftHalfPlane_zero hk₀ hk) (P.vertex_mem_leftHalfPlane_zero hk₁ hk₁')).2
      (P.vertex_add_one_mem_leftHalfPlane hk₀.symm hk₁.symm)

/-- Seen from `vertex 0`, the vertices are in increasing angular order. -/
theorem toReal_orientedAngle_lt {j k : Fin n} (hj : j ≠ 0) (hjk : j < k) :
    (orientedAngle (P.vertex 0) (P.vertex 1) (P.vertex j)).toReal <
      (orientedAngle (P.vertex 0) (P.vertex 1) (P.vertex k)).toReal := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  induction k using Fin.induction with
  | zero => exact absurd hjk (Fin.not_lt_zero j)
  | succ k ih =>
    have hk₁ : Fin.castSucc k + 1 ≠ 0 := by rw [Fin.coeSucc_eq_succ]; exact Fin.succ_ne_zero k
    rw [← Fin.coeSucc_eq_succ]
    rcases (Fin.le_castSucc_iff.2 hjk).lt_or_eq with h | rfl
    · exact (ih h).trans (P.toReal_orientedAngle_lt_add_one
        ((Fin.pos_iff_ne_zero.2 hj).trans_le h.le).ne' hk₁)
    · exact P.toReal_orientedAngle_lt_add_one hj hk₁

/-! ### Cutting off the last vertex

Throughout this section `P : CompactConvexPolygon (n + 2)` with `2 ≤ n`, so `P` has at least four
vertices: the penultimate one is `P.vertex (Fin.castSucc (Fin.last n))` (index `n`) and the last
one is `P.vertex (Fin.last (n + 1))` (index `n + 1`). The diagonal from the penultimate vertex to
`vertex 0` cuts `P` into the polygon `P.eraseLast hn : CompactConvexPolygon (n + 1)` on the first
`n + 1` vertices, indexed through `Fin.castSucc`, and the triangle on the penultimate vertex, the
last vertex and `vertex 0`. -/

section eraseLast

variable (P : CompactConvexPolygon (n + 2)) (hn : 2 ≤ n)

omit [NeZero n]

/-- Every vertex other than `vertex 0` and the last two lies to the left of the diagonal from the
penultimate vertex to `vertex 0`. -/
theorem mem_leftHalfPlane_diagonal {j : Fin (n + 2)} (hj₀ : j ≠ 0) (hj : j.val < n) :
    P.vertex j ∈ leftHalfPlane (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n)))
      (P.vertex 0)) := by
  have hn : 2 ≤ n := by have := Fin.pos_iff_ne_zero.2 hj₀; omega
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  have key : P.vertex (Fin.castSucc (Fin.last n)) ∈
      leftHalfPlane (geodesicBetween (P.vertex 0) (P.vertex j)) := by
    by_cases hj₁ : j = 1
    · subst hj₁
      exact P.vertex_mem_leftHalfPlane_zero (Fin.castSucc_last_ne_zero hn₀)
        (Fin.castSucc_last_ne_one hn₁)
    · exact (toReal_orientedAngle_lt_iff
        (P.vertex_mem_leftHalfPlane_zero hj₀ hj₁)
        (P.vertex_mem_leftHalfPlane_zero (Fin.castSucc_last_ne_zero hn₀)
          (Fin.castSucc_last_ne_one hn₁))).1 (P.toReal_orientedAngle_lt hj₀ (Fin.lt_def.2 hj))
  exact mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane
    (P.vertex_injective.ne (Fin.ne_of_val_ne hj.ne))
    (mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane (P.vertex_injective.ne hj₀.symm) key)

include hn in
/-- The last vertex lies to the right of the diagonal from the penultimate vertex to
`vertex 0`. -/
theorem last_mem_rightHalfPlane_diagonal :
    P.vertex (Fin.last (n + 1)) ∈
      rightHalfPlane (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex 0)) := by
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  rw [← leftHalfPlane_geodesicBetween_swap (P.vertex_injective.ne (Fin.castSucc_last_ne_zero hn₀))]
  exact (toReal_orientedAngle_lt_iff
    (P.vertex_mem_leftHalfPlane_zero (Fin.castSucc_last_ne_zero hn₀) (Fin.castSucc_last_ne_one hn₁))
    (P.vertex_mem_leftHalfPlane_zero (Fin.last_pos' ..).ne' (Fin.last_ne_one hn₀))).1
    (P.toReal_orientedAngle_lt (Fin.castSucc_last_ne_zero hn₀) (Fin.castSucc_lt_last _))

/-- The convex polygon on the first `n + 1` vertices of a convex polygon with `n + 2 ≥ 4`
vertices. -/
def eraseLast : CompactConvexPolygon (n + 1) where
  vertex := P.vertex ∘ Fin.castSucc
  three_le := by omega
  vertex_mem_leftHalfPlane := by
    intro i j hji hji'
    simp only [Function.comp_apply]
    by_cases hi : i = Fin.last n
    · subst hi
      rw [Fin.last_add_one, Fin.castSucc_zero]
      exact P.mem_leftHalfPlane_diagonal
        (Fin.castSucc_ne_zero_iff.2 (by rwa [Fin.last_add_one] at hji')) (Fin.val_lt_last hji)
    · rw [Fin.castSucc_add_one_of_ne_last hi]
      exact P.vertex_mem_leftHalfPlane _ _ ((Fin.castSucc_injective _).ne hji)
        (by rw [← Fin.castSucc_add_one_of_ne_last hi]; exact (Fin.castSucc_injective _).ne hji')

/-- The vertices of `eraseLast`. -/
@[simp]
theorem vertex_eraseLast (i : Fin (n + 1)) :
    (P.eraseLast hn).vertex i = P.vertex (Fin.castSucc i) := by
  rfl

include hn in
/-- `vertex 0` lies to the left of the edge from the penultimate vertex to the last one. -/
private theorem zero_mem_leftHalfPlane_penultimate_last :
    P.vertex 0 ∈ leftHalfPlane (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n)))
      (P.vertex (Fin.last (n + 1)))) := by
  have hn₀ : n ≠ 0 := by omega
  rw [← (Fin.coeSucc_eq_succ.trans (Fin.succ_last _))]
  exact P.vertex_mem_leftHalfPlane _ _ (Fin.castSucc_last_ne_zero hn₀).symm
    (by rw [(Fin.coeSucc_eq_succ.trans (Fin.succ_last _))]; exact (Fin.last_pos' ..).ne)

include hn in
/-- The penultimate vertex lies to the left of the edge from the last vertex to `vertex 0`. -/
private theorem penultimate_mem_leftHalfPlane_last_zero :
    P.vertex (Fin.castSucc (Fin.last n)) ∈
      leftHalfPlane (geodesicBetween (P.vertex (Fin.last (n + 1))) (P.vertex 0)) := by
  have hn₀ : n ≠ 0 := by omega
  rw [← Fin.last_add_one (n + 1)]
  exact P.vertex_mem_leftHalfPlane _ _ (Fin.castSucc_lt_last _).ne
    (by rw [Fin.last_add_one]; exact Fin.castSucc_last_ne_zero hn₀)

include hn in
/-- The last vertex lies to the left of the diagonal from `vertex 0` to the penultimate
vertex. -/
private theorem last_mem_leftHalfPlane_zero_penultimate :
    P.vertex (Fin.last (n + 1)) ∈
      leftHalfPlane (geodesicBetween (P.vertex 0) (P.vertex (Fin.castSucc (Fin.last n)))) := by
  have hn₀ : n ≠ 0 := by omega
  rw [leftHalfPlane_geodesicBetween_swap (P.vertex_injective.ne (Fin.castSucc_last_ne_zero hn₀))]
  exact P.last_mem_rightHalfPlane_diagonal hn

include hn in
/-- The triangle on the last three vertices is the intersection of the closed left half-planes of
the last two edges with the closed right half-plane of the diagonal. -/
private theorem triangle_eq_inter :
    triangle (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1))) (P.vertex 0) =
      closure (leftHalfPlane (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n)))
          (P.vertex (Fin.castSucc (Fin.last n) + 1)))) ∩
        closure (leftHalfPlane (geodesicBetween (P.vertex (Fin.last (n + 1)))
          (P.vertex (Fin.last (n + 1) + 1)))) ∩
        closure (rightHalfPlane (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n)))
          (P.vertex 0))) := by
  have hn₀ : n ≠ 0 := by omega
  rw [triangle_def, (Fin.coeSucc_eq_succ.trans (Fin.succ_last _)), Fin.last_add_one,
    ← leftHalfPlane_geodesicBetween_swap (P.vertex_injective.ne (Fin.castSucc_last_ne_zero hn₀)),
    ← closedSide_eq_closure_leftHalfPlane_of_mem (P.zero_mem_leftHalfPlane_penultimate_last hn),
    ← closedSide_eq_closure_leftHalfPlane_of_mem (P.penultimate_mem_leftHalfPlane_last_zero hn),
    ← closedSide_eq_closure_leftHalfPlane_of_mem (P.last_mem_leftHalfPlane_zero_penultimate hn)]

/-- A point lies in the carrier of `eraseLast` if and only if it lies in the closed left
half-planes of the first `n` edges and of the diagonal. -/
theorem mem_carrier_eraseLast_iff (z : ℍ) :
    z ∈ (P.eraseLast hn).carrier ↔
      (∀ i : Fin (n + 2), i.val < n →
        z ∈ closure (leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))))) ∧
      z ∈ closure (leftHalfPlane (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n)))
        (P.vertex 0))) := by
  rw [mem_carrier_iff]
  simp only [vertex_eraseLast]
  constructor
  · intro h
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · obtain ⟨i, rfl⟩ : ∃ i' : Fin (n + 1), Fin.castSucc i' = i := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      have := h i
      rwa [Fin.castSucc_add_one_of_ne_last (Fin.ne_of_val_ne hi.ne)] at this
    · have := h (Fin.last n)
      rwa [Fin.last_add_one, Fin.castSucc_zero] at this
  · rintro ⟨h, hc⟩ i
    by_cases hi : i = Fin.last n
    · subst hi
      rwa [Fin.last_add_one, Fin.castSucc_zero]
    · rw [Fin.castSucc_add_one_of_ne_last hi]
      exact h _ (Fin.val_lt_last hi)

/-- The carrier of a convex polygon is the union of the carrier of `eraseLast` and the triangle
on the last three vertices, provided both lie in the relevant closed half-planes. These
hypotheses are discharged in `carrier_eq_union_triangle` once the hull property is known. -/
private theorem carrier_eq_union_triangle_of_subset
    (hK : ∀ i : Fin (n + 2), n ≤ i.val → (P.eraseLast hn).carrier ⊆
      closure (leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1)))))
    (hT : ∀ i : Fin (n + 2), i.val < n →
      triangle (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1))) (P.vertex 0) ⊆
        closure (leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))))) :
    P.carrier = (P.eraseLast hn).carrier ∪
      triangle (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1)))
        (P.vertex 0) := by
  ext z
  rw [Set.mem_union, mem_carrier_iff]
  constructor
  · intro h
    by_cases hz : z ∈ closure (leftHalfPlane (geodesicBetween
      (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex 0)))
    · exact Or.inl ((P.mem_carrier_eraseLast_iff hn z).2 ⟨fun i _ ↦ h i, hz⟩)
    · rw [mem_closure_leftHalfPlane_iff, not_le] at hz
      refine Or.inr ?_
      rw [P.triangle_eq_inter hn]
      exact ⟨⟨h _, h _⟩, (mem_closure_rightHalfPlane_iff _ _).2 hz.le⟩
  · rintro (hz | hz) i
    · by_cases hi : i.val < n
      · exact ((P.mem_carrier_eraseLast_iff hn z).1 hz).1 i hi
      · exact hK i (not_lt.1 hi) hz
    · by_cases hi : i.val < n
      · exact hT i hi hz
      · rw [P.triangle_eq_inter hn] at hz
        rcases Fin.eq_castSucc_last_or_eq_last (not_lt.1 hi) with rfl | rfl
        · exact hz.1.1
        · exact hz.1.2

/-- The two pieces of the cut meet only on the geodesic line through the diagonal. -/
theorem carrier_eraseLast_inter_triangle_subset :
    (P.eraseLast hn).carrier ∩
        triangle (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1)))
          (P.vertex 0) ⊆
      Set.range (geodesicLine (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n)))
        (P.vertex 0))) := by
  rintro z ⟨hzK, hzT⟩
  rw [P.triangle_eq_inter hn] at hzT
  rw [mem_range_geodesicLine_iff]
  exact le_antisymm
    ((mem_closure_leftHalfPlane_iff _ _).1 ((P.mem_carrier_eraseLast_iff hn z).1 hzK).2)
    ((mem_closure_rightHalfPlane_iff _ _).1 hzT.2)

/-- The interior angle at `vertex 0` splits along the diagonal. -/
theorem interiorAngle_zero_eq :
    P.interiorAngle 0 = (P.eraseLast hn).interiorAngle 0 +
      UpperHalfPlane.interiorAngle (P.vertex 0) (P.vertex (Fin.castSucc (Fin.last n)))
        (P.vertex (Fin.last (n + 1))) := by
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  have h₁ : Fin.castSucc (1 : Fin (n + 1)) = 1 := by
    rw [← zero_add (1 : Fin (n + 1)), Fin.castSucc_add_one_of_ne_last (Fin.last_ne_zero hn₀).symm,
      Fin.castSucc_zero, zero_add]
  simp only [CompactConvexPolygon.interiorAngle_def, vertex_eraseLast, Fin.zero_sub_one_eq_last, h₁,
    Fin.castSucc_zero, zero_add]
  rw [interiorAngle_comm (P.vertex 0) (P.vertex 1) (P.vertex (Fin.last (n + 1))),
    interiorAngle_comm (P.vertex 0) (P.vertex 1) (P.vertex (Fin.castSucc (Fin.last n)))]
  exact interiorAngle_add
    (P.vertex_mem_leftHalfPlane_zero (Fin.castSucc_last_ne_zero hn₀) (Fin.castSucc_last_ne_one hn₁))
    (P.vertex_mem_leftHalfPlane_zero (Fin.last_pos' ..).ne' (Fin.last_ne_one hn₀))
    (P.last_mem_leftHalfPlane_zero_penultimate hn)

/-- The interior angle at the penultimate vertex splits along the diagonal. -/
theorem interiorAngle_penultimate_eq :
    P.interiorAngle (Fin.castSucc (Fin.last n)) =
      (P.eraseLast hn).interiorAngle (Fin.last n) +
        UpperHalfPlane.interiorAngle (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex 0)
          (P.vertex (Fin.last (n + 1))) := by
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  have hD : P.vertex (Fin.castSucc (Fin.last n) - 1) ∈ leftHalfPlane (geodesicBetween
      (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1)))) := by
    rw [← (Fin.coeSucc_eq_succ.trans (Fin.succ_last _))]
    exact P.vertex_mem_leftHalfPlane _ _ (sub_one_ne_self (by omega) _)
      (add_one_ne_sub_one (by omega) _).symm
  have hCD : P.vertex (Fin.castSucc (Fin.last n) - 1) ∈ leftHalfPlane (geodesicBetween
      (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex 0)) :=
    P.mem_leftHalfPlane_diagonal (sub_ne_zero.2 (Fin.castSucc_last_ne_one hn₁))
      (by rw [Fin.coe_sub_one, ite_eq_right (Fin.castSucc_last_ne_zero hn₀), Fin.val_castSucc,
            Fin.val_last]
          omega)
  simp only [CompactConvexPolygon.interiorAngle_def, vertex_eraseLast, Fin.coeSucc_eq_succ,
    Fin.succ_last, Fin.castSucc_sub_one_of_ne_zero (Fin.last_ne_zero hn₀), Fin.last_add_one,
    Fin.castSucc_zero]
  rw [interiorAngle_comm (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1)))
      (P.vertex (Fin.castSucc (Fin.last n) - 1)),
    interiorAngle_comm (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex 0)
      (P.vertex (Fin.castSucc (Fin.last n) - 1)),
    interiorAngle_comm (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1)))
      (P.vertex 0)]
  exact (interiorAngle_add (P.zero_mem_leftHalfPlane_penultimate_last hn) hD hCD).trans
    (add_comm _ _)

/-- The interior angle at the last vertex is that of the triangle on the last three vertices. -/
theorem interiorAngle_last_eq :
    P.interiorAngle (Fin.last (n + 1)) =
      UpperHalfPlane.interiorAngle (P.vertex (Fin.last (n + 1)))
        (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex 0) := by
  rw [CompactConvexPolygon.interiorAngle_def,
    (eq_sub_of_add_eq (Fin.coeSucc_eq_succ.trans (Fin.succ_last _))).symm,
    Fin.last_add_one]

/-- The interior angles away from the diagonal are unchanged. -/
theorem interiorAngle_castSucc_eq {i : Fin (n + 1)} (hi₀ : i ≠ 0) (hi : i ≠ Fin.last n) :
    P.interiorAngle (Fin.castSucc i) = (P.eraseLast hn).interiorAngle i := by
  simp only [CompactConvexPolygon.interiorAngle_def, vertex_eraseLast,
    Fin.castSucc_sub_one_of_ne_zero hi₀, Fin.castSucc_add_one_of_ne_last hi]

/-- The sum of the interior angles splits along the diagonal. -/
theorem sum_interiorAngle_eq :
    ∑ i, P.interiorAngle i = ∑ i, (P.eraseLast hn).interiorAngle i +
      (UpperHalfPlane.interiorAngle (P.vertex (Fin.castSucc (Fin.last n)))
          (P.vertex (Fin.last (n + 1))) (P.vertex 0) +
        UpperHalfPlane.interiorAngle (P.vertex (Fin.last (n + 1))) (P.vertex 0)
          (P.vertex (Fin.castSucc (Fin.last n))) +
        UpperHalfPlane.interiorAngle (P.vertex 0) (P.vertex (Fin.castSucc (Fin.last n)))
          (P.vertex (Fin.last (n + 1)))) := by
  have hS : ∑ i ∈ (Finset.univ.erase 0).erase (Fin.last n), P.interiorAngle (Fin.castSucc i) =
      ∑ i ∈ (Finset.univ.erase 0).erase (Fin.last n), (P.eraseLast hn).interiorAngle i :=
    Finset.sum_congr rfl fun i hi ↦ P.interiorAngle_castSucc_eq hn
      (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1 (Finset.mem_erase.1 hi).1
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eq_zero_add_last_add_sum_erase (by omega),
    Fin.sum_univ_eq_zero_add_last_add_sum_erase (by omega), hS, Fin.castSucc_zero,
    P.interiorAngle_zero_eq hn, P.interiorAngle_penultimate_eq hn, P.interiorAngle_last_eq,
    interiorAngle_comm (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1)))
      (P.vertex 0),
    interiorAngle_comm (P.vertex (Fin.last (n + 1))) (P.vertex 0)
      (P.vertex (Fin.castSucc (Fin.last n)))]
  ring

/-- The last two vertices are distinct. -/
private theorem vertex_penultimate_ne_last :
    P.vertex (Fin.castSucc (Fin.last n)) ≠ P.vertex (Fin.last (n + 1)) :=
  (Fin.coeSucc_eq_succ.trans (Fin.succ_last _)) ▸ P.vertex_ne_vertex_add_one _

include hn in
/-- `vertex 0` is not on the geodesic through the edge from the penultimate vertex to the last
one. -/
private theorem zero_notMem_range_geodesicLine_penultimate_last :
    P.vertex 0 ∉ Set.range (geodesicLine (geodesicBetween (P.vertex (Fin.castSucc (Fin.last n)))
      (P.vertex (Fin.last (n + 1))))) := by
  have hn₀ : n ≠ 0 := by omega
  rw [← (Fin.coeSucc_eq_succ.trans (Fin.succ_last _))]
  exact P.vertex_notMem_range_geodesicLine (Fin.castSucc_last_ne_zero hn₀).symm
    (by rw [(Fin.coeSucc_eq_succ.trans (Fin.succ_last _))]; exact (Fin.last_pos' ..).ne)

include hn in
/-- The triangle on the last three vertices lies in the closed left half-plane of every edge. -/
private theorem triangle_subset_closure_leftHalfPlane_edge (i : Fin (n + 2)) :
    triangle (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1))) (P.vertex 0) ⊆
      closure (leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1)))) :=
  triangle_subset_closure_leftHalfPlane P.vertex_penultimate_ne_last
    (P.zero_notMem_range_geodesicLine_penultimate_last hn) (P.vertex_mem_closure_leftHalfPlane i _)
    (P.vertex_mem_closure_leftHalfPlane i _) (P.vertex_mem_closure_leftHalfPlane i _)

end eraseLast

/-! ### Induction on the number of vertices -/

/-- To prove a property of every convex polygon, prove it for polygons with three vertices and
show that it passes from `Q.eraseLast hn` to `Q`. In the inductive step `Q : CompactConvexPolygon (n
+ 2)` with `2 ≤ n` has at least four vertices, and `Q.eraseLast hn : CompactConvexPolygon (n + 1)`
is the polygon on its first `n + 1` vertices: the vertex cut off is `Q.vertex (Fin.last (n + 1))`,
and the last vertex of `Q.eraseLast hn` is the penultimate vertex `Q.vertex (Fin.castSucc (Fin.last
n))` of `Q`. -/
@[elab_as_elim]
theorem induction {motive : ∀ {n : ℕ} [NeZero n], CompactConvexPolygon n → Prop}
    (triangle : ∀ Q : CompactConvexPolygon 3, motive Q)
    (eraseLast : ∀ {n : ℕ} (hn : 2 ≤ n) (Q : CompactConvexPolygon (n + 2)),
      motive (Q.eraseLast hn) → motive Q)
    (P : CompactConvexPolygon n) : motive P := by
  have key : ∀ m, 3 ≤ m → ∀ [NeZero m] (Q : CompactConvexPolygon m), motive Q := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun Q ↦ triangle Q
    | succ m hm ih =>
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact fun Q ↦ eraseLast (by omega) Q (ih _)
  exact key n P.three_le P

/-! ### The hull property and compactness -/

/-- In a polygon with three vertices, the third vertex is off the geodesic through the first
edge. -/
private theorem vertex_two_notMem_range_geodesicLine (P : CompactConvexPolygon 3) :
    P.vertex 2 ∉ Set.range (geodesicLine (geodesicBetween (P.vertex 0) (P.vertex 1))) :=
  P.vertex_notMem_range_geodesicLine (by decide) (by decide)

/-- **The carrier lies in every closed half-plane containing the vertices.** -/
theorem carrier_subset_closure_leftHalfPlane {g : PSL(2, ℝ)}
    (h : ∀ i, P.vertex i ∈ closure (leftHalfPlane g)) : P.carrier ⊆ closure (leftHalfPlane g) := by
  induction P using CompactConvexPolygon.induction generalizing g with
  | triangle Q =>
    rw [Q.carrier_three]
    exact triangle_subset_closure_leftHalfPlane Q.vertex_zero_ne_vertex_one
      Q.vertex_two_notMem_range_geodesicLine (h 0) (h 1) (h 2)
  | eraseLast hn Q ih =>
    rw [Q.carrier_eq_union_triangle_of_subset hn
      (fun i _ ↦ ih fun j ↦ Q.vertex_mem_closure_leftHalfPlane i (Fin.castSucc j))
      fun i _ ↦ Q.triangle_subset_closure_leftHalfPlane_edge hn i]
    exact Set.union_subset (ih fun j ↦ h (Fin.castSucc j))
      (triangle_subset_closure_leftHalfPlane Q.vertex_penultimate_ne_last
        (Q.zero_notMem_range_geodesicLine_penultimate_last hn) (h _) (h _) (h _))

omit [NeZero n] in
/-- The carrier of a convex polygon is the union of the carrier of `eraseLast` and the triangle
on the last three vertices. -/
theorem carrier_eq_union_triangle (P : CompactConvexPolygon (n + 2)) (hn : 2 ≤ n) :
    P.carrier = (P.eraseLast hn).carrier ∪
      triangle (P.vertex (Fin.castSucc (Fin.last n))) (P.vertex (Fin.last (n + 1)))
        (P.vertex 0) :=
  P.carrier_eq_union_triangle_of_subset hn
    (fun i _ ↦ (P.eraseLast hn).carrier_subset_closure_leftHalfPlane fun j ↦
      P.vertex_mem_closure_leftHalfPlane i (Fin.castSucc j))
    fun i _ ↦ P.triangle_subset_closure_leftHalfPlane_edge hn i

/-- The carrier is compact. -/
theorem isCompact_carrier : IsCompact P.carrier := by
  induction P using CompactConvexPolygon.induction with
  | triangle Q =>
    rw [Q.carrier_three]
    exact isCompact_triangle Q.vertex_zero_ne_vertex_one Q.vertex_two_notMem_range_geodesicLine
  | eraseLast hn Q ih =>
    rw [Q.carrier_eq_union_triangle hn]
    exact ih.union (isCompact_triangle Q.vertex_penultimate_ne_last
      (Q.zero_notMem_range_geodesicLine_penultimate_last hn))

/-! ### Gauss–Bonnet -/

/-- The Gauss–Bonnet formula for compact convex polygons (all vertices in `ℍ`) together with the
nonnegativity of the angular defect, the form in which the induction runs. -/
theorem volume_carrier_and_le :
    0 ≤ (n - 2) * π - ∑ i, P.interiorAngle i ∧
      volume P.carrier = ENNReal.ofReal ((n - 2) * π - ∑ i, P.interiorAngle i) := by
  induction P using CompactConvexPolygon.induction with
  | triangle Q =>
    have hAB := Q.vertex_zero_ne_vertex_one
    have hC := Q.vertex_two_notMem_range_geodesicLine
    have hle := interiorAngle_add_add_le_pi hAB hC
    rw [Q.sum_interiorAngle_three, Q.carrier_three, volume_triangle hAB hC]
    push_cast
    exact ⟨by linarith, congrArg _ (by ring)⟩
  | eraseLast hn Q ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hAB := Q.vertex_penultimate_ne_last
    have hC := Q.zero_notMem_range_geodesicLine_penultimate_last hn
    have hle := interiorAngle_add_add_le_pi hAB hC
    rw [Q.carrier_eq_union_triangle hn,
      measure_union₀ (measurableSet_triangle _ _ _).nullMeasurableSet
        (measure_mono_null (Q.carrier_eraseLast_inter_triangle_subset hn)
          (volume_range_geodesicLine _)),
      ih₂, volume_triangle hAB hC, ← ENNReal.ofReal_add ih₁, Q.sum_interiorAngle_eq hn]
    · push_cast at ih₁ ⊢
      exact ⟨by linarith, congrArg _ (by ring)⟩
    · linarith

/-- **The Gauss–Bonnet formula for compact convex hyperbolic polygons**: the area of a convex
polygon with `n` vertices, all in `ℍ` (no ideal vertices), is `(n - 2) π` minus the sum of its
interior angles.
Source: Walkden, *Hyperbolic geometry* (MATH32051), Theorem 7.2.2. -/
theorem volume_carrier :
    volume P.carrier = ENNReal.ofReal ((n - 2) * π - ∑ i, P.interiorAngle i) :=
  P.volume_carrier_and_le.2

/-- The angular defect of a compact convex polygon (all vertices in `ℍ`) is nonnegative: the sum
of its interior angles is at most `(n - 2) π`. -/
theorem sum_interiorAngle_le : ∑ i, P.interiorAngle i ≤ (n - 2) * π :=
  sub_nonneg.1 P.volume_carrier_and_le.1

end CompactConvexPolygon

end TauCeti.UpperHalfPlane
