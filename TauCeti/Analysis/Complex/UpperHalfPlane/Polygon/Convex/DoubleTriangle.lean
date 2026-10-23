/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Reflection
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.VertexSector
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# The double of a hyperbolic triangle

Let `P` be a convex hyperbolic triangle, with vertices in `ℍ ∪ ∂ℍ`, whose interior angles at the
two ends `P 0`, `P 1` of side `0` are acute. Reflecting `P` in the geodesic line of side `0` gives
a second triangle, and together they form the convex quadrilateral `P.doubleTriangle` with
vertices `P 0`, `P 2'`, `P 1`, `P 2`, where `P 2'` is the mirror image of `P 2`
(`ConvexPolygon.carrier_doubleTriangle`). The acute angles are what makes it strictly convex at
`P 0` and `P 1`. Its interior angles there are twice those of `P`, and at `P 2` and its
mirror image they equal the angle of `P` at `P 2`. Another side of `P` can be doubled by first
relabelling the vertices with `ConvexPolygon.rotate`.

Its side pairing by products of reflections, used to construct hyperbolic triangle groups, is
`ConvexPolygon.doubleTriangleSidePairing` in
`TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.DoubleTriangle`.

## Main declarations

* `ConvexPolygon.extGeodesicReflection_sideGeodesic_vertex` and
  `ConvexPolygon.extGeodesicReflection_sideGeodesic_vertex_of_add_one_eq`: the reflection in a
  side of a convex polygon fixes the ends of that side.
* `ConvexPolygon.doubleTriangle`: the double of a triangle across side `0`.
* `ConvexPolygon.carrier_doubleTriangle`: it is the union of the triangle and its mirror image.
* `ConvexPolygon.interiorAngle_doubleTriangle_zero`,
  `ConvexPolygon.interiorAngle_doubleTriangle_two`: the angles at `P 0` and `P 1` double.
* `ConvexPolygon.interiorAngle_doubleTriangle_one`,
  `ConvexPolygon.interiorAngle_doubleTriangle_three`: the angles at `P 2` and at its mirror image
  are the angle of `P` at `P 2`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §10.6 (the fundamental polygon of a triangle group is the union of the triangle and one
  of its reflections).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped Real

namespace TauCeti.UpperHalfPlane.ConvexPolygon

/-- The reflection in the line of a side of a convex polygon fixes the starting vertex of that
side. -/
@[simp]
theorem extGeodesicReflection_sideGeodesic_vertex {n : ℕ} [NeZero n] (P : ConvexPolygon n)
    (i : Fin n) : extGeodesicReflection (P.sideGeodesic i) (P.vertex i) = P.vertex i :=
  (P.isGeodesicFromTo_sideGeodesic i).extGeodesicReflection_left

/-- The reflection in the line of a side of a convex polygon fixes the final vertex of that
side. The index of that vertex is a separate variable, so that `simp` can use this lemma for
explicit indices such as `P.vertex 2` and side `1`. -/
@[simp]
theorem extGeodesicReflection_sideGeodesic_vertex_of_add_one_eq {n : ℕ} [NeZero n]
    (P : ConvexPolygon n) {i j : Fin n} (h : i + 1 = j) :
    extGeodesicReflection (P.sideGeodesic i) (P.vertex j) = P.vertex j :=
  h ▸ (P.isGeodesicFromTo_sideGeodesic i).extGeodesicReflection_right

variable (P : ConvexPolygon 3)

/-- **The double of a triangle across a side.** For a triangle `P` whose angles at the ends of
side `0` are acute, the convex quadrilateral with vertices `P 0`, the mirror image of `P 2` in
side `0`, `P 1` and `P 2`, in this counterclockwise order. Its carrier is the union of `P` and
its mirror image (`carrier_doubleTriangle`). -/
def doubleTriangle (h₀ : P.interiorAngle 0 < π / 2) (h₁ : P.interiorAngle 1 < π / 2) :
    ConvexPolygon 4 where
  vertex := ![P.vertex 0, extGeodesicReflection (P.sideGeodesic 0) (P.vertex 2), P.vertex 1,
    P.vertex 2]
  three_le := by norm_num
  vertex_ne_vertex_add_one := by
    have hρ := extGeodesicReflection_injective (P.sideGeodesic 0)
    have hv := P.vertex_injective
    have e₀ := P.extGeodesicReflection_sideGeodesic_vertex 0
    have e₁ := P.extGeodesicReflection_sideGeodesic_vertex_of_add_one_eq (i := 0) (j := 1) rfl
    intro i
    fin_cases i <;> simp only [Fin.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val]
    · rw [← e₀]
      exact hρ.ne (hv.ne (by decide))
    · rw [← e₁]
      exact hρ.ne (hv.ne (by decide))
    · exact hv.ne (by decide)
    · exact hv.ne (by decide)
  vertex_mem_extLeftHalfPlane := by
    -- the mirror image of `P 2` lies strictly to the left of the other two sides
    have hg := P.isGeodesicFromTo_sideGeodesic 0
    have hc := P.vertex_mem_extLeftHalfPlane_sideGeodesic (i := 0) (j := 2) (by decide) (by decide)
    rw [interiorAngle_def] at h₀ h₁
    have hK₀ := extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_left hg hc h₀
    have hK₁ := extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_right hg hc h₁
    have hP₁ : P.vertex 0 ∈ extLeftHalfPlane (geodesicFromTo (P.vertex 1) (P.vertex 2)) :=
      P.vertex_mem_extLeftHalfPlane 1 0 (by decide) (by decide)
    have hP₂ : P.vertex 1 ∈ extLeftHalfPlane (geodesicFromTo (P.vertex 2) (P.vertex 0)) :=
      P.vertex_mem_extLeftHalfPlane 2 1 (by decide) (by decide)
    -- the sides at the mirror image of `P 2` are the mirror images of the sides at `P 2`
    have hR {p q : Fin 3} (hpq : p ≠ q) (r : ℍ ⊕ OnePoint ℝ) :=
      extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_iff (P.sideGeodesic 0)
        (P.vertex_injective.ne hpq) r
    have e₀ := P.extGeodesicReflection_sideGeodesic_vertex 0
    have e₁ := P.extGeodesicReflection_sideGeodesic_vertex_of_add_one_eq (i := 0) (j := 1) rfl
    intro i j hji hji'
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceAdd, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val, ne_eq, not_true_eq_false] at hji hji' ⊢
    · simpa only [e₀, e₁] using (hR (p := 2) (q := 0) (by decide) _).2 hP₂
    · simpa only [e₀, extGeodesicReflection_extGeodesicReflection] using
        (hR (p := 2) (q := 0) (by decide) _).2 hK₀
    · simpa only [e₀, e₁] using (hR (p := 1) (q := 2) (by decide) _).2 hP₁
    · simpa only [e₁, extGeodesicReflection_extGeodesicReflection] using
        (hR (p := 1) (q := 2) (by decide) _).2 hK₁
    · exact hP₁
    · exact hK₁
    · exact hK₀
    · exact hP₂

variable {P} {h₀ : P.interiorAngle 0 < π / 2} {h₁ : P.interiorAngle 1 < π / 2}

/-- The vertices of the double of a triangle. -/
@[simp]
theorem doubleTriangle_vertex :
    (P.doubleTriangle h₀ h₁).vertex = ![P.vertex 0,
      extGeodesicReflection (P.sideGeodesic 0) (P.vertex 2), P.vertex 1, P.vertex 2] :=
  (rfl)

/-- The double of a triangle contains the triangle. -/
private theorem carrier_subset_carrier_doubleTriangle :
    P.carrier ⊆ (P.doubleTriangle h₀ h₁).carrier := by
  set Q := P.doubleTriangle h₀ h₁
  rw [Q.carrier_def]
  refine Set.subset_iInter fun i ↦ P.carrier_subset_closure_leftHalfPlane_of_forall fun k ↦ ?_
  -- the vertices of `P` are vertices of its double
  obtain ⟨l, hl⟩ : ∃ l, P.vertex k = Q.vertex l :=
    ⟨![0, 2, 3] k, by fin_cases k <;> simp [Q]⟩
  rw [hl]
  exact Q.vertex_mem_extClosedLeftHalfPlane_sideGeodesic i l

/-- The double of a triangle is symmetric under the reflection in side `0`, which exchanges the
two sides at `P 0` and the two sides at `P 1`. -/
private theorem geodesicReflection_mem_carrier_doubleTriangle {z : ℍ}
    (hz : z ∈ (P.doubleTriangle h₀ h₁).carrier) :
    geodesicReflection (P.sideGeodesic 0) z ∈ (P.doubleTriangle h₀ h₁).carrier := by
  set Q := P.doubleTriangle h₀ h₁
  set ρ := geodesicReflection (P.sideGeodesic 0)
  have e₀ := P.extGeodesicReflection_sideGeodesic_vertex 0
  have e₁ := P.extGeodesicReflection_sideGeodesic_vertex_of_add_one_eq (i := 0) (j := 1) rfl
  have f₀ (w : ℍ) : ρ w ∈ closure (leftHalfPlane (geodesicFromTo (Q.vertex 0) (Q.vertex 1))) ↔
      w ∈ closure (leftHalfPlane (geodesicFromTo (Q.vertex 3) (Q.vertex 0))) := by
    have h := geodesicReflection_mem_closure_leftHalfPlane_geodesicFromTo_iff (P.sideGeodesic 0)
      (P.vertex_injective.ne (by decide : (2 : Fin 3) ≠ 0)) w
    rwa [e₀] at h
  have f₁ (w : ℍ) : ρ w ∈ closure (leftHalfPlane (geodesicFromTo (Q.vertex 1) (Q.vertex 2))) ↔
      w ∈ closure (leftHalfPlane (geodesicFromTo (Q.vertex 2) (Q.vertex 3))) := by
    have h := geodesicReflection_mem_closure_leftHalfPlane_geodesicFromTo_iff (P.sideGeodesic 0)
      (P.vertex_injective.ne (by decide : (1 : Fin 3) ≠ 2)) w
    rwa [e₁] at h
  have hρρ (w : ℍ) : ρ (ρ w) = w := geodesicReflection_geodesicReflection _ w
  simp only [Q.mem_carrier_iff, sideGeodesic_def] at hz ⊢
  -- normalise the `Fin 4` indices `2 + 1` and `3 + 1` of the sides used below
  have h₂ := hz 2
  have h₃ := hz 3
  simp only [Fin.reduceAdd] at h₂ h₃
  intro i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd]
  · exact (f₀ z).2 h₃
  · exact (f₁ z).2 h₂
  · simpa [hρρ] using (f₁ (ρ z)).1 (by simpa [hρρ] using hz 1)
  · simpa [hρρ] using (f₀ (ρ z)).1 (by simpa [hρρ] using hz 0)

/-- **The double of a triangle is the union of the triangle and its mirror image** in side `0`. -/
theorem carrier_doubleTriangle :
    (P.doubleTriangle h₀ h₁).carrier =
      P.carrier ∪ geodesicReflection (P.sideGeodesic 0) '' P.carrier := by
  set Q := P.doubleTriangle h₀ h₁
  set ρ := geodesicReflection (P.sideGeodesic 0)
  -- the sides of `Q` at `P 2` are those of `P`
  have hQ₂ : Q.sideGeodesic 2 = P.sideGeodesic 1 := by
    simp [Q, sideGeodesic_def]
  have hQ₃ : Q.sideGeodesic 3 = P.sideGeodesic 2 := by
    simp [Q, sideGeodesic_def]
  have hP (w : ℍ) (h₀ : w ∈ closure (leftHalfPlane (P.sideGeodesic 0)))
      (hw : w ∈ Q.carrier) : w ∈ P.carrier := by
    rw [Q.mem_carrier_iff] at hw
    refine (P.mem_carrier_iff w).2 fun i ↦ ?_
    fin_cases i
    · exact h₀
    · exact hQ₂ ▸ hw 2
    · exact hQ₃ ▸ hw 3
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · by_cases ht : z ∈ closure (leftHalfPlane (P.sideGeodesic 0))
    · exact .inl (hP z ht hz)
    · -- otherwise its mirror image lies on the side of `P`, and so in `P`
      rw [mem_closure_leftHalfPlane_iff, not_le, ← mem_rightHalfPlane_iff] at ht
      refine .inr ⟨ρ z, hP (ρ z) ?_ (geodesicReflection_mem_carrier_doubleTriangle hz),
        geodesicReflection_geodesicReflection _ z⟩
      exact subset_closure ((geodesicReflection_mem_leftHalfPlane_iff _ z).2 ht)
  · rintro (hz | ⟨y, hy, rfl⟩)
    · exact carrier_subset_carrier_doubleTriangle hz
    · exact geodesicReflection_mem_carrier_doubleTriangle (carrier_subset_carrier_doubleTriangle hy)

/-! ### Interior angles -/

/-- Reflection in side `0` preserves the triangle angle at either end of that side. -/
private theorem vertexAngle_sideZero_reflected_vertex {i : Fin 3} (hi : i = 0 ∨ i = 1) :
    vertexAngle (P.vertex i) (extGeodesicReflection (P.sideGeodesic 0) (P.vertex 2))
      (P.vertex (1 - i)) = P.interiorAngle i := by
  have hfix (j : Fin 3) (hj : j = 0 ∨ j = 1) :
      extGeodesicReflection (P.sideGeodesic 0) (P.vertex j) = P.vertex j := by
    rcases hj with rfl | rfl
    · exact P.extGeodesicReflection_sideGeodesic_vertex 0
    · exact P.extGeodesicReflection_sideGeodesic_vertex_of_add_one_eq (i := 0) rfl
  have hi₂ : i ≠ 2 := by rcases hi with rfl | rfl <;> decide
  have hiOpp : i ≠ 1 - i := by rcases hi with rfl | rfl <;> decide
  have hOther : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> decide
  have hnegOne : (-1 : Fin 3) = 2 := by decide
  have hρ := vertexAngle_extGeodesicReflection (P.sideGeodesic 0)
    (P.vertex_injective.ne hi₂) (P.vertex_injective.ne hiOpp)
  rw [hfix i hi, hfix (1 - i) hOther] at hρ
  rw [hρ, interiorAngle_def]
  rcases hi with rfl | rfl <;> simp [hnegOne, vertexAngle_comm]

/-- **The angle of the double at `P 0` is twice that of `P`**: the ray towards `P 1` bisects it,
the reflection in side `0` exchanging its two halves. -/
@[simp]
theorem interiorAngle_doubleTriangle_zero :
    (P.doubleTriangle h₀ h₁).interiorAngle 0 = 2 * P.interiorAngle 0 := by
  set Q := P.doubleTriangle h₀ h₁
  rcases hz : P.vertex 0 with z | ξ
  · have hQz : Q.vertex 0 = .inl z := by simp [Q, hz]
    -- the points at parameter `1` of the rays from `z` towards `P 1`, `P 2` and its mirror image
    set C := geodesicLine (rayToward z (P.vertex 1)) 1
    set D := geodesicLine (rayToward z (P.vertex 2)) 1
    set D' := geodesicLine (rayToward z (extGeodesicReflection (P.sideGeodesic 0) (P.vertex 2))) 1
    have hQ : orientedAngle z D' D = Q.interiorAngle 0 := by
      simpa [Q] using Q.orientedAngle_rayToward_vertex_eq_interiorAngle hQz
    have hP : orientedAngle z C D = P.interiorAngle 0 := by
      have hnegOne : (-1 : Fin 3) = 2 := by decide
      simpa [hnegOne] using
        P.orientedAngle_rayToward_vertex_eq_interiorAngle hz
    -- the angle between the mirror image of `P 2` and `P 1` is that of `P` at `P 0`
    have habs : |(orientedAngle z D' C).toReal| = P.interiorAngle 0 := by
      rw [← interiorAngle_eq_abs_toReal_orientedAngle, ← vertexAngle_inl_eq_interiorAngle]
      simpa [hz] using vertexAngle_sideZero_reflected_vertex (P := P) (i := 0) (.inl rfl)
    refine Real.Angle.eq_two_mul_of_abs_toReal_eq habs ?_
      (Q.interiorAngle_pos_of_isLeft_vertex (by simp [hQz]))
      (Q.interiorAngle_lt_pi 0)
    rw [← hP, orientedAngle_add, hQ]
  · have hQξ : Q.vertex 0 = .inr ξ := by simp [Q, hz]
    rw [Q.interiorAngle_eq_zero_of_vertex_eq_inr hQξ, P.interiorAngle_eq_zero_of_vertex_eq_inr hz,
      mul_zero]

/-- **The angle of the double at `P 1` is twice that of `P`**: the ray towards `P 0` bisects it,
the reflection in side `0` exchanging its two halves. -/
@[simp]
theorem interiorAngle_doubleTriangle_two :
    (P.doubleTriangle h₀ h₁).interiorAngle 2 = 2 * P.interiorAngle 1 := by
  set Q := P.doubleTriangle h₀ h₁
  rcases hz : P.vertex 1 with z | ξ
  · have hQz : Q.vertex 2 = .inl z := by simp [Q, hz]
    -- the points at parameter `1` of the rays from `z` towards `P 0`, `P 2` and its mirror image
    set C := geodesicLine (rayToward z (P.vertex 0)) 1
    set D := geodesicLine (rayToward z (P.vertex 2)) 1
    set D' := geodesicLine (rayToward z (extGeodesicReflection (P.sideGeodesic 0) (P.vertex 2))) 1
    have hQ : orientedAngle z D D' = Q.interiorAngle 2 := by
      simpa [Q] using Q.orientedAngle_rayToward_vertex_eq_interiorAngle hQz
    have hP : orientedAngle z D C = P.interiorAngle 1 := by
      simpa using P.orientedAngle_rayToward_vertex_eq_interiorAngle hz
    -- the angle between `P 0` and the mirror image of `P 2` is that of `P` at `P 1`
    have habs : |(orientedAngle z C D').toReal| = P.interiorAngle 1 := by
      rw [← interiorAngle_eq_abs_toReal_orientedAngle, ← vertexAngle_inl_eq_interiorAngle]
      simpa [hz, vertexAngle_comm] using
        vertexAngle_sideZero_reflected_vertex (P := P) (i := 1) (.inr rfl)
    refine Real.Angle.eq_two_mul_of_abs_toReal_eq habs ?_
      (Q.interiorAngle_pos_of_isLeft_vertex (by simp [hQz]))
      (Q.interiorAngle_lt_pi 2)
    rw [← hP, add_comm, orientedAngle_add, hQ]
  · have hQξ : Q.vertex 2 = .inr ξ := by simp [Q, hz]
    rw [Q.interiorAngle_eq_zero_of_vertex_eq_inr hQξ, P.interiorAngle_eq_zero_of_vertex_eq_inr hz,
      mul_zero]

/-- The angle of the double at the mirror image of `P 2` is the angle of `P` at `P 2`. -/
@[simp]
theorem interiorAngle_doubleTriangle_one :
    (P.doubleTriangle h₀ h₁).interiorAngle 1 = P.interiorAngle 2 := by
  have hρ := vertexAngle_extGeodesicReflection (P.sideGeodesic 0)
    (P.vertex_injective.ne (by decide : (2 : Fin 3) ≠ 0))
    (P.vertex_injective.ne (by decide : (2 : Fin 3) ≠ 1))
  rw [extGeodesicReflection_sideGeodesic_vertex,
    extGeodesicReflection_sideGeodesic_vertex_of_add_one_eq _ (i := 0) (j := 1) rfl] at hρ
  rw [interiorAngle_def, interiorAngle_def]
  simpa [vertexAngle_comm] using hρ

/-- The angle of the double at `P 2` is the angle of `P` there. -/
@[simp]
theorem interiorAngle_doubleTriangle_three :
    (P.doubleTriangle h₀ h₁).interiorAngle 3 = P.interiorAngle 2 := by
  rw [interiorAngle_def, interiorAngle_def]
  simp

end TauCeti.UpperHalfPlane.ConvexPolygon
