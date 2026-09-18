/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.GlobalTurning
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ClosingSide
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.LongTurn
import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Bounded Schwarz--Christoffel sides are supporting lines

Under the classical convex-polygon hypotheses (strictly ordered prevertices, exponents in
`(-1, 0)` and total exponent `-2`), the line through each bounded side of the Schwarz--Christoffel
polygon supports the whole polygon: after rotating the side's direction to the positive real
axis, every point of the polygon boundary lies on or above the rotated line through the side.

The argument follows the boundary once around, starting at the side.  Measured from the side's
direction, the directions of the successive sides and of the closing side increase through less
than one full turn.  Hence the rotated height first increases and then decreases along the
boundary, and since it returns to zero it is nonnegative throughout.

Combined with the fact that the image of the upper half-plane under the Schwarz--Christoffel
primitive is open and lies in the filled hull of the polygon boundary, this puts the image in the
open half-plane on the interior side of each bounded side.  In particular the image misses every
bounded side.

## Main results

* `TauCeti.im_exp_neg_mul_sub_schwarzChristoffelVertex_nonneg_of_mem_boundary` -- the polygon
  boundary lies on the interior side of the line through a bounded side.
* `TauCeti.im_exp_neg_mul_schwarzChristoffelPrimitive_sub_pos` -- every value of the primitive
  lies strictly on the interior side of that line.
* `TauCeti.disjoint_image_schwarzChristoffelPrimitive_edgeSet_castSucc_castSucc` -- the image of
  the upper half-plane misses every bounded side.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Metric Set UpperHalfPlane
open scoped ComplexOrder

namespace TauCeti

variable {n : ℕ}

/-- The planar core of the supporting-line argument.  A closed chain of `n + 2` steps starts and
ends at height zero: `n` steps `H l ↦ H (l + 1)` whose directions `φ l` are monotone in
`(-2π, 0]` with `φ n = 0`, followed by two steps through `Hinf` in direction `0`.  All heights are
measured after rotating the direction `φ i` of the first step to zero, so a step of length `d` and
direction `ψ` raises the height by `d * sin (ψ - φ i)`.  Then every height is nonnegative. -/
private lemma nonneg_of_turning {i : ℕ} (hi : i < n) {H φ : ℕ → ℝ} {Hinf : ℝ}
    (hmono : ∀ l m, l ≤ m → m ≤ n → φ l ≤ φ m) (hlow : ∀ l ≤ n, -2 * Real.pi < φ l)
    (hlast : φ n = 0)
    (hstep : ∀ l < n, ∃ d, 0 ≤ d ∧ H (l + 1) - H l = d * Real.sin (φ l - φ i))
    (hclose₁ : ∃ r, 0 ≤ r ∧ Hinf - H n = r * Real.sin (-φ i))
    (hclose₂ : ∃ r, 0 ≤ r ∧ H 0 - Hinf = r * Real.sin (-φ i)) (hHi : H i = 0) :
    (∀ k ≤ n, 0 ≤ H k) ∧ 0 ≤ Hinf := by
  set θ := φ i
  have hθ0 : θ ≤ 0 := hlast ▸ hmono i n hi.le le_rfl
  have hθlow : -2 * Real.pi < θ := hlow i hi.le
  -- Signs of the individual steps, according to where the direction lies relative to `θ`.
  have hstep_nonneg (l : ℕ) (hl : l < n) (h₁ : θ ≤ φ l) (h₂ : φ l ≤ θ + Real.pi) :
      0 ≤ H (l + 1) - H l := by
    obtain ⟨d, hd, h⟩ := hstep l hl
    rw [h]
    exact mul_nonneg hd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  have hstep_nonneg' (l : ℕ) (hl : l < n) (h : φ l ≤ θ - Real.pi) :
      0 ≤ H (l + 1) - H l := by
    obtain ⟨d, hd, h'⟩ := hstep l hl
    have := hlow l hl.le
    rw [h', ← Real.sin_add_two_pi]
    exact mul_nonneg hd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  have hstep_nonpos (l : ℕ) (hl : l < n) (h₁ : θ - Real.pi ≤ φ l) (h₂ : φ l ≤ θ) :
      H (l + 1) - H l ≤ 0 := by
    obtain ⟨d, hd, h⟩ := hstep l hl
    rw [h]
    exact mul_nonpos_of_nonneg_of_nonpos hd
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))
  have hstep_nonpos' (l : ℕ) (hl : l < n) (h : θ + Real.pi ≤ φ l) :
      H (l + 1) - H l ≤ 0 := by
    obtain ⟨d, hd, h'⟩ := hstep l hl
    have := hmono l n hl.le le_rfl
    rw [hlast] at this
    rw [h', ← Real.sin_sub_two_pi]
    exact mul_nonpos_of_nonneg_of_nonpos hd
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))
  obtain ⟨r₁, hr₁, hc₁⟩ := hclose₁
  obtain ⟨r₂, hr₂, hc₂⟩ := hclose₂
  -- The closing steps rise when the side points no further back than `-π`, and fall otherwise.
  have hclose_nonneg (h : -Real.pi ≤ θ) : 0 ≤ Hinf - H n ∧ 0 ≤ H 0 - Hinf := by
    have hsin : 0 ≤ Real.sin (-θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    exact ⟨hc₁ ▸ mul_nonneg hr₁ hsin, hc₂ ▸ mul_nonneg hr₂ hsin⟩
  have hclose_nonpos (h : θ ≤ -Real.pi) : Hinf - H n ≤ 0 ∧ H 0 - Hinf ≤ 0 := by
    have hsin : Real.sin (-θ) ≤ 0 := by
      rw [← Real.sin_sub_two_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    exact ⟨hc₁ ▸ mul_nonpos_of_nonneg_of_nonpos hr₁ hsin,
      hc₂ ▸ mul_nonpos_of_nonneg_of_nonpos hr₂ hsin⟩
  have hvertex (k : ℕ) (hk : k ≤ n) : 0 ≤ H k := by
    rcases lt_or_ge i k with hik | hki
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      by_cases hshort : φ k ≤ θ + Real.pi
      · -- Every side from `i` up to vertex `k` turns by at most `π`: the height rises.
        have htel := Finset.sum_Ico_sub H (show i ≤ k + 1 by omega)
        rw [hHi, sub_zero] at htel
        rw [← htel]
        refine Finset.sum_nonneg fun l hl ↦ ?_
        rw [Finset.mem_Ico] at hl
        exact hstep_nonneg l (by omega) (hmono i l hl.1 (by omega))
          ((hmono l k (by omega) (by omega)).trans hshort)
      · -- Otherwise follow the boundary on through the closing side back to `i`: the height
        -- only falls, and it returns to zero.
        rw [not_le] at hshort
        have hθπ : θ < -Real.pi := by linarith [hmono k n (by omega) le_rfl]
        have h₁ : ∑ l ∈ Finset.Ico (k + 1) n, (H (l + 1) - H l) ≤ 0 :=
          Finset.sum_nonpos fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonpos' l hl.2 (hshort.le.trans (hmono k l (by omega) hl.2.le))
        have h₂ : ∑ l ∈ Finset.Ico 0 i, (H (l + 1) - H l) ≤ 0 :=
          Finset.sum_nonpos fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonpos l (by omega) (by linarith [hlow l (by omega)])
              (hmono l i hl.2.le hi.le)
        rw [Finset.sum_Ico_sub H hk, Finset.sum_Ico_sub H (Nat.zero_le i), hHi] at *
        linarith [hclose_nonpos hθπ.le]
    · by_cases hshort : θ - Real.pi ≤ φ k
      · -- Every side from vertex `k` up to `i` turns back by at most `π`: the height falls
        -- to zero.
        have h : ∑ l ∈ Finset.Ico k i, (H (l + 1) - H l) ≤ 0 :=
          Finset.sum_nonpos fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonpos l (by omega) (hshort.trans (hmono k l hl.1 (by omega)))
              (hmono l i hl.2.le hi.le)
        rw [Finset.sum_Ico_sub H hki, hHi] at h
        linarith
      · -- Otherwise reach vertex `k` from `i` the other way round: the height only rises.
        rw [not_le] at hshort
        have hθπ : -Real.pi ≤ θ := by linarith [hlow k hk]
        have h₁ : 0 ≤ ∑ l ∈ Finset.Ico i n, (H (l + 1) - H l) :=
          Finset.sum_nonneg fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            have := hmono l n hl.2.le le_rfl
            exact hstep_nonneg l hl.2 (hmono i l hl.1 hl.2.le) (by linarith)
        have h₂ : 0 ≤ ∑ l ∈ Finset.Ico 0 k, (H (l + 1) - H l) :=
          Finset.sum_nonneg fun l hl ↦ by
            rw [Finset.mem_Ico] at hl
            exact hstep_nonneg' l (by omega)
              ((hmono l k hl.2.le hk).trans hshort.le)
        rw [Finset.sum_Ico_sub H hi.le, Finset.sum_Ico_sub H (Nat.zero_le k), hHi] at *
        linarith [hclose_nonneg hθπ]
  refine ⟨hvertex, ?_⟩
  rcases le_total (-Real.pi) θ with hθπ | hθπ
  · linarith [hvertex n le_rfl, (hclose_nonneg hθπ).1]
  · linarith [hvertex 0 (Nat.zero_le n), (hclose_nonpos hθπ).2]

/-- A closed half-plane `{z | 0 ≤ (u * (z - w)).im}` is convex. -/
private lemma convex_setOf_im_mul_sub_nonneg (u w : ℂ) :
    Convex ℝ {z : ℂ | 0 ≤ (u * (z - w)).im} := by
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Complex.imLm_coe, mul_sub,
    sub_im, sub_nonneg] using
    convex_halfSpace_ge (Complex.imLm.comp (LinearMap.mulLeft ℝ u)).isLinear (u * w).im

/-- **The finite vertices and the vertex at infinity lie on the interior side of each bounded
side.**  Under the classical convex-polygon hypotheses, rotate the direction of the bounded side
from vertex `i` to vertex `i + 1` to the positive real axis; then no vertex lies below the
rotated side. -/
private lemma im_exp_neg_mul_sub_schwarzChristoffelVertex_nonneg (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0)
    (hsum : ∑ k, e k = -2) (i : Fin n) :
    (∀ k, 0 ≤ (Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
      (schwarzChristoffelVertex a e z₀ k - schwarzChristoffelVertex a e z₀ i.castSucc)).im) ∧
    0 ≤ (Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
      (schwarzChristoffelVertexAtInfinity a e z₀ - schwarzChristoffelVertex a e z₀ i.castSucc)).im
    := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  set θ := schwarzChristoffelEdgeAngle a e (a i.castSucc)
  set u := Complex.exp (-θ * Complex.I)
  set w := schwarzChristoffelVertex a e z₀ i.castSucc
  set Vinf := schwarzChristoffelVertexAtInfinity a e z₀
  -- Natural-number indexing of the vertices, their rotated heights and the edge angles.
  let V : ℕ → ℂ := fun m ↦ if hm : m < n + 1 then schwarzChristoffelVertex a e z₀ ⟨m, hm⟩ else 0
  let H : ℕ → ℝ := fun m ↦ (u * (V m - w)).im
  let φ : ℕ → ℝ := fun m ↦
    if hm : m < n + 1 then schwarzChristoffelEdgeAngle a e (a ⟨m, hm⟩) else 0
  have hV (k : Fin (n + 1)) : V k = schwarzChristoffelVertex a e z₀ k := by
    simp only [V, k.isLt, ↓reduceDIte, Fin.eta]
  have hφ (k : Fin (n + 1)) : φ k = schwarzChristoffelEdgeAngle a e (a k) := by
    simp only [φ, k.isLt, ↓reduceDIte, Fin.eta]
  have hangle := schwarzChristoffelEdgeAngle_comp_strictMono a e ha fun k ↦ (he k).2
  have hmono (l m : ℕ) (hlm : l ≤ m) (hm : m ≤ n) : φ l ≤ φ m := by
    have := hangle.monotone
      (Fin.mk_le_mk.mpr hlm : (⟨l, by omega⟩ : Fin (n + 1)) ≤ ⟨m, by omega⟩)
    simpa only [← hφ] using this
  have hlow (l : ℕ) (hl : l ≤ n) : -2 * Real.pi < φ l := by
    have := (schwarzChristoffelEdgeAngle_mem_Ioc a e (fun k ↦ (he k).2) hsum ⟨l, by omega⟩).1
    simpa only [← hφ] using this
  have hlast : φ n = 0 := by
    have :=
      schwarzChristoffelEdgeAngle_eq_zero_of_last_le a e ha.monotone (le_refl (a (Fin.last n)))
    simpa only [← hφ, Fin.val_last] using this
  have hθ : φ i = θ := by simpa only [Fin.val_castSucc] using hφ i.castSucc
  -- Each bounded side contributes its length times the sine of its turn from side `i`.
  have hstep (l : ℕ) (hl : l < n) :
      ∃ d, 0 ≤ d ∧ H (l + 1) - H l = d * Real.sin (φ l - φ i) := by
    have h := im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq a e z₀ ha θ ⟨l, hl⟩
      (hfinite _) (hfinite _)
    have hl' : V l = schwarzChristoffelVertex a e z₀ (Fin.castSucc ⟨l, hl⟩) :=
      hV (Fin.castSucc ⟨l, hl⟩)
    have hl'' : V (l + 1) = schwarzChristoffelVertex a e z₀ (Fin.succ ⟨l, hl⟩) :=
      hV (Fin.succ ⟨l, hl⟩)
    have hφl : φ l = schwarzChristoffelEdgeAngle a e (a (Fin.castSucc ⟨l, hl⟩)) :=
      hφ (Fin.castSucc ⟨l, hl⟩)
    rw [hθ, hφl, ← Complex.sub_im, ← mul_sub, sub_sub_sub_cancel_right, hl', hl'']
    exact ⟨_, norm_nonneg _, h⟩
  -- The two closing steps are horizontal and point in the positive real direction.
  obtain ⟨hr, hl⟩ := schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha
      (fun k ↦ (he k).1) hsum
  have hhoriz {x y : ℂ} (hxy : x < y) :
      ∃ r, 0 ≤ r ∧ (u * (y - w)).im - (u * (x - w)).im = r * Real.sin (-φ i) := by
    refine ⟨(y - x).re, sub_nonneg.mpr (Complex.lt_def.mp hxy).1.le, ?_⟩
    have hu : u.im = Real.sin (-θ) := by
      have h := Complex.exp_ofReal_mul_I_im (-θ)
      push_cast at h
      exact h
    rw [← Complex.sub_im, ← mul_sub, sub_sub_sub_cancel_right, Complex.mul_im, Complex.sub_im,
      (Complex.lt_def.mp hxy).2, sub_self, mul_zero, zero_add, hu, hθ, mul_comm]
  have hVn : V n = schwarzChristoffelVertex a e z₀ (Fin.last n) := by
    simpa only [Fin.val_last] using hV (Fin.last n)
  have hV0 : V 0 = schwarzChristoffelVertex a e z₀ 0 := hV 0
  have hHi : H i = 0 := by
    simp only [H, ← Fin.val_castSucc i, hV, w, sub_self, mul_zero, Complex.zero_im]
  obtain ⟨hvert, hinf⟩ := nonneg_of_turning (H := H) (Hinf := (u * (Vinf - w)).im) i.isLt hmono
    hlow hlast hstep (by simpa only [H, hVn] using hhoriz hr)
    (by simpa only [H, hV0] using hhoriz hl) hHi
  refine ⟨fun k ↦ ?_, hinf⟩
  simpa only [H, hV] using hvert k (Nat.lt_succ_iff.mp k.isLt)

/-- **The Schwarz--Christoffel polygon lies on the interior side of each bounded side.**  Under
the classical convex-polygon hypotheses, rotate the direction of the bounded side from vertex `i`
to vertex `i + 1` to the positive real axis.  Then every point of the polygon boundary lies on or
above the rotated line through that side. -/
theorem im_exp_neg_mul_sub_schwarzChristoffelVertex_nonneg_of_mem_boundary
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) (i : Fin n) {z : ℂ}
    (hz : z ∈ (schwarzChristoffelPolygon a e z₀).boundary ℝ) :
    0 ≤ (Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
      (z - schwarzChristoffelVertex a e z₀ i.castSucc)).im := by
  obtain ⟨hvert, hinf⟩ := im_exp_neg_mul_sub_schwarzChristoffelVertex_nonneg a e z₀ ha he hsum i
  have hconv := convex_setOf_im_mul_sub_nonneg
    (Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I))
    (schwarzChristoffelVertex a e z₀ i.castSucc)
  rw [schwarzChristoffelPolygon_boundary] at hz
  rcases hz with (hz | hz) | hz
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    exact hconv.segment_subset (hvert _) (hvert _) hj
  · exact hconv.segment_subset (hvert _) hinf hz
  · exact hconv.segment_subset hinf (hvert _) hz

/-- **The Schwarz--Christoffel image lies strictly on the interior side of each bounded side.**
Under the classical convex-polygon hypotheses, rotate the direction of the bounded side from
vertex `i` to vertex `i + 1` to the positive real axis.  Then every value of the primitive on the
upper half-plane lies strictly above the rotated line through that side. -/
theorem im_exp_neg_mul_schwarzChristoffelPrimitive_sub_pos
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) (i : Fin n) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    0 < (Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
      (schwarzChristoffelPrimitive a e z₀ z - schwarzChristoffelVertex a e z₀ i.castSucc)).im := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  have hinfty : ∑ k, e k < -1 := by rw [hsum]; norm_num
  set u := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
  set w := schwarzChristoffelVertex a e z₀ i.castSucc
  set F := schwarzChristoffelPrimitive a e z₀
  -- The rotation about `w` is a homeomorphism carrying the half-plane to `{0 ≤ im}`.
  let g : ℂ ≃ₜ ℂ := (Homeomorph.subRight w).trans (Homeomorph.mulLeft₀ u (Complex.exp_ne_zero _))
  have hg (x : ℂ) : g x = u * (x - w) := rfl
  set P := range (schwarzChristoffelCompactifiedBoundary a e z₀)
  have hP : P = (schwarzChristoffelPolygon a e z₀).boundary ℝ :=
    range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hinfty
  have hPH : P ⊆ g ⁻¹' {x | 0 ≤ x.im} := fun x hx ↦ by
    rw [hP] at hx
    exact im_exp_neg_mul_sub_schwarzChristoffelVertex_nonneg_of_mem_boundary a e z₀ ha he hsum i hx
  have hclosed : IsClosed (g ⁻¹' {x : ℂ | 0 ≤ x.im}) :=
    (isClosed_le continuous_const Complex.continuous_im).preimage g.continuous
  have hconvex : Convex ℝ (g ⁻¹' {x : ℂ | 0 ≤ x.im}) := by
    simpa only [preimage_ofPred_eq, hg] using convex_setOf_im_mul_sub_nonneg u w
  -- The open image lies in the filled hull, hence in the closed convex hull of the boundary.
  have himage : F '' upperHalfPlaneSet ⊆ g ⁻¹' {x | 0 ≤ x.im} :=
    (image_schwarzChristoffelPrimitive_subset_filledHull a e z₀ hfinite hinfty).trans
      ((filledHull_subset_closedConvexHull (range_nonempty _)).trans
        (closedConvexHull_min hPH hconvex hclosed))
  have hopen := isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet
    subset_rfl
  have hmem := interior_maximal himage hopen (mem_image_of_mem F hz)
  rw [← g.preimage_interior, interior_setOfPred_le_im] at hmem
  simpa only [mem_preimage, hg, mem_ofPred_eq] using hmem

/-- **The Schwarz--Christoffel image misses every bounded side.**  Under the classical
convex-polygon hypotheses, the image of the upper half-plane under the primitive is disjoint from
the bounded side from vertex `i` to vertex `i + 1`. -/
theorem disjoint_image_schwarzChristoffelPrimitive_edgeSet_castSucc_castSucc
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) (i : Fin n) :
    Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc) := by
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc, Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ hside
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  set u := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
  set w := schwarzChristoffelVertex a e z₀ i.castSucc
  -- Both ends of the side lie on the rotated line, hence so does the whole side.
  have hend : (u * (schwarzChristoffelVertex a e z₀ i.succ - w)).im = 0 := by
    rw [im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq a e z₀ ha _ i (hfinite _)
      (hfinite _), sub_self, Real.sin_zero, mul_zero]
  have hle := (convex_setOf_im_mul_sub_nonneg (-u) w).segment_subset
    (by simp only [mem_ofPred_eq, sub_self, mul_zero, zero_im, le_refl])
    (by simp only [mem_ofPred_eq, neg_mul, neg_im, hend, neg_zero, le_refl]) hside
  simp only [mem_ofPred_eq, neg_mul, neg_im, Left.nonneg_neg_iff] at hle
  exact hle.not_gt (im_exp_neg_mul_schwarzChristoffelPrimitive_sub_pos a e z₀ ha he hsum i hz)

end TauCeti
