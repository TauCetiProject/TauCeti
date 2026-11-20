/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PeriodicPolygon
import TauCeti.Analysis.InnerProductSpace.Sphere.Chord
import TauCeti.Analysis.InnerProductSpace.Triangle

/-!
# Inscribed polygon perimeter bounds on spheres

This file proves sharp upper bounds and equality characterizations for the perimeter
`TauCeti.inscribedPerimeter χ s = ∑ₖ ‖χ(s_(k+1)) - χ(s_k)‖` of closed polygons whose vertices lie
on a sphere `Metric.sphere c R` in a real inner product space `F`.

* **General `N`-gon diameter bound.** In any normed group, if every vertex lies at distance at most
  `R` from `c`, then `inscribedPerimeter χ s ≤ 2 N R`
  (`TauCeti.inscribedPerimeter_le_two_mul_of_dist_le`). In a real inner product space, a polygon on
  `Metric.sphere c R` attains `2 N R` if and only if consecutive vertices are antipodal across `c`,
  `χ(s_(k+1)) - c = -(χ(s_k) - c)` (`TauCeti.inscribedPerimeter_eq_two_mul_iff_of_mem_sphere`), in
  which case the vertices repeat with period `2`, `χ(s_(k+2)) = χ(s_k)`
  (`TauCeti.apply_add_two_eq_of_inscribedPerimeter_eq_two_mul`). Specializing to `N = 2` and
  `N = 4` gives the bounds `4 R` and `8 R` and their antipodal equality cases.
* **Triangles (`N = 3`).** Every triangle on `Metric.sphere c R` has perimeter at most `3 √3 R`
  (`TauCeti.inscribedPerimeter_zmod_three_le_of_mem_sphere`), with exact quadratic deficit
  `(3 √3 R)² - P² = 3 ‖(p₀ - c) + (p₁ - c) + (p₂ - c)‖² + ∑ (side length differences)²`
  (`TauCeti.three_sqrt_three_sq_sub_inscribedPerimeter_sq`). Equality holds if and only if every
  side has length `√3 R` (`TauCeti.inscribedPerimeter_zmod_three_eq_iff_norm_sub_eq`),
  equivalently if and only if the centroid of the vertices is `c`
  (`TauCeti.inscribedPerimeter_zmod_three_eq_iff_sum_sub_eq_zero`).

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2.
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 6.
-/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace TauCeti

variable {α F : Type*}

section NormedGroup

variable [NormedAddCommGroup F]

/-- Every polygon with `N` vertices at distance at most `R` from `c` has perimeter at most
`2 N R`. -/
theorem inscribedPerimeter_le_two_mul_of_dist_le {N : ℕ} [NeZero N] {χ : α → F} {s : ZMod N → α}
    {c : F} {R : ℝ} (hs : ∀ k, dist (χ (s k)) c ≤ R) :
    inscribedPerimeter χ s ≤ 2 * (N : ℝ) * R := by
  have hterm (k : ZMod N) : ‖χ (s (k + 1)) - χ (s k)‖ ≤ 2 * R := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right (χ (s (k + 1))) (χ (s k)) c, hs (k + 1), hs k]
  calc
    inscribedPerimeter χ s = ∑ k : ZMod N, ‖χ (s (k + 1)) - χ (s k)‖ := inscribedPerimeter_def χ s
    _ ≤ ∑ _ : ZMod N, (2 * R) := Finset.sum_le_sum fun k _ ↦ hterm k
    _ = 2 * (N : ℝ) * R := by
      simp [ZMod.card]
      ring

/-- Every `2`-gon inscribed in the sphere of radius `R` has perimeter at most `4 R`. -/
theorem inscribedPerimeter_zmod_two_le_of_mem_sphere {χ : α → F} {s : ZMod 2 → α} {c : F} {R : ℝ}
    (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s ≤ 4 * R :=
  (inscribedPerimeter_le_two_mul_of_dist_le fun k ↦ (Metric.mem_sphere.1 (hs k)).le).trans_eq
    (by push_cast; ring)

/-- Every `4`-gon inscribed in the sphere of radius `R` has perimeter at most `8 R`. -/
theorem inscribedPerimeter_zmod_four_le_of_mem_sphere {χ : α → F} {s : ZMod 4 → α} {c : F} {R : ℝ}
    (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s ≤ 8 * R :=
  (inscribedPerimeter_le_two_mul_of_dist_le fun k ↦ (Metric.mem_sphere.1 (hs k)).le).trans_eq
    (by push_cast; ring)

end NormedGroup

section InnerProduct

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An `N`-gon on the sphere of center `c` and radius `R` has maximal chordwise perimeter `2 N R`
if and only if every pair of consecutive vertices is antipodal across `c`. -/
theorem inscribedPerimeter_eq_two_mul_iff_of_mem_sphere {N : ℕ} [NeZero N] {χ : α → F}
    {s : ZMod N → α} {c : F} {R : ℝ} (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s = 2 * (N : ℝ) * R ↔ ∀ k, χ (s (k + 1)) - c = -(χ (s k) - c) := by
  have hle (k : ZMod N) : ‖χ (s (k + 1)) - χ (s k)‖ ≤ 2 * R := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right (χ (s (k + 1))) (χ (s k)) c,
      (Metric.mem_sphere.1 (hs (k + 1))).le, (Metric.mem_sphere.1 (hs k)).le]
  have hconst : (∑ _ : ZMod N, (2 * R)) = 2 * (N : ℝ) * R := by
    simp [ZMod.card]
    ring
  rw [inscribedPerimeter_def, ← hconst,
    Finset.sum_eq_sum_iff_of_le fun k _ ↦ hle k]
  simp only [Finset.mem_univ, forall_true_left]
  exact forall_congr' fun k ↦ norm_sub_eq_two_mul_iff_of_mem_sphere (hs k) (hs (k + 1))

/-- Any polygon on a sphere whose consecutive vertices are antipodal repeats every two steps:
`χ(s_(k+2)) = χ(s_k)`. -/
theorem apply_add_two_eq_of_inscribedPerimeter_eq_two_mul {N : ℕ} [NeZero N] {χ : α → F}
    {s : ZMod N → α} {c : F} {R : ℝ} (hs : ∀ k, χ (s k) ∈ Metric.sphere c R)
    (hmax : inscribedPerimeter χ s = 2 * (N : ℝ) * R) (k : ZMod N) :
    χ (s (k + 2)) = χ (s k) := by
  have hant := (inscribedPerimeter_eq_two_mul_iff_of_mem_sphere hs).1 hmax
  have hk1 := hant (k + 1)
  have hk0 := hant k
  have h2 : k + 1 + 1 = k + 2 := by ring
  rw [h2, hk0, neg_neg, sub_left_inj] at hk1
  exact hk1

/-- A `2`-gon on a sphere of radius `R` has perimeter `4 R` if and only if its vertices are
antipodal. -/
theorem inscribedPerimeter_zmod_two_eq_iff_of_mem_sphere {χ : α → F} {s : ZMod 2 → α} {c : F}
    {R : ℝ} (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s = 4 * R ↔ χ (s 1) - c = -(χ (s 0) - c) := by
  have heq : (2 : ℝ) * (2 : ℕ) * R = 4 * R := by push_cast; ring
  rw [← heq, inscribedPerimeter_eq_two_mul_iff_of_mem_sphere hs]
  refine ⟨fun h ↦ h 0, fun h ↦ ?_⟩
  have h1 : χ (s ((1 : ZMod 2) + 1)) - c = -(χ (s 1) - c) := by
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [h11, h, neg_neg]
  intro k
  fin_cases k
  · exact h
  · exact h1

/-- A `4`-gon on a sphere of radius `R` has perimeter `8 R` if and only if consecutive vertices
are antipodal. -/
theorem inscribedPerimeter_zmod_four_eq_iff_of_mem_sphere {χ : α → F} {s : ZMod 4 → α} {c : F}
    {R : ℝ} (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s = 8 * R ↔ ∀ k, χ (s (k + 1)) - c = -(χ (s k) - c) := by
  have heq : (2 : ℝ) * (4 : ℕ) * R = 8 * R := by push_cast; ring
  rw [← heq, inscribedPerimeter_eq_two_mul_iff_of_mem_sphere hs]

/-- Exact quadratic deficit of the perimeter of a triangle on the sphere of radius `R`:
`(3 √3 R)² - P² = 3 ‖(p₀ - c) + (p₁ - c) + (p₂ - c)‖² + ∑ (side length differences)²`. -/
theorem three_sqrt_three_sq_sub_inscribedPerimeter_sq {χ : α → F} {s : ZMod 3 → α} {c : F}
    {R : ℝ} (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    (3 * √3 * R) ^ 2 - inscribedPerimeter χ s ^ 2 =
      3 * ‖(χ (s 0) - c) + (χ (s 1) - c) + (χ (s 2) - c)‖ ^ 2 +
        (‖χ (s 1) - χ (s 0)‖ - ‖χ (s 2) - χ (s 1)‖) ^ 2 +
        (‖χ (s 2) - χ (s 1)‖ - ‖χ (s 0) - χ (s 2)‖) ^ 2 +
        (‖χ (s 0) - χ (s 2)‖ - ‖χ (s 1) - χ (s 0)‖) ^ 2 := by
  have hn (k : ZMod 3) : ‖χ (s k) - c‖ = R := by simpa [dist_eq_norm] using hs k
  set x₀ := χ (s 0) - c
  set x₁ := χ (s 1) - c
  set x₂ := χ (s 2) - c
  have hsum : ‖x₁ - x₀‖ ^ 2 + ‖x₂ - x₁‖ ^ 2 + ‖x₀ - x₂‖ ^ 2 + ‖x₀ + x₁ + x₂‖ ^ 2 =
      3 * (‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2) := by
    rw [norm_sub_sq_real x₁ x₀, norm_sub_sq_real x₂ x₁, norm_sub_sq_real x₀ x₂,
      norm_add_sq_real (x₀ + x₁) x₂, norm_add_sq_real x₀ x₁, inner_add_left,
      real_inner_comm x₁ x₀, real_inner_comm x₂ x₁]
    ring
  rw [sub_sub_sub_cancel_right (χ (s 1)) (χ (s 0)) c,
    sub_sub_sub_cancel_right (χ (s 2)) (χ (s 1)) c,
    sub_sub_sub_cancel_right (χ (s 0)) (χ (s 2)) c, hn 0, hn 1, hn 2] at hsum
  have h27 : (3 * √3 * R) ^ 2 = 27 * R ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [h27, inscribedPerimeter_zmod_three χ s]
  linear_combination -3 * hsum

/-- **Upper bound on the perimeter of an inscribed triangle.** Every triangle with vertices on the
sphere of center `c` and radius `R` in a real inner product space has perimeter at most `3 √3 R`. -/
theorem inscribedPerimeter_zmod_three_le_of_mem_sphere {χ : α → F} {s : ZMod 3 → α} {c : F} {R : ℝ}
    (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s ≤ 3 * √3 * R := by
  have hR : 0 ≤ R := hs 0 ▸ dist_nonneg
  have hper_nonneg : 0 ≤ inscribedPerimeter χ s := by
    rw [inscribedPerimeter_def]
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hdef := three_sqrt_three_sq_sub_inscribedPerimeter_sq hs
  have hsq : inscribedPerimeter χ s ^ 2 ≤ (3 * √3 * R) ^ 2 := by
    nlinarith [sq_nonneg ‖(χ (s 0) - c) + (χ (s 1) - c) + (χ (s 2) - c)‖,
      sq_nonneg (‖χ (s 1) - χ (s 0)‖ - ‖χ (s 2) - χ (s 1)‖),
      sq_nonneg (‖χ (s 2) - χ (s 1)‖ - ‖χ (s 0) - χ (s 2)‖),
      sq_nonneg (‖χ (s 0) - χ (s 2)‖ - ‖χ (s 1) - χ (s 0)‖)]
  exact (pow_le_pow_iff_left₀ hper_nonneg (by positivity) two_ne_zero).1 hsq

/-- **Equilateral characterization of maximal inscribed triangles.** A triangle on the sphere of
center `c` and radius `R` has perimeter `3 √3 R` if and only if each of its sides has length
`√3 R`. -/
theorem inscribedPerimeter_zmod_three_eq_iff_norm_sub_eq {χ : α → F} {s : ZMod 3 → α} {c : F}
    {R : ℝ} (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s = 3 * √3 * R ↔ ∀ k, ‖χ (s (k + 1)) - χ (s k)‖ = √3 * R := by
  have hper := inscribedPerimeter_zmod_three χ s
  constructor
  · intro h
    have hdef := three_sqrt_three_sq_sub_inscribedPerimeter_sq hs
    rw [h, sub_self] at hdef
    have hab : ‖χ (s 1) - χ (s 0)‖ = ‖χ (s 2) - χ (s 1)‖ := by
      nlinarith [sq_nonneg ‖(χ (s 0) - c) + (χ (s 1) - c) + (χ (s 2) - c)‖,
        sq_nonneg (‖χ (s 1) - χ (s 0)‖ - ‖χ (s 2) - χ (s 1)‖),
        sq_nonneg (‖χ (s 2) - χ (s 1)‖ - ‖χ (s 0) - χ (s 2)‖),
        sq_nonneg (‖χ (s 0) - χ (s 2)‖ - ‖χ (s 1) - χ (s 0)‖)]
    have hbd : ‖χ (s 2) - χ (s 1)‖ = ‖χ (s 0) - χ (s 2)‖ := by
      nlinarith [sq_nonneg ‖(χ (s 0) - c) + (χ (s 1) - c) + (χ (s 2) - c)‖,
        sq_nonneg (‖χ (s 1) - χ (s 0)‖ - ‖χ (s 2) - χ (s 1)‖),
        sq_nonneg (‖χ (s 2) - χ (s 1)‖ - ‖χ (s 0) - χ (s 2)‖),
        sq_nonneg (‖χ (s 0) - χ (s 2)‖ - ‖χ (s 1) - χ (s 0)‖)]
    rw [hper, hab, hbd] at h
    have he0 : ‖χ (s ((0 : ZMod 3) + 1)) - χ (s 0)‖ = √3 * R := by
      have h01 : (0 : ZMod 3) + 1 = 1 := rfl
      rw [h01, hab, hbd]; linarith
    have he1 : ‖χ (s ((1 : ZMod 3) + 1)) - χ (s 1)‖ = √3 * R := by
      have h11 : (1 : ZMod 3) + 1 = 2 := rfl
      rw [h11, hbd]; linarith
    have he2 : ‖χ (s ((2 : ZMod 3) + 1)) - χ (s 2)‖ = √3 * R := by
      have h21 : (2 : ZMod 3) + 1 = 0 := rfl
      rw [h21]; linarith
    intro k
    fin_cases k
    · exact he0
    · exact he1
    · exact he2
  · intro h
    have h0 : ‖χ (s 1) - χ (s 0)‖ = √3 * R := h 0
    have h1 : ‖χ (s 2) - χ (s 1)‖ = √3 * R := h 1
    have h2 : ‖χ (s 0) - χ (s 2)‖ = √3 * R := h 2
    rw [hper, h0, h1, h2]
    ring

/-- **Centroid characterization of maximal inscribed triangles.** A triangle on the sphere of
center `c` and radius `R` has perimeter `3 √3 R` if and only if the centroid of its vertices is
`c`: `∑ₖ (χ(s_k) - c) = 0`. -/
theorem inscribedPerimeter_zmod_three_eq_iff_sum_sub_eq_zero {χ : α → F} {s : ZMod 3 → α} {c : F}
    {R : ℝ} (hs : ∀ k, χ (s k) ∈ Metric.sphere c R) :
    inscribedPerimeter χ s = 3 * √3 * R ↔ ∑ k : ZMod 3, (χ (s k) - c) = 0 := by
  have hn (k : ZMod 3) : ‖χ (s k) - c‖ = R := by simpa [dist_eq_norm] using hs k
  have hsum3 : ∑ k : ZMod 3, (χ (s k) - c) =
      (χ (s 0) - c) + (χ (s 1) - c) + (χ (s 2) - c) := by
    have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      ← add_assoc]
  rw [hsum3]
  constructor
  · intro h
    have hdef := three_sqrt_three_sq_sub_inscribedPerimeter_sq hs
    rw [h, sub_self] at hdef
    have h0 : ‖(χ (s 0) - c) + (χ (s 1) - c) + (χ (s 2) - c)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (‖χ (s 1) - χ (s 0)‖ - ‖χ (s 2) - χ (s 1)‖),
        sq_nonneg (‖χ (s 2) - χ (s 1)‖ - ‖χ (s 0) - χ (s 2)‖),
        sq_nonneg (‖χ (s 0) - χ (s 2)‖ - ‖χ (s 1) - χ (s 0)‖)]
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 h0)
  · intro hsum
    rw [inscribedPerimeter_zmod_three_eq_iff_norm_sub_eq hs]
    have he0 : ‖χ (s ((0 : ZMod 3) + 1)) - χ (s 0)‖ = √3 * R := by
      have h01 : (0 : ZMod 3) + 1 = 1 := rfl
      rw [h01, ← sub_sub_sub_cancel_right (χ (s 1)) (χ (s 0)) c]
      exact norm_sub_eq_sqrt_three_mul_of_add_add_eq_zero (hn 0) (hn 1) (hn 2) hsum
    have he1 : ‖χ (s ((1 : ZMod 3) + 1)) - χ (s 1)‖ = √3 * R := by
      have h11 : (1 : ZMod 3) + 1 = 2 := rfl
      have hsum' : (χ (s 1) - c) + (χ (s 2) - c) + (χ (s 0) - c) = 0 := by rw [← hsum]; abel
      rw [h11, ← sub_sub_sub_cancel_right (χ (s 2)) (χ (s 1)) c]
      exact norm_sub_eq_sqrt_three_mul_of_add_add_eq_zero (hn 1) (hn 2) (hn 0) hsum'
    have he2 : ‖χ (s ((2 : ZMod 3) + 1)) - χ (s 2)‖ = √3 * R := by
      have h21 : (2 : ZMod 3) + 1 = 0 := rfl
      have hsum' : (χ (s 2) - c) + (χ (s 0) - c) + (χ (s 1) - c) = 0 := by rw [← hsum]; abel
      rw [h21, ← sub_sub_sub_cancel_right (χ (s 0)) (χ (s 2)) c]
      exact norm_sub_eq_sqrt_three_mul_of_add_add_eq_zero (hn 2) (hn 0) (hn 1) hsum'
    intro k
    fin_cases k
    · exact he0
    · exact he1
    · exact he2

end InnerProduct

end TauCeti
