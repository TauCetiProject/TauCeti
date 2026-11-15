/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PeriodicPolygon

/-!
# Inscribed polygon perimeter bounds on spheres

This file proves sharp upper bounds and equality characterizations for the perimeter
`TauCeti.inscribedPerimeter χ s = ∑ₖ ‖χ(s_(k+1)) - χ(s_k)‖` of closed polygons whose vertices lie
on a sphere `Metric.sphere c R` in a real inner product space `F`, together with the `N = 2`
double-normal characterization of the equal-angle reflection law.

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
* **Double-normal characterization for `N = 2`.** Equality of the incoming and outgoing unit-chord
  inner products at both vertices of a `2`-gon holds if and only if the chord is orthogonal to the
  tangent vectors at both endpoints (`TauCeti.inner_eq_inner_zmod_two_iff`).

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

/-- Explicit three-term expansion of `inscribedPerimeter` for `N = 3`. -/
theorem inscribedPerimeter_zmod_three (χ : α → F) (s : ZMod 3 → α) :
    inscribedPerimeter χ s =
      ‖χ (s 1) - χ (s 0)‖ + ‖χ (s 2) - χ (s 1)‖ + ‖χ (s 0) - χ (s 2)‖ := by
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have h01 : (0 : ZMod 3) + 1 = 1 := rfl
  have h11 : (1 : ZMod 3) + 1 = 2 := rfl
  have h21 : (2 : ZMod 3) + 1 = 0 := rfl
  rw [inscribedPerimeter_def, huniv, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, h01, h11, h21]
  ring

end NormedGroup

section InnerProduct

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Two points on a sphere of center `c` and radius `R` lie at distance `2 R` if and only if they
are antipodal across `c`. -/
theorem norm_sub_eq_two_mul_iff_of_mem_sphere {x y c : F} {R : ℝ} (hx : x ∈ Metric.sphere c R)
    (hy : y ∈ Metric.sphere c R) :
    ‖y - x‖ = 2 * R ↔ y - c = -(x - c) := by
  have hR : 0 ≤ R := hx ▸ dist_nonneg
  have hx' : ‖x - c‖ = R := by simpa [dist_eq_norm] using hx
  have hy' : ‖y - c‖ = R := by simpa [dist_eq_norm] using hy
  have hpar : ‖(y - c) + (x - c)‖ ^ 2 + ‖y - x‖ ^ 2 = 4 * R ^ 2 := by
    rw [← sub_sub_sub_cancel_right y x c, norm_add_sq_real (y - c) (x - c),
      norm_sub_sq_real (y - c) (x - c), hx', hy']
    ring
  constructor
  · intro h
    have h0 : ‖(y - c) + (x - c)‖ ^ 2 = 0 := by
      rw [h] at hpar
      nlinarith
    exact eq_neg_of_add_eq_zero_left (norm_eq_zero.1 (sq_eq_zero_iff.1 h0))
  · intro h
    have hadd : (y - c) + (x - c) = 0 := add_eq_zero_iff_eq_neg.2 h
    rw [hadd, norm_zero] at hpar
    have hsq : ‖y - x‖ ^ 2 = (2 * R) ^ 2 := by nlinarith
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

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

end InnerProduct

section SeminormedInnerProduct

variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **For `N = 2`, the equal-angle reflection law is double normality.** Equality of the incoming
and outgoing unit-chord inner products at both vertices of a `2`-gon is equivalent to orthogonality
of the chord `χ(s_1) - χ(s_0)` to both `d(s_0)` and `d(s_1)`. -/
theorem inner_eq_inner_zmod_two_iff (χ d : α → F) (s : ZMod 2 → α) :
    (∀ k : ZMod 2,
        ⟪‖χ (s k) - χ (s (k - 1))‖⁻¹ • (χ (s k) - χ (s (k - 1))), d (s k)⟫ =
          ⟪‖χ (s (k + 1)) - χ (s k)‖⁻¹ • (χ (s (k + 1)) - χ (s k)), d (s k)⟫) ↔
      ⟪χ (s 1) - χ (s 0), d (s 0)⟫ = 0 ∧ ⟪χ (s 1) - χ (s 0), d (s 1)⟫ = 0 := by
  have hall {P : ZMod 2 → Prop} : (∀ k, P k) ↔ P 0 ∧ P 1 :=
    ⟨fun h ↦ ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ k ↦ by fin_cases k; exacts [h0, h1]⟩
  have hunit (v u : F) : ‖v‖⁻¹ * ⟪v, u⟫ = 0 ↔ ⟪v, u⟫ = 0 := by
    refine ⟨fun h ↦ (mul_eq_zero.1 h).elim (fun hv ↦ ?_) id, fun h ↦ by rw [h, mul_zero]⟩
    have habs := abs_real_inner_le_norm v u
    rw [inv_eq_zero.1 hv, zero_mul] at habs
    exact abs_nonpos_iff.1 habs
  have h0_sub : (0 : ZMod 2) - 1 = 1 := rfl
  have h0_add : (0 : ZMod 2) + 1 = 1 := rfl
  have h1_sub : (1 : ZMod 2) - 1 = 0 := rfl
  have h1_add : (1 : ZMod 2) + 1 = 0 := rfl
  rw [hall, h0_sub, h0_add, h1_sub, h1_add, norm_sub_rev (χ (s 0)) (χ (s 1)),
    ← neg_sub (χ (s 1)) (χ (s 0)), smul_neg]
  refine and_congr ?_ ?_ <;>
    (rw [inner_neg_left, real_inner_smul_left];
      exact ⟨fun h ↦ (hunit _ _).1 (by linarith), fun h ↦ by rw [(hunit _ _).2 h]; ring⟩)

end SeminormedInnerProduct

section InnerProductTriangles

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

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
  have hR : 0 ≤ R := hs 0 ▸ dist_nonneg
  have hn (k : ZMod 3) : ‖χ (s k) - c‖ = R := by simpa [dist_eq_norm] using hs k
  have hsum3 : ∑ k : ZMod 3, (χ (s k) - c) =
      (χ (s 0) - c) + (χ (s 1) - c) + (χ (s 2) - c) :=
    Fin.sum_univ_three fun k : Fin 3 ↦ χ (s (k : ZMod 3)) - c
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
    -- When `x₀ + x₁ + x₂ = 0` with `‖xᵢ‖ = R`, the parallelogram law gives
    -- `‖x_(k+1) - x_k‖ = √3 R`.
    have hedge {x y z : F} (hx : ‖x‖ = R) (hy : ‖y‖ = R) (hz : ‖z‖ = R) (hxyz : x + y + z = 0) :
        ‖y - x‖ = √3 * R := by
      have hxy : y + x = -z := eq_neg_of_add_eq_zero_left (by rwa [add_comm y x])
      have hpar : ‖y + x‖ ^ 2 + ‖y - x‖ ^ 2 = 4 * R ^ 2 := by
        rw [norm_add_sq_real, norm_sub_sq_real, hx, hy]
        ring
      rw [hxy, norm_neg, hz] at hpar
      have hsq : ‖y - x‖ ^ 2 = (√3 * R) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        linarith
      exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    have he0 : ‖χ (s ((0 : ZMod 3) + 1)) - χ (s 0)‖ = √3 * R := by
      have h01 : (0 : ZMod 3) + 1 = 1 := rfl
      rw [h01, ← sub_sub_sub_cancel_right (χ (s 1)) (χ (s 0)) c]
      exact hedge (hn 0) (hn 1) (hn 2) hsum
    have he1 : ‖χ (s ((1 : ZMod 3) + 1)) - χ (s 1)‖ = √3 * R := by
      have h11 : (1 : ZMod 3) + 1 = 2 := rfl
      have hsum' : (χ (s 1) - c) + (χ (s 2) - c) + (χ (s 0) - c) = 0 := by rw [← hsum]; abel
      rw [h11, ← sub_sub_sub_cancel_right (χ (s 2)) (χ (s 1)) c]
      exact hedge (hn 1) (hn 2) (hn 0) hsum'
    have he2 : ‖χ (s ((2 : ZMod 3) + 1)) - χ (s 2)‖ = √3 * R := by
      have h21 : (2 : ZMod 3) + 1 = 0 := rfl
      have hsum' : (χ (s 2) - c) + (χ (s 0) - c) + (χ (s 1) - c) = 0 := by rw [← hsum]; abel
      rw [h21, ← sub_sub_sub_cancel_right (χ (s 0)) (χ (s 2)) c]
      exact hedge (hn 2) (hn 0) (hn 1) hsum'
    intro k
    fin_cases k
    · exact he0
    · exact he1
    · exact he2

end InnerProductTriangles

end TauCeti
