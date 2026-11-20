/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.BottSamelson.Moment

import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# The moment image of the word `121` Bott–Samelson variety

Let `X = {(L₁, P, L) | L₁ ⊆ P₀, L₁ ⊆ P, L ⊆ P}` be the Bott–Samelson variety of the word `121`,
with `L₁, L` lines and `P` a plane of `ℂ³` and `P₀ = span(e₀, e₁)`, and let
`μ(L₁, P, L) = a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)` be the moment map of the diagonal torus
(`TauCeti.BottSamelson.moment`). This file computes the image of `μ` exactly: for nonnegative
weights it is the hexagon

`x + y + z = a + 2b + c`, `0 ≤ x, y, z`, `x ≤ a + b + c`, `y ≤ a + b + c`, `z ≤ b + c`

(`TauCeti.BottSamelson.incidence_moment_range`), which is the convex hull of the moment values of
the eight torus-fixed triples (`TauCeti.BottSamelson.incidence_moment_range_eq_convexHull`).
This is the description of the image that the convexity theorem of Atiyah and
Guillemin–Sternberg predicts for this torus action.

The inclusion of the image in the hexagon is `TauCeti.BottSamelson.moment_mem_momentPolygon`. The
other inclusion is proved here by explicit points of `X`, with no convexity theorem. The line
`z = b` cuts the hexagon into two trapezoids, and each is the image of a two-parameter family of
triples. Write `u_s = (√s, √(1 - s), 0)`, a unit vector of `P₀`, for `s ∈ [0, 1]`.

* For `z ≤ b`, take `L₁ = L = span(u_s)` and `P = w^⊥` for the unit vector
  `w = (√t √(1 - s), -√t √s, √(1 - t))` orthogonal to `u_s`. Then
  `μ = ((a + c) s + b (1 - t (1 - s)), (a + c) (1 - s) + b (1 - t s), b t)`, and for each `t` the
  parameter `s` runs along the segment of the hexagon on which `z = b t`.
* For `z ≥ b`, take `L₁ = span(u_s)`, `P = span(u_s, e₂)` and `L` the line spanned by
  `√(1 - p) u_s + √p e₂`. Then `μ = (r s, r (1 - s), b + c p)` with `r = a + b + c (1 - p)`, and
  for each `p` the parameter `s` runs along the segment of the hexagon on which `z = b + c p`.

These families need no sign condition on the weights: every point of the hexagon is a moment value
for all real `a, b, c` (`TauCeti.BottSamelson.exists_moment_eq_of_mem_momentPolygon`).

At the boundary `a = 0` the moment map no longer depends on `L₁`, and it is the moment map
`b diag(Π_P) + c diag(Π_L)` of the flag manifold of pairs `L ⊆ P`, pulled back along the
projection `π(L₁, P, L) = (L, P)`. This projection is onto, because every plane `P` meets `P₀` in
a line (`TauCeti.BottSamelson.exists_finrank_eq_one_le_initialPlane_le`). Hence the moment image
of the flag manifold is the image of `μ` at `a = 0`, the permutohedron of the eigenvalues
`(b + c, b, 0)`, the convex hull of their six rearrangements
(`TauCeti.BottSamelson.flag_moment_range`).

## Main results

* `TauCeti.BottSamelson.exists_moment_eq_of_mem_momentPolygon`: every point of the hexagon is a
  moment value.
* `TauCeti.BottSamelson.incidence_moment_range`,
  `TauCeti.BottSamelson.incidence_moment_range_eq_convexHull`: the moment image is the hexagon,
  the convex hull of the eight fixed values.
* `TauCeti.BottSamelson.exists_finrank_eq_one_le_initialPlane_le`: the projection to the flag
  manifold is onto.
* `TauCeti.BottSamelson.flag_moment_range`: the moment image of the flag manifold of `ℂ³` for the
  eigenvalues `(b + c, b, 0)` is their permutohedron.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15;
  V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513 (the convexity theorem).
* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electron. J. Combin. 23
  (2016), §3.2 and §4.1 (Bott–Samelson varieties inside products of Grassmannians).
-/

public section

noncomputable section

namespace TauCeti.BottSamelson

open Module Set Submodule

/-! ### Points of the incidence variety from vectors -/

/-- A triple of lines spanned by vectors `u`, `l` and the plane orthogonal to a vector `w` lies in
the Bott–Samelson variety when `u ∈ P₀` and `w` is orthogonal to `u` and `l`, and its moment value
is computed from the coordinates of the three vectors. -/
private theorem exists_moment_eq_of_inner_eq_zero (a b c : ℝ)
    {u w l : EuclideanSpace ℂ (Fin 3)} (hu : u ≠ 0) (hw : w ≠ 0) (hl : l ≠ 0) (hu₂ : u 2 = 0)
    (hwu : inner ℂ w u = 0) (hwl : inner ℂ w l = 0) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
        moment a b c L₁ P L = fun i ↦ a * (‖u i‖ ^ 2 / ‖u‖ ^ 2) +
          b * (1 - ‖w i‖ ^ 2 / ‖w‖ ^ 2) + c * (‖l i‖ ^ 2 / ‖l‖ ^ 2) := by
  have : Fact (finrank ℂ (EuclideanSpace ℂ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  refine ⟨ℂ ∙ u, (ℂ ∙ w)ᗮ, ℂ ∙ l, finrank_span_singleton hu, finrank_orthogonal_span_singleton hw,
    finrank_span_singleton hl, ?_, ?_, ?_, ?_⟩
  · rw [span_singleton_le_iff_mem, initialPlane_eq_span_image, image_pair]
    refine mem_span_pair.2 ⟨u 0, u 1, ?_⟩
    ext i
    fin_cases i <;> simp [hu₂]
  · exact (span_singleton_le_iff_mem _ _).2 (mem_orthogonal_singleton_iff_inner_right.2 hwu)
  · exact (span_singleton_le_iff_mem _ _).2 (mem_orthogonal_singleton_iff_inner_right.2 hwl)
  · ext i
    simp [projectorDiagonal_orthogonal, projectorDiagonal_span_singleton]

/-- The vector of `ℂ³` with real coordinates `x, y, z`. -/
private abbrev realVec (x y z : ℝ) : EuclideanSpace ℂ (Fin 3) := !₂[(x : ℂ), y, z]

private theorem norm_realVec_sq (x y z : ℝ) : ‖realVec x y z‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

private theorem inner_realVec (x y z x' y' z' : ℝ) :
    inner ℂ (realVec x y z) (realVec x' y' z') = ((x * x' + y * y' + z * z' : ℝ) : ℂ) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- A number between `0` and `A` is a multiple `t A` of `A` with `t ∈ [0, 1]`. -/
private theorem exists_mul_eq {y A : ℝ} (h₀ : 0 ≤ y) (h₁ : y ≤ A) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ t * A = y := by
  have hy : y ∈ (· * A) '' Icc 0 1 := by
    rw [image_mul_right_Icc zero_le_one (h₀.trans h₁), zero_mul, one_mul]
    exact ⟨h₀, h₁⟩
  obtain ⟨t, ⟨ht₀, ht₁⟩, rfl⟩ := hy
  exact ⟨t, ht₀, ht₁, rfl⟩

private theorem ne_zero_of_norm_sq_eq_one {v : EuclideanSpace ℂ (Fin 3)} (hv : ‖v‖ ^ 2 = 1) :
    v ≠ 0 := by
  rintro rfl
  simp at hv

/-! ### Every point of the hexagon is a moment value -/

/-- The trapezoid `z ≤ b` of the hexagon consists of the moment values of the triples
`(span u_s, w^⊥, span u_s)` with `u_s = (√s, √(1 - s), 0)` and
`w = (√t √(1 - s), -√t √s, √(1 - t))`. -/
private theorem exists_moment_eq_of_le {a b c : ℝ} {x : Fin 3 → ℝ}
    (hx : x ∈ momentPolygon a b c) (h : x 2 ≤ b) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧ moment a b c L₁ P L = x := by
  obtain ⟨hsum, -, -, hx₂, hx₃, hx₄, -⟩ := mem_momentPolygon.1 hx
  -- `z = t b` and `x = b - z + s (a + c + z)`
  obtain ⟨t, ht₀, ht₁, ht⟩ := exists_mul_eq hx₂ h
  obtain ⟨s, hs₀, hs₁, hs⟩ := exists_mul_eq (y := x 0 - b + x 2) (A := a + c + x 2)
    (by linarith) (by linarith)
  have hu : ‖realVec √s √(1 - s) 0‖ ^ 2 = 1 := by
    rw [norm_realVec_sq, Real.sq_sqrt hs₀, Real.sq_sqrt (by linarith)]
    ring
  have hw : ‖realVec (√t * √(1 - s)) (-(√t * √s)) √(1 - t)‖ ^ 2 = 1 := by
    rw [norm_realVec_sq, neg_sq, mul_pow, mul_pow, Real.sq_sqrt ht₀, Real.sq_sqrt hs₀,
      Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring
  have hwu : inner ℂ (realVec (√t * √(1 - s)) (-(√t * √s)) √(1 - t))
      (realVec √s √(1 - s) 0) = 0 := by
    rw [inner_realVec, Complex.ofReal_eq_zero]
    ring
  obtain ⟨L₁, P, L, h₁, h₂, h₃, h₄, h₅, h₆, hμ⟩ := exists_moment_eq_of_inner_eq_zero a b c
    (ne_zero_of_norm_sq_eq_one hu) (ne_zero_of_norm_sq_eq_one hw) (ne_zero_of_norm_sq_eq_one hu)
    (by simp) hwu hwu
  refine ⟨L₁, P, L, h₁, h₂, h₃, h₄, h₅, h₆, ?_⟩
  rw [hμ, hu, hw]
  ext i
  fin_cases i <;> simp [mul_pow, Real.sq_sqrt ht₀, Real.sq_sqrt hs₀,
    Real.sq_sqrt (sub_nonneg.2 hs₁), Real.sq_sqrt (sub_nonneg.2 ht₁)]
  · linear_combination hs + (s - 1) * ht
  · linear_combination -hs - s * ht - hsum
  · linear_combination ht

/-- The trapezoid `z ≥ b` of the hexagon consists of the moment values of the triples
`(span u_s, span(u_s, e₂), span(√(1 - p) u_s + √p e₂))` with `u_s = (√s, √(1 - s), 0)`; the plane
`span(u_s, e₂)` is the orthogonal complement of `(√(1 - s), -√s, 0)`. -/
private theorem exists_moment_eq_of_ge {a b c : ℝ} {x : Fin 3 → ℝ}
    (hx : x ∈ momentPolygon a b c) (h : b ≤ x 2) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧ moment a b c L₁ P L = x := by
  obtain ⟨hsum, hx₀, hx₁, -, -, -, hx₅⟩ := mem_momentPolygon.1 hx
  -- `z = b + p c` and `x = s (x + y)`
  obtain ⟨p, hp₀, hp₁, hp⟩ := exists_mul_eq (y := x 2 - b) (A := c) (by linarith) (by linarith)
  obtain ⟨s, hs₀, hs₁, hs⟩ := exists_mul_eq (y := x 0) (A := x 0 + x 1) hx₀ (by linarith)
  have hu : ‖realVec √s √(1 - s) 0‖ ^ 2 = 1 := by
    rw [norm_realVec_sq, Real.sq_sqrt hs₀, Real.sq_sqrt (by linarith)]
    ring
  have hw : ‖realVec √(1 - s) (-√s) 0‖ ^ 2 = 1 := by
    rw [norm_realVec_sq, neg_sq, Real.sq_sqrt hs₀, Real.sq_sqrt (by linarith)]
    ring
  have hl : ‖realVec (√(1 - p) * √s) (√(1 - p) * √(1 - s)) √p‖ ^ 2 = 1 := by
    rw [norm_realVec_sq, mul_pow, mul_pow, Real.sq_sqrt hp₀, Real.sq_sqrt hs₀,
      Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring
  obtain ⟨L₁, P, L, h₁, h₂, h₃, h₄, h₅, h₆, hμ⟩ := exists_moment_eq_of_inner_eq_zero a b c
    (ne_zero_of_norm_sq_eq_one hu) (ne_zero_of_norm_sq_eq_one hw) (ne_zero_of_norm_sq_eq_one hl)
    (by simp) (by rw [inner_realVec, Complex.ofReal_eq_zero]; ring)
    (by rw [inner_realVec, Complex.ofReal_eq_zero]; ring)
  refine ⟨L₁, P, L, h₁, h₂, h₃, h₄, h₅, h₆, ?_⟩
  rw [hμ, hu, hw, hl]
  ext i
  fin_cases i <;> simp [mul_pow, Real.sq_sqrt hp₀, Real.sq_sqrt hs₀,
    Real.sq_sqrt (sub_nonneg.2 hs₁), Real.sq_sqrt (sub_nonneg.2 hp₁)]
  · linear_combination hs - s * hp - s * hsum
  · linear_combination (s - 1) * hsum + (s - 1) * hp - hs
  · linear_combination hp

/-- **Every point of the moment hexagon is a moment value** of the Bott–Samelson variety of the
word `121`. No sign condition on the weights is needed. -/
theorem exists_moment_eq_of_mem_momentPolygon {a b c : ℝ} {x : Fin 3 → ℝ}
    (hx : x ∈ momentPolygon a b c) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧ moment a b c L₁ P L = x := by
  rcases le_total (x 2) b with h | h
  exacts [exists_moment_eq_of_le hx h, exists_moment_eq_of_ge hx h]

/-! ### The moment image -/

/-- **The moment image of the word `121` Bott–Samelson variety.** For nonnegative weights, the
image of the moment map `μ(L₁, P, L) = a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)` on the triples
of lines `L₁, L` and planes `P` of `ℂ³` with `L₁ ⊆ P₀`, `L₁ ⊆ P` and `L ⊆ P` is the hexagon
`x + y + z = a + 2b + c`, `0 ≤ x, y, z`, `x ≤ a + b + c`, `y ≤ a + b + c`, `z ≤ b + c`. -/
theorem incidence_moment_range {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    {x | ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧
      finrank ℂ P = 2 ∧ finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
        moment a b c L₁ P L = x} = momentPolygon a b c := by
  refine Subset.antisymm ?_ fun x hx ↦ exists_moment_eq_of_mem_momentPolygon hx
  rintro _ ⟨L₁, P, L, hL₁, hP, hL, h, -, -, rfl⟩
  exact moment_mem_momentPolygon ha hb hc hL₁ hP hL h

/-- For nonnegative weights, the moment image of the Bott–Samelson variety of the word `121` is the
convex hull of the moment values of its eight torus-fixed triples. -/
theorem incidence_moment_range_eq_convexHull {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    {x | ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧
      finrank ℂ P = 2 ∧ finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
        moment a b c L₁ P L = x} = convexHull ℝ (range (fixedMoment a b c)) := by
  rw [incidence_moment_range ha hb hc, convexHull_range_fixedMoment ha hb hc]

/-! ### The boundary `a = 0`: the flag manifold -/

/-- Every plane `P` of `ℂ³` contains a line `L₁ ⊆ P₀`: the projection `(L₁, P, L) ↦ (L, P)` from the
Bott–Samelson variety of the word `121` to the flag manifold of `ℂ³` is onto. -/
theorem exists_finrank_eq_one_le_initialPlane_le {P : Submodule ℂ (EuclideanSpace ℂ (Fin 3))}
    (hP : finrank ℂ P = 2) : ∃ L₁ : Submodule ℂ (EuclideanSpace ℂ (Fin 3)),
      finrank ℂ L₁ = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (P ⊓ initialPlane)).1
    (Submodule.inf_ne_bot_of_finrank_lt (by simp [hP, finrank_initialPlane]))
  exact ⟨ℂ ∙ v, finrank_span_singleton hv0, (span_singleton_le_iff_mem _ _).2 (mem_inf.1 hv).2,
    (span_singleton_le_iff_mem _ _).2 (mem_inf.1 hv).1⟩

/-- **The moment image of the flag manifold of `ℂ³`.** For nonnegative `b, c`, the image of the map
`(L, P) ↦ b diag(Π_P) + c diag(Π_L)` on the flags `L ⊆ P` of a line and a plane of `ℂ³` is the
permutohedron of the eigenvalues `(b + c, b, 0)` of `b Π_P + c Π_L`, the convex hull of their six
rearrangements. -/
theorem flag_moment_range {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    {x | ∃ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ P = 2 ∧ finrank ℂ L = 1 ∧
      L ≤ P ∧ b • P.projectorDiagonal + c • L.projectorDiagonal = x} =
      convexHull ℝ (range fun σ : Equiv.Perm (Fin 3) ↦ ![b + c, b, 0] ∘ σ) := by
  rw [← range_fixedMoment_zero_left, ← incidence_moment_range_eq_convexHull le_rfl hb hc]
  ext x
  constructor
  · rintro ⟨P, L, hP, hL, hLP, rfl⟩
    obtain ⟨L₁, hL₁, h₁, h₂⟩ := exists_finrank_eq_one_le_initialPlane_le hP
    exact ⟨L₁, P, L, hL₁, hP, hL, h₁, h₂, hLP, by simp [moment_def]⟩
  · rintro ⟨L₁, P, L, -, hP, hL, -, -, hLP, rfl⟩
    exact ⟨P, L, hP, hL, hLP, by simp [moment_def]⟩

end TauCeti.BottSamelson
