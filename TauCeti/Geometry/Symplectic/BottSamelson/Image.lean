/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.BottSamelson.Moment

/-!
# The moment image of the word `121` Bott–Samelson variety

Let `X = {(L₁, P, L) | L₁ ⊆ P₀, L₁ ⊆ P, L ⊆ P}` be the Bott–Samelson variety of the word `121`,
of lines `L₁, L` and planes `P` of `ℂ³` with `P₀ = span(e₀, e₁)`
(`TauCeti.BottSamelson.initialPlane`), and let

`μ(L₁, P, L) = a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)`

be the moment map of the diagonal torus for weights `a, b, c`
(`TauCeti.BottSamelson.moment`). This file proves that for nonnegative weights the image of `X`
under `μ` is exactly the hexagon `TauCeti.BottSamelson.momentPolygon a b c`, the convex hull of
the eight fixed values `TauCeti.BottSamelson.fixedMoment a b c`
(`TauCeti.BottSamelson.exists_moment_eq_iff_mem_convexHull`). One inclusion is
`TauCeti.BottSamelson.moment_mem_convexHull`; this file proves the other one, that every point
of the hexagon is a moment value
(`TauCeti.BottSamelson.exists_moment_eq_of_mem_momentPolygon`). This inclusion needs no sign
condition on the weights: the inequalities defining the hexagon already force the signs that the
construction uses.

The convexity theorem for torus actions gives this inclusion abstractly. Here it is proved by an
explicit family of points of `X`, with no symplectic input. For real unit vectors `p, q ∈ ℝ³` with
`p ⊥ q` and `p₂ = 0`, and `t ∈ [0, 1]`, put

`L₁ = ℂ p`, `P = ℂ p + ℂ q`, `L = ℂ (√t p + i √(1 - t) q)`.

Then `L₁ ⊆ P₀`, `L₁ ⊆ P` and `L ⊆ P`. The factor `i` makes the coordinates of the generator of `L`
have real part from `p` and imaginary part from `q`, so that the diagonal of `Π_L` is the convex
combination `t p² + (1 - t) q²` of the squared coordinates. Since `Π_P` has diagonal
`p² + q²`, the moment value is

`μ = (a + b + c t) p² + (b + c (1 - t)) q²`.

Taking `p = (√s, √(1 - s), 0)` and `q = (-√r √(1 - s), √r √s, √(1 - r))`, with
`p² = (s, 1 - s, 0)` and `q² = (r (1 - s), r s, 1 - r)`, two subfamilies cover the hexagon. A
point `(x, y, z)` with `z ≤ b` is reached with `t = 1`, that is `L = L₁`, and a point with
`z ≥ b` with `r = 0`, that is `P = L₁ + ℂ e₂`.

For `a = 0` the hexagon is the convex hull of the six rearrangements of `(b + c, b, 0)`
(`TauCeti.BottSamelson.range_fixedMoment_zero_left`), the permutohedron of the flag manifold for
these eigenvalues, so the moment image of `X` is that permutohedron.

## Main results

* `TauCeti.BottSamelson.exists_moment_eq_of_mem_momentPolygon`: every point of the hexagon is the
  moment value of a point of `X`.
* `TauCeti.BottSamelson.exists_moment_eq_iff_mem_momentPolygon`,
  `TauCeti.BottSamelson.exists_moment_eq_iff_mem_convexHull`: the moment image of `X` is the
  hexagon, the convex hull of the eight fixed values.

## References

* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electron. J. Combin. 23
  (2016), §3.2 and §4.1 (Bott–Samelson varieties inside products of Grassmannians).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 27.1 (the convexity theorem for torus actions).
-/

public section

noncomputable section

namespace TauCeti.BottSamelson

open Module Set Submodule Complex

/-! ### An explicit family of points of the Bott–Samelson variety -/

/-- The vector of `ℂ³` with the real coordinates `p`. -/
private def ofReal3 (p : Fin 3 → ℝ) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 fun i ↦ (p i : ℂ)

private theorem inner_ofReal3 (p q : Fin 3 → ℝ) :
    inner ℂ (ofReal3 p) (ofReal3 q) = ((∑ i, p i * q i : ℝ) : ℂ) := by
  simp [ofReal3, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem norm_ofReal3 (p : Fin 3 → ℝ) : ‖ofReal3 p‖ = √(∑ i, p i ^ 2) := by
  simp [EuclideanSpace.norm_eq, ofReal3]

/-- The vector `√t p + i √(1 - t) q`, whose coordinates have real part `√t pᵢ` and imaginary part
`√(1 - t) qᵢ`. -/
private def mix (p q : Fin 3 → ℝ) (t : ℝ) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 fun i ↦ ((√t * p i : ℝ) : ℂ) + ((√(1 - t) * q i : ℝ) : ℂ) * I

private theorem mix_eq (p q : Fin 3 → ℝ) (t : ℝ) :
    mix p q t = (√t : ℂ) • ofReal3 p + ((√(1 - t) : ℂ) * I) • ofReal3 q := by
  ext i
  simp only [mix, ofReal3, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    ofReal_mul]
  ring

private theorem norm_mix_apply_sq (p q : Fin 3 → ℝ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (i : Fin 3) : ‖mix p q t i‖ ^ 2 = t * p i ^ 2 + (1 - t) * q i ^ 2 := by
  simp only [mix, PiLp.toLp_apply]
  rw [Complex.sq_norm, Complex.normSq_add_mul_I, mul_pow, mul_pow, Real.sq_sqrt ht₀,
    Real.sq_sqrt (by linarith)]

private theorem orthonormal_single {u : EuclideanSpace ℂ (Fin 3)} (hu : ‖u‖ = 1) :
    Orthonormal ℂ ![u] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i; fin_cases j
  simp [hu]

/-- For real unit vectors `p ⊥ q` with `p₂ = 0` and `t ∈ [0, 1]`, the triple
`(ℂ p, ℂ p + ℂ q, ℂ (√t p + i √(1 - t) q))` lies in the Bott–Samelson variety and has moment value
`(a + b + c t) p² + (b + c (1 - t)) q²`. -/
private theorem exists_moment_eq_of_orthonormal (a b c : ℝ) {p q : Fin 3 → ℝ}
    (hp : ∑ i, p i ^ 2 = 1) (hq : ∑ i, q i ^ 2 = 1) (hpq : ∑ i, p i * q i = 0) (hp₂ : p 2 = 0)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
        moment a b c L₁ P L = fun i ↦ (a + b + c * t) * p i ^ 2 + (b + c * (1 - t)) * q i ^ 2 := by
  have huv : Orthonormal ℂ ![ofReal3 p, ofReal3 q] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [inner_ofReal3, norm_ofReal3, hp, hq, hpq, mul_comm]
  have hu : Orthonormal ℂ ![ofReal3 p] := orthonormal_single (by simp [norm_ofReal3, hp])
  have hℓ : Orthonormal ℂ ![mix p q t] := by
    refine orthonormal_single ?_
    have h : ‖mix p q t‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [norm_mix_apply_sq p q ht₀ ht₁, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq]
      ring
    rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h
  refine ⟨span ℂ (range ![ofReal3 p]), span ℂ (range ![ofReal3 p, ofReal3 q]),
    span ℂ (range ![mix p q t]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [finrank_span_eq_card hu.linearIndependent]
  · simp [finrank_span_eq_card huv.linearIndependent]
  · simp [finrank_span_eq_card hℓ.linearIndependent]
  · -- `p = p₀ e₀ + p₁ e₁` lies in `P₀`, since `p₂ = 0`
    have h : ofReal3 p = (p 0 : ℂ) • EuclideanSpace.single 0 1 +
        (p 1 : ℂ) • EuclideanSpace.single 1 1 := by
      ext i
      fin_cases i <;> simp [ofReal3, hp₂]
    rw [span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    simp only [Matrix.cons_val_fin_one, SetLike.mem_coe, h, initialPlane_eq_span_image]
    exact add_mem (smul_mem _ _ (subset_span ⟨0, by simp, rfl⟩))
      (smul_mem _ _ (subset_span ⟨1, by simp, rfl⟩))
  · refine span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨0, by fin_cases j; rfl⟩
  · rw [span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    simp only [Matrix.cons_val_fin_one, SetLike.mem_coe, mix_eq]
    exact add_mem (smul_mem _ _ (subset_span ⟨0, rfl⟩)) (smul_mem _ _ (subset_span ⟨1, rfl⟩))
  · ext i
    simp only [moment_apply, projectorDiagonal_span_range_of_orthonormal hu,
      projectorDiagonal_span_range_of_orthonormal huv,
      projectorDiagonal_span_range_of_orthonormal hℓ, Fin.sum_univ_one, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, norm_mix_apply_sq p q ht₀ ht₁]
    simp only [ofReal3, PiLp.toLp_apply, norm_real, Real.norm_eq_abs, sq_abs]
    ring

/-! ### Parameters of the points of the hexagon -/

/-- Every point `(x, y, z)` of the hexagon is `(a + b + c t) (s, 1 - s, 0) +
(b + c (1 - t)) (r (1 - s), r s, 1 - r)` for some `s, r, t ∈ [0, 1]`: with `t = 1` when `z ≤ b`
and with `r = 0` when `z ≥ b`. Only the first and last coordinates are recorded; the middle one
follows from the trace. -/
private theorem exists_params_of_mem_momentPolygon {a b c : ℝ} {x : Fin 3 → ℝ}
    (hx : x ∈ momentPolygon a b c) :
    ∃ s r t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
      x 0 = (a + b + c * t) * s + (b + c * (1 - t)) * (r * (1 - s)) ∧
      x 2 = (b + c * (1 - t)) * (1 - r) := by
  obtain ⟨hsum, hx₀, hx₁, hx₂, hx₀', hx₁', hx₂'⟩ := mem_momentPolygon.1 hx
  rcases le_total (x 2) b with hzb | hbz
  · -- `t = 1`, `b r = b - z` and `(a + b + c) s + (b - z) (1 - s) = x`
    have hr : b * (1 - x 2 / b) = b - x 2 := by
      rcases eq_or_ne b 0 with h | h
      · simp [h, le_antisymm (h ▸ hzb) hx₂]
      · field_simp
    have hb : 0 ≤ b := hx₂.trans hzb
    have hd : 0 ≤ a + c + x 2 := by linarith
    have hs : (a + c + x 2) * ((x 0 - (b - x 2)) / (a + c + x 2)) = x 0 - (b - x 2) := by
      rcases eq_or_ne (a + c + x 2) 0 with h | h
      · rw [h, zero_mul]
        linarith
      · field_simp
    refine ⟨(x 0 - (b - x 2)) / (a + c + x 2), 1 - x 2 / b, 1, div_nonneg (by linarith) hd,
      div_le_one_of_le₀ (by linarith) hd, by linarith [div_le_one_of_le₀ hzb hb],
      by linarith [div_nonneg hx₂ hb], zero_le_one, le_rfl, ?_, ?_⟩
    · linear_combination -(1 - (x 0 - (b - x 2)) / (a + c + x 2)) * hr - hs
    · linear_combination hr
  · -- `r = 0`, `c (1 - t) = z - b` and `(a + 2b + c - z) s = x`
    have hc : 0 ≤ c := by linarith
    have ht : c * (1 - (b + c - x 2) / c) = x 2 - b := by
      rcases eq_or_ne c 0 with h | h
      · simp only [h, zero_mul]
        linarith
      · field_simp
        ring
    have hd : 0 ≤ a + 2 * b + c - x 2 := by linarith
    have hs : (a + 2 * b + c - x 2) * (x 0 / (a + 2 * b + c - x 2)) = x 0 := by
      rcases eq_or_ne (a + 2 * b + c - x 2) 0 with h | h
      · rw [h, zero_mul]
        linarith
      · field_simp
    refine ⟨x 0 / (a + 2 * b + c - x 2), 0, (b + c - x 2) / c, div_nonneg hx₀ hd,
      div_le_one_of_le₀ (by linarith) hd, le_rfl, zero_le_one, div_nonneg (by linarith) hc,
      div_le_one_of_le₀ (by linarith) hc, ?_, ?_⟩
    · linear_combination x 0 / (a + 2 * b + c - x 2) * ht - hs
    · linear_combination -ht

/-! ### The moment image -/

/-- **Every point of the hexagon is a moment value** of the Bott–Samelson variety of the word
`121`: there are a line `L₁ ⊆ P₀`, a plane `P ⊇ L₁` and a line `L ⊆ P` with `μ(L₁, P, L) = x`.
This is the inclusion of the hexagon in the moment image given by the convexity theorem for torus
actions. It holds for all real weights. -/
theorem exists_moment_eq_of_mem_momentPolygon {a b c : ℝ} {x : Fin 3 → ℝ}
    (hx : x ∈ momentPolygon a b c) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧ moment a b c L₁ P L = x := by
  obtain ⟨s, r, t, hs₀, hs₁, hr₀, hr₁, ht₀, ht₁, hx₀, hx₂⟩ :=
    exists_params_of_mem_momentPolygon hx
  have hs₁' : 0 ≤ 1 - s := by linarith
  have hr₁' : 0 ≤ 1 - r := by linarith
  -- `p = (√s, √(1 - s), 0)` and `q = (-√r √(1 - s), √r √s, √(1 - r))`
  obtain ⟨L₁, P, L, hL₁, hP, hL, h₀, h₁, h₂, hμ⟩ :=
    exists_moment_eq_of_orthonormal a b c (p := ![√s, √(1 - s), 0])
      (q := ![-(√r * √(1 - s)), √r * √s, √(1 - r)])
      (by simp [Fin.sum_univ_three, Real.sq_sqrt hs₀, Real.sq_sqrt hs₁'])
      (by simp [Fin.sum_univ_three, mul_pow, Real.sq_sqrt hs₀, Real.sq_sqrt hs₁',
        Real.sq_sqrt hr₀, Real.sq_sqrt hr₁']; ring)
      (by simp [Fin.sum_univ_three]; ring) rfl ht₀ ht₁
  refine ⟨L₁, P, L, hL₁, hP, hL, h₀, h₁, h₂, ?_⟩
  have hsum := (mem_momentPolygon.1 hx).1
  rw [hμ]
  ext i
  fin_cases i <;>
    simp [mul_pow, Real.sq_sqrt hs₀, Real.sq_sqrt hs₁', Real.sq_sqrt hr₀, Real.sq_sqrt hr₁']
  · linear_combination -hx₀
  · linear_combination -hsum + hx₀ + hx₂
  · linear_combination -hx₂

/-- **The moment image of the Bott–Samelson variety of the word `121` is the hexagon**, for
nonnegative weights: a point is the moment value of a line `L₁ ⊆ P₀`, a plane `P ⊇ L₁` and a line
`L ⊆ P` exactly when it lies in `momentPolygon a b c`. -/
theorem exists_moment_eq_iff_mem_momentPolygon {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) {x : Fin 3 → ℝ} :
    (∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧ moment a b c L₁ P L = x) ↔
      x ∈ momentPolygon a b c := by
  refine ⟨?_, exists_moment_eq_of_mem_momentPolygon⟩
  rintro ⟨L₁, P, L, hL₁, hP, hL, h₀, -, -, rfl⟩
  exact moment_mem_momentPolygon ha hb hc hL₁ hP hL h₀

/-- **The moment image of the Bott–Samelson variety of the word `121` is the convex hull of the
eight fixed values**, for nonnegative weights. -/
theorem exists_moment_eq_iff_mem_convexHull {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) {x : Fin 3 → ℝ} :
    (∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧ moment a b c L₁ P L = x) ↔
      x ∈ convexHull ℝ (range (fixedMoment a b c)) := by
  rw [convexHull_range_fixedMoment ha hb hc, exists_moment_eq_iff_mem_momentPolygon ha hb hc]

end TauCeti.BottSamelson
