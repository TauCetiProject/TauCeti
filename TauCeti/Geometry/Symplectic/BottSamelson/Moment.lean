/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Diagonal
public import TauCeti.Geometry.Symplectic.BottSamelson.FixedMoment

/-!
# The moment map of the word `121` Bott–Samelson variety

Let `P₀ = span(e₀, e₁) ⊆ ℂ³` (`TauCeti.BottSamelson.initialPlane`). The Bott–Samelson variety of
the word `121` in the flag variety of `ℂ³` is the incidence variety

`X = {(L₁, P, L) | L₁ ⊆ P₀, L₁ ⊆ P, L ⊆ P}`

of lines `L₁, L` and planes `P` of `ℂ³`, a smooth projective threefold. The torus `T = (S¹)³` acts
on `ℂ³` diagonally, preserves `P₀`, and so acts on `X`. Identifying lines and planes with their
orthogonal projectors `Π_V`, that is with coadjoint orbits of `U(3)`, the moment map of this action
for the weights `a, b, c` of the Kirillov–Kostant–Souriau forms of the three factors is the diagonal
of the Hermitian matrix `a Π_{L₁} + b Π_P + c Π_L`:

`μ(L₁, P, L) = a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)`

(`TauCeti.BottSamelson.moment`, built on `Submodule.projectorDiagonal`). This file works with this
map on triples of subspaces directly; no symplectic form enters the statements.

The torus-fixed points of `X` are triples of coordinate subspaces. Writing `ij` for the plane
`span(eᵢ, eⱼ)` and `eᵢ` for the line it spans, eight such triples satisfy the incidence conditions,
and their moment values are the rows of `TauCeti.BottSamelson.fixedMoment`
(`TauCeti.BottSamelson.exists_moment_eq_fixedMoment`), in the order

`(e₀, 01, e₀)`, `(e₀, 01, e₁)`, `(e₀, 02, e₀)`, `(e₀, 02, e₂)`,
`(e₁, 01, e₀)`, `(e₁, 01, e₁)`, `(e₁, 12, e₁)`, `(e₁, 12, e₂)`.

For nonnegative weights `a, b, c`, every value of `μ` lies in the hexagon
`TauCeti.BottSamelson.momentPolygon`, the convex hull of these eight values
(`TauCeti.BottSamelson.moment_mem_convexHull`). The diagonal entries of a
projector lie in `[0, 1]` and sum to its rank, which gives the trace and the first five bounds, and
the third diagonal entry of `Π_{L₁}` vanishes because `L₁ ⊆ P₀`, which gives `z ≤ b + c`. This is
one inclusion of the description of the image of `μ` as the hexagon; the other one, that every
point of the hexagon is a moment value, is the content of the convexity theorem for torus actions.

## Main definitions

* `TauCeti.BottSamelson.initialPlane`: the coordinate plane `P₀ = span(e₀, e₁)`.
* `TauCeti.BottSamelson.moment`: the weighted diagonal `a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)`.

## Main results

* `TauCeti.BottSamelson.exists_moment_eq_fixedMoment`: each row of `fixedMoment` is the moment
  value of a triple of coordinate subspaces in `X`.
* `TauCeti.BottSamelson.sum_moment`: on `X`, the coordinates of `μ` sum to `a + 2b + c`.
* `TauCeti.BottSamelson.moment_mem_momentPolygon`,
  `TauCeti.BottSamelson.moment_mem_convexHull`: for nonnegative weights, every moment value lies
  in the hexagon, the convex hull of the eight fixed values.

## References

* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electron. J. Combin. 23
  (2016), §3.2 and §4.1 (Bott–Samelson varieties inside products of Grassmannians).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15;
  V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513 (the convexity theorem).
-/

public section

noncomputable section

namespace TauCeti.BottSamelson

open Module Set Submodule

/-! ### The weighted moment map -/

/-- The coordinate plane `P₀ = span(e₀, e₁)` of `ℂ³` containing the first line of a point of the
Bott–Samelson variety of the word `121`. -/
def initialPlane : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) :=
  span ℂ {EuclideanSpace.single 0 1, EuclideanSpace.single 1 1}

/-- The plane `P₀` is the coordinate subspace of the coordinates `0` and `1`. -/
theorem initialPlane_eq_span_image :
    initialPlane =
      span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' ({0, 1} : Set (Fin 3))) := by
  rw [initialPlane, image_pair]

/-- The diagonal of the projector onto `P₀` is `(1, 1, 0)`. -/
@[simp]
theorem projectorDiagonal_initialPlane : initialPlane.projectorDiagonal = ![1, 1, 0] := by
  rw [initialPlane_eq_span_image, projectorDiagonal_span_single]
  ext i
  fin_cases i <;> simp

@[simp]
theorem finrank_initialPlane : finrank ℂ initialPlane = 2 := by
  rw [initialPlane_eq_span_image, ← Finset.coe_pair, finrank_span_image_single]
  rfl

/-- The weighted moment map `μ(L₁, P, L) = a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)` of the
diagonal torus on triples of subspaces of `ℂ³`, the diagonal of the Hermitian matrix
`a Π_{L₁} + b Π_P + c Π_L`. -/
def moment (a b c : ℝ) (L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) : Fin 3 → ℝ :=
  a • L₁.projectorDiagonal + b • P.projectorDiagonal + c • L.projectorDiagonal

section Moment

variable (a b c : ℝ) (L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))

@[simp]
theorem moment_apply (i : Fin 3) :
    moment a b c L₁ P L i =
      a * L₁.projectorDiagonal i + b * P.projectorDiagonal i + c * L.projectorDiagonal i := (rfl)

/-- The moment map is additive in the weights. -/
theorem moment_add (a' b' c' : ℝ) :
    moment (a + a') (b + b') (c + c') L₁ P L = moment a b c L₁ P L + moment a' b' c' L₁ P L := by
  ext i
  simp only [moment_apply, Pi.add_apply]
  ring

/-- The moment map is homogeneous in the weights. -/
theorem moment_mul (r : ℝ) : moment (r * a) (r * b) (r * c) L₁ P L = r • moment a b c L₁ P L := by
  ext i
  simp only [moment_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable {L₁ P L}

/-- On triples of a line, a plane and a line, the coordinates of the moment map sum to
`a + 2b + c`, the trace of `a Π_{L₁} + b Π_P + c Π_L`. -/
theorem sum_moment (hL₁ : finrank ℂ L₁ = 1) (hP : finrank ℂ P = 2) (hL : finrank ℂ L = 1) :
    ∑ i, moment a b c L₁ P L i = a + 2 * b + c := by
  simp only [moment_apply, Finset.sum_add_distrib, ← Finset.mul_sum, sum_projectorDiagonal, hL₁,
    hP, hL]
  ring

end Moment

/-! ### Moment values -/

/-- Each fixed value is the moment value of a triple of coordinate subspaces in the Bott–Samelson
variety of the word `121`: a line `L₁ ⊆ P₀`, a plane `P ⊇ L₁` and a line `L ⊆ P`. -/
theorem exists_moment_eq_fixedMoment (a b c : ℝ) (k : Fin 8) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
        moment a b c L₁ P L = fixedMoment a b c k := by
  -- the coordinate subspace spanned by the `eᵢ` with `i ∈ s`
  let C : Finset (Fin 3) → Submodule ℂ (EuclideanSpace ℂ (Fin 3)) :=
    fun s ↦ span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' s)
  have hC : ∀ {s t : Finset (Fin 3)}, s ⊆ t → C s ≤ C t :=
    fun h ↦ span_mono (image_mono (Finset.coe_subset.2 h))
  have key : ∀ i j l : Fin 3, i ≠ j → i ∈ ({0, 1} : Finset (Fin 3)) → l ∈ ({i, j} : Finset _) →
      moment a b c (C {i}) (C {i, j}) (C {l}) = fixedMoment a b c k →
      ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
        finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
          moment a b c L₁ P L = fixedMoment a b c k := by
    intro i j l hij hi hl hμ
    refine ⟨C {i}, C {i, j}, C {l}, finrank_span_image_single _, ?_, finrank_span_image_single _,
      ?_, hC (by simp), hC (by simpa using hl), hμ⟩
    · rw [finrank_span_image_single, Finset.card_pair hij]
    · rw [initialPlane_eq_span_image, ← Finset.coe_pair]
      exact hC (by simpa using hi)
  have hμ : ∀ s t u : Finset (Fin 3), moment a b c (C s) (C t) (C u) =
      a • (s : Set (Fin 3)).indicator 1 + b • (t : Set (Fin 3)).indicator 1 +
        c • (u : Set (Fin 3)).indicator 1 := by
    intro s t u
    simp only [moment, C, projectorDiagonal_span_single]
  -- the indices `(i, j, l)` of the triple `(eᵢ, span(eᵢ, eⱼ), eₗ)` with moment value the row `k`
  let f : Fin 8 → Fin 3 × Fin 3 × Fin 3 := ![(0, 1, 0), (0, 1, 1), (0, 2, 0), (0, 2, 2),
    (1, 0, 0), (1, 0, 1), (1, 2, 1), (1, 2, 2)]
  refine key (f k).1 (f k).2.1 (f k).2.2 (by fin_cases k <;> decide)
    (by fin_cases k <;> decide) (by fin_cases k <;> decide) ?_
  rw [hμ]
  ext i
  fin_cases k <;> fin_cases i <;> simp [f, fixedMoment_def]

/-- Every moment value of the Bott–Samelson variety of the word `121` lies in the hexagon, for
nonnegative weights. The incidences `L₁ ⊆ P` and `L ⊆ P` are not needed. -/
theorem moment_mem_momentPolygon {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))} (hL₁ : finrank ℂ L₁ = 1)
    (hP : finrank ℂ P = 2) (hL : finrank ℂ L = 1) (h : L₁ ≤ initialPlane) :
    moment a b c L₁ P L ∈ momentPolygon a b c := by
  -- the third basis vector is orthogonal to `P₀`, hence to `L₁`
  have h₂ : L₁.projectorDiagonal 2 = 0 := by
    refine (projectorDiagonal_eq_zero_iff _).2 (orthogonal_le h ?_)
    rw [← projectorDiagonal_eq_zero_iff, projectorDiagonal_initialPlane]
    simp
  have hsum := sum_moment a b c hL₁ hP hL
  rw [Fin.sum_univ_three] at hsum
  have h0 := fun i ↦ L₁.projectorDiagonal_nonneg i
  have h1 := fun i ↦ P.projectorDiagonal_nonneg i
  have h2 := fun i ↦ L.projectorDiagonal_nonneg i
  have h3 := fun i ↦ L₁.projectorDiagonal_le_one i
  have h4 := fun i ↦ P.projectorDiagonal_le_one i
  have h5 := fun i ↦ L.projectorDiagonal_le_one i
  have hnn (i : Fin 3) : 0 ≤ moment a b c L₁ P L i := by
    simp only [moment_apply]
    have := h0 i; have := h1 i; have := h2 i; positivity
  refine mem_momentPolygon.2 ⟨hsum, hnn 0, hnn 1, hnn 2, ?_, ?_, ?_⟩ <;> simp only [moment_apply]
  · nlinarith [mul_le_mul_of_nonneg_left (h3 0) ha, mul_le_mul_of_nonneg_left (h4 0) hb,
      mul_le_mul_of_nonneg_left (h5 0) hc]
  · nlinarith [mul_le_mul_of_nonneg_left (h3 1) ha, mul_le_mul_of_nonneg_left (h4 1) hb,
      mul_le_mul_of_nonneg_left (h5 1) hc]
  · rw [h₂, mul_zero, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left (h4 2) hb, mul_le_mul_of_nonneg_left (h5 2) hc]

/-- For nonnegative weights, every moment value of the Bott–Samelson variety of the word `121`
lies in the convex hull of the moment values of its eight torus-fixed points. -/
theorem moment_mem_convexHull {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))} (hL₁ : finrank ℂ L₁ = 1)
    (hP : finrank ℂ P = 2) (hL : finrank ℂ L = 1) (h : L₁ ≤ initialPlane) :
    moment a b c L₁ P L ∈ convexHull ℝ (range (fixedMoment a b c)) := by
  rw [convexHull_range_fixedMoment ha hb hc]
  exact moment_mem_momentPolygon ha hb hc hL₁ hP hL h

end TauCeti.BottSamelson
