/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Combinatorics.SimpleGraph.StronglyRegular.Basic

import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# The spectrum of a strongly regular graph

A strongly regular graph with parameters `(n, k, ℓ, μ)` has adjacency matrix `A` with
`A² = (ℓ - μ) A + (k - μ) I + μ J`, where `J` is the all-ones matrix. Writing `r` and `s` for the
two roots of `x² - (ℓ - μ) x - (k - μ)`, this says `(A - r I)(A - s I) = μ J`, and since `A` is
regular of degree `k`, `(A - k I)(A - r I)(A - s I) = 0`. So every eigenvalue of `A` is `k`, `r`
or `s`. For a graph that is neither complete nor edgeless all three occur: if `r` (say) were not
an eigenvalue, then `(A - k I)(A - s I) = 0`, whose entries at a nonadjacent pair and at an
adjacent pair force `μ = 0` and then `r = k`.

The roots are defined from the parameters alone, with the discriminant
`srgDiscriminant k ℓ μ = (ℓ - μ)² + 4 (k - μ)` and `Real.sqrt` (which is `0` at negative
arguments), as `srgEigenvalueR k ℓ μ = ((ℓ - μ) + √Δ) / 2` and
`srgEigenvalueS k ℓ μ = ((ℓ - μ) - √Δ) / 2`. The multiplicities of the eigenvalues and the
feasibility conditions on the parameters are read off from this spectrum.

## Main definitions

* `TauCeti.srgDiscriminant k ℓ μ`: the discriminant `(ℓ - μ)² + 4 (k - μ)`.
* `TauCeti.srgEigenvalueR k ℓ μ`, `TauCeti.srgEigenvalueS k ℓ μ`: the larger and the
  smaller root of `x² - (ℓ - μ) x - (k - μ)`.

## Main results

* `TauCeti.sq_eq_iff_eq_srgEigenvalueR_or_eq_srgEigenvalueS`: for a nonnegative
  discriminant, `r` and `s` are exactly the roots of `x² - (ℓ - μ) x - (k - μ)`.
* `SimpleGraph.IsSRGWith.adjMatrix_sub_srgEigenvalueR_mul_sub_srgEigenvalueS`:
  `(A - r I)(A - s I) = μ J`.
* `SimpleGraph.IsSRGWith.adjMatrix_sub_mul_sub_mul_sub_eq_zero`: `(A - k I)(A - r I)(A - s I) = 0`.
* `SimpleGraph.IsSRGWith.spectrum_adjMatrix`: a strongly regular graph that is neither complete
  nor edgeless has spectrum exactly `{k, r, s}`.
* `SimpleGraph.IsSRGWith.srgEigenvalueS_lt_srgEigenvalueR`,
  `SimpleGraph.IsSRGWith.srgEigenvalueR_lt`: `s < r`, and `r < k` when `0 < μ`, so these three
  eigenvalues are distinct.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012,
  Theorem 9.1.2 and Theorem 9.1.3 (ii), pp. 115–116 of the authors' version.
-/

public section

open Matrix Polynomial

namespace TauCeti

/-! ### The two restricted eigenvalues -/

/-- The discriminant `(ℓ - μ)² + 4 (k - μ)` of the quadratic `x² - (ℓ - μ) x - (k - μ)`, whose
roots are the eigenvalues other than the degree of a strongly regular graph with parameters
`(n, k, ℓ, μ)`. -/
noncomputable def srgDiscriminant (k ℓ μ : ℕ) : ℝ :=
  ((ℓ : ℝ) - μ) ^ 2 + 4 * ((k : ℝ) - μ)

/-- The larger root `r = ((ℓ - μ) + √Δ) / 2` of `x² - (ℓ - μ) x - (k - μ)`, where `Δ` is
`srgDiscriminant k ℓ μ`. It is defined for all parameters, using `Real.sqrt`. -/
noncomputable def srgEigenvalueR (k ℓ μ : ℕ) : ℝ :=
  ((ℓ : ℝ) - μ + √(srgDiscriminant k ℓ μ)) / 2

/-- The smaller root `s = ((ℓ - μ) - √Δ) / 2` of `x² - (ℓ - μ) x - (k - μ)`, where `Δ` is
`srgDiscriminant k ℓ μ`. It is defined for all parameters, using `Real.sqrt`. -/
noncomputable def srgEigenvalueS (k ℓ μ : ℕ) : ℝ :=
  ((ℓ : ℝ) - μ - √(srgDiscriminant k ℓ μ)) / 2

variable {k ℓ μ : ℕ}

/-- The defining formula of `srgDiscriminant`. -/
theorem srgDiscriminant_def :
    srgDiscriminant k ℓ μ = ((ℓ : ℝ) - μ) ^ 2 + 4 * ((k : ℝ) - μ) := (rfl)

/-- The defining formula of `srgEigenvalueR`. -/
theorem srgEigenvalueR_def :
    srgEigenvalueR k ℓ μ = ((ℓ : ℝ) - μ + √(srgDiscriminant k ℓ μ)) / 2 := (rfl)

/-- The defining formula of `srgEigenvalueS`. -/
theorem srgEigenvalueS_def :
    srgEigenvalueS k ℓ μ = ((ℓ : ℝ) - μ - √(srgDiscriminant k ℓ μ)) / 2 := (rfl)

/-- The discriminant is nonnegative when `μ ≤ k`. -/
theorem srgDiscriminant_nonneg (hμk : μ ≤ k) : 0 ≤ srgDiscriminant k ℓ μ := by
  have : (μ : ℝ) ≤ k := by exact_mod_cast hμk
  rw [srgDiscriminant_def]
  nlinarith [sq_nonneg ((ℓ : ℝ) - μ)]

/-- The discriminant is positive when `μ ≤ k` and `ℓ < k`. -/
theorem srgDiscriminant_pos (hμk : μ ≤ k) (hℓk : ℓ < k) : 0 < srgDiscriminant k ℓ μ := by
  rw [srgDiscriminant_def]
  rcases hμk.lt_or_eq with hμk | rfl
  · have : (μ : ℝ) < k := by exact_mod_cast hμk
    nlinarith [sq_nonneg ((ℓ : ℝ) - μ)]
  · have : (ℓ : ℝ) < μ := by exact_mod_cast hℓk
    nlinarith

/-- The sum of the two roots is `ℓ - μ`. -/
theorem srgEigenvalueR_add_srgEigenvalueS :
    srgEigenvalueR k ℓ μ + srgEigenvalueS k ℓ μ = (ℓ : ℝ) - μ := by
  rw [srgEigenvalueR_def, srgEigenvalueS_def]
  ring

/-- The difference of the two roots is the square root of the discriminant. -/
theorem srgEigenvalueR_sub_srgEigenvalueS :
    srgEigenvalueR k ℓ μ - srgEigenvalueS k ℓ μ = √(srgDiscriminant k ℓ μ) := by
  rw [srgEigenvalueR_def, srgEigenvalueS_def]
  ring

/-- For a nonnegative discriminant, the product of the two roots is `μ - k`. -/
theorem srgEigenvalueR_mul_srgEigenvalueS (hΔ : 0 ≤ srgDiscriminant k ℓ μ) :
    srgEigenvalueR k ℓ μ * srgEigenvalueS k ℓ μ = (μ : ℝ) - k := by
  have hsq := Real.sq_sqrt hΔ
  rw [srgDiscriminant_def] at hsq
  rw [srgEigenvalueR_def, srgEigenvalueS_def, srgDiscriminant_def]
  linear_combination (-1 / 4 : ℝ) * hsq

/-- For a nonnegative discriminant, `srgEigenvalueR k ℓ μ` and `srgEigenvalueS k ℓ μ` are exactly
the roots of `x² - (ℓ - μ) x - (k - μ)`. -/
theorem sq_eq_iff_eq_srgEigenvalueR_or_eq_srgEigenvalueS (hΔ : 0 ≤ srgDiscriminant k ℓ μ)
    {x : ℝ} : x ^ 2 = ((ℓ : ℝ) - μ) * x + ((k : ℝ) - μ) ↔
      x = srgEigenvalueR k ℓ μ ∨ x = srgEigenvalueS k ℓ μ := by
  have h₁ := srgEigenvalueR_add_srgEigenvalueS (k := k) (ℓ := ℓ) (μ := μ)
  have h₂ := srgEigenvalueR_mul_srgEigenvalueS hΔ
  have hfac : x ^ 2 - (((ℓ : ℝ) - μ) * x + ((k : ℝ) - μ)) =
      (x - srgEigenvalueR k ℓ μ) * (x - srgEigenvalueS k ℓ μ) := by
    linear_combination x * h₁ - h₂
  rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The smaller root is less than the larger one when `μ ≤ k` and `ℓ < k`. -/
theorem srgEigenvalueS_lt_srgEigenvalueR (hμk : μ ≤ k) (hℓk : ℓ < k) :
    srgEigenvalueS k ℓ μ < srgEigenvalueR k ℓ μ := by
  have := Real.sqrt_pos.2 (srgDiscriminant_pos hμk hℓk)
  rw [srgEigenvalueR_def, srgEigenvalueS_def]
  linarith

end TauCeti

namespace SimpleGraph

open TauCeti

/-! ### The spectrum -/

variable {k ℓ μ : ℕ} {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

/-- A strongly regular graph with `0 < μ` that is not complete has an edge. -/
theorem IsSRGWith.ne_bot (h : G.IsSRGWith n k ℓ μ) (hμ : 0 < μ) (htop : G ≠ ⊤) : G ≠ ⊥ := by
  obtain ⟨v, w, hne, hvw⟩ := ne_top_iff_exists_not_adj.1 htop
  obtain ⟨⟨u, hu⟩⟩ : Nonempty (G.commonNeighbors v w) := by
    rw [← Fintype.card_pos_iff, h.of_not_adj hne hvw]
    exact hμ
  exact ne_bot_iff_exists_adj.2 ⟨v, u, ((G.mem_commonNeighbors).1 hu).1⟩

/-- In a strongly regular graph that is neither complete nor edgeless, the smaller restricted
eigenvalue `s` is less than the larger one `r`. -/
theorem IsSRGWith.srgEigenvalueS_lt_srgEigenvalueR (h : G.IsSRGWith n k ℓ μ) (htop : G ≠ ⊤)
    (hbot : G ≠ ⊥) : srgEigenvalueS k ℓ μ < srgEigenvalueR k ℓ μ :=
  TauCeti.srgEigenvalueS_lt_srgEigenvalueR (h.le_of_ne_top htop) (h.lt_of_ne_bot hbot)

/-- In a strongly regular graph with an edge and `0 < μ`, the larger restricted eigenvalue `r` is
less than the degree `k`. -/
theorem IsSRGWith.srgEigenvalueR_lt (h : G.IsSRGWith n k ℓ μ) (hμ : 0 < μ) (hbot : G ≠ ⊥) :
    srgEigenvalueR k ℓ μ < k := by
  obtain ⟨v, -, -⟩ := ne_bot_iff_exists_adj.1 hbot
  have hn : 0 < n := h.card ▸ Fintype.card_pos_iff.2 ⟨v⟩
  have hp := h.param_eq_cast (R := ℝ) hn
  have hℓk : (ℓ : ℝ) + 1 ≤ k := by exact_mod_cast h.lt_of_ne_bot hbot
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- `x² - (ℓ - μ) x - (k - μ)` is `μ n > 0` at `x = k`, which lies right of the vertex.
  have hsqrt : √(srgDiscriminant k ℓ μ) < 2 * k - ((ℓ : ℝ) - μ) := by
    rw [Real.sqrt_lt' (by linarith), srgDiscriminant_def]
    nlinarith [mul_pos hμ' hn']
  rw [srgEigenvalueR_def]
  linarith

variable [DecidableEq V]

/-- **The factored strongly regular equation.** If `G` is strongly regular with parameters
`(n, k, ℓ, μ)` and the discriminant is nonnegative, then `(A - r I)(A - s I) = μ J`, where `A` is
the real adjacency matrix and `J` the all-ones matrix. -/
theorem IsSRGWith.adjMatrix_sub_srgEigenvalueR_mul_sub_srgEigenvalueS (h : G.IsSRGWith n k ℓ μ)
    (hΔ : 0 ≤ srgDiscriminant k ℓ μ) :
    (G.adjMatrix ℝ - srgEigenvalueR k ℓ μ • 1) * (G.adjMatrix ℝ - srgEigenvalueS k ℓ μ • 1) =
      (μ : ℝ) • Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  have hsq := (isSRGWith_iff_adjMatrix_sq_eq (R := ℝ)).1 h |>.2
  have hs : srgEigenvalueS k ℓ μ = (ℓ : ℝ) - μ - srgEigenvalueR k ℓ μ := by
    linarith [srgEigenvalueR_add_srgEigenvalueS (k := k) (ℓ := ℓ) (μ := μ)]
  have hrs : srgEigenvalueR k ℓ μ * ((ℓ : ℝ) - μ - srgEigenvalueR k ℓ μ) = (μ : ℝ) - k :=
    hs ▸ srgEigenvalueR_mul_srgEigenvalueS hΔ
  rw [sq] at hsq
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hsq, hs]
  linear_combination (norm := module) hrs • (1 : Matrix V V ℝ)

/-- If `G` is strongly regular with parameters `(n, k, ℓ, μ)` and the discriminant is nonnegative,
then `(A - k I)(A - r I)(A - s I) = 0`, where `A` is the real adjacency matrix. -/
theorem IsSRGWith.adjMatrix_sub_mul_sub_mul_sub_eq_zero (h : G.IsSRGWith n k ℓ μ)
    (hΔ : 0 ≤ srgDiscriminant k ℓ μ) :
    (G.adjMatrix ℝ - (k : ℝ) • 1) *
      ((G.adjMatrix ℝ - srgEigenvalueR k ℓ μ • 1) * (G.adjMatrix ℝ - srgEigenvalueS k ℓ μ • 1)) =
      0 := by
  rw [h.adjMatrix_sub_srgEigenvalueR_mul_sub_srgEigenvalueS hΔ, mul_smul_comm,
    h.regular.adjMatrix_sub_smul_one_mul_of_one, smul_zero]

/-- If `G` is regular of degree `k` and neither complete nor edgeless, and `c ≠ k` is such that
`(A - c I)(A - d I)` is a multiple of the all-ones matrix `J`, then `c` is an eigenvalue of `A`. -/
private theorem mem_spectrum_adjMatrix_of_mul_eq_smul (hreg : G.IsRegularOfDegree k)
    (htop : G ≠ ⊤) (hbot : G ≠ ⊥) {c d m : ℝ} (hck : c ≠ k)
    (hcd : (G.adjMatrix ℝ - c • 1) * (G.adjMatrix ℝ - d • 1) = m • Matrix.of (fun _ _ ↦ 1)) :
    c ∈ spectrum ℝ (G.adjMatrix ℝ) := by
  set A := G.adjMatrix ℝ
  set J : Matrix V V ℝ := Matrix.of fun _ _ ↦ 1
  -- Otherwise `A - c I` is invertible and kills `(A - k I)(A - d I)`, whose entries at a
  -- nonadjacent pair and at an adjacent pair cannot both vanish.
  by_contra hc
  have hu : IsUnit (A - c • 1) := by
    rw [← IsUnit.neg_iff, neg_sub, ← Algebra.algebraMap_eq_smul_one]
    exact spectrum.notMem_iff.1 hc
  have hAJ : A * J = (k : ℝ) • J := hreg.adjMatrix_mul_of_one
  -- `(A - k I)(A - d I) = (c - k)(A - d I) + m J`, and `A - c I` kills it.
  have hQ : (A - (k : ℝ) • 1) * (A - d • 1) = (c - k) • (A - d • 1) + m • J := by
    rw [← hcd]
    simp only [sub_mul, smul_mul_assoc, one_mul]
    module
  have hkill : (A - c • 1) * ((A - (k : ℝ) • 1) * (A - d • 1)) = 0 := by
    simp only [hQ, mul_add, mul_smul_comm, hcd, sub_mul, smul_mul_assoc, one_mul, hAJ]
    module
  rw [hu.mul_right_eq_zero, hQ] at hkill
  obtain ⟨v, w, hne, hvw⟩ := ne_top_iff_exists_not_adj.1 htop
  obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.1 hbot
  have hm := congr_fun₂ hkill v w
  have hxy' := congr_fun₂ hkill x y
  simp [A, J, hne, hvw, hxy, hxy.ne] at hm hxy'
  exact hck (by linarith)

/-- **The spectrum of a strongly regular graph.** A strongly regular graph with parameters
`(n, k, ℓ, μ)` that is neither complete nor edgeless has exactly the eigenvalues `k`,
`r = srgEigenvalueR k ℓ μ` and `s = srgEigenvalueS k ℓ μ`. When moreover `0 < μ`, these three
eigenvalues are distinct: `s < r < k` (`IsSRGWith.srgEigenvalueS_lt_srgEigenvalueR`,
`IsSRGWith.srgEigenvalueR_lt`). -/
theorem IsSRGWith.spectrum_adjMatrix (h : G.IsSRGWith n k ℓ μ) (htop : G ≠ ⊤) (hbot : G ≠ ⊥) :
    spectrum ℝ (G.adjMatrix ℝ) = {(k : ℝ), srgEigenvalueR k ℓ μ, srgEigenvalueS k ℓ μ} := by
  obtain ⟨v, -, -⟩ := ne_bot_iff_exists_adj.1 hbot
  have : Nonempty V := ⟨v⟩
  have hΔ := srgDiscriminant_nonneg (ℓ := ℓ) (h.le_of_ne_top htop)
  have hk : (k : ℝ) ∈ spectrum ℝ (G.adjMatrix ℝ) := h.regular.mem_spectrum_adjMatrix (R := ℝ)
  have hrs := h.adjMatrix_sub_srgEigenvalueR_mul_sub_srgEigenvalueS hΔ
  -- `A - r I` and `A - s I` commute, so the factors may be taken in either order.
  have hsr : (G.adjMatrix ℝ - srgEigenvalueS k ℓ μ • 1) *
      (G.adjMatrix ℝ - srgEigenvalueR k ℓ μ • 1) = (μ : ℝ) • Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
    rw [← hrs]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul]
    module
  apply subset_antisymm
  · -- `(A - k I)(A - r I)(A - s I) = 0`, so every eigenvalue is a root of `(x - k)(x - r)(x - s)`.
    intro θ hθ
    let p : ℝ[X] :=
      (X - C (k : ℝ)) * ((X - C (srgEigenvalueR k ℓ μ)) * (X - C (srgEigenvalueS k ℓ μ)))
    have hp : aeval (G.adjMatrix ℝ) p = 0 := by
      simpa only [p, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] using
        h.adjMatrix_sub_mul_sub_mul_sub_eq_zero hΔ
    have := spectrum.subset_polynomial_aeval (G.adjMatrix ℝ) p ⟨θ, hθ, rfl⟩
    rw [hp, spectrum.zero_eq, Set.mem_singleton_iff] at this
    simp only [p, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at this
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  · rintro θ (rfl | rfl | rfl)
    · exact hk
    · by_cases hrk : srgEigenvalueR k ℓ μ = k
      · exact hrk ▸ hk
      · exact mem_spectrum_adjMatrix_of_mul_eq_smul h.regular htop hbot hrk hrs
    · by_cases hsk : srgEigenvalueS k ℓ μ = k
      · exact hsk ▸ hk
      · exact mem_spectrum_adjMatrix_of_mul_eq_smul h.regular htop hbot hsk hsr

end SimpleGraph
