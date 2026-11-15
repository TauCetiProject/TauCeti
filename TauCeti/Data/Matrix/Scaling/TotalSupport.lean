/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling.Support
public import TauCeti.Data.Matrix.TotalSupport

/-!
# Total support and doubly stochastic scaling

A nonnegative square matrix of positive order admits a doubly stochastic diagonal scaling
by strictly positive factors exactly when it has total support. This is the square,
unit-marginal specialization of the support-feasibility criterion
`Matrix.exists_sinkhorn_scaling_iff`: the same-support doubly stochastic realization is
supplied by `Matrix.hasTotalSupport_iff_exists_mem_doublyStochastic`.

The theorem allows support zeros. It concerns existence of a scaling, rather than
convergence of alternating normalization when only a positive diagonal is available.

## References

* R. Sinkhorn and P. Knopp, *Concerning nonnegative matrices and doubly stochastic matrices*,
  Pacific J. Math. 21 (1967), 343–348, theorem on p. 344.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  {K : Matrix n n ℝ}

/-- **The total-support criterion for doubly stochastic scaling.** A nonnegative square
matrix of positive order admits a diagonal scaling by strictly positive row and column
factors to a doubly stochastic matrix if and only if it has total support. -/
theorem exists_doublyStochastic_diagonalScaling_iff (hK : ∀ i j, 0 ≤ K i j) :
    (∃ (u v : n → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (Matrix.of fun i j ↦ u i * K i j * v j) ∈ doublyStochastic ℝ n) ↔ HasTotalSupport K := by
  have hscale := exists_sinkhorn_scaling_iff hK (a := fun _ ↦ 1) (b := fun _ ↦ 1)
  simp only [mem_doublyStochastic_iff_sum, of_apply]
  constructor
  · rintro ⟨u, v, hu, hv, -, hrow, hcol⟩
    obtain ⟨P, hP, hPK, hPm⟩ := hscale.1 ⟨u, v, hu, hv, hrow, hcol⟩
    exact hasTotalSupport_iff_exists_mem_doublyStochastic.2
      ⟨P, mem_doublyStochastic_iff_sum.2 ⟨hP, (hasMarginals_def _ _ _).1 hPm⟩, hPK⟩
  · intro htotal
    obtain ⟨P, hP, hPK⟩ := htotal.exists_mem_doublyStochastic (R := ℝ)
    obtain ⟨hP0, hrow, hcol⟩ := mem_doublyStochastic_iff_sum.1 hP
    obtain ⟨u, v, hu, hv, hrow', hcol'⟩ :=
      hscale.2 ⟨P, hP0, hPK, (hasMarginals_def _ _ _).2 ⟨hrow, hcol⟩⟩
    exact ⟨u, v, hu, hv, fun i j ↦ mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le,
      hrow', hcol'⟩

end Matrix
