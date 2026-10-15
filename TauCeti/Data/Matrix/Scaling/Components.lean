/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Data.Matrix.Scaling.Basic
public import TauCeti.Data.Matrix.SupportGraph

/-!
# The component ambiguity of matrix scaling factors

The nonzero entries of a rectangular matrix `K` define a bipartite graph on its rows and
columns, `Matrix.supportGraph`. A diagonal scaling of `K` is unchanged when the row factors
in each connected component are multiplied by a nonzero scalar and the column factors in
that component by its inverse. Conversely, these are all the ambiguities between two
nonzero factor pairs producing the same scaled matrix.

The criterion `Matrix.isDiagonalScaling_iff_exists_component_rescale_factors` allows zero
entries, zero rows and zero columns of `K`. An isolated vertex is a component of its own:
its factor is unrestricted by the scaled matrix. No finiteness or sign hypothesis on the
matrix is needed. For the positive factors used by Sinkhorn scaling,
`Matrix.isDiagonalScaling_iff_exists_pos_component_rescale_factors` gives positive component
scalars.

## References

* M. Idel, *A review of matrix scaling and Sinkhorn's normal form for matrices and positive
  maps*, arXiv:1609.06349 (2016), Theorem 4.3, for the blockwise scalar ambiguity of scaling
  factors. Here the blocks are expressed by connected components of the support graph,
  including isolated row and column vertices.
-/

public section

namespace Matrix

variable {ι κ : Type*}

/-- Rescaling the row factors by one nonzero scalar per support component, and the column
factors by the inverse scalar, preserves a diagonal scaling. -/
theorem IsDiagonalScaling.rescale_component_factors {P K : Matrix ι κ ℝ}
    {u : ι → ℝ} {v : κ → ℝ} (h : IsDiagonalScaling P K u v)
    (r : K.supportGraph.ConnectedComponent → ℝ) (hr : ∀ C, r C ≠ 0) :
    IsDiagonalScaling P K
      (fun i ↦ r (K.supportGraph.connectedComponentMk (.inl i)) * u i)
      (fun j ↦ (r (K.supportGraph.connectedComponentMk (.inr j)))⁻¹ * v j) := by
  rw [isDiagonalScaling_def] at h ⊢
  intro i j
  by_cases hij : K i j = 0
  · simp [h i j, hij]
  · have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      ((supportGraph_adj_inl_inr K i j).2 hij)
    rw [← heq]
    calc P i j = u i * K i j * v j := h i j
      _ = (u i * K i j * v j) *
          (r (K.supportGraph.connectedComponentMk (.inl i)) *
            (r (K.supportGraph.connectedComponentMk (.inl i)))⁻¹) := by
        rw [mul_inv_cancel₀ (hr _), mul_one]
      _ = _ := by ring

private theorem exists_component_factor {P K : Matrix ι κ ℝ}
    {u u' : ι → ℝ} {v v' : κ → ℝ} (h : IsDiagonalScaling P K u v)
    (h' : IsDiagonalScaling P K u' v') (hu' : ∀ i, u' i ≠ 0) (hv : ∀ j, v j ≠ 0) :
    ∃ r : K.supportGraph.ConnectedComponent → ℝ,
      (∀ s, r (K.supportGraph.connectedComponentMk s) =
        Sum.elim (fun i ↦ u i / u' i) (fun j ↦ v' j / v j) s) := by
  let f : ι ⊕ κ → ℝ := Sum.elim (fun i ↦ u i / u' i) (fun j ↦ v' j / v j)
  rw [isDiagonalScaling_def] at h h'
  have hedge (i : ι) (j : κ) (hij : K i j ≠ 0) : f (.inl i) = f (.inr j) := by
    dsimp [f]
    apply (div_eq_div_iff (hu' i) (hv j)).2
    exact mul_right_cancel₀ hij (by linear_combination (h' i j) - (h i j))
  have hadj : ∀ a b, K.supportGraph.Adj a b → f a = f b := by
    rintro (i | j) (i' | j') hab
    · exact False.elim ((supportGraph_not_adj_inl_inl K i i') hab)
    · exact hedge i j' ((supportGraph_adj_inl_inr K i j').1 hab)
    · exact (hedge i' j ((supportGraph_adj_inr_inl K j i').1 hab)).symm
    · exact False.elim ((supportGraph_not_adj_inr_inr K j j') hab)
  have hwalk : ∀ a b (p : K.supportGraph.Walk a b), f a = f b := by
    intro a b p
    induction p with
    | nil => rfl
    | cons hab p ih => exact (hadj _ _ hab).trans ih
  exact ⟨SimpleGraph.ConnectedComponent.lift f (fun a b p _ ↦ hwalk a b p), fun _ ↦ rfl⟩

/-- Two nonzero factor pairs give the same diagonal scaling exactly when they differ by
one nonzero scalar per connected component of the support graph. All four nonvanishing
hypotheses include isolated vertices, whose factors are unconstrained by the matrix. -/
theorem isDiagonalScaling_iff_exists_component_rescale_factors {P K : Matrix ι κ ℝ}
    {u u' : ι → ℝ} {v v' : κ → ℝ} (h' : IsDiagonalScaling P K u' v')
    (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0) (hu' : ∀ i, u' i ≠ 0)
    (hv' : ∀ j, v' j ≠ 0) :
    IsDiagonalScaling P K u v ↔
      ∃ r : K.supportGraph.ConnectedComponent → ℝ, (∀ C, r C ≠ 0) ∧
        (∀ i, u i = r (K.supportGraph.connectedComponentMk (.inl i)) * u' i) ∧
        ∀ j, v j = (r (K.supportGraph.connectedComponentMk (.inr j)))⁻¹ * v' j := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := exists_component_factor h h' hu' hv
    refine ⟨r, ?_, fun i ↦ ?_, fun j ↦ ?_⟩
    · intro C
      induction C using SimpleGraph.ConnectedComponent.ind with
      | h s => cases s with
        | inl i => simpa [hr] using div_ne_zero (hu i) (hu' i)
        | inr j => simpa [hr] using div_ne_zero (hv' j) (hv j)
    · rw [hr]
      simp [hu' i]
    · rw [hr]
      simp [hv' j]
  · rintro ⟨r, hr, hrow, hcol⟩
    convert h'.rescale_component_factors r hr using 1 <;> funext s
    · exact hrow s
    · exact hcol s

/-- For positive factor pairs the support-component scalars in the ambiguity criterion
can be chosen positive. This is the form used by nonnegative-kernel Sinkhorn scaling. -/
theorem isDiagonalScaling_iff_exists_pos_component_rescale_factors {P K : Matrix ι κ ℝ}
    {u u' : ι → ℝ} {v v' : κ → ℝ} (h' : IsDiagonalScaling P K u' v')
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) (hu' : ∀ i, 0 < u' i)
    (hv' : ∀ j, 0 < v' j) :
    IsDiagonalScaling P K u v ↔
      ∃ r : K.supportGraph.ConnectedComponent → ℝ, (∀ C, 0 < r C) ∧
        (∀ i, u i = r (K.supportGraph.connectedComponentMk (.inl i)) * u' i) ∧
        ∀ j, v j = (r (K.supportGraph.connectedComponentMk (.inr j)))⁻¹ * v' j := by
  constructor
  · intro h
    obtain ⟨r, -, hrow, hcol⟩ :=
      (isDiagonalScaling_iff_exists_component_rescale_factors h' (fun i ↦ (hu i).ne')
        (fun j ↦ (hv j).ne') (fun i ↦ (hu' i).ne') (fun j ↦ (hv' j).ne')).1 h
    refine ⟨r, ?_, hrow, hcol⟩
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h s => cases s with
      | inl i => exact (mul_pos_iff_of_pos_right (hu' i)).1 ((hrow i) ▸ hu i)
      | inr j => exact inv_pos.1 ((mul_pos_iff_of_pos_right (hv' j)).1 ((hcol j) ▸ hv j))
  · rintro ⟨r, hr, hrow, hcol⟩
    exact (isDiagonalScaling_iff_exists_component_rescale_factors h' (fun i ↦ (hu i).ne')
      (fun j ↦ (hv j).ne') (fun i ↦ (hu' i).ne') (fun j ↦ (hv' j).ne')).2
        ⟨r, fun C ↦ (hr C).ne', hrow, hcol⟩

end Matrix
