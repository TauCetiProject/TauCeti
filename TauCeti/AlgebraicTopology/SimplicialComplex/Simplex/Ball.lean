/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.Analysis.Convex.CoordinateSimplex

/-!
# A simplex and its boundary as a ball and its sphere

The weak realization of the standard `n`-simplex is homeomorphic to the Euclidean closed
`n`-ball. The same homeomorphism takes exactly the proper faces to the unit sphere, so it
identifies the pair consisting of a simplex and its boundary with the ball and sphere pair.
This supplies compatible geometric models for combinatorial balls and their boundaries.
Dimension zero is included: the simplex and ball are singletons and their boundaries empty.

Dropping the last barycentric coordinate gives an explicit homeomorphism to the coordinate
simplex. The omitted coordinate is one minus the sum of the others. The subsequent ball
identification uses Mathlib's convex-body gauge rescaling through
`TauCeti.exists_homeomorph_coordinateSimplex`. The first comparison reuses
`realizationTopHomeomorphStdSimplex` and Mathlib's `Convexity.StdSimplex`.

Reference: C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 2 (simplices and polyhedra).
-/

public section

noncomputable section

open Set Metric TauCeti

namespace AbstractSimplicialComplex

private def topToCoordinateSimplex (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    coordinateSimplex (Fin n) := by
  let y : Fin n → ℝ := fun i => x.1 i.castSucc
  have hsum : (∑ i, y i) + x.1 (Fin.last n) = 1 := by
    have h := Realization.sum_eq_one _ x
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
    exact h
  refine ⟨y, (mem_coordinateSimplex _ _).mpr ⟨fun i => Realization.nonneg _ x i.castSucc, ?_⟩⟩
  have := Realization.nonneg _ x (Fin.last n)
  linarith

private theorem topToCoordinateSimplex_apply (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) (i : Fin n) :
    (topToCoordinateSimplex n x).1 i = x.1 i.castSucc := (rfl)

private def coordinateSimplexToTop (n : ℕ) (y : coordinateSimplex (Fin n)) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) := by
  have hy := (mem_coordinateSimplex _ _).mp y.2
  let z : Fin (n + 1) →₀ ℝ := Finsupp.equivFunOnFinite.symm
    (Fin.snoc y.1 (1 - ∑ i, y.1 i))
  refine (realizationTopHomeomorphStdSimplex (ι := Fin (n + 1))).symm ⟨z, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [z] using sub_nonneg.mpr hy.2
    · simpa [z] using hy.1 j
  · simp [z, Finsupp.sum_fintype, Fin.sum_univ_castSucc]

private theorem coordinateSimplexToTop_castSucc (n : ℕ) (y : coordinateSimplex (Fin n))
    (i : Fin n) : (coordinateSimplexToTop n y).1 i.castSucc = y.1 i := by
  simp [coordinateSimplexToTop, realizationTopHomeomorphStdSimplex_symm_apply_val]

private theorem coordinateSimplexToTop_last (n : ℕ) (y : coordinateSimplex (Fin n)) :
    (coordinateSimplexToTop n y).1 (Fin.last n) = 1 - ∑ i, y.1 i := by
  simp [coordinateSimplexToTop, realizationTopHomeomorphStdSimplex_symm_apply_val]

/-- Dropping the last barycentric coordinate identifies the weak realization of a standard
`n`-simplex with the full-dimensional coordinate simplex. -/
def realizationTopHomeomorphCoordinateSimplex (n : ℕ) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃ₜ coordinateSimplex (Fin n) := by
  let e : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃
      coordinateSimplex (Fin n) := {
    toFun := topToCoordinateSimplex n
    invFun := coordinateSimplexToTop n
    left_inv x := by
      apply Subtype.ext
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [coordinateSimplexToTop_last]
        have h := Realization.sum_eq_one _ x
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
        simp only [topToCoordinateSimplex_apply]
        linarith
      · simp only [coordinateSimplexToTop_castSucc, topToCoordinateSimplex_apply]
    right_inv y := by
      apply Subtype.ext
      funext i
      simp only [topToCoordinateSimplex_apply, coordinateSimplexToTop_castSucc] }
  have hc : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (continuous_apply i.castSucc).comp (continuous_realization_coe _)
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

/-- The coordinate-simplex comparison reads the first barycentric coordinates. -/
@[simp]
theorem realizationTopHomeomorphCoordinateSimplex_apply (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) (i : Fin n) :
    (realizationTopHomeomorphCoordinateSimplex n x).1 i = x.1 i.castSucc := (rfl)

/-- The inverse comparison restores the last coordinate as the missing mass. -/
@[simp]
theorem realizationTopHomeomorphCoordinateSimplex_symm_last (n : ℕ)
    (y : coordinateSimplex (Fin n)) :
    ((realizationTopHomeomorphCoordinateSimplex n).symm y).1 (Fin.last n) =
      1 - ∑ i, y.1 i :=
  coordinateSimplexToTop_last n y

/-- The inverse comparison preserves the retained coordinates. -/
@[simp]
theorem realizationTopHomeomorphCoordinateSimplex_symm_castSucc (n : ℕ)
    (y : coordinateSimplex (Fin n)) (i : Fin n) :
    ((realizationTopHomeomorphCoordinateSimplex n).symm y).1 i.castSucc = y.1 i :=
  coordinateSimplexToTop_castSucc n y i

/-- A simplex point maps to the geometric frontier exactly when its support is a proper
face. This includes the empty boundary of the zero-simplex. -/
@[simp 1100]
theorem realizationTopHomeomorphCoordinateSimplex_mem_frontier_iff (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    (realizationTopHomeomorphCoordinateSimplex n x).1 ∈ frontier (coordinateSimplex (Fin n)) ↔
      x.1.support ≠ Finset.univ := by
  rw [mem_frontier_coordinateSimplex]
  rw [iff_true_intro ((mem_coordinateSimplex _ _).mp
    (realizationTopHomeomorphCoordinateSimplex n x).2), true_and]
  simp only [realizationTopHomeomorphCoordinateSimplex_apply]
  have hsum : (∑ i : Fin n, x.1 i.castSucc) + x.1 (Fin.last n) = 1 := by
    have h := Realization.sum_eq_one _ x
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
  have hmissing : x.1.support ≠ Finset.univ ↔ ∃ i, x.1 i = 0 := by
    simp [Finset.eq_univ_iff_forall, Finsupp.mem_support_iff]
  rw [hmissing]
  constructor
  · rintro (⟨i, hi⟩ | hs)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, by linarith⟩
  · rintro ⟨i, hi⟩
    refine Fin.lastCases ?_ (fun j hj => Or.inl ⟨j, hj⟩) i hi
    intro hl
    exact Or.inr (by linarith)

/-- The weak realization of the standard `n`-simplex is homeomorphic to the Euclidean unit
closed `n`-ball. Its proper-face boundary is taken to the sphere. -/
def realizationTopHomeomorphClosedBall (n : ℕ) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  let h := Classical.choose (exists_homeomorph_coordinateSimplex (Fin n))
  (realizationTopHomeomorphCoordinateSimplex n).trans
    ((h.image (coordinateSimplex (Fin n))).trans
      (Homeomorph.setCongr (Classical.choose_spec
        (exists_homeomorph_coordinateSimplex (Fin n))).1))

/-- Under the simplex-to-ball homeomorphism, exactly the proper faces land on the sphere. -/
@[simp]
theorem realizationTopHomeomorphClosedBall_norm_eq_one_iff (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    ‖(realizationTopHomeomorphClosedBall n x).1‖ = 1 ↔
      x.1.support ≠ Finset.univ := by
  rw [← mem_sphere_zero_iff_norm]
  let h := Classical.choose (exists_homeomorph_coordinateSimplex (Fin n))
  have hfr : h '' frontier (coordinateSimplex (Fin n)) =
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    (Classical.choose_spec (exists_homeomorph_coordinateSimplex (Fin n))).2.2
  have he : (realizationTopHomeomorphClosedBall n x).1 =
      h (realizationTopHomeomorphCoordinateSimplex n x).1 := (rfl)
  rw [he, ← hfr]
  simpa only [h.injective.mem_set_image] using
    realizationTopHomeomorphCoordinateSimplex_mem_frontier_iff n x

end AbstractSimplicialComplex
