/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.CWModel
import TauCeti.AlgebraicTopology.Cellular.Dimension
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Examples: CW homotopy models of smooth affine curves and sharpness of closedness

This file illustrates `TauCeti.Geometry.Manifold.Complex.CWModel` on concrete complex-geometric
examples and verifies that the closedness hypothesis in Milnor's Theorem 7.2 cannot be omitted:

* **The smooth affine hyperbola `{z ∈ ℂ² | z₀ z₁ - 1 = 0}`.** Its single defining polynomial
  `X₀ X₁ - 1` has partial derivative `∂(X₀ X₁ - 1)/∂X₀ = X₁`, which never vanishes on the hyperbola
  since `z₀ z₁ = 1`. Thus the Jacobian matrix is surjective at every point of the zero locus
  (`surjective_jacobiMatrixAt_affineHyperbolaPoly`), and
  `TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus` gives a finite-dimensional Hausdorff CW
  homotopy model of the hyperbola with no cells in dimensions strictly above `1`
  (`exists_cwComplex_homotopyEquiv_affineHyperbola`).
* **Closed holomorphic graphs in a non-Euclidean normed product.** Given any entire holomorphic
  function `g : (Fin 2 → ℂ) → ℂ`, the graph map `y ↦ ((y : Fin 2 → ℂ), g y)` from the affine
  hyperbola into `(Fin 2 → ℂ) × ℂ` is a smooth closed holomorphic immersion into a complex normed
  space carrying the `ℓ^∞` product norm (with no inner product structure), illustrating
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding` on a non-Euclidean ambient space
  (`exists_cwComplex_homotopyEquiv_affineHyperbola_graph`).
* **Closedness is essential in Milnor's Theorem 7.2.** The punctured space `ℂ² ∖ {0}` is an open
  `2`-dimensional complex submanifold of `ℂ²` along whose open holomorphic inclusion every squared
  distance `z ↦ ‖z - a‖²` is strictly plurisubharmonic
  (`TauCeti.Examples.Geometry.Manifold.Complex.PuncturedSpace`), yet `ℂ² ∖ {0} ≃ₕ S³` has
  `dim_ℚ H₃(ℂ² ∖ {0}; ℚ) = 1` and therefore admits **no** Hausdorff CW homotopy model with empty
  cell sets above dimension `2` (`not_exists_cwComplex_homotopyEquiv_le_two_compl_zero`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7, Theorem 7.2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Function Limits Module MvPolynomial Set Topology
open Topology.RelCWComplex
open scoped ContDiff ContinuousMap Manifold

namespace TauCeti.AffineCWModelExample

/-- The single defining equation `X₀ X₁ - 1` of the smooth affine hyperbola in `ℂ²`. -/
def affineHyperbolaPoly : Unit → MvPolynomial (Fin 2) ℂ :=
  fun _ ↦ X 0 * X 1 - 1

theorem affineHyperbolaPoly_apply (u : Unit) :
    affineHyperbolaPoly u = X 0 * X 1 - 1 :=
  (rfl)

/-- At every point `z` of the affine hyperbola `z₀ z₁ - 1 = 0`, the coordinate `z₁` is nonzero, so
`∂(X₀ X₁ - 1)/∂X₀ = z₁ ≠ 0` and the Jacobian matrix is surjective. -/
theorem surjective_jacobiMatrixAt_affineHyperbolaPoly :
    ∀ z ∈ affineZeroLocus affineHyperbolaPoly,
      Surjective (jacobiMatrixAt affineHyperbolaPoly z).mulVec := by
  intro z hz
  rw [mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
  refine ⟨0, ?_⟩
  have hz0 : z 0 * z 1 - 1 = 0 := by
    simpa [affineHyperbolaPoly] using mem_affineZeroLocus.1 hz ()
  have hz1 : z 1 ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_sub] at hz0
    exact neg_ne_zero.2 one_ne_zero hz0
  simpa [affineHyperbolaPoly] using hz1

/-- The smooth affine hyperbola `{z ∈ ℂ² | z₀ z₁ - 1 = 0}` has the homotopy type of a
finite-dimensional Hausdorff CW complex with no cells in dimensions strictly above `1`. -/
theorem exists_cwComplex_homotopyEquiv_affineHyperbola :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧
      Nonempty (affineZeroLocus affineHyperbolaPoly ≃ₕ X) ∧
      ∀ m, 1 < m → IsEmpty (cell (univ : Set X) m) := by
  simpa using exists_cwComplex_homotopyEquiv_affineZeroLocus
    surjective_jacobiMatrixAt_affineHyperbolaPoly

/-- Along the closed holomorphic graph embedding `y ↦ ((y : Fin 2 → ℂ), g y)` of the affine
hyperbola into the `ℓ^∞`-normed product `(Fin 2 → ℂ) × ℂ` determined by an entire function `g`,
`TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding` produces a Hausdorff CW homotopy model
of dimension at most `1` without any inner product on the ambient space. -/
theorem exists_cwComplex_homotopyEquiv_affineHyperbola_graph
    {g : (Fin 2 → ℂ) → ℂ} (hg : ContDiff ℂ ∞ g) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧
      Nonempty (affineZeroLocus affineHyperbolaPoly ≃ₕ X) ∧
      ∀ m, 1 < m → IsEmpty (cell (univ : Set X) m) := by
  let hp := surjective_jacobiMatrixAt_affineHyperbolaPoly
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  let ι : affineZeroLocus affineHyperbolaPoly → (Fin 2 → ℂ) × ℂ :=
    fun y ↦ ((y : Fin 2 → ℂ), g y)
  have hcoe : ContMDiff 𝓘(ℂ, Fin (Fintype.card (Fin 2) - Fintype.card Unit) → ℂ)
      𝓘(ℂ, Fin 2 → ℂ) ∞ (fun y : affineZeroLocus affineHyperbolaPoly ↦ (y : Fin 2 → ℂ)) :=
    contMDiff_coe_affineZeroLocus hp ∞
  have hι : ContMDiff 𝓘(ℂ, Fin (Fintype.card (Fin 2) - Fintype.card Unit) → ℂ)
      𝓘(ℂ, (Fin 2 → ℂ) × ℂ) ∞ ι :=
    hcoe.prodMk_space (hg.contMDiff.comp hcoe)
  have hinj (y : affineZeroLocus affineHyperbolaPoly) :
      Injective (mvfderiv 𝓘(ℂ, Fin (Fintype.card (Fin 2) - Fintype.card Unit) → ℂ) ι y) := by
    intro v w hvw
    have hmd : MDifferentiableAt
        𝓘(ℂ, Fin (Fintype.card (Fin 2) - Fintype.card Unit) → ℂ) 𝓘(ℂ, (Fin 2 → ℂ) × ℂ) ι y :=
      ((hι y).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).mdifferentiableAt one_ne_zero
    have hdfst : DifferentiableAt ℂ (Prod.fst : (Fin 2 → ℂ) × ℂ → Fin 2 → ℂ) (ι y) :=
      (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ℂ).differentiableAt
    have hfst : mvfderiv 𝓘(ℂ, Fin (Fintype.card (Fin 2) - Fintype.card Unit) → ℂ)
        (Prod.fst ∘ ι) y v =
      mvfderiv 𝓘(ℂ, Fin (Fintype.card (Fin 2) - Fintype.card Unit) → ℂ)
        (Prod.fst ∘ ι) y w := by
      rw [mvfderiv_comp_apply_of_differentiableAt hdfst hmd,
        mvfderiv_comp_apply_of_differentiableAt hdfst hmd, hvw]
    exact injective_mvfderiv_iff.2 (injective_mfderiv_coe_affineZeroLocus hp y) hfst
  have hleft : LeftInverse Prod.fst (fun z : Fin 2 → ℂ ↦ (z, g z)) := fun _ ↦ rfl
  have hclosed_graph : IsClosedEmbedding (fun z : Fin 2 → ℂ ↦ (z, g z)) :=
    hleft.isClosedEmbedding continuous_fst (continuous_id.prodMk hg.continuous)
  have hclosed : IsClosedEmbedding ι :=
    hclosed_graph.comp (isClosed_affineZeroLocus affineHyperbolaPoly).isClosedEmbedding_subtypeVal
  have hcard : finrank ℂ (Fin (Fintype.card (Fin 2) - Fintype.card Unit) → ℂ) = 1 := by
    rw [Module.finrank_fin_fun, Fintype.card_fin, Fintype.card_unit]
  simpa only [hcard] using
    exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hι hinj hclosed

/-- **Closedness cannot be dropped in Milnor's Theorem 7.2.** Although `{0}ᶜ ⊆ ℂ²` is an open
`2`-dimensional complex manifold holomorphically embedded in `ℂ²`, it is homotopy equivalent to `S³`
and therefore cannot be homotopy equivalent to any Hausdorff CW complex having no cells in
dimensions strictly above `2`. -/
theorem not_exists_cwComplex_homotopyEquiv_le_two_compl_zero :
    ¬ ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (({0}ᶜ : Set (EuclideanSpace ℂ (Fin 2))) ≃ₕ X) ∧
      ∀ m, 2 < m → IsEmpty (cell (univ : Set X) m) := by
  rintro ⟨X, _, _, _, ⟨h⟩, hempty⟩
  let eSphere : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ≃ₕ (univ : Set X) :=
    (complSingletonHomotopyEquivSphere (0 : EuclideanSpace ℂ (Fin 2))).symm.trans
      (h.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv)
  have hzero : IsZero (((singularHomologyFunctor (ModuleCat.{0} ℚ) 3).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))) :=
    eSphere.isZero_singularHomology_of_isEmpty_cell_gt (ModuleCat.of ℚ ℚ) hempty (by omega)
  have hsub := ModuleCat.isZero_iff_subsingleton.1 hzero
  have hrank0 : finrank ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) 3).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))) = 0 :=
    finrank_zero_of_subsingleton
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1 := by
    have hmul := Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin 2))
    rw [Complex.finrank_real_complex, finrank_euclideanSpace_fin] at hmul
    omega
  have hrank1 := ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ
    (M := ModuleCat.of ℚ ℚ) hdim 3
  simp at hrank1
  omega

end TauCeti.AffineCWModelExample
