/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicTopology.Cellular.Dimension
import TauCeti.Geometry.Manifold.Complex.CWModel

/-!
# Examples: CW homotopy model and homology of the smooth affine hyperbola

The smooth affine hyperbola `V = {z ∈ ℂ² | z₀ z₁ = 1}` (`ℂ*`) is a smooth affine complete
intersection of complex dimension `2 - 1 = 1` in `ℂ²`. Applying
`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus` yields a finite-dimensional Hausdorff CW
homotopy model `X ≃ₕ V` with no cells above dimension `1`. Transferring cellular dimension bounds
across that CW homotopy equivalence recovers vanishing of singular homology `Hₖ(V; ℤ)` and
cohomology `Hᵏ(V; ℤ)` for `k > 1`, as well as freeness of `H₁(V; ℤ)`.

## Used results

* `TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`: CW homotopy model of a smooth affine
  complete intersection.
* `ContinuousMap.HomotopyEquiv.isZero_singularHomology_of_isEmpty_cell_gt`,
  `ContinuousMap.HomotopyEquiv.isZero_singularCohomology_of_isEmpty_cell_gt`, and
  `ContinuousMap.HomotopyEquiv.free_singularHomology_of_isEmpty_cell_succ`: homological and
  cohomological consequences of cellular dimension bounds.

## References

* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of
  Mathematics (2) 69 (1959), 713–717.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7, Theorem 7.2.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Function Limits MvPolynomial Set Topology
open Topology.RelCWComplex
open scoped ContinuousMap

namespace TauCeti

/-- **Check: the smooth affine hyperbola `z₀ z₁ = 1` in `ℂ²` (`ℂ*`).** The zero locus is
nonempty, smooth of complex dimension `2 - 1 = 1`, and homotopy equivalent to a Hausdorff CW
complex with no cells above dimension `1`; transferring cellular dimension bounds across that CW
homotopy equivalence recovers `Hₖ = 0` and `Hᵏ = 0` for `k > 1` and freeness of `H₁(-; ℤ)`. -/
example :
    let p : Unit → MvPolynomial (Fin 2) ℂ := fun _ ↦ MvPolynomial.X 0 * MvPolynomial.X 1 - 1
    Nonempty (affineZeroLocus p) ∧
      ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
        Nonempty (affineZeroLocus p ≃ₕ X) ∧
        (∀ k, 1 < k → IsEmpty (cell (univ : Set X) k)) ∧
        (∀ k, 1 < k → IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of (affineZeroLocus p)))) ∧
        (∀ k, 1 < k → IsZero ((TopCat.of (affineZeroLocus p)).singularCohomology
          (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) k)) ∧
        Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of (affineZeroLocus p))) := by
  intro p
  have hne : Nonempty (affineZeroLocus p) :=
    ⟨⟨![1, 1], mem_affineZeroLocus.2 fun _ ↦ by simp [p]⟩⟩
  have hp : ∀ z ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p z).mulVec := by
    intro z hz
    rw [mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
    have hz_eq : z 0 * z 1 - 1 = 0 := by simpa [p] using mem_affineZeroLocus.1 hz ()
    refine ⟨0, ?_⟩
    have hz1 : z 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero, zero_sub] at hz_eq
      exact neg_ne_zero.2 one_ne_zero hz_eq
    simpa [p, pderiv_mul, pderiv_X] using hz1
  obtain ⟨X, _, _, _, _, ⟨h⟩, hdim⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
  have hdim' : ∀ k, 1 < k → IsEmpty (cell (univ : Set X) k) :=
    fun k hk ↦ hdim k (by simpa only [Fintype.card_fin, Fintype.card_unit] using hk)
  let e : affineZeroLocus p ≃ₕ (univ : Set X) :=
    h.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv
  have : IsEmpty (cell (univ : Set X) (1 + 1)) := hdim' 2 (by omega)
  exact ⟨hne, X, _, ‹_›, ‹_›, ⟨h⟩, hdim',
    fun k hk ↦ e.isZero_singularHomology_of_isEmpty_cell_gt _ hdim' hk,
    fun k hk ↦ e.isZero_singularCohomology_of_isEmpty_cell_gt _ _ hdim' hk,
    e.free_singularHomology_of_isEmpty_cell_succ (ModuleCat.of ℤ ℤ) 1⟩

end TauCeti
