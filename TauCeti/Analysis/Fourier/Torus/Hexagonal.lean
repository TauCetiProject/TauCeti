/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Hexagonal
public import TauCeti.Analysis.Fourier.LaplacianSymbol

/-!
# The Laplacian-symbol minimum for the hexagonal flat torus

The least squared norm of a nonzero reciprocal vector of the hexagonal lattice is `4/3`.
In the Fourier normalization supplied by `TauCeti.laplacianSymbol_apply`, the corresponding
minimum of the negative Laplacian symbol is `16π²/3`.
-/

public section

open Real

namespace TauCeti.HexagonalLattice

/-- The least symbol of the negative Laplacian on nonzero reciprocal vectors is `16π²/3`. -/
theorem isLeast_neg_laplacianSymbol_dual :
    IsLeast ((fun x : EuclideanSpace ℝ (Fin 2) ↦ -laplacianSymbol x) ''
      {x | x ∈ ZLattice.dual lattice ∧ x ≠ 0})
      (16 * π ^ 2 / 3) := by
  have hmono : Monotone (fun t : ℝ ↦ (4 * π ^ 2) * t) :=
    fun _ _ h ↦ mul_le_mul_of_nonneg_left h (by positivity)
  simpa only [Set.image_image, laplacianSymbol_apply, neg_neg,
    show (4 * π ^ 2) * (4 / 3) = 16 * π ^ 2 / 3 by ring] using
    hmono.map_isLeast isLeast_norm_sq_dual

end TauCeti.HexagonalLattice
