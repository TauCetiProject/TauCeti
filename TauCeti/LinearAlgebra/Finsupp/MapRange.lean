/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear combinations of finitely supported vectors along a ring homomorphism

For a ring homomorphism `f : A → B`, applying `f` to every coefficient of finitely supported
vectors with values in `A` commutes with linear combinations: the image of `∑ᵢ gᵢ • vᵢ` is
`∑ᵢ f gᵢ • (f ∘ vᵢ)` (`Finsupp.mapRange_linearCombination`). Here the vectors `vᵢ : κ →₀ A` are
themselves finitely supported, as for the rows of a matrix with finite rows; the identity says that
changing the ring of coefficients along `f` commutes with substituting such rows.
-/

public section

namespace Finsupp

variable {ι κ A B F : Type*} [Semiring A] [Semiring B] [FunLike F A B] [RingHomClass F A B]

/-- Applying a ring homomorphism to every coefficient commutes with linear combinations of
finitely supported vectors: the image of `∑ᵢ gᵢ • vᵢ` is `∑ᵢ f gᵢ • (f ∘ vᵢ)`. -/
theorem mapRange_linearCombination (f : F) (v : ι → κ →₀ A) (g : ι →₀ A) :
    mapRange f (map_zero f) (linearCombination A v g) =
      linearCombination B (fun i ↦ mapRange f (map_zero f) (v i)) (mapRange f (map_zero f) g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' =>
    rw [map_add, mapRange_add (map_add f), mapRange_add (map_add f), map_add, hg, hg']
  | single i a =>
    rw [linearCombination_single, mapRange_single, linearCombination_single,
      mapRange_smul' a (f a) (v i) (map_mul f a)]

end Finsupp
