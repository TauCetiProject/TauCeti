/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic

/-!
# Bidegree components of reduced deconcatenation

The positive `(p, q)` component of reduced deconcatenation is the splitting of the
input component of length `p + q`. This formula lets one recover tensor-length
components by projecting the outputs of a coproduct. It is obtained by restricting
`TensorWords.map_component_comp_deconcatenation` to positive lengths, using the
inclusion and projection between reduced and coaugmented tensor words.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped TensorProduct

namespace TauCeti.ReducedTensorWords

universe uR uM

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Each positive bidegree of reduced deconcatenation splits the component of the total
length. This is the positive-length restriction of the coaugmented coproduct formula. -/
theorem map_component_comp_deconcatenation (p q : {n : ℕ // 0 < n}) :
    TensorProduct.map (component R M p) (component R M q) ∘ₗ deconcatenation R M =
      (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap ∘ₗ
        component R M ⟨p.1 + q.1, Nat.add_pos_left p.2 q.1⟩ := by
  have hc (k : {n : ℕ // 0 < n}) :
      component R M k ∘ₗ TensorWords.reducedProjection R M = TensorWords.component R M k.1 :=
    LinearMap.ext (TensorWords.component_reducedProjection R M k)
  have hi (k : {n : ℕ // 0 < n}) :
      TensorWords.component R M k.1 ∘ₗ TensorWords.reducedInclusion R M = component R M k := by
    rw [← hc k, LinearMap.comp_assoc, TensorWords.reducedProjection_comp_reducedInclusion,
      LinearMap.comp_id]
  calc
    _ = TensorProduct.map (component R M p) (component R M q) ∘ₗ
        (TensorProduct.map (TensorWords.reducedProjection R M)
          (TensorWords.reducedProjection R M) ∘ₗ TensorWords.deconcatenation R M ∘ₗ
            TensorWords.reducedInclusion R M) := by
      rw [TensorWords.map_reducedProjection_comp_deconcatenation_comp_reducedInclusion]
    _ = TensorProduct.map (TensorWords.component R M p.1) (TensorWords.component R M q.1) ∘ₗ
        TensorWords.deconcatenation R M ∘ₗ TensorWords.reducedInclusion R M := by
      rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ← TensorProduct.map_comp, hc p, hc q,
        LinearMap.comp_assoc]
    _ = _ := by
      rw [← LinearMap.comp_assoc, TensorWords.map_component_comp_deconcatenation,
        LinearMap.comp_assoc, hi ⟨p.1 + q.1, Nat.add_pos_left p.2 q.1⟩]

end TauCeti.ReducedTensorWords
