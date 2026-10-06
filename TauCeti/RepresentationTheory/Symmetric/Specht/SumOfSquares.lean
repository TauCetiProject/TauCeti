/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.HookLength

-- Non-public: the degree sum the identity is read off is used only inside the proofs below; no
-- statement here mentions the character table.
import TauCeti.RepresentationTheory.Symmetric.Specht.Orthogonality

/-!
# The sum of the squares of the numbers of standard Young tableaux

For every `n`,

`∑_{μ ⊢ n} (f^μ)² = n !`,

where `f^μ` is the number of standard Young tableaux of shape `μ`.  Both sides count `|Sₙ|`: the
right-hand side directly, and the left-hand side because the Specht modules `S^μ` are a complete
list of the irreducible representations of `Sₙ` and `f^μ` is the degree of `S^μ`, so that the sum
is the sum of the squares of the degrees of the irreducibles.  The identity has an equivalent
bijective reading through the RSK correspondence, which matches a permutation of `Fin n` with a
pair of standard tableaux of a common shape.

Substituting the hook-length formula writes each summand in terms of the shape alone, and
comparing a single summand with the whole sum bounds `f^μ` by `√(n !)`.

## Main results

* `TauCeti.sum_sq_standardCount`: **the sum-of-squares identity** `∑_{μ ⊢ n} (f^μ)² = n !`.
* `TauCeti.sum_sq_factorial_div_prod_hookLength`: the same identity with `f^μ` written by the
  hook-length formula.
* `TauCeti.standardCount_sq_le_factorial`: the resulting bound `f^μ ≤ √(n !)` for a single shape,
  in the form `(f^μ)² ≤ n !`.

## References

* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Chapter 2 for the classification of the
  irreducibles of `Sₙ`, and Chapter 3 for the RSK proof of the identity.
* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
-/

public section

open Finset Nat

namespace TauCeti

/-- **The sum-of-squares identity for standard Young tableaux**: the squares of the numbers `f^μ`
of standard Young tableaux, summed over the partitions `μ` of `n`, give `n !`.

Both sides count `|Sₙ|`.  On the left, `f^μ` is the degree of the Specht module `S^μ` and the
Specht modules are a complete list of the irreducible representations of `Sₙ`, so the sum is the
sum of the squares of the degrees of the irreducibles.  Equivalently, by the RSK correspondence
the summands count the pairs of standard tableaux of a common shape. -/
theorem sum_sq_standardCount (n : ℕ) :
    ∑ μ : n.Partition, standardCount (diagramOf μ) ^ 2 = n ! := by
  rw [← sum_finrank_spechtModule_sq n]
  exact Finset.sum_congr rfl fun μ _ => by rw [finrank_spechtModule μ]

/-- **The sum-of-squares identity with the hook-length formula substituted**: the shapes alone
determine the summands, each being `n !` divided by the product of the hook lengths. -/
theorem sum_sq_factorial_div_prod_hookLength (n : ℕ) :
    ∑ μ : n.Partition,
        (n ! / ∏ c ∈ (diagramOf μ).cells, (diagramOf μ).hookLength c) ^ 2 = n ! := by
  refine .trans (Finset.sum_congr rfl fun μ _ => ?_) (sum_sq_standardCount n)
  rw [standardCount_eq_factorial_div_prod_hookLength, card_diagramOf]

/-- **A single shape has at most `√(n !)` standard Young tableaux**, in the form `(f^μ)² ≤ n !`
for a diagram `μ` with `n` cells. -/
theorem standardCount_sq_le_factorial (μ : YoungDiagram) :
    standardCount μ ^ 2 ≤ μ.card ! := by
  have h := Finset.single_le_sum
    (f := fun ν : μ.card.Partition => standardCount (diagramOf ν) ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (shapePartition μ))
  simp only [diagramOf_shapePartition] at h
  rw [← sum_sq_standardCount μ.card]
  exact h

end TauCeti
