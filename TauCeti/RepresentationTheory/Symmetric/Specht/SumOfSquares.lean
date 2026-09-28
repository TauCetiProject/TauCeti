/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.HookLength

-- Non-public: the degree sum `TauCeti.sum_finrank_spechtModule_sq` the identity is read off is
-- used only inside the proofs below; no statement here mentions the character table.
import TauCeti.RepresentationTheory.Symmetric.Specht.Orthogonality

/-!
# The sum of the squares of the numbers of standard Young tableaux

For every `n`,

`∑_{μ ⊢ n} (f^μ)² = n !`,

where `f^μ` is the number of standard Young tableaux of shape `μ`.  Both sides count `|Sₙ|`: the
right-hand side directly, and the left-hand side because the Specht modules are a complete list of
the irreducible representations of `Sₙ` and `f^μ` is the degree of `S^μ`.

Only the last step is new here.  The degree sum `∑_μ (dim_ℚ S^μ)² = n !` is
`TauCeti.sum_finrank_spechtModule_sq`, column orthogonality of the character table of `Sₙ` at the
class of the identity, and `dim_ℚ S^μ = f^μ` is `TauCeti.finrank_spechtModule`, the standard
basis of `S^μ`.  Substituting the second into the first is the identity, and substituting the
hook-length formula in turn expresses each summand by the shape alone.

The classical bijective proof is instead the RSK correspondence, which matches a permutation of
`Fin n` with a pair of standard tableaux of a common shape; the library does not yet have it.

## Main results

* `TauCeti.sum_sq_standardCount`: **the sum-of-squares identity** `∑_{μ ⊢ n} (f^μ)² = n !`.
* `TauCeti.sum_sq_factorial_div_prod_hookLength`: the same identity with `f^μ` written by the
  hook-length formula.
* `TauCeti.standardCount_sq_le_factorial`: the resulting bound `f^μ ≤ √(n !)`, in the form
  `(f^μ)² ≤ n !`, with `TauCeti.finrank_spechtModule_sq_le_factorial` its degree form.

## References

* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Chapter 2 for the classification of the
  irreducibles of `Sₙ`, and Chapter 3 for the RSK proof of the identity.
* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
-/

public section

open Finset Module Nat

namespace TauCeti

variable {n : ℕ}

/-- **The sum-of-squares identity for standard Young tableaux**: the squares of the numbers `f^μ`
of standard Young tableaux, summed over the partitions `μ` of `n`, give `n !`.

Both sides count `|Sₙ|`. The classical bijective proof is the RSK correspondence, which matches a
permutation with a pair of standard tableaux of a common shape; the proof here is the
representation-theoretic one, `f^μ` being the degree of the Specht module `S^μ`
(`TauCeti.finrank_spechtModule`) and the degrees of the Specht modules square-summing to `n !`
(`TauCeti.sum_finrank_spechtModule_sq`). -/
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

/-- **The tableau count of a single shape is at most `√(n !)`**, in the form `(f^μ)² ≤ n !`: one
summand of `TauCeti.sum_sq_standardCount` is at most the whole sum. -/
theorem standardCount_sq_le_factorial (μ : n.Partition) :
    standardCount (diagramOf μ) ^ 2 ≤ n ! := by
  rw [← sum_sq_standardCount n]
  exact Finset.single_le_sum (f := fun ν : n.Partition => standardCount (diagramOf ν) ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)

/-- **The degree of a Specht module is at most `√(n !)`**, the representation-theoretic reading of
`TauCeti.standardCount_sq_le_factorial`. -/
theorem finrank_spechtModule_sq_le_factorial (μ : n.Partition) :
    finrank ℚ (spechtModule μ) ^ 2 ≤ n ! := by
  rw [finrank_spechtModule μ]
  exact standardCount_sq_le_factorial μ

end TauCeti
