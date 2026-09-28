/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RepresentationTheory.Symmetric.Specht.Complex
public import TauCeti.RepresentationTheory.Symmetric.Specht.HookLength

-- Non-public: `Complex.isAlgClosed` is what puts the complex Specht modules in the scope of the
-- degree sum, and it is used only inside the proofs below; no statement here mentions algebraic
-- closedness.
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The sum of the squares of the numbers of standard Young tableaux

For every `n`,

`∑_{μ ⊢ n} (f^μ)² = n !`,

where `f^μ` is the number of standard Young tableaux of shape `μ`.  Both sides count `|Sₙ|`: the
right-hand side directly, and the left-hand side because the Specht modules are a complete list of
the irreducible representations of `Sₙ` and `f^μ` is the degree of `S^μ`.

The route taken is the dimension count of the group algebra rather than the RSK correspondence,
the other classical proof, which the library does not yet have.  The complex Specht modules
`ℂ ⊗_ℚ S^μ` are simple, pairwise non-isomorphic
(`TauCeti.spechtModuleℂ_iso_iff`), and indexed by the partitions of `n`, which are as many as the
conjugacy classes of `Sₙ` (`TauCeti.partitionEquivConjClasses`); that is exactly the input to
`TauCeti.ClassFunction.sum_sq_finrank_eq_natCard`, the identity column of the second orthogonality
relation.  Extending the scalars does not change the degree
(`TauCeti.finrank_spechtModuleℂ`), and the degree of the rational Specht module is `f^μ`
(`TauCeti.finrank_spechtModule`), so the degree sum is the tableau count sum.

The passage through `ℂ` is what the degree sum asks for, not a detour: the second orthogonality
relation it is the identity column of is stated over an algebraically closed field, and `ℚ` is not
one.  (The rational identity is nevertheless true as stated, and for the classical reason: `ℚ` is a
splitting field for `Sₙ`, since `End_{ℚ[Sₙ]} S^μ = ℚ`.)  The rational and combinatorial forms are
read off the complex one because none of the three numbers differ.

## Main results

* `TauCeti.sum_sq_finrank_spechtModuleℂ` and `TauCeti.sum_sq_finrank_spechtModule`: **the squares
  of the degrees of the Specht modules sum to `n !`**, over `ℂ` and over `ℚ`.
* `TauCeti.sum_sq_standardCount`: **the sum-of-squares identity** `∑_{μ ⊢ n} (f^μ)² = n !`.
* `TauCeti.sum_sq_factorial_div_prod_hookLength`: the same identity with `f^μ` written by the
  hook-length formula.
* `TauCeti.standardCount_sq_le_factorial`: the resulting bound `f^μ ≤ √(n !)`, in the form
  `(f^μ)² ≤ n !`.

## References

* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Chapter 2 for the classification of the
  irreducibles of `Sₙ`, and Chapter 3 for the RSK proof of the identity.
* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
-/

public section

open Finset Module Nat

namespace TauCeti

variable {n : ℕ}

/-- Complex Specht modules of distinct shapes are inequivalent as representations. This is
`TauCeti.spechtModuleℂ_iso_iff` read at the level of `Representation.Equiv`, the language the
degree sum is stated in. -/
private theorem isEmpty_equiv_spechtModuleℂ {μ ν : n.Partition} (h : μ ≠ ν) :
    IsEmpty (Representation.Equiv (spechtModuleℂ μ).ρ (spechtModuleℂ ν).ρ) := by
  rw [← not_nonempty_iff]
  intro hne
  exact h ((spechtModuleℂ_iso_iff μ ν).mp (nonempty_fdRepIso_iff.mpr hne))

/-- The complex Specht module carries an irreducible representation:
`TauCeti.instSimpleSpechtModuleℂ` read through `FDRep.simple_iff_isIrreducible`. -/
private instance isIrreducible_spechtModuleℂ (μ : n.Partition) :
    Representation.IsIrreducible (spechtModuleℂ μ).ρ :=
  FDRep.isIrreducible_of_simple _

/-- **The squares of the degrees of the complex Specht modules sum to `n !`.** The complex Specht
modules are a complete list of the irreducibles of `Sₙ`, one for each partition of `n`, and the
partitions of `n` are as many as the conjugacy classes, so the identity column of the second
orthogonality relation applies. -/
theorem sum_sq_finrank_spechtModuleℂ (n : ℕ) :
    ∑ μ : n.Partition, finrank ℂ (spechtModuleℂ μ) ^ 2 = n ! := by
  have h := ClassFunction.sum_sq_finrank_eq_natCard
    (fun μ : n.Partition => (spechtModuleℂ μ).ρ)
    (fun _ _ hμν => isEmpty_equiv_spechtModuleℂ hμν)
    (Nat.card_congr (partitionEquivConjClasses n))
  rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h

/-- **The squares of the degrees of the rational Specht modules sum to `n !`.** Extending the
scalars to `ℂ` changes no degree (`TauCeti.finrank_spechtModuleℂ`), so this is
`TauCeti.sum_sq_finrank_spechtModuleℂ`.

The statement is about `ℚ` but the proof is not: the degree sum is proved from the second
orthogonality relation, which is stated over an algebraically closed field. -/
theorem sum_sq_finrank_spechtModule (n : ℕ) :
    ∑ μ : n.Partition, finrank ℚ (spechtModule μ) ^ 2 = n ! := by
  rw [← sum_sq_finrank_spechtModuleℂ n]
  exact Finset.sum_congr rfl fun μ _ => by rw [finrank_spechtModuleℂ μ]

/-- **The sum-of-squares identity for standard Young tableaux**: the squares of the numbers `f^μ`
of standard Young tableaux, summed over the partitions `μ` of `n`, give `n !`.

Both sides count `|Sₙ|`. The classical bijective proof is the RSK correspondence, which matches a
permutation with a pair of standard tableaux of a common shape; the proof here is the
representation-theoretic one, `f^μ` being the degree of the Specht module `S^μ`
(`TauCeti.finrank_spechtModule`) and the Specht modules being all the irreducibles. -/
theorem sum_sq_standardCount (n : ℕ) :
    ∑ μ : n.Partition, standardCount (diagramOf μ) ^ 2 = n ! := by
  rw [← sum_sq_finrank_spechtModule n]
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
