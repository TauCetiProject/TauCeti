/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.YoungRule
import TauCeti.RepresentationTheory.Rep.DirectSum.Character
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-!
# The Specht decomposition of Young permutation modules

A Young permutation module over `ℚ` is equivalent to the direct sum of the Specht modules,
with one copy for each unit of its Kostka multiplicity. The sum is indexed by pairs
`(λ, j)` with `j : Fin (kostkaNumber λ μ)`, so zero multiplicities contribute no summands.

This is the representation form of Young's rule. It upgrades the character identity
`char_permutationModule_eq_sum_kostkaNumber_mul_spechtChar` using characteristic-zero
character determination and the character formula for finite direct sums. Both the
unbundled representation equivalence and the categorical isomorphism are provided.

## References

* G. D. James, *The Representation Theory of the Symmetric Groups* (1978), Chapter 14.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.11.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- Young's rule as an equivalence of representations: the Young permutation module is the
finite direct sum of the Specht representations with their Kostka multiplicities. -/
theorem nonempty_equiv_permutationModule_directSum_spechtModule (μ : n.Partition) :
    Nonempty ((permutationModule μ).ρ.Equiv
      (Representation.directSum fun i : Σ lam : n.Partition, Fin (kostkaNumber lam μ) ↦
        (spechtModule i.1).ρ)) := by
  classical
  apply Representation.nonempty_equiv_of_character_eq
  funext g
  rw [Representation.char_directSum, Fintype.sum_sigma]
  trans ∑ lam : n.Partition, (kostkaNumber lam μ : ℚ) * (spechtModule lam).character g
  · simpa only [← spechtChar_cast] using
      char_permutationModule_eq_sum_kostkaNumber_mul_spechtChar μ g
  · apply Finset.sum_congr rfl
    intro lam _
    rw [← FDRep.character_ρ (spechtModule lam) g]
    simpa only [nsmul_eq_mul] using
      (Fin.sum_const (kostkaNumber lam μ) (Representation.character (spechtModule lam).ρ g)).symm

/-- The categorical form of Young's rule: `M^μ` is isomorphic to the finite direct sum
of `K_{λμ}` copies of each Specht module `S^λ`. -/
theorem nonempty_iso_permutationModuleFDRep_directSum_spechtModule (μ : n.Partition) :
    Nonempty (permutationModuleFDRep μ ≅
      FDRep.of (Representation.directSum fun i : Σ lam : n.Partition, Fin (kostkaNumber lam μ) ↦
        (spechtModule i.1).ρ)) :=
  nonempty_fdRepIso_iff.mpr (nonempty_equiv_permutationModule_directSum_spechtModule μ)

end TauCeti
