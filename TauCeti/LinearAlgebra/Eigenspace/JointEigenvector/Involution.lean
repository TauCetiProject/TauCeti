/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# Joint eigenvectors of commuting involutions

Over a field in which `2` is invertible, an involution is diagonalizable with eigenvalues `±1`.
Hence a pairwise-commuting family of involutions of a nonzero finite-dimensional vector space has a
joint eigenvector, on which each member of the family acts by `1` or by `-1`. The same holds inside
any nonzero finite-dimensional subspace preserved by the family. This is how a sum `∑ᵢ cᵢ • fᵢ` of
commuting involutions is shown to act on its eigenvectors by a signed sum `∑ᵢ ±cᵢ`.

## Main results

* `TauCeti.exists_jointEigenvector_of_pairwise_commute_of_involutive`: commuting involutions have a
  joint eigenvector with eigenvalues `±1`.
* `TauCeti.exists_mem_jointEigenvector_of_pairwise_commute_of_involutive`: such a joint eigenvector
  can be found inside any nonzero finite-dimensional subspace preserved by the family.
-/

public section

namespace TauCeti

variable {K V ι : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  (f : ι → Module.End K V)

/-- **Commuting involutions have a joint eigenvector**: a pairwise-commuting family of involutions
of a nonzero finite-dimensional vector space has a nonzero vector on which each member of the family
acts by `1` or by `-1`. -/
theorem exists_jointEigenvector_of_pairwise_commute_of_involutive [FiniteDimensional K V]
    [Nontrivial V] (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hinv : ∀ i, Function.Involutive (f i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, f i v = v ∨ f i v = -v := by
  obtain ⟨χ, v, hv, hmem⟩ := exists_jointEigenvector_of_pairwise_commute f hcomm fun i ↦ by
    rw [eq_top_iff, ← (isCompl_eigenspace_one_neg_one (isUnit_of_invertible 2) (hinv i)).sup_eq_top]
    exact sup_le (Module.End.eigenspace_le_maxGenEigenspace.trans (le_iSup _ 1))
      (Module.End.eigenspace_le_maxGenEigenspace.trans (le_iSup _ (-1)))
  refine ⟨v, hv, fun i ↦ ?_⟩
  have heig : f i v = χ i • v := Module.End.mem_eigenspace_iff.1 (hmem i)
  -- The eigenvalue squares to `1`, because `f i` does.
  have hsq : (χ i * χ i) • v = (1 : K) • v := by
    rw [mul_smul, ← heig, ← map_smul, ← heig, hinv i v, one_smul]
  rcases mul_self_eq_one_iff.1 (smul_left_injective K hv hsq) with h | h <;> simp [heig, h]

/-- **Commuting involutions have a joint eigenvector in every invariant subspace**: inside a
nonzero finite-dimensional subspace preserved by a pairwise-commuting family of involutions, there
is a nonzero vector on which each member of the family acts by `1` or by `-1`. -/
theorem exists_mem_jointEigenvector_of_pairwise_commute_of_involutive
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hinv : ∀ i, Function.Involutive (f i))
    {p : Submodule K V} [FiniteDimensional K p] (hp : p ≠ ⊥) (hmaps : ∀ i, ∀ x ∈ p, f i x ∈ p) :
    ∃ v ∈ p, v ≠ 0 ∧ ∀ i, f i v = v ∨ f i v = -v := by
  have : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
  obtain ⟨v, hv, h⟩ := exists_jointEigenvector_of_pairwise_commute_of_involutive
    (fun i ↦ (f i).restrict (hmaps i))
    (fun i j hij ↦ LinearMap.restrict_commute (hcomm hij) (hmaps i) (hmaps j))
    fun i w ↦ Subtype.ext <| by rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply,
      hinv i w]
  refine ⟨v, v.2, Submodule.coe_eq_zero.not.mpr hv, fun i ↦ ?_⟩
  simpa only [Subtype.ext_iff, LinearMap.coe_restrict_apply, Submodule.coe_neg] using h i

end TauCeti
