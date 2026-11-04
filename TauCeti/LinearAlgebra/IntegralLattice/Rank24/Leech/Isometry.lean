/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.MinimalVectors
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.NormShell

/-!
# The faithful minimal-vector action of the Leech isometry group

The norm-four vectors of the Construction-B Leech lattice span its rational ambient space.
Already the vectors of shape `(±4², 0²²)` in congruence coordinates suffice: adding two such
vectors with opposite signs at the second coordinate isolates a nonzero multiple of any
coordinate vector.

Consequently the full lattice isometry group acts faithfully on the 196560 minimal vectors.
This realizes the group usually denoted `Co₀` as a finite permutation group, without assuming
that any proposed list of Conway generators generates all lattice isometries. This is the
action on vectors, not the action on antipodal pairs used for `Co₁`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

open IntegralLattice

private theorem pair_mem_minimalSpan {i j : Fin 24} (hij : i ≠ j) (s t : ℤˣ) :
    (fun k ↦ (leechPairVector i j s t k : ℚ) / 2) ∈
      Submodule.span ℚ (Subtype.val '' leechLattice.vectorsOfNorm 4 : Set (Fin 24 → ℚ)) := by
  obtain ⟨hmem, hnorm⟩ := leechPairVector_mem hij s t
  apply Submodule.subset_span
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  rw [mem_vectorsOfNorm, leechLattice_norm_intCast_div_two, hnorm]
  norm_num

/-- The Leech minimal vectors span the entire rational coordinate space. This is a rational
span assertion; it does not assert that the first family alone generates the integral lattice. -/
theorem span_vectorsOfNorm_four_leechLattice :
    Submodule.span ℚ (Subtype.val '' leechLattice.vectorsOfNorm 4 : Set (Fin 24 → ℚ)) = ⊤ := by
  let S := Submodule.span ℚ
    (Subtype.val '' leechLattice.vectorsOfNorm 4 : Set (Fin 24 → ℚ))
  have hsingle (i : Fin 24) : Pi.single i (1 : ℚ) ∈ S := by
    obtain ⟨j, hji⟩ := exists_ne i
    have h := S.smul_mem (1 / 4 : ℚ)
      (S.add_mem (pair_mem_minimalSpan hji.symm 1 1) (pair_mem_minimalSpan hji.symm 1 (-1)))
    have heq : (1 / 4 : ℚ) •
        ((fun k ↦ (leechPairVector i j 1 1 k : ℚ) / 2) +
          (fun k ↦ (leechPairVector i j 1 (-1) k : ℚ) / 2)) = Pi.single i 1 := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [leechPairVector_apply]
      · by_cases hkj : k = j
        · subst k
          norm_num [leechPairVector_apply, hji]
        · simp [leechPairVector_apply, hki, hkj]
    exact heq ▸ h
  apply top_unique
  intro x _
  rw [pi_eq_sum_univ' x]
  exact S.sum_mem fun i _ ↦ S.smul_mem (x i) (hsingle i)

/-- The full Leech isometry group's action on the norm-four vectors is faithful. -/
theorem leech_normShellHom_injective :
    Function.Injective (IntegralLattice.Isometry.normShellHom leechLattice 4) :=
  IntegralLattice.Isometry.normShellHom_injective 4 span_vectorsOfNorm_four_leechLattice

/-- The norm-four shell of the Leech lattice is finite. -/
instance finite_leechMinimalVectors : Finite (leechLattice.vectorsOfNorm 4) :=
  Nat.finite_of_card_ne_zero (by
    rw [Nat.card_coe_set_eq, ncard_vectorsOfNorm_four_leechLattice]
    norm_num)

/-- The full Leech lattice isometry group is finite, via its faithful minimal-vector action. -/
instance finite_leechIsometry : Finite (IntegralLattice.Isometry leechLattice leechLattice) :=
  Finite.of_injective _ leech_normShellHom_injective

end TauCeti
