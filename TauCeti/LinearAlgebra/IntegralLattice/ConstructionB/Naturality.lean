/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionB.Basic
public import TauCeti.InformationTheory.Coding.Additive.Equivalence

/-!
# Signed coordinate changes in Construction B

Construction B of a binary code `C` is preserved by the coordinate permutations preserving `C`,
and by the sign changes whose sign word lies in the Euclidean dual of `C`, for instance a
codeword when `C` is self-orthogonal. Both are
signed coordinate changes `TauCeti.signedEquiv`, so these are the Construction B counterparts of
the naturality of Construction A in
`TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Naturality`.

## Main statements

* `TauCeti.ConstructionB.signedEquiv_one_mem_lattice`: a permutation automorphism of `C`
  preserves Construction B.
* `TauCeti.ConstructionB.signedEquiv_refl_mem_lattice`: a sign change whose sign word lies in the
  Euclidean dual of `C` preserves Construction B.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10, §3.
-/

public section

namespace TauCeti.ConstructionB

open Matrix

variable {ι : Type*} [Fintype ι] {C : LinearCode (ZMod 2) ι}

/-- Construction B is preserved by a permutation automorphism of the code: it permutes the
coordinates of an integer vector, preserving its reduction modulo two in the code and its
coordinate sum. -/
theorem signedEquiv_one_mem_lattice {σ : Equiv.Perm ι}
    (hσ : σ ∈ AdditiveCode.permutationAut C.toAddSubgroup) {x : ι → ℚ} (hx : x ∈ lattice C) :
    signedEquiv 1 σ x ∈ lattice C := by
  obtain ⟨z, rfl⟩ := exists_intCast_eq_of_mem hx
  obtain ⟨hz, hsum⟩ := (intCast_mem_lattice C z).mp hx
  have heq : signedEquiv 1 σ (fun i ↦ (z i : ℚ)) = fun i ↦ ((z (σ.symm i) : ℤ) : ℚ) := by
    funext i
    simp [signedEquiv_apply]
  rw [heq, intCast_mem_lattice, Equiv.sum_comp σ.symm z]
  exact ⟨AdditiveCode.comp_symm_mem_of_mem_permutationAut hσ hz, hsum⟩

/-- Construction B of a binary code is preserved by a sign change whose sign word, `1` at the
negated coordinates and `0` elsewhere, lies in the Euclidean dual of the code: the change in the
coordinate sum is twice the sum over the negated coordinates, which is even because the sign word
is orthogonal to the reduction of the vector modulo two. -/
theorem signedEquiv_refl_mem_lattice {u : ι → ℤˣ}
    (hu : (fun i ↦ if u i = 1 then (0 : ZMod 2) else 1) ∈ Submodule.euclideanDual C)
    {x : ι → ℚ} (hx : x ∈ lattice C) :
    signedEquiv u (Equiv.refl ι) x ∈ lattice C := by
  obtain ⟨z, rfl⟩ := exists_intCast_eq_of_mem hx
  obtain ⟨hz, hsum⟩ := (intCast_mem_lattice C z).mp hx
  have heq : signedEquiv u (Equiv.refl ι) (fun i ↦ (z i : ℚ)) =
      fun i ↦ ((z i - 2 * if u i = 1 then 0 else z i : ℤ) : ℚ) := by
    funext i
    rcases Int.units_eq_one_or (u i) with h | h
    · simp [signedEquiv_apply, h]
    · simp [signedEquiv_apply, h]
      ring
  rw [heq, intCast_mem_lattice]
  constructor
  · convert hz using 2 with i
    push_cast
    simp only [CharTwo.two_eq_zero, zero_mul, sub_zero]
  · -- The sum over the negated coordinates is the dot product of the sign word with `z` modulo
    -- two.
    have hdot : ((∑ i, if u i = 1 then 0 else z i : ℤ) : ZMod 2) = 0 := by
      have h := Submodule.mem_euclideanDual'.mp hu _ hz
      rw [dotProduct] at h
      push_cast
      simpa only [apply_ite (Int.cast : ℤ → ZMod 2), Int.cast_zero, ite_mul, zero_mul, one_mul]
        using h
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hdot
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hk]
    exact dvd_sub hsum ⟨k, by ring⟩

end TauCeti.ConstructionB
