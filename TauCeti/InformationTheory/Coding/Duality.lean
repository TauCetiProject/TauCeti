/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.DotProduct
public import TauCeti.InformationTheory.Coding.DirectSum
public import TauCeti.InformationTheory.Coding.Equivalence
public import TauCeti.InformationTheory.Coding.EuclideanDual
public import TauCeti.InformationTheory.Coding.Puncture

/-!
# Euclidean duals of derived codes

This file computes the Euclidean dual of the codes obtained from a linear code by the elementary
constructions: puncturing, shortening, direct sums, reindexing, and monomial transformations.

For a set `s` of *retained* coordinates, puncturing and shortening are exchanged by duality:
`(puncture C s)^⊥ = shorten C^⊥ s` and `(shorten C s)^⊥ = puncture C^⊥ s`. The dual of a direct
sum is the direct sum of the duals. A monomial transformation which rescales coordinates by units
`u` acts on the dual through the contragredient transformation, which rescales by the inverse
units `u⁻¹` and relabels the coordinates in the same way; in particular, monomially (respectively
permutation) equivalent codes have monomially (respectively permutation) equivalent duals.

## Main statements

* `TauCeti.euclideanDual_puncture`, `TauCeti.euclideanDual_shorten`: duality exchanges
  puncturing and shortening.
* `Submodule.euclideanDual_directSum`: the dual of a direct sum.
* `TauCeti.euclideanDual_reindex`: duality commutes with a change of coordinates.
* `TauCeti.euclideanDual_map_monomialEquiv`: the contragredient action of a monomial
  transformation on the dual.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.5 and 1.6.
-/

public section

open Matrix

namespace Submodule

variable {R ι κ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]

/-- The Euclidean dual of a direct sum is the direct sum of the Euclidean duals. -/
@[simp]
theorem euclideanDual_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    euclideanDual (directSum C D) = directSum (euclideanDual C) (euclideanDual D) := by
  have hdot (x y : ι ⊕ κ → R) : x ⬝ᵥ y =
      (fun i ↦ x (.inl i)) ⬝ᵥ (fun i ↦ y (.inl i)) +
        (fun j ↦ x (.inr j)) ⬝ᵥ (fun j ↦ y (.inr j)) := by
    rw [← sumElim_dotProduct_sumElim]
    congr <;> exact (Sum.elim_comp_inl_inr _).symm
  ext y
  rw [mem_euclideanDual, mem_directSum_iff, mem_euclideanDual, mem_euclideanDual]
  constructor
  · intro hy
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · have h := hy (Sum.elim x 0) (sumElim_zero_mem_directSum D hx)
      simpa [hdot] using h
    · have h := hy (Sum.elim 0 x) (zero_sumElim_mem_directSum C hx)
      simpa [hdot] using h
  · rintro ⟨hC, hD⟩ x hx
    obtain ⟨hxC, hxD⟩ := mem_directSum_iff.mp hx
    rw [hdot, hC _ hxC, hD _ hxD, add_zero]

end Submodule

namespace TauCeti

open Submodule

variable {F ι κ : Type*} [Field F]

section Puncture

variable [Fintype ι] (s : Set ι) [Fintype s]

/-- The Euclidean dual of a punctured code is the shortened Euclidean dual, with the same
retained coordinates. -/
@[simp]
theorem euclideanDual_puncture (C : LinearCode F ι) :
    euclideanDual (puncture C s) = shorten (euclideanDual C) s := by
  ext y
  rw [mem_shorten_iff_extend_mem, mem_euclideanDual, mem_euclideanDual]
  simp only [dotProduct_extend_zero Subtype.val_injective, mem_puncture]
  constructor
  · exact fun h x hx ↦ h _ ⟨x, hx, fun _ ↦ rfl⟩
  · rintro h z ⟨x, hx, hxz⟩
    rw [← h x hx]
    exact congrArg (· ⬝ᵥ y) (funext hxz).symm

/-- The Euclidean dual of a shortened code is the punctured Euclidean dual, with the same
retained coordinates. -/
@[simp]
theorem euclideanDual_shorten (C : LinearCode F ι) :
    euclideanDual (shorten C s) = puncture (euclideanDual C) s := by
  rw [← euclideanDual_euclideanDual (puncture (euclideanDual C) s), euclideanDual_puncture,
    euclideanDual_euclideanDual]

variable [DecidableEq ι]

/-- The Euclidean dual of the code punctured at `i` is the dual shortened at `i`. -/
@[simp]
theorem euclideanDual_punctureAt (C : LinearCode F ι) (i : ι) :
    euclideanDual (punctureAt C i) = shortenAt (euclideanDual C) i := by
  rw [punctureAt_def, shortenAt_def, euclideanDual_puncture]

/-- The Euclidean dual of the code shortened at `i` is the dual punctured at `i`. -/
@[simp]
theorem euclideanDual_shortenAt (C : LinearCode F ι) (i : ι) :
    euclideanDual (shortenAt C i) = punctureAt (euclideanDual C) i := by
  rw [shortenAt_def, punctureAt_def, euclideanDual_shorten]

end Puncture

section Monomial

variable {R : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]

/-- A monomial transformation is adjoint, for the dot product, to the inverse of the
transformation with inverse scalars and the same relabelling. -/
theorem monomialEquiv_dotProduct (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) (y : κ → R) :
    monomialEquiv u e x ⬝ᵥ y = x ⬝ᵥ (monomialEquiv u⁻¹ e).symm y := by
  simp only [dotProduct, monomialEquiv_apply, monomialEquiv_symm_apply, Pi.inv_apply, inv_inv]
  rw [← e.sum_comp]
  exact Fintype.sum_congr _ _ fun i ↦ by rw [e.symm_apply_apply]; ring

/-- The Euclidean dual of the image of a code under a monomial transformation is the image of
the dual under the contragredient transformation, with inverse scalars. -/
@[simp]
theorem euclideanDual_map_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (C : Submodule R (ι → R)) :
    euclideanDual (C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R))) =
      (euclideanDual C).map (monomialEquiv u⁻¹ e : (ι → R) →ₗ[R] (κ → R)) := by
  ext y
  rw [mem_euclideanDual, mem_map_equiv, mem_euclideanDual]
  constructor
  · intro h x hx
    rw [← monomialEquiv_dotProduct]
    exact h _ (mem_map_of_mem hx)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, monomialEquiv_dotProduct]
    exact h x hx

/-- Monomially equivalent codes have monomially equivalent Euclidean duals. -/
theorem IsMonomialEquivalent.euclideanDual {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}
    (h : IsMonomialEquivalent C D) :
    IsMonomialEquivalent (euclideanDual C) (euclideanDual D) := by
  obtain ⟨u, e, rfl⟩ := isMonomialEquivalent_iff.mp h
  exact isMonomialEquivalent_iff.mpr ⟨u⁻¹, e, (euclideanDual_map_monomialEquiv u e C).symm⟩

/-- Permutation-equivalent codes have permutation-equivalent Euclidean duals. -/
theorem IsPermutationEquivalent.euclideanDual {C : Submodule R (ι → R)}
    {D : Submodule R (κ → R)} (h : IsPermutationEquivalent C D) :
    IsPermutationEquivalent (euclideanDual C) (euclideanDual D) := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  refine isPermutationEquivalent_iff.mpr ⟨e, ?_⟩
  have h := euclideanDual_map_monomialEquiv (1 : ι → Rˣ) e C
  rw [inv_one, monomialEquiv_one] at h
  exact h.symm

end Monomial

/-- Euclidean duality commutes with a change of coordinates. -/
@[simp]
theorem euclideanDual_reindex [Fintype ι] [Fintype κ] (C : LinearCode F ι) (e : κ ≃ ι) :
    euclideanDual (reindex C e) = reindex (euclideanDual C) e := by
  have h := euclideanDual_map_monomialEquiv (1 : ι → Fˣ) e.symm C
  rw [inv_one, monomialEquiv_one, Equiv.symm_symm] at h
  rw [reindex_def, reindex_def, h]

end TauCeti
