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
public import TauCeti.InformationTheory.Coding.Puncture.Basic
public import TauCeti.InformationTheory.Coding.Reindex

/-!
# Euclidean duals of derived codes

This file computes the Euclidean dual of the codes obtained from a linear code by the elementary
constructions: puncturing, shortening, direct sums, reindexing, and linear (in particular
monomial) equivalences of the coordinate space, and compares the automorphism groups of a code
and of its dual.

For a set `s` of *retained* coordinates, puncturing and shortening are exchanged by duality:
`(puncture C s)^⊥ = shorten C^⊥ s` and `(shorten C s)^⊥ = puncture C^⊥ s`. The dual of a direct
sum is the direct sum of the duals. A linear equivalence of the coordinate space acts on the
dual through its contragredient for the dot product. The contragredient of a monomial
transformation which rescales coordinates by units `u` rescales by the inverse units `u⁻¹` and
relabels the coordinates in the same way; in particular, monomially (respectively permutation)
equivalent codes have monomially (respectively permutation) equivalent duals, and a coordinate
permutation preserves self-orthogonality and self-duality. A direct sum is self-orthogonal
(respectively self-dual) exactly when both summands are.

Taking contragredients carries the monomial automorphisms of a code to those of its dual, and
fixes every coordinate permutation. Over a field, where the dual of the dual is the code itself,
a code and its dual therefore have the same permutation automorphism group and isomorphic
monomial automorphism groups.

## Main statements

* `TauCeti.euclideanDual_puncture`, `TauCeti.euclideanDual_shorten`: duality exchanges
  puncturing and shortening.
* `Submodule.euclideanDual_directSum`: the dual of a direct sum.
* `Submodule.isSelfDual_directSum_iff`: a direct sum is self-dual exactly when both summands are.
* `TauCeti.euclideanDual_reindex`: duality commutes with a change of coordinates.
* `Submodule.euclideanDual_map_linearEquiv`: the dual of the image of a code under a linear
  equivalence is the image of the dual under the contragredient.
* `TauCeti.euclideanDual_map_monomialEquiv`: the contragredient action of a monomial
  transformation on the dual.
* `TauCeti.permutationAut_euclideanDual`: a code and its dual have the same permutation
  automorphisms.
* `TauCeti.mem_monomialAut_euclideanDual_iff`, `TauCeti.monomialAutEquivEuclideanDual`: taking
  contragredients identifies the monomial automorphism groups of a code and of its dual.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.5, 1.6 and 1.7.
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
    · have h := hy (Sum.elim x 0) (sumElim_zero_right_mem_directSum D hx)
      simpa [hdot] using h
    · have h := hy (Sum.elim 0 x) (sumElim_zero_left_mem_directSum C hx)
      simpa [hdot] using h
  · rintro ⟨hC, hD⟩ x hx
    obtain ⟨hxC, hxD⟩ := mem_directSum_iff.mp hx
    rw [hdot, hC _ hxC, hD _ hxD, add_zero]

/-- A direct sum is self-orthogonal exactly when both summands are. -/
@[simp]
theorem isSelfOrthogonal_directSum_iff {C : Submodule R (ι → R)} {D : Submodule R (κ → R)} :
    (directSum C D).IsSelfOrthogonal ↔ C.IsSelfOrthogonal ∧ D.IsSelfOrthogonal := by
  simp only [isSelfOrthogonal_iff_le, euclideanDual_directSum, directSum_le_directSum_iff]

/-- A direct sum is self-dual exactly when both summands are. -/
@[simp]
theorem isSelfDual_directSum_iff {C : Submodule R (ι → R)} {D : Submodule R (κ → R)} :
    (directSum C D).IsSelfDual ↔ C.IsSelfDual ∧ D.IsSelfDual := by
  simp only [isSelfDual_iff, euclideanDual_directSum, directSum_inj]

section Contragredient

variable [DecidableEq ι] [DecidableEq κ]

/-- The Euclidean dual of the image of a code under a linear equivalence is the image of the dual
under the contragredient equivalence. -/
@[simp]
theorem euclideanDual_map_linearEquiv (C : Submodule R (ι → R)) (f : (ι → R) ≃ₗ[R] (κ → R)) :
    euclideanDual (C.map (f : (ι → R) →ₗ[R] (κ → R))) =
      (euclideanDual C).map (f.dotProductContragredient : (ι → R) →ₗ[R] (κ → R)) := by
  ext y
  obtain ⟨z, rfl⟩ := f.dotProductContragredient.surjective y
  rw [mem_map_equiv, LinearEquiv.symm_apply_apply, mem_euclideanDual, mem_euclideanDual]
  constructor
  · intro h x hx
    rw [← f.apply_dotProduct_dotProductContragredient_apply]
    exact h _ (mem_map_of_mem hx)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, f.apply_dotProduct_dotProductContragredient_apply]
    exact h x hx

end Contragredient

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
  simp only [Subtype.val_injective.dotProduct_extend_zero, mem_puncture]
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

/-- The contragredient of a monomial transformation is the monomial transformation with the
inverse scalars and the same relabelling. -/
@[simp]
theorem dotProductContragredient_monomialEquiv [DecidableEq ι] [DecidableEq κ] (u : ι → Rˣ)
    (e : ι ≃ κ) : (monomialEquiv u e).dotProductContragredient = monomialEquiv u⁻¹ e := by
  refine (LinearEquiv.eq_dotProductContragredient_iff.2 fun y x ↦ ?_).symm
  rw [dotProduct_comm, monomialEquiv_dotProduct, LinearEquiv.symm_apply_apply, dotProduct_comm]

/-- The Euclidean dual of the image of a code under a monomial transformation is the image of
the dual under the contragredient transformation, with inverse scalars. -/
theorem euclideanDual_map_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (C : Submodule R (ι → R)) :
    euclideanDual (C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R))) =
      (euclideanDual C).map (monomialEquiv u⁻¹ e : (ι → R) →ₗ[R] (κ → R)) := by
  classical
  rw [euclideanDual_map_linearEquiv, dotProductContragredient_monomialEquiv]

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

/-- Permutation equivalence preserves self-orthogonality. -/
theorem IsPermutationEquivalent.isSelfOrthogonal_iff {C : Submodule R (ι → R)}
    {D : Submodule R (κ → R)} (h : IsPermutationEquivalent C D) :
    C.IsSelfOrthogonal ↔ D.IsSelfOrthogonal := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  have hdual := euclideanDual_map_monomialEquiv (1 : ι → Rˣ) e C
  rw [inv_one, monomialEquiv_one] at hdual
  rw [isSelfOrthogonal_iff_le, isSelfOrthogonal_iff_le, hdual,
    map_le_map_iff_of_injective (LinearEquiv.funCongrLeft R R e.symm).injective]

/-- Permutation equivalence preserves self-duality. -/
theorem IsPermutationEquivalent.isSelfDual_iff {C : Submodule R (ι → R)}
    {D : Submodule R (κ → R)} (h : IsPermutationEquivalent C D) :
    C.IsSelfDual ↔ D.IsSelfDual := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  have hdual := euclideanDual_map_monomialEquiv (1 : ι → Rˣ) e C
  rw [inv_one, monomialEquiv_one] at hdual
  rw [Submodule.isSelfDual_iff, Submodule.isSelfDual_iff, hdual,
    (map_injective_of_injective (LinearEquiv.funCongrLeft R R e.symm).injective).eq_iff]

end Monomial

/-! ### Automorphism groups of the Euclidean dual -/

section Aut

variable {R : Type*} [CommSemiring R] [Fintype ι] {C : Submodule R (ι → R)}

/-- The contragredient of a coordinate permutation is the permutation itself. -/
theorem dotProductContragredient_eq_self_of_mem_permutationGroup [DecidableEq ι]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ permutationGroup R ι) :
    f.dotProductContragredient = f := by
  obtain ⟨e, rfl⟩ := mem_permutationGroup.1 hf
  rw [← monomialEquiv_one, dotProductContragredient_monomialEquiv, inv_one]

/-- The contragredient of a linear automorphism is monomial exactly when the automorphism is. -/
theorem dotProductContragredient_mem_monomialGroup_iff [DecidableEq ι]
    {f : (ι → R) ≃ₗ[R] (ι → R)} :
    f.dotProductContragredient ∈ monomialGroup R ι ↔ f ∈ monomialGroup R ι := by
  have key {g : (ι → R) ≃ₗ[R] (ι → R)} (hg : g ∈ monomialGroup R ι) :
      g.dotProductContragredient ∈ monomialGroup R ι := by
    obtain ⟨u, e, rfl⟩ := mem_monomialGroup.1 hg
    rw [dotProductContragredient_monomialEquiv]
    exact monomialEquiv_mem_monomialGroup _ _
  exact ⟨fun h ↦ by
    simpa only [LinearEquiv.dotProductContragredient_dotProductContragredient] using key h, key⟩

/-- The contragredient of a monomial automorphism of a code is a monomial automorphism of its
Euclidean dual. -/
theorem dotProductContragredient_mem_monomialAut_euclideanDual [DecidableEq ι]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ monomialAut C) :
    f.dotProductContragredient ∈ monomialAut (euclideanDual C) :=
  mem_monomialAut.2 ⟨dotProductContragredient_mem_monomialGroup_iff.2 (mem_monomialAut.1 hf).1,
    by rw [← euclideanDual_map_linearEquiv, (mem_monomialAut.1 hf).2]⟩

/-- A permutation automorphism of a code is a permutation automorphism of its Euclidean dual. -/
theorem permutationAut_le_permutationAut_euclideanDual :
    permutationAut C ≤ permutationAut (euclideanDual C) := by
  classical
  intro f hf
  have h := C.euclideanDual_map_linearEquiv f
  obtain ⟨hf, hfC⟩ := mem_permutationAut.1 hf
  rw [hfC, dotProductContragredient_eq_self_of_mem_permutationGroup hf] at h
  exact mem_permutationAut.2 ⟨hf, h.symm⟩

end Aut

section AutField

variable {K : Type*} [Field K] [Fintype ι]

/-- A linear code and its Euclidean dual have the same permutation automorphisms. -/
@[simp]
theorem permutationAut_euclideanDual (C : Submodule K (ι → K)) :
    permutationAut (euclideanDual C) = permutationAut C := by
  refine le_antisymm ?_ permutationAut_le_permutationAut_euclideanDual
  simpa only [Submodule.euclideanDual_euclideanDual] using
    permutationAut_le_permutationAut_euclideanDual (C := euclideanDual C)

variable [DecidableEq ι]

/-- A linear automorphism is a monomial automorphism of the Euclidean dual of a linear code
exactly when its contragredient is a monomial automorphism of the code. -/
theorem mem_monomialAut_euclideanDual_iff {C : Submodule K (ι → K)}
    {f : (ι → K) ≃ₗ[K] (ι → K)} :
    f ∈ monomialAut (euclideanDual C) ↔ f.dotProductContragredient ∈ monomialAut C := by
  refine ⟨fun h ↦ by
    simpa only [Submodule.euclideanDual_euclideanDual] using
      dotProductContragredient_mem_monomialAut_euclideanDual h, fun h ↦ ?_⟩
  simpa only [LinearEquiv.dotProductContragredient_dotProductContragredient] using
    dotProductContragredient_mem_monomialAut_euclideanDual h

/-- The monomial automorphism groups of a linear code and of its Euclidean dual are isomorphic,
by taking contragredients. -/
def monomialAutEquivEuclideanDual (C : Submodule K (ι → K)) :
    monomialAut C ≃* monomialAut (euclideanDual C) where
  toFun f := ⟨(f : (ι → K) ≃ₗ[K] (ι → K)).dotProductContragredient,
    dotProductContragredient_mem_monomialAut_euclideanDual f.2⟩
  invFun f := ⟨(f : (ι → K) ≃ₗ[K] (ι → K)).dotProductContragredient,
    mem_monomialAut_euclideanDual_iff.1 f.2⟩
  left_inv f := Subtype.ext <|
    (f : (ι → K) ≃ₗ[K] (ι → K)).dotProductContragredient_dotProductContragredient
  right_inv f := Subtype.ext <|
    (f : (ι → K) ≃ₗ[K] (ι → K)).dotProductContragredient_dotProductContragredient
  map_mul' f g := Subtype.ext <| by
    simp only [Subgroup.coe_mul, LinearEquiv.mul_eq_trans,
      LinearEquiv.dotProductContragredient_trans]

@[simp]
theorem coe_monomialAutEquivEuclideanDual_apply (C : Submodule K (ι → K)) (f : monomialAut C) :
    (monomialAutEquivEuclideanDual C f : (ι → K) ≃ₗ[K] (ι → K)) =
      (f : (ι → K) ≃ₗ[K] (ι → K)).dotProductContragredient :=
  (rfl)

@[simp]
theorem coe_monomialAutEquivEuclideanDual_symm_apply (C : Submodule K (ι → K))
    (f : monomialAut (euclideanDual C)) :
    ((monomialAutEquivEuclideanDual C).symm f : (ι → K) ≃ₗ[K] (ι → K)) =
      (f : (ι → K) ≃ₗ[K] (ι → K)).dotProductContragredient :=
  (rfl)

end AutField

/-- Euclidean duality commutes with a change of coordinates. -/
@[simp]
theorem euclideanDual_reindex [Fintype ι] [Fintype κ] (C : LinearCode F ι) (e : κ ≃ ι) :
    euclideanDual (reindex C e) = reindex (euclideanDual C) e := by
  have h := euclideanDual_map_monomialEquiv (1 : ι → Fˣ) e.symm C
  rw [inv_one, monomialEquiv_one, Equiv.symm_symm] at h
  rw [reindex_def, reindex_def, h]

end TauCeti
