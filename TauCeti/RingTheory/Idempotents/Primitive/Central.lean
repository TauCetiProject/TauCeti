/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Uniqueness of primitive decompositions in a commutative ring

Commuting primitive idempotents with nonzero product are equal
(`TauCeti.IsPrimitiveIdempotent.eq_of_commute_of_mul_ne_zero`). In a commutative ring every pair
of idempotents commutes, so a primitive idempotent is a term of every complete family of
orthogonal primitive idempotents, and any two such families agree up to reindexing. This is the
uniqueness of the block decomposition of a ring along the primitive idempotents of its centre:
unlike the noncommutative uniqueness theorem
`CompleteOrthogonalIdempotents.exists_equiv_linearEquiv_span_singleton`, which matches the left
ideals `Aeᵢ` only up to isomorphism, here the idempotents themselves agree.

## Main results

* `CompleteOrthogonalIdempotents.existsUnique_eq_of_isPrimitiveIdempotent`: in a commutative ring,
  a primitive idempotent is exactly one term of a complete orthogonal family of primitive
  idempotents.
* `CompleteOrthogonalIdempotents.exists_equiv_of_isPrimitiveIdempotent`: in a commutative ring,
  two complete orthogonal families of primitive idempotents indexed by finite types agree up to a
  bijection of the index types.
* `CompleteOrthogonalIdempotents.exists_eq_sum_of_isIdempotentElem`: in a commutative ring, every
  idempotent is the sum of a subfamily of a complete orthogonal family of primitive idempotents.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 12.1.1 and 12.1.2.
-/

public section

namespace CompleteOrthogonalIdempotents

variable {A : Type*} [CommRing A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **A primitive idempotent is exactly one term of a primitive decomposition of `1`**, in a
commutative ring. From `f = ∑ i, f * e i`, some `f * e i` is nonzero, and then `f = e i` because
commuting primitive idempotents with nonzero product are equal; orthogonality makes `i` unique. -/
theorem existsUnique_eq_of_isPrimitiveIdempotent {e : ι → A}
    (he : CompleteOrthogonalIdempotents e) (hep : ∀ i, TauCeti.IsPrimitiveIdempotent (e i))
    {f : A} (hf : TauCeti.IsPrimitiveIdempotent f) :
    ∃! i, f = e i := by
  have hex : ∃ i, f * e i ≠ 0 := by
    by_contra! h
    refine hf.ne_zero ?_
    rw [← mul_one f, ← he.complete, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i _ ↦ h i
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hf.eq_of_commute_of_mul_ne_zero (hep i) (Commute.all _ _) hi, ?_⟩
  rintro j rfl
  by_contra hji
  exact hi (he.ortho hji)

/-- **Uniqueness of the primitive decomposition of `1` in a commutative ring.** Two complete
orthogonal families of primitive idempotents indexed by finite types agree up to a bijection of
the index types: each term of one family is exactly one term of the other. -/
theorem exists_equiv_of_isPrimitiveIdempotent {e : ι → A} {f : κ → A}
    (he : CompleteOrthogonalIdempotents e) (hf : CompleteOrthogonalIdempotents f)
    (hep : ∀ i, TauCeti.IsPrimitiveIdempotent (e i))
    (hfp : ∀ j, TauCeti.IsPrimitiveIdempotent (f j)) :
    ∃ σ : ι ≃ κ, ∀ i, e i = f (σ i) := by
  choose σ hσ using fun i ↦ (hf.existsUnique_eq_of_isPrimitiveIdempotent hfp (hep i)).exists
  choose τ hτ using fun j ↦ (he.existsUnique_eq_of_isPrimitiveIdempotent hep (hfp j)).exists
  refine ⟨⟨σ, τ, fun i ↦ ?_, fun j ↦ ?_⟩, hσ⟩
  · exact (he.existsUnique_eq_of_isPrimitiveIdempotent hep (hep i)).unique
      ((hσ i).trans (hτ (σ i))) rfl
  · exact (hf.existsUnique_eq_of_isPrimitiveIdempotent hfp (hfp j)).unique
      ((hτ j).trans (hσ (τ j))) rfl

/-- **Every idempotent is a sum of primitive ones**, in a commutative ring with a complete
orthogonal family of primitive idempotents `e`. From `f = ∑ i, f * e i`, each `f * e i` is `0` or
`e i` because `e i` is primitive, so `f` is the sum of the `e i` with `f * e i = e i`. -/
theorem exists_eq_sum_of_isIdempotentElem {e : ι → A} (he : CompleteOrthogonalIdempotents e)
    (hep : ∀ i, TauCeti.IsPrimitiveIdempotent (e i)) {f : A} (hf : IsIdempotentElem f) :
    ∃ s : Finset ι, f = ∑ i ∈ s, e i := by
  classical
  refine ⟨Finset.univ.filter fun i ↦ e i * f = e i, ?_⟩
  conv_lhs => rw [← one_mul f, ← he.complete, Finset.sum_mul]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs with h
  · exact h
  · exact ((hep i).mul_eq_zero_or_eq_of_commute hf (Commute.all _ _)).resolve_right h

end CompleteOrthogonalIdempotents
