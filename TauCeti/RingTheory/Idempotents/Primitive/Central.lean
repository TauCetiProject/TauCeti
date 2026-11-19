/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Commuting primitive idempotents and central decompositions

Two commuting idempotents `e` and `f` multiply to an idempotent below both of them. When `e` is
primitive this product is therefore `0` or `e`, and when both are primitive and the product is
nonzero, `e = f`. In a commutative ring every pair of idempotents commutes, so a primitive
idempotent is a term of every complete family of orthogonal primitive idempotents, and any two
such families agree up to reindexing. This is the uniqueness of the block decomposition of a ring
along the primitive idempotents of its centre: unlike the noncommutative uniqueness theorem
`CompleteOrthogonalIdempotents.exists_equiv_linearEquiv_span_singleton`, which matches the left
ideals `Aeᵢ` only up to isomorphism, here the idempotents themselves agree.

A central idempotent acts on a module by an idempotent module endomorphism. On an indecomposable
module such an endomorphism is `0` or `1`, so an indecomposable module is sent to itself by
exactly one term of a complete family of orthogonal central idempotents, and killed by the
others.

## Main results

* `TauCeti.IsPrimitiveIdempotent.mul_eq_zero_or_eq_of_commute`: for `e` primitive and `f` an
  idempotent commuting with it, `e * f` is `0` or `e`.
* `TauCeti.IsPrimitiveIdempotent.eq_of_commute_of_mul_ne_zero`: commuting primitive idempotents
  with nonzero product are equal.
* `CompleteOrthogonalIdempotents.existsUnique_eq_of_isPrimitiveIdempotent`: in a commutative ring,
  a primitive idempotent is exactly one term of a complete orthogonal family of primitive
  idempotents.
* `CompleteOrthogonalIdempotents.exists_equiv_of_isPrimitiveIdempotent`: in a commutative ring,
  two complete orthogonal families of primitive idempotents indexed by finite types agree up to a
  bijection of the index types.
* `TauCeti.IsIndecomposableModule.existsUnique_forall_smul_eq_self`: an indecomposable module is
  fixed by exactly one term of a complete orthogonal family of central idempotents.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 12.1.1 and 12.1.2 and
  Corollary 12.1.3.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] {e f : A}

/-- **A primitive idempotent absorbs or annihilates a commuting idempotent.** If `f` is an
idempotent commuting with the primitive idempotent `e`, then `e * f` is an idempotent of the
corner ring `eAe`, hence `0` or `e`. -/
theorem IsPrimitiveIdempotent.mul_eq_zero_or_eq_of_commute (he : IsPrimitiveIdempotent e)
    (hf : IsIdempotentElem f) (hef : Commute e f) : e * f = 0 ∨ e * f = e :=
  he.eq_zero_or_eq (.mul_of_commute hef he.isIdempotentElem hf)
    (by rw [← mul_assoc, he.isIdempotentElem.eq])
    (by rw [mul_assoc, ← hef.eq, ← mul_assoc, he.isIdempotentElem.eq])

/-- **Commuting primitive idempotents with nonzero product are equal**: the product is `e` by
primitivity of `e` and `f` by primitivity of `f`. -/
theorem IsPrimitiveIdempotent.eq_of_commute_of_mul_ne_zero (he : IsPrimitiveIdempotent e)
    (hf : IsPrimitiveIdempotent f) (hef : Commute e f) (h : e * f ≠ 0) : e = f := by
  have h₁ : e * f = e := (he.mul_eq_zero_or_eq_of_commute hf.isIdempotentElem hef).resolve_left h
  have h₂ : f * e = f :=
    (hf.mul_eq_zero_or_eq_of_commute he.isIdempotentElem hef.symm).resolve_left
      (by rwa [← hef.eq])
  rw [← h₁, hef.eq, h₂]

/-- **An indecomposable module lies over exactly one central idempotent of a decomposition.**
Each central idempotent `e i` acts on `M` by an idempotent module endomorphism, which is `0` or
`1` because `M` is indecomposable. Not all of them act by `0`, because they sum to `1` and `M` is
nonzero, and two of them cannot act by `1`, because their product is `0`. -/
theorem IsIndecomposableModule.existsUnique_forall_smul_eq_self {M : Type*} [AddCommGroup M]
    [Module A M] (hM : IsIndecomposableModule A M) {ι : Type*} [Fintype ι] {e : ι → A}
    (he : CompleteOrthogonalIdempotents e) (hc : ∀ i, e i ∈ Set.center A) :
    ∃! i, ∀ m : M, e i • m = m := by
  have : Nontrivial M := hM.nontrivial
  let φ : ι → Module.End A M := fun i ↦
    { toFun m := e i • m
      map_add' := smul_add (e i)
      map_smul' a m := by
        simp only [RingHom.id_apply, smul_smul, (Semigroup.mem_center_iff.mp (hc i) a).symm] }
  have hφ (i : ι) : φ i = 0 ∨ φ i = 1 := hM.eq_zero_or_eq_one_of_isIdempotentElem <|
    LinearMap.ext fun m ↦ by
      change e i • e i • m = e i • m
      rw [smul_smul, (he.idem i).eq]
  have hφ₁ (i : ι) : φ i = 1 ↔ ∀ m : M, e i • m = m := LinearMap.ext_iff
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hex : ∃ i, φ i = 1 := by
    by_contra! h
    refine hm ?_
    calc m = (∑ i, e i) • m := by rw [he.complete, one_smul]
      _ = ∑ i, φ i m := Finset.sum_smul ..
      _ = 0 := Finset.sum_eq_zero fun i _ ↦ by rw [(hφ i).resolve_right (h i), LinearMap.zero_apply]
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, (hφ₁ i).mp hi, fun j hj ↦ by_contra fun hji ↦ hm ?_⟩
  calc m = e j • e i • m := by rw [(hφ₁ i).mp hi, hj]
    _ = 0 := by rw [smul_smul, he.ortho hji, zero_smul]

end TauCeti

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

end CompleteOrthogonalIdempotents
