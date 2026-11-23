/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Compressions of operators between ranges of idempotents

For continuous linear endomorphisms `p`, `q` and `T` of a topological module `M`, the
*compression* `ContinuousLinearMap.compress p q T` is the operator `x ↦ q (T x)` from the range of
`p` to the range of `q`. When `p` and `q` are idempotent these ranges are closed complemented
subspaces, and `compress p q T` is the operator `q T p` regarded as a map between them. Toeplitz
operators, the compressions `P u P` of an invertible operator by a projection, and the
compressions `e F e` of the operator of a Fredholm module by an idempotent, from which the index
pairing of a Fredholm module with K-theory is built, are all of this form. The idempotents need
not be self-adjoint, or even defined on a Hilbert space.

Compression is linear in `T` and composes as
`compress q r S ∘ compress p q T = compress p r (S q T)`. A compact operator compresses to a
compact operator, and compression only sees `T` through `T p`. Atkinson's theorem then gives a
Fredholm criterion: `compress p q T` is Fredholm as soon as `compress q p S` inverts it modulo
compact operators, which holds when `p S q T p - p` and `q T p S q - q` are compact
(`ContinuousLinearMap.isFredholm_compress`). In particular, if `T` is
invertible and commutes with an idempotent `p` modulo compact operators, then `p T p` is Fredholm
on the range of `p` (`ContinuousLinearMap.isFredholm_compress_self`), which is the abstract form of
the Fredholm property of Toeplitz operators with invertible symbol.

## Main definitions

* `ContinuousLinearMap.compress p q T`: the compression `q T p : range p → range q`.

## Main results

* `ContinuousLinearMap.compress_comp_compress`, `ContinuousLinearMap.compress_one`: composition
  of compressions, and the compression of the identity by an idempotent.
* `ContinuousLinearMap.compress_mul_self`: compression only depends on `T p`.
* `IsCompactOperator.compress`: compressions of compact operators are compact.
* `ContinuousLinearMap.isCompactOperator_compress_mul_sub`: if `T` commutes with an idempotent
  `p` modulo compact operators, then compressing `S T` by `p` is the product of the compressions
  modulo compact operators.
* `ContinuousLinearMap.isFredholm_compress`: Atkinson's criterion for compressions.
* `ContinuousLinearMap.isFredholm_compress_self`: the compression of an invertible operator by an
  idempotent commuting with it modulo compact operators is Fredholm.
* `ContinuousLinearMap.isFredholm_compress_add_of_isCompactOperator`,
  `ContinuousLinearMap.index_compress_add_of_isCompactOperator`: perturbing `T` by an operator `K`
  with `K p` compact preserves the Fredholm property and the index of the compression.
* `ContinuousLinearMap.index_compress_mul`: if `T` commutes with an idempotent `p` modulo compact
  operators, the index of the compression of `S T` by `p` is the sum of the indices.
* `ContinuousLinearMap.index_compress_conj`, `ContinuousLinearMap.index_compress_conjStarAlgEquiv`:
  conjugating by an isomorphism, or by a unitary of Hilbert spaces, preserves the index of the
  compression.

## References

* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, second edition, Springer GTM 179,
  Chapter 7.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), Chapter 8,
  §8.7.
-/

public section

namespace ContinuousLinearMap

section Semiring

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- The **compression** of `T` by `p` and `q`: the operator `x ↦ q (T x)` from the range of `p`
to the range of `q`. For idempotents `p` and `q` it is the operator `q T p` regarded as a map
between these ranges. -/
def compress (p q T : M →L[R] M) : p.range →L[R] q.range :=
  (q * T).restrict fun x _ ↦ ⟨T x, rfl⟩

/-- The compression of `T` by `p` and `q` applies `q ∘ T`. -/
@[simp]
theorem coe_compress_apply (p q T : M →L[R] M) (x : p.range) :
    (compress p q T x : M) = q (T x) :=
  (rfl)

/-- **Composition of compressions.** Compressing `T` by `p` and `q` and then `S` by `q` and `r`
is compressing `S q T` by `p` and `r`. -/
theorem compress_comp_compress (p q r S T : M →L[R] M) :
    compress q r S ∘L compress p q T = compress p r (S * q * T) := by
  ext x
  simp

/-- The compression of the zero operator is zero. -/
@[simp]
theorem compress_zero (p q : M →L[R] M) : compress p q 0 = 0 := by
  ext x
  simp

end Semiring

section CommSemiring

variable {R M : Type*} [CommSemiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousConstSMul R M]

/-- Compression commutes with scalar multiplication. -/
@[simp]
theorem compress_smul (c : R) (p q T : M →L[R] M) : compress p q (c • T) = c • compress p q T := by
  ext x
  simp

end CommSemiring

section Ring

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

/-- The compression of the identity by an idempotent `p` is the identity of its range. -/
@[simp]
theorem compress_one {p : M →L[R] M} (hp : IsIdempotentElem p) : compress p p 1 = 1 := by
  ext x
  simp [IsIdempotentElem.apply_coe_range hp]

/-- The compression by an idempotent `p` only depends on `T p`. -/
theorem compress_mul_self {p : M →L[R] M} (hp : IsIdempotentElem p) (q T : M →L[R] M) :
    compress p q (T * p) = compress p q T := by
  ext x
  simp [IsIdempotentElem.apply_coe_range hp]

/-- The compression into the range of an idempotent `q` only depends on `q T`. -/
theorem compress_self_mul {q : M →L[R] M} (hq : IsIdempotentElem q) (p T : M →L[R] M) :
    compress p q (q * T) = compress p q T := by
  ext x
  simpa using congr($hq.eq (T x))

variable [IsTopologicalAddGroup M]

/-- Compression is additive. -/
@[simp]
theorem compress_add (p q S T : M →L[R] M) :
    compress p q (S + T) = compress p q S + compress p q T := by
  ext x
  simp

/-- Compression commutes with negation. -/
@[simp]
theorem compress_neg (p q T : M →L[R] M) : compress p q (-T) = -compress p q T := by
  ext x
  simp

/-- Compression commutes with subtraction. -/
@[simp]
theorem compress_sub (p q S T : M →L[R] M) :
    compress p q (S - T) = compress p q S - compress p q T := by
  ext x
  simp

/-- The compression of a compact operator, with values in a closed range, is compact. -/
theorem _root_.IsCompactOperator.compress [T1Space M] {T : M →L[R] M} (hT : IsCompactOperator T)
    (p : M →L[R] M) {q : M →L[R] M} (hq : IsIdempotentElem q) :
    IsCompactOperator (compress p q T) :=
  ((hT.clm_comp q).comp_clm p.range.subtypeL).codRestrict _
    (IsIdempotentElem.isClosed_range hq)

/-- If `K p` is compact for an idempotent `p`, then the compression of `K` by `p` and an
idempotent `q` is compact. -/
theorem isCompactOperator_compress_of_isCompactOperator_mul [T1Space M] {p q K : M →L[R] M}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hK : IsCompactOperator (K * p)) :
    IsCompactOperator (compress p q K) := by
  rw [← compress_mul_self hp]
  exact hK.compress p hq

/-- **Compressions of products.** If `T p - p T` is compact for an idempotent `p`, then the
compression of `S T` by `p` is the product of the compressions of `S` and `T` modulo compact
operators: `p S T p - (p S p) (p T p) = p S (T p - p T) p`. -/
theorem isCompactOperator_compress_mul_sub [T1Space M] {p : M →L[R] M} (hp : IsIdempotentElem p)
    (S : M →L[R] M) {T : M →L[R] M} (hT : IsCompactOperator (T * p - p * T)) :
    IsCompactOperator (compress p p (S * T) - compress p p S ∘L compress p p T) := by
  have h : compress p p (S * T) - compress p p S ∘L compress p p T =
      compress p p (S * (T * p - p * T) * p) := by
    rw [compress_comp_compress, ← compress_sub, ← compress_mul_self hp p (S * T - S * p * T)]
    congr 1
    rw [show S * (T * p - p * T) * p = S * T * (p * p) - S * p * T * p by noncomm_ring, hp.eq]
    noncomm_ring
  rw [h]
  exact ((hT.mul_left S).mul_right p).compress p hp

end Ring

section Conj

variable {R M N : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N] (U : M ≃L[R] N)

/-- An isomorphism `U` carries the range of `p` onto the range of `U p U⁻¹`. -/
theorem _root_.ContinuousLinearEquiv.map_range_eq_range_conj (p : M →L[R] M) :
    p.range.map (U : M →ₗ[R] N) = ((U : M →L[R] N) ∘L p ∘L (U.symm : N →L[R] M)).range := by
  rw [toLinearMap_comp, toLinearMap_comp, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  exact LinearMap.range_eq_top.2 U.symm.surjective

/-- **Conjugation of compressions.** Conjugating `p`, `q` and `T` by an isomorphism `U`
conjugates the compression of `T` by the isomorphisms of ranges induced by `U`. -/
theorem compress_conj (p q T : M →L[R] M) :
    compress ((U : M →L[R] N) ∘L p ∘L (U.symm : N →L[R] M))
        ((U : M →L[R] N) ∘L q ∘L (U.symm : N →L[R] M))
        ((U : M →L[R] N) ∘L T ∘L (U.symm : N →L[R] M)) =
      (ContinuousLinearEquiv.ofSubmodules U q.range
          ((U : M →L[R] N) ∘L q ∘L (U.symm : N →L[R] M)).range (U.map_range_eq_range_conj q) :
          q.range →L[R] _) ∘L compress p q T ∘L
        ((ContinuousLinearEquiv.ofSubmodules U p.range
          ((U : M →L[R] N) ∘L p ∘L (U.symm : N →L[R] M)).range
            (U.map_range_eq_range_conj p)).symm : _ →L[R] p.range) := by
  ext x
  simp only [coe_compress_apply, coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.ofSubmodules_apply, ContinuousLinearEquiv.ofSubmodules_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Conjugating `p`, `q` and `T` by an isomorphism does not change the index of the
compression. -/
@[simp]
theorem index_compress_conj (p q T : M →L[R] M) :
    (compress ((U : M →L[R] N) ∘L p ∘L (U.symm : N →L[R] M))
        ((U : M →L[R] N) ∘L q ∘L (U.symm : N →L[R] M))
        ((U : M →L[R] N) ∘L T ∘L (U.symm : N →L[R] M))).index = (compress p q T).index := by
  rw [compress_conj, index_equiv_comp, index_comp_equiv]

end Conj

section ConjStarAlgEquiv

variable {𝕜 H K : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- Conjugating `p`, `q` and `T` by a unitary `U` of Hilbert spaces does not change the index of
the compression. -/
@[simp]
theorem index_compress_conjStarAlgEquiv (U : H ≃ₗᵢ[𝕜] K) (p q T : H →L[𝕜] H) :
    (compress (U.conjStarAlgEquiv p) (U.conjStarAlgEquiv q) (U.conjStarAlgEquiv T)).index =
      (compress p q T).index := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    index_compress_conj]

end ConjStarAlgEquiv

/-- For a left inverse `S` of `T` and an idempotent `p` of a ring, the defect `p S p T p - p` is
`p S [p, T] p`. -/
private theorem mul_inv_mul_compress_sub_eq {R : Type*} [Ring R] {p S T : R}
    (hp : IsIdempotentElem p) (hST : S * T = 1) :
    p * S * p * T * p - p = p * S * (p * T - T * p) * p :=
  calc p * S * p * T * p - p = p * S * p * T * p - p * (S * T) * p * p := by
        rw [hST, mul_one, hp.eq, hp.eq]
    _ = p * S * (p * T - T * p) * p := by noncomm_ring

section Fredholm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E}

omit [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E] in
/-- `compress q p S` inverts `compress p q T` on the left modulo compact operators when
`p S q T p - p` is compact. -/
private theorem isCompactOperator_compress_comp_compress_sub_one (hp : IsIdempotentElem p)
    {S T : E →L[𝕜] E} (h : IsCompactOperator (p * S * q * T * p - p)) :
    IsCompactOperator (compress q p S ∘L compress p q T - 1 : p.range →L[𝕜] p.range) := by
  have hpp (y : E) : p (p y) = p y := congr($hp.eq y)
  have heq : compress q p S ∘L compress p q T - 1 = compress p p (p * S * q * T * p - p) := by
    ext x
    simp [hpp, IsIdempotentElem.apply_coe_range hp x]
  rw [heq]
  exact h.compress p hp

/-- **Atkinson's criterion for compressions.** Let `p` and `q` be idempotents of a Banach space.
If `p S q T p - p` and `q T p S q - q` are compact, then the compression of `T`, from the range of
`p` to the range of `q`, is Fredholm, with parametrix the compression of `S`. -/
theorem isFredholm_compress (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) {S T : E →L[𝕜] E}
    (hpq : IsCompactOperator (p * S * q * T * p - p))
    (hqp : IsCompactOperator (q * T * p * S * q - q)) :
    (compress p q T).IsFredholm := by
  have := IsIdempotentElem.completeSpace_range hp
  have := IsIdempotentElem.completeSpace_range hq
  exact .of_isCompactOperator_comp_sub_one (S := compress q p S)
    (isCompactOperator_compress_comp_compress_sub_one hp hpq)
    (isCompactOperator_compress_comp_compress_sub_one hq hqp)

/-- **Compressions of invertible operators.** If `T` is invertible and commutes with an idempotent
`p` modulo compact operators, then the compression `p T p` of `T` to the range of `p` is Fredholm,
with parametrix the compression of `T⁻¹`. -/
theorem isFredholm_compress_self (hp : IsIdempotentElem p) {S T : E →L[𝕜] E} (hST : S * T = 1)
    (hTS : T * S = 1) (hT : IsCompactOperator (p * T - T * p)) :
    (compress p p T).IsFredholm := by
  -- `[S, p] = S [p, T] S` is compact as well.
  have hS : IsCompactOperator (p * S - S * p) := by
    have heq : S * p - p * S = S * (p * T - T * p) * S :=
      calc S * p - p * S = S * p * (T * S) - S * T * p * S := by rw [hST, hTS, one_mul, mul_one]
        _ = S * (p * T - T * p) * S := by noncomm_ring
    rw [isCompactOperator_sub_comm, heq]
    exact (hT.mul_left S).mul_right S
  refine isFredholm_compress hp hp (S := S) ?_ ?_
  · rw [mul_inv_mul_compress_sub_eq hp hST]
    exact (hT.mul_left (p * S)).mul_right p
  · rw [mul_inv_mul_compress_sub_eq hp hTS]
    exact (hS.mul_left (p * T)).mul_right p

/-- **Relatively compact perturbations of compressions.** If the compression of `T` is Fredholm
and `K p` is compact, then the compression of `T + K` is Fredholm. -/
theorem isFredholm_compress_add_of_isCompactOperator (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) {T K : E →L[𝕜] E} (hT : (compress p q T).IsFredholm)
    (hK : IsCompactOperator (K * p)) : (compress p q (T + K)).IsFredholm := by
  have := IsIdempotentElem.completeSpace_range hp
  have := IsIdempotentElem.completeSpace_range hq
  rw [compress_add]
  exact hT.add_of_isCompactOperator (isCompactOperator_compress_of_isCompactOperator_mul hp hq hK)

/-- **Relatively compact perturbations of compressions.** If the compression of `T` is Fredholm
and `K p` is compact, then the compression of `T + K` has the same index. -/
theorem index_compress_add_of_isCompactOperator (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) {T K : E →L[𝕜] E} (hT : (compress p q T).IsFredholm)
    (hK : IsCompactOperator (K * p)) : (compress p q (T + K)).index = (compress p q T).index := by
  have := IsIdempotentElem.completeSpace_range hp
  have := IsIdempotentElem.completeSpace_range hq
  rw [compress_add]
  exact index_add_of_isCompactOperator hT
    (isCompactOperator_compress_of_isCompactOperator_mul hp hq hK)

/-- **Index of a compressed product.** If the compressions of `S` and `T` by an idempotent `p` are
Fredholm and `T p - p T` is compact, then the index of the compression of `S T` is the sum of
their indices. -/
theorem index_compress_mul (hp : IsIdempotentElem p) {S T : E →L[𝕜] E}
    (hS : (compress p p S).IsFredholm) (hT : (compress p p T).IsFredholm)
    (hTc : IsCompactOperator (T * p - p * T)) :
    (compress p p (S * T)).index = (compress p p S).index + (compress p p T).index := by
  have := IsIdempotentElem.completeSpace_range hp
  rw [← add_sub_cancel (compress p p S ∘L compress p p T) (compress p p (S * T)),
    index_add_of_isCompactOperator (hS.comp hT) (isCompactOperator_compress_mul_sub hp S hTc)]
  exact index_comp hS hT

end Fredholm

end ContinuousLinearMap
