/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Center
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Principal

/-!
# Scalar extension of blocks

A ring homomorphism `f : R →+* S` of commutative semirings induces the ring homomorphism
`MonoidAlgebra.centerMapRingHom G f : Z(R[G]) →+* Z(S[G])` of centres
(`TauCeti.Algebra.MonoidAlgebra.Center`).

The image of a block idempotent of `R[G]` is a central idempotent of `S[G]`, hence a sum of blocks
of `S[G]` whenever `1` is a sum of orthogonal blocks of `S[G]`
(`TauCeti.exists_centerMapRingHom_eq_sum`); this holds for every central idempotent, since in the
commutative ring `Z(S[G])` every idempotent is a sum of members of a complete orthogonal family of
primitive idempotents (`CompleteOrthogonalIdempotents.exists_eq_sum_of_isIdempotentElem`). Over an
Artinian `S` and a finite `G` such a family exists
(`TauCeti.exists_completeOrthogonalIdempotents_centerMapRingHom_eq_sum`). The image need not be a
single block: along `𝔽₂ ⊆ 𝔽₄`, the block `r + r²` of `𝔽₂[C₃]` splits into the two blocks
`1 + α² r + α r²` and `1 + α r + α² r²` of `𝔽₄[C₃]`, where `α² + α + 1 = 0`.

The augmentation commutes with `f`, so for a field extension `k ⊆ k'` and a finite `G`, the
principal block of `k[G]`, if it stays a block of `k'[G]`, is the principal block of `k'[G]`, and
the image of a non-principal block has augmentation `0`.

## Main results

* `TauCeti.exists_centerMapRingHom_eq_sum`: the image of a central idempotent of `R[G]`, in
  particular of a block idempotent, is a sum of members of any complete orthogonal family of
  block idempotents of `S[G]`.
* `TauCeti.exists_completeOrthogonalIdempotents_centerMapRingHom_eq_sum`: over an Artinian `S`
  and a finite `G`, the image of a block idempotent of `R[G]` is a sum of block idempotents
  of `S[G]` taken from a complete orthogonal family.
* `TauCeti.centerAugmentation_centerMapRingHom`: the augmentation of `f b` is `f` of that of `b`.
* `TauCeti.centerMapRingHom_principalBlockIdempotent_of_isBlockIdempotent`: for a field
  extension, if the image of the principal block idempotent of `k[G]` is a block idempotent of
  `k'[G]`, it is the principal block idempotent of `k'[G]`.
* `TauCeti.centerAugmentation_centerMapRingHom_eq_zero`: the image of a non-principal block
  idempotent of `k[G]` has augmentation `0`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 12.1.1 and 12.1.2,
  p. 227.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R S G : Type*} [CommSemiring R] [CommRing S] [Monoid G]

/-- **Scalar extension of blocks.** For `f : R →+* S`, the image in `Z(S[G])` of a central
idempotent `b` of `R[G]`, in particular of a block idempotent, is the sum of a subfamily of any
complete orthogonal family `c` of block idempotents of `S[G]`. The subfamily may have several
members: scalar extension need not preserve primitivity. -/
theorem exists_centerMapRingHom_eq_sum (f : R →+* S) {b : Subalgebra.center R R[G]}
    (hb : IsIdempotentElem b) {ι : Type*} [Fintype ι] {c : ι → Subalgebra.center S S[G]}
    (hc : CompleteOrthogonalIdempotents c) (hcp : ∀ i, IsBlockIdempotent (c i)) :
    ∃ s : Finset ι, centerMapRingHom G f b = ∑ i ∈ s, c i :=
  hc.exists_eq_sum_of_isIdempotentElem hcp (hb.map _)

/-- **Scalar extension of blocks over an Artinian ring.** For `f : R →+* S` with `S` Artinian
and `G` finite, `1` is a sum of finitely many orthogonal block idempotents of `S[G]`, and the
image of a central idempotent of `R[G]`, in particular of a block idempotent, is the sum of some
of them. -/
theorem exists_completeOrthogonalIdempotents_centerMapRingHom_eq_sum [IsArtinianRing S]
    [Finite G] (f : R →+* S) {b : Subalgebra.center R R[G]} (hb : IsIdempotentElem b) :
    ∃ (n : ℕ) (c : Fin n → Subalgebra.center S S[G]), CompleteOrthogonalIdempotents c ∧
      (∀ i, IsBlockIdempotent (c i)) ∧
        ∃ s : Finset (Fin n), centerMapRingHom G f b = ∑ i ∈ s, c i := by
  obtain ⟨n, c, hc, hcp⟩ := exists_completeOrthogonalIdempotents_isBlockIdempotent S G
  exact ⟨n, c, hc, hcp, exists_centerMapRingHom_eq_sum f hb hc hcp⟩

section Augmentation

variable {R S G : Type*} [CommRing R] [CommRing S] [Monoid G]

/-- The augmentation commutes with a change of coefficients on the centre:
`ε(f b) = f(ε(b))`. -/
theorem centerAugmentation_centerMapRingHom (f : R →+* S)
    (b : Subalgebra.center R (MonoidAlgebra R G)) :
    centerAugmentation S G (centerMapRingHom G f b) = f (centerAugmentation R G b) := by
  rw [centerAugmentation_apply, centerAugmentation_apply, coe_centerMapRingHom,
    augmentation_mapRingHom]

variable {k : Type*} [Field k] [Finite G]

/-- **The principal block under scalar extension.** For a field extension `f : k →+* k'`, if the
image of the principal block idempotent of `k[G]` is a block idempotent of `k'[G]`, then it is
the principal block idempotent of `k'[G]`: its augmentation is `f 1 = 1`. -/
theorem centerMapRingHom_principalBlockIdempotent_of_isBlockIdempotent {k' : Type*} [Field k']
    (f : k →+* k')
    (h : IsBlockIdempotent (centerMapRingHom G f (principalBlockIdempotent k G))) :
    centerMapRingHom G f (principalBlockIdempotent k G) = principalBlockIdempotent k' G := by
  rw [h.eq_principalBlockIdempotent_iff, centerAugmentation_centerMapRingHom,
    centerAugmentation_principalBlockIdempotent, map_one]
  exact one_ne_zero

/-- **Non-principal blocks under scalar extension.** For a ring homomorphism `f : k →+* k'` to a
commutative ring, the image of a block idempotent of `k[G]` other than the principal one has
augmentation `0`. -/
theorem centerAugmentation_centerMapRingHom_eq_zero {k' : Type*} [CommRing k'] (f : k →+* k')
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    (hne : b ≠ principalBlockIdempotent k G) :
    centerAugmentation k' G (centerMapRingHom G f b) = 0 := by
  rw [centerAugmentation_centerMapRingHom, hb.centerAugmentation_eq_zero hne, map_zero]

end Augmentation

end TauCeti
