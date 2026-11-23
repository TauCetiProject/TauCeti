/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.RepresentationTheory.GroupAlgebra.Block

/-!
# Scalar extension of blocks

A ring homomorphism `f : R →+* S` of commutative semirings induces the ring homomorphism
`MonoidAlgebra.mapRingHom G f : R[G] →+* S[G]` applying `f` to the coefficients. It carries the
centre of `R[G]` into the centre of `S[G]` (`MonoidAlgebra.mapRingHom_mem_center`), because
`S[G]` is spanned over its central scalars `S` by the elements `of S G g`, the images of the
`of R G g`.
The restriction is `MonoidAlgebra.centerMapRingHom G f : Z(R[G]) →+* Z(S[G])`.

The image of a block idempotent of `R[G]` is a central idempotent of `S[G]`, hence a sum of blocks
of `S[G]` whenever `1` is a sum of orthogonal blocks of `S[G]`
(`TauCeti.exists_centerMapRingHom_eq_sum`); this holds for every central idempotent, since in the
commutative ring `Z(S[G])` every idempotent is a sum of members of a complete orthogonal family of
primitive idempotents (`CompleteOrthogonalIdempotents.exists_eq_sum_of_isIdempotentElem`). Over an
Artinian `S` and a finite `G` such a family exists
(`TauCeti.exists_completeOrthogonalIdempotents_centerMapRingHom_eq_sum`). The image need not be a
single block: along `𝔽₂ ⊆ 𝔽₄`, the block `r + r²` of `𝔽₂[C₃]` splits into the two blocks
`1 + α² r + α r²` and `1 + α r + α² r²` of `𝔽₄[C₃]`, where `α² + α + 1 = 0`.

## Main definitions

* `MonoidAlgebra.centerMapRingHom G f`: the ring homomorphism `Z(R[G]) →+* Z(S[G])` induced by
  `f : R →+* S`.

## Main results

* `MonoidAlgebra.mapRingHom_mem_center`: the coefficient map preserves centrality.
* `TauCeti.exists_centerMapRingHom_eq_sum`: the image of a central idempotent of `R[G]`, in
  particular of a block idempotent, is a sum of members of any complete orthogonal family of
  block idempotents of `S[G]`.
* `TauCeti.exists_completeOrthogonalIdempotents_centerMapRingHom_eq_sum`: over an Artinian `S`
  and a finite `G`, the image of a block idempotent of `R[G]` is a sum of block idempotents
  of `S[G]` taken from a complete orthogonal family.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 12.1.1 and 12.1.2,
  p. 227.
-/

public section

namespace MonoidAlgebra

variable {R S : Type*} (G : Type*) [CommSemiring R] [CommSemiring S] [Monoid G]

/-- **The coefficient map preserves centrality.** For `f : R →+* S` and `x` in the centre of
`R[G]`, the image of `x` in `S[G]` is central: it commutes with the scalars `S`, which are central,
and with each `single g 1`, the image of the element `single g 1` of `R[G]`. -/
theorem mapRingHom_mem_center (f : R →+* S) {x : R[G]}
    (hx : x ∈ Subalgebra.center R R[G]) :
    mapRingHom G f x ∈ Subalgebra.center S S[G] := by
  rw [Subalgebra.mem_center_iff] at hx ⊢
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => rw [add_mul, mul_add, hy, hz]
  | single g s =>
    have hg : of S G g = mapRingHom G f (of R G g) := by simp
    rw [single_eq_algebraMap_mul_of, mul_assoc, Algebra.left_comm, hg, ← map_mul, ← map_mul, hx]

/-- The ring homomorphism `Z(R[G]) →+* Z(S[G])` of centres induced by a ring homomorphism
`f : R →+* S`: the restriction of `MonoidAlgebra.mapRingHom G f`. -/
noncomputable def centerMapRingHom (f : R →+* S) :
    Subalgebra.center R R[G] →+* Subalgebra.center S S[G] :=
  ((mapRingHom G f).comp (Subalgebra.center R R[G]).toSubsemiring.subtype).codRestrict
    (Subalgebra.center S S[G]).toSubsemiring fun x ↦ mapRingHom_mem_center G f x.property

@[simp]
theorem coe_centerMapRingHom (f : R →+* S) (x : Subalgebra.center R R[G]) :
    (centerMapRingHom G f x : S[G]) = mapRingHom G f x := by
  simp [centerMapRingHom]

end MonoidAlgebra

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

end TauCeti
