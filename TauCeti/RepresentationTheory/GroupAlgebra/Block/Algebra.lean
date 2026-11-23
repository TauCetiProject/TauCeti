/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.RingTheory.Idempotents.Corner.Central

/-!
# Block algebras of a group algebra

Let `e_B` be a block idempotent of the group algebra `R[G]` over a commutative semiring `R`
(`TauCeti.IsBlockIdempotent`). Since `e_B` is central, the corner `e_B R[G] e_B` is the two-sided
ideal `e_B R[G]`, and it is an `R`-algebra with identity `e_B`: the **block algebra** of `B`. It is
nonzero, since a block idempotent is nonzero.

A complete orthogonal family of block idempotents splits the group algebra as the product of its
block algebras, `R[G] ≃ₐ[R] ∏_B e_B R[G]`, by `x ↦ (e_B x)_B` with inverse `(y_B)_B ↦ ∑_B y_B`
(Webb, Proposition 12.1.1). Over an Artinian ring and for `G` finite such a family exists
(`TauCeti.exists_completeOrthogonalIdempotents_isBlockIdempotent`), and it is unique up to
reindexing (`TauCeti.complete_blockIdempotents_unique`).

## Main definitions

* `TauCeti.IsBlockIdempotent.BlockAlgebra`: the block algebra `e_B R[G]` of a block idempotent
  `e_B`, Mathlib's corner ring of `e_B` in `R[G]`, an `R`-algebra with identity `e_B`.
* `TauCeti.algEquivPiBlockAlgebra`: the block decomposition `R[G] ≃ₐ[R] ∏_B e_B R[G]` defined by
  a complete orthogonal family of block idempotents.

## Main results

* `TauCeti.algEquivPiBlockAlgebra_apply_val`: the component of `x` in the block `B` is `e_B x`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 12.1.1, p. 227.
-/

public section

namespace TauCeti

variable {R G : Type*} [CommSemiring R] [Monoid G]

namespace IsBlockIdempotent

variable {b : Subalgebra.center R (MonoidAlgebra R G)}

/-- A block idempotent of `R[G]`, read in `R[G]`, is idempotent. -/
theorem isIdempotentElem_val (hb : IsBlockIdempotent b) :
    IsIdempotentElem (b : MonoidAlgebra R G) :=
  hb.isIdempotentElem.map (Subalgebra.center R (MonoidAlgebra R G)).val

/-- The **block algebra** `e_B R[G]` of a block idempotent `e_B` of `R[G]`: Mathlib's corner ring
`e_B R[G] e_B`, which is `e_B R[G]` because `e_B` is central. It is an `R`-algebra with identity
`e_B`. -/
abbrev BlockAlgebra (hb : IsBlockIdempotent b) : Type _ :=
  hb.isIdempotentElem_val.Corner

namespace BlockAlgebra

/-- The block algebra of a block idempotent is nonzero, because its identity `e_B` is nonzero. -/
instance instNontrivial (hb : IsBlockIdempotent b) : Nontrivial hb.BlockAlgebra :=
  ⟨1, 0, fun h ↦ hb.ne_zero <| Subtype.ext <| by
    simpa only [IsIdempotentElem.Corner.val_one, IsIdempotentElem.Corner.val_zero,
      ZeroMemClass.coe_zero] using congrArg Subtype.val h⟩

end BlockAlgebra

end IsBlockIdempotent

variable {ι : Type*} [Fintype ι] {b : ι → Subalgebra.center R (MonoidAlgebra R G)}

/-- **The block decomposition of a group algebra.** A complete orthogonal family of block
idempotents `e_B` of `R[G]` splits it as the product of its block algebras,
`R[G] ≃ₐ[R] ∏_B e_B R[G]`, by `x ↦ (e_B x)_B` with inverse `(y_B)_B ↦ ∑_B y_B`. -/
noncomputable def algEquivPiBlockAlgebra (hb : CompleteOrthogonalIdempotents b)
    (hbp : ∀ i, IsBlockIdempotent (b i)) :
    MonoidAlgebra R G ≃ₐ[R] ∀ i, (hbp i).BlockAlgebra :=
  (hb.map (Subalgebra.center R (MonoidAlgebra R G)).val.toRingHom).algEquivOfIsMulCentral
    fun i ↦ Set.mem_center_iff.mp (b i).property

/-- The component of `x` in the block algebra `e_B R[G]` is `e_B x`. -/
@[simp]
theorem algEquivPiBlockAlgebra_apply_val (hb : CompleteOrthogonalIdempotents b)
    (hbp : ∀ i, IsBlockIdempotent (b i)) (x : MonoidAlgebra R G) (i : ι) :
    (algEquivPiBlockAlgebra hb hbp x i).val = b i * x :=
  (hb.map _).algEquivOfIsMulCentral_apply_val _ x i

/-- An element of `∏_B e_B R[G]` corresponds to the sum of its components in `R[G]`. -/
@[simp]
theorem algEquivPiBlockAlgebra_symm_apply (hb : CompleteOrthogonalIdempotents b)
    (hbp : ∀ i, IsBlockIdempotent (b i)) (y : ∀ i, (hbp i).BlockAlgebra) :
    (algEquivPiBlockAlgebra hb hbp).symm y = ∑ i, (y i).val :=
  CompleteOrthogonalIdempotents.algEquivOfIsMulCentral_symm_apply
    (hb.map (Subalgebra.center R (MonoidAlgebra R G)).val.toRingHom)
    (fun i ↦ Set.mem_center_iff.mp (b i).property) y

end TauCeti
