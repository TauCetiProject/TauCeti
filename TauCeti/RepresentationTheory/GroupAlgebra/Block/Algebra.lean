/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Eigenvector
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.RingTheory.Idempotents.Corner.Basic

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

If every `g ∈ G` acts on an idempotent `e` of `R[G]` by a scalar, then the corner `e R[G] e` is
spanned by `e`. In particular, over a field `K`, the block algebra `b K[G]` of such a block
idempotent `b` is the line `K b`, so it is isomorphic to `K`.

## Main definitions

* `TauCeti.IsBlockIdempotent.BlockAlgebra`: the block algebra `e_B R[G]` of a block idempotent
  `e_B`, Mathlib's corner ring of `e_B` in `R[G]`, an `R`-algebra with identity `e_B`.
* `TauCeti.algEquivPiBlockAlgebra`: the block decomposition `R[G] ≃ₐ[R] ∏_B e_B R[G]` defined by
  a complete orthogonal family of block idempotents.
* `TauCeti.blockAlgebraAlgEquivOfMulOfEqSmul`: the block algebra of a block idempotent of `K[G]`
  on which `G` acts by scalars is isomorphic to `K`.

## Main results

* `TauCeti.val_algEquivPiBlockAlgebra_apply`: the component of `x` in the block `B` is `e_B x`.
* `IsIdempotentElem.algebraMap_surjective_corner_of_mul_of_eq_smul`: the corner of an idempotent
  of `R[G]` on which `G` acts by scalars is spanned by its identity.
* `TauCeti.blockAlgebraAlgEquivOfMulOfEqSmul_apply`,
  `TauCeti.val_blockAlgebraAlgEquivOfMulOfEqSmul_symm_apply`: the isomorphism with `K` sends
  `a b` to `a`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 12.1.1, p. 227.
-/

public section

namespace TauCeti

variable {R G : Type*} [CommSemiring R] [Monoid G]

namespace IsBlockIdempotent

variable {b : Subalgebra.center R (MonoidAlgebra R G)}

/-- The **block algebra** `e_B R[G]` of a block idempotent `e_B` of `R[G]`: Mathlib's corner ring
`e_B R[G] e_B`, which is `e_B R[G]` because `e_B` is central. It is an `R`-algebra with identity
`e_B`. -/
abbrev BlockAlgebra (hb : IsBlockIdempotent b) : Type _ :=
  hb.isIdempotentElem_val.Corner

namespace BlockAlgebra

/-- The block algebra of a block idempotent is nonzero, because its identity `e_B` is nonzero. -/
instance instNontrivial (hb : IsBlockIdempotent b) : Nontrivial hb.BlockAlgebra :=
  IsIdempotentElem.Corner.nontrivial _ fun h ↦ hb.ne_zero <| Subtype.ext <| by simpa using h

end BlockAlgebra

end IsBlockIdempotent

variable {ι : Type*} [Fintype ι] {b : ι → Subalgebra.center R (MonoidAlgebra R G)}

-- The corner `(hb.val_center.idem i).Corner` is `(hbp i).BlockAlgebra`: both are the corner of
-- `(b i : R[G])`, with two proofs of idempotence, which are equal by proof irrelevance.
/-- **The block decomposition of a group algebra.** A complete orthogonal family of block
idempotents `e_B` of `R[G]` splits it as the product of its block algebras,
`R[G] ≃ₐ[R] ∏_B e_B R[G]`, by `x ↦ (e_B x)_B` with inverse `(y_B)_B ↦ ∑_B y_B`. -/
noncomputable def algEquivPiBlockAlgebra (hb : CompleteOrthogonalIdempotents b)
    (hbp : ∀ i, IsBlockIdempotent (b i)) :
    MonoidAlgebra R G ≃ₐ[R] ∀ i, (hbp i).BlockAlgebra :=
  hb.val_center.algEquivOfIsMulCentral fun i ↦ Set.mem_center_iff.mp (b i).property

/-- The component of `x` in the block algebra `e_B R[G]` is the compression `e_B x e_B`. -/
theorem algEquivPiBlockAlgebra_apply (hb : CompleteOrthogonalIdempotents b)
    (hbp : ∀ i, IsBlockIdempotent (b i)) (x : MonoidAlgebra R G) (i : ι) :
    algEquivPiBlockAlgebra hb hbp x i = (hbp i).isIdempotentElem_val.compress x :=
  hb.val_center.algEquivOfIsMulCentral_apply _ x i

/-- The component of `x` in the block algebra `e_B R[G]` is `e_B x`. -/
@[simp]
theorem val_algEquivPiBlockAlgebra_apply (hb : CompleteOrthogonalIdempotents b)
    (hbp : ∀ i, IsBlockIdempotent (b i)) (x : MonoidAlgebra R G) (i : ι) :
    (algEquivPiBlockAlgebra hb hbp x i).val = b i * x :=
  hb.val_center.val_algEquivOfIsMulCentral_apply _ x i

/-- An element of `∏_B e_B R[G]` corresponds to the sum of its components in `R[G]`. -/
@[simp]
theorem algEquivPiBlockAlgebra_symm_apply (hb : CompleteOrthogonalIdempotents b)
    (hbp : ∀ i, IsBlockIdempotent (b i)) (y : ∀ i, (hbp i).BlockAlgebra) :
    (algEquivPiBlockAlgebra hb hbp).symm y = ∑ i, (y i).val :=
  hb.val_center.algEquivOfIsMulCentral_symm_apply _ y

/-! ### Blocks on which the group acts by scalars -/

section Scalar

variable [Finite G]

/-- If every `g ∈ G` acts on the idempotent `e` of `R[G]` by a scalar, `e g = c(g) e`, then every
element of the corner `e R[G] e` is a scalar multiple of its identity `e`. -/
theorem _root_.IsIdempotentElem.algebraMap_surjective_corner_of_mul_of_eq_smul
    {e : MonoidAlgebra R G} (he : IsIdempotentElem e) {c : G → R}
    (hc : ∀ g, e * MonoidAlgebra.of R G g = c g • e) :
    Function.Surjective (algebraMap R he.Corner) := by
  have := Fintype.ofFinite G
  intro x
  have hx : x.val = e * x.val := (IsIdempotentElem.mul_corner_val _ x).symm
  rw [mul_eq_smul_of_mul_of_eq_smul hc] at hx
  exact ⟨_, Subtype.ext (by rw [IsIdempotentElem.Corner.val_algebraMap, ← hx])⟩

variable {K : Type*} [Field K]
  {b : Subalgebra.center K (MonoidAlgebra K G)} (hb : IsBlockIdempotent b)

/-- If every `g ∈ G` acts on the block idempotent `b` by a scalar, then the block algebra
`b K[G]` is isomorphic to `K`. -/
noncomputable def blockAlgebraAlgEquivOfMulOfEqSmul {c : G → K}
    (hc : ∀ g, (b : MonoidAlgebra K G) * MonoidAlgebra.of K G g = c g • (b : MonoidAlgebra K G)) :
    hb.BlockAlgebra ≃ₐ[K] K :=
  -- The `show` keeps the bijectivity proof at type `Function.Bijective` rather than its unfolding
  -- `Injective ∧ Surjective`, so that `AlgEquiv.ofBijective` lemmas rewrite this term.
  (AlgEquiv.ofBijective (Algebra.ofId K hb.BlockAlgebra) (show Function.Bijective _ from
    ⟨(algebraMap K hb.BlockAlgebra).injective,
      hb.isIdempotentElem_val.algebraMap_surjective_corner_of_mul_of_eq_smul hc⟩)).symm

/-- The isomorphism `b K[G] ≃ₐ[K] K` sends `a b` to `a`. -/
theorem blockAlgebraAlgEquivOfMulOfEqSmul_apply {c : G → K}
    (hc : ∀ g, (b : MonoidAlgebra K G) * MonoidAlgebra.of K G g = c g • (b : MonoidAlgebra K G))
    {x : hb.BlockAlgebra} {a : K} (hx : x.val = a • (b : MonoidAlgebra K G)) :
    blockAlgebraAlgEquivOfMulOfEqSmul hb hc x = a := by
  obtain rfl : x = algebraMap K _ a := Subtype.ext hx
  simp [blockAlgebraAlgEquivOfMulOfEqSmul]

/-- The inverse of the isomorphism `b K[G] ≃ₐ[K] K` sends `a` to `a b`. -/
@[simp]
theorem val_blockAlgebraAlgEquivOfMulOfEqSmul_symm_apply {c : G → K}
    (hc : ∀ g, (b : MonoidAlgebra K G) * MonoidAlgebra.of K G g = c g • (b : MonoidAlgebra K G))
    (a : K) :
    ((blockAlgebraAlgEquivOfMulOfEqSmul hb hc).symm a).val = a • (b : MonoidAlgebra K G) := by
  simp [blockAlgebraAlgEquivOfMulOfEqSmul, IsIdempotentElem.Corner.val_algebraMap]

end Scalar

end TauCeti
