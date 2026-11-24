/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.RingTheory.Idempotents.Primitive.Central
public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition

/-!
# Block idempotents of a group algebra

A **block** of the group algebra `R[G]` over a commutative ring `R` is a primitive idempotent of
its centre `Z(R[G])`, written `e_B`. It is not a Wedderburn factor of a semisimple algebra: over a
field of characteristic `p` dividing `|G|` the algebra `k[G]` is not semisimple, and a block may
contain several simple modules. Over `𝔽₂`, the algebra `𝔽₂[C₂] ≅ 𝔽₂[ε]/(ε²)` has the single block
`1`, while `𝔽₃[C₂]` has the two blocks `(1 ± t)/2`, whose sum `1` is central and idempotent but not
primitive.

When the centre is an Artinian ring, which holds when `R` is Artinian and `G` is finite since the
centre is then a finite `R`-module, `1` is a sum of finitely many orthogonal block idempotents
(`TauCeti.exists_completeOrthogonalIdempotents_isBlockIdempotent`). Because the centre is
commutative, such a family is unique up to reindexing (`TauCeti.complete_blockIdempotents_unique`),
over any commutative ring: a block idempotent `f` satisfies `f = ∑ᵢ f e_i`, and each nonzero
`f e_i` forces `f = e_i`. A group isomorphism carries blocks to blocks
(`TauCeti.IsBlockIdempotent.domCongr`).

A complete family of block idempotents splits every `R[G]`-module `M` as `⨁_B e_B M`
(`TauCeti.isInternal_smul_top`), and an indecomposable module lies in exactly one block: exactly
one `e_B` acts on it as the identity, and the others act by `0`
(`TauCeti.IsIndecomposableModule.existsUnique_forall_smul_eq_self`, applied to the block
idempotents read in `R[G]`).

## Main definitions

* `TauCeti.IsBlockIdempotent b`: `b ∈ Z(R[G])` is a primitive idempotent of `Z(R[G])`.

## Main results

* `TauCeti.exists_completeOrthogonalIdempotents_isBlockIdempotent`: over an Artinian commutative
  ring `R` and for `G` finite, `1` is a finite sum of orthogonal block idempotents.
* `TauCeti.complete_blockIdempotents_unique`: two complete orthogonal families of block
  idempotents indexed by finite types agree up to a bijection of the index types.
* `TauCeti.IsBlockIdempotent.domCongr`: transport of blocks along an isomorphism of groups.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 12.1.1 and 12.1.2,
  p. 227, and Corollary 12.1.3, p. 228.
* A. Martínez, *Modular representation theory of finite groups*, Theorem 2.11, p. 15.
-/

public section

namespace TauCeti

variable {R G : Type*}

/-- A **block idempotent** of the group algebra `R[G]` is a primitive idempotent of its centre
`Z(R[G])`. It is written `e_B` for the block `B`. -/
abbrev IsBlockIdempotent [CommSemiring R] [Monoid G] (b : Subalgebra.center R (MonoidAlgebra R G)) :
    Prop :=
  IsPrimitiveIdempotent b

/-- A block idempotent of `R[G]`, read in `R[G]`, is idempotent. -/
theorem IsBlockIdempotent.isIdempotentElem_val [CommSemiring R] [Monoid G]
    {b : Subalgebra.center R (MonoidAlgebra R G)} (hb : IsBlockIdempotent b) :
    IsIdempotentElem (b : MonoidAlgebra R G) :=
  hb.isIdempotentElem.map (Subalgebra.center R (MonoidAlgebra R G)).val

/-- **Transport of blocks along a group isomorphism.** The algebra isomorphism `R[G] ≃ R[G']`
induced by `G ≃* G'` restricts to the centres and carries block idempotents to block
idempotents. -/
theorem IsBlockIdempotent.domCongr [CommSemiring R] [Monoid G] {G' : Type*} [Monoid G']
    (σ : G ≃* G') {b : Subalgebra.center R (MonoidAlgebra R G)} (hb : IsBlockIdempotent b) :
    IsBlockIdempotent (Subalgebra.centerCongr (MonoidAlgebra.domCongr R R σ) b) :=
  IsPrimitiveIdempotent.map (Subalgebra.centerCongr (MonoidAlgebra.domCongr R R σ)).toRingEquiv hb

/-- **Existence of the block decomposition.** Over an Artinian commutative ring `R`, for a finite
group (or monoid) `G`, the centre of `R[G]` is a finite `R`-module, hence an Artinian ring, and so
`1` is a finite sum of orthogonal block idempotents. -/
theorem exists_completeOrthogonalIdempotents_isBlockIdempotent (R G : Type*) [CommRing R]
    [IsArtinianRing R] [Monoid G] [Finite G] :
    ∃ (n : ℕ) (b : Fin n → Subalgebra.center R (MonoidAlgebra R G)),
      CompleteOrthogonalIdempotents b ∧ ∀ i, IsBlockIdempotent (b i) := by
  have : IsNoetherian R (Subalgebra.center R (MonoidAlgebra R G)) :=
    isNoetherian_submodule' (Subalgebra.toSubmodule (Subalgebra.center R (MonoidAlgebra R G)))
  have : IsArtinianRing (Subalgebra.center R (MonoidAlgebra R G)) := IsArtinianRing.of_finite R _
  exact exists_completeOrthogonalIdempotents_isPrimitiveIdempotent _

/-- **Uniqueness of the block decomposition.** Two complete orthogonal families of block
idempotents of `R[G]`, indexed by finite types, agree up to a bijection of the index types. This
holds over every commutative ring, because the centre of `R[G]` is commutative. -/
theorem complete_blockIdempotents_unique [CommRing R] [Monoid G] {ι κ : Type*} [Fintype ι]
    [Fintype κ] {b : ι → Subalgebra.center R (MonoidAlgebra R G)}
    {c : κ → Subalgebra.center R (MonoidAlgebra R G)} (hb : CompleteOrthogonalIdempotents b)
    (hc : CompleteOrthogonalIdempotents c) (hbp : ∀ i, IsBlockIdempotent (b i))
    (hcp : ∀ j, IsBlockIdempotent (c j)) :
    ∃ σ : ι ≃ κ, ∀ i, b i = c (σ i) :=
  hb.exists_equiv_of_isPrimitiveIdempotent hc hbp hcp

end TauCeti
