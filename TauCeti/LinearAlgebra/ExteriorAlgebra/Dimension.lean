/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Freeness and dimension of an exterior algebra

Mathlib records the graded pieces of an exterior algebra in full: `exteriorPower.instFree` says
that `⋀[R]^n M` is free when `M` is, and `exteriorPower.finrank_eq` computes its rank as
`(finrank R M).choose n`. It also builds the basis `Module.Basis.ExteriorAlgebra` of the whole
algebra, indexed by the *finite subsets* of the index set of a basis of `M`. This file records the
consequences for the whole algebra: `ExteriorAlgebra R M` is a free module when `M` is free, a
finite module when `M` is finite, and of rank `2 ^ finrank R M` when `M` is finite free.

The rank count is `Fintype.card_finset`, the observation that a finite set with `n` elements has
`2 ^ n` subsets, which is the same `∑ₖ (n choose k) = 2 ^ n` that summing
`exteriorPower.finrank_eq` over the graded pieces would give. These counts are what the dimension
count for a Clifford algebra rests on: over a ring in which `2` is invertible,
`CliffordAlgebra.equivExterior` identifies `CliffordAlgebra Q` with `ExteriorAlgebra R M` as a
module, so every rank statement about the Clifford algebra is a rank statement about the exterior
algebra transported along that isomorphism. See
`TauCeti/LinearAlgebra/CliffordAlgebra/Dimension.lean`.

No invertibility of `2` is needed here: the exterior algebra of a free module has a basis over any
commutative ring.

## Main results

* `TauCeti.ExteriorAlgebra.instFree`: the exterior algebra of a free module is free.
* `TauCeti.ExteriorAlgebra.instFinite`: the exterior algebra of a finite module is a finite module.
* `TauCeti.ExteriorAlgebra.finrank_eq_two_pow`: `finrank R (ExteriorAlgebra R M) = 2 ^ finrank R M`.
-/

public section

open Module

universe u v

namespace TauCeti

namespace ExteriorAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The exterior algebra of a free module is free, on the finite subsets of a basis index set. -/
instance instFree [Module.Free R M] : Module.Free R (ExteriorAlgebra R M) :=
  let : LinearOrder (Free.ChooseBasisIndex R M) := WellOrderingRel.isWellOrder.linearOrder
  .of_basis (Free.chooseBasis R M).ExteriorAlgebra

/-- The exterior algebra of a finite module is a finite module. -/
instance instFinite [Module.Finite R M] : Module.Finite R (ExteriorAlgebra R M) := by
  -- A surjection `(Fin n → R) → M` induces a surjection of exterior algebras, and the exterior
  -- algebra of `Fin n → R` has a finite basis.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have : Module.Finite R (ExteriorAlgebra R (Fin n → R)) :=
    .of_basis (Pi.basisFun R (Fin n)).ExteriorAlgebra
  exact .of_surjective (ExteriorAlgebra.map f).toLinearMap (ExteriorAlgebra.map_surjective_iff.2 hf)

/-- The exterior algebra of a finite free module of rank `n` has rank `2 ^ n`. -/
theorem finrank_eq_two_pow [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    finrank R (ExteriorAlgebra R M) = 2 ^ finrank R M := by
  let : LinearOrder (Free.ChooseBasisIndex R M) := WellOrderingRel.isWellOrder.linearOrder
  rw [finrank_eq_card_basis (Free.chooseBasis R M).ExteriorAlgebra, Fintype.card_finset,
    finrank_eq_card_chooseBasisIndex]

end ExteriorAlgebra

end TauCeti
