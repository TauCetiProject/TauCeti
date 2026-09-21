/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Normal closures of a number field

The subfield dictionary of a number field `K` is read off the set of embeddings `K →ₐ[ℚ] M` into
a field `M` large enough to contain every conjugate of `K`, rather than off an unnamed ambient
field. `NormalClosureData K M` is the data exhibiting such an `M`: a chosen embedding of `K` into
a Galois extension `M / ℚ` whose embedded images generate `M`.

The action on those embeddings, and the facts the dictionary rests on — transitivity over a
normal extension, faithfulness when the images generate, and the count of embeddings for a finite
separable extension — are general field theory and live in
`TauCeti/FieldTheory/Normal/Embeddings.lean`, with the underlying postcomposition action in
`TauCeti/Algebra/GroupAction/AlgHom.lean`. This file supplies only the number-field packaging, so
that a consumer with a `NormalClosureData` can feed the generation half of `isNormalClosure`, and
`d.embedding`, to those general results.

## Main definitions

* `TauCeti.NumberField.NormalClosureData`: data exhibiting `M` as a normal closure of a number
  field `K` over `ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2 and §9.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

/-- Data exhibiting `M` as a **normal closure** of a number field `K` over `ℚ`: a chosen
embedding of `K` into `M`, together with Mathlib's `IsNormalClosure ℚ K M`.

`IsNormalClosure` carries both halves that the dictionary needs — the minimal polynomials of `K`
split in `M`, and the embedded images generate `M`. The generation half is what gives the
permutation representation on `K →ₐ[ℚ] M` a trivial kernel; without it `M` could be strictly
larger than the compositum of the conjugates of `K`. No separate Galois assumption on `M / ℚ` is
required: `NumberField M` supplies finiteness and separability, and the splitting half of
`isNormalClosure` supplies normality.

The general consequences are stated in `TauCeti/FieldTheory/Normal/Embeddings.lean` and are used
directly: `(Algebra.IsAlgebraic.isNormalClosure_iff.mp d.isNormalClosure).2` feeds
`TauCeti.FieldTheory.eq_one_of_forall_smul_eq` and
`TauCeti.FieldTheory.faithfulSMul_of_normalClosure_eq_top`, after which `smul_left_injective'`
gives injectivity of the permutation representation; `d.embedding` feeds
`MulAction.orbit_eq_univ` and supplies the `Nonempty` hypothesis of `AlgHom.card_of_normal`. -/
@[ext]
structure NormalClosureData (K M : Type*) [Field K] [NumberField K] [Field M]
    [NumberField M] where
  /-- The chosen embedding of `K` into the closure. -/
  embedding : K →ₐ[ℚ] M
  /-- `M` is a normal closure of `K` over `ℚ`, in Mathlib's sense. -/
  isNormalClosure : IsNormalClosure ℚ K M

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]

end TauCeti.NumberField

end
