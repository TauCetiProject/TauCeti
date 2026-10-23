/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Quotient

/-!
# Quotients of the absolute Galois group

`TauCeti.quotientFixingSubgroupEquiv` identifies the quotient of the Galois group of a normal
extension `E/F` by the fixing subgroup of an intermediate field `M` normal over `F` with the Galois
group `Gal(M/F)`, as topological groups. This file reads that comparison at
`E = AlgebraicClosure K`, where the quotient is a quotient of `Field.absoluteGaloisGroup K`:

```
Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup ≃ₜ* Gal(M/K).
```

The comparison is restated here rather than left to the reading at `Gal(AlgebraicClosure K/K)`:
`Field.absoluteGaloisGroup K` is a definition carrying its own derived group and topology
instances, so a statement about `Gal(AlgebraicClosure K/K)` is not available to `rw` at a quotient
of `Field.absoluteGaloisGroup K`. The same reason is recorded for the transported instances in
`TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic`.

## Main results

* `TauCeti.absoluteGaloisGroupQuotientEquiv`: the isomorphism of topological groups comparing a
  quotient of `Field.absoluteGaloisGroup K` with the Galois group of a normal subextension of an
  algebraic closure of `K`.
-/

public section

noncomputable section

namespace TauCeti

variable (K : Type*) [Field K] (M : IntermediateField K (AlgebraicClosure K)) [Normal K M]

/-- **The Galois group of a normal subextension of an algebraic closure is a quotient of the
absolute Galois group**: `Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup ≃ₜ* Gal(M/K)`.

This is `quotientFixingSubgroupEquiv` read at `E = AlgebraicClosure K`. -/
def absoluteGaloisGroupQuotientEquiv :
    Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup ≃ₜ* Gal(↥M/K) :=
  quotientFixingSubgroupEquiv K (AlgebraicClosure K) M

variable {K M}

/-- The comparison isomorphism sends the class of `σ` to its restriction to `M`, whose value at a
point of `M` is `σ` evaluated there, by `AlgEquiv.restrictNormalHom_apply`. -/
@[simp]
theorem absoluteGaloisGroupQuotientEquiv_mk (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisGroupQuotientEquiv K M (σ : Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup) =
      AlgEquiv.restrictNormalHom M σ :=
  quotientFixingSubgroupEquiv_mk σ

/-- The inverse of the comparison isomorphism sends the restriction of `σ` back to the class of
`σ`; with `AlgEquiv.restrictNormalHom_surjective` this computes it on every element. -/
@[simp]
theorem absoluteGaloisGroupQuotientEquiv_symm_restrictNormalHom (σ : Gal(AlgebraicClosure K/K)) :
    (absoluteGaloisGroupQuotientEquiv K M).symm (AlgEquiv.restrictNormalHom M σ) =
      (σ : Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup) :=
  quotientFixingSubgroupEquiv_symm_restrictNormalHom σ

end TauCeti
