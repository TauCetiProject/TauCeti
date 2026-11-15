/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Basic
public import TauCeti.RingTheory.Syntomic.StandardSyntomic
import TauCeti.RingTheory.Node.BaseChange
import TauCeti.RingTheory.Node.Flat

/-!
# The node is standard syntomic

The local model `R[x, y] ⧸ (xy - a)` of a node is a standard syntomic `R`-algebra of relative
dimension one, for every commutative ring `R` and every `a ∈ R`. Its presentation has two
generators and the single relation `xy - a`; it is free, hence flat, over `R`; and its fibre over a
prime `p` of `R` is the node `κ(p)[x, y] ⧸ (xy - ā)` over the residue field, which has Krull
dimension one whether or not `ā` vanishes. This is the local shape of a family of curves with at
worst nodal singularities over a discrete valuation ring with uniformizer `π`, where `a = πⁿ`.

## Main results

* `TauCeti.NodeAlgebra.isStandardSyntomicOfRelativeDimension`: `R[x, y] ⧸ (xy - a)` is standard
  syntomic of relative dimension one over `R`.

## References

* [The Stacks Project, Example 55.14.1, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

public section

namespace TauCeti

namespace NodeAlgebra

variable {R : Type*} [CommRing R] (a : R)

/-- The local model `R[x, y] ⧸ (xy - a)` of a node is standard syntomic of relative dimension
one over `R`. -/
instance isStandardSyntomicOfRelativeDimension :
    Algebra.IsStandardSyntomicOfRelativeDimension 1 R (NodeAlgebra R a) :=
  (presentation a).isStandardSyntomicOfRelativeDimension (by simp) fun p _ _ ↦ by
    -- The fibre over `p` is the node over the residue field `κ(p)`.
    rw [ringKrullDim_eq_of_ringEquiv (baseChange (S := p.ResidueField) a).toRingEquiv,
      ringKrullDim_eq_one, Nat.cast_one]

end NodeAlgebra

end TauCeti
