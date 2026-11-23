/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Product
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Ordered negative-root multiplication as a scheme morphism

For any Chevalley datum `D` and any list of distinct negative roots, ordered root multiplication is
a monomorphism into `D.groupScheme`. The assertion is integral: it tests arbitrary commutative
rings, not just fields or reduced schemes. It is the uniqueness part of the scheme-theoretic
negative-root factorization, and does not assert that its image is the opposite unipotent radical
or that the multiplication is a closed immersion.

The proof specializes `ChevalleyDatum.mono_rootProduct_of_degree_pos` to the negated height degree
`-DynkinType.weightDegree`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Ordered multiplication of distinct negative root schemes is a monomorphism into the Chevalley
group scheme of any Chevalley datum. The test schemes need not be affine or reduced. -/
theorem mono_rootProduct_of_negRoots (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hneg : ∀ γ ∈ l, γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    Mono (D.rootProduct l) :=
  D.mono_rootProduct_of_degree_pos (-t.weightDegree ht) l hl
    (fun γ hγ => neg_pos.mpr (t.weightDegree_root_neg ht (hneg γ hγ)))

end TauCeti.DynkinType.ChevalleyDatum
