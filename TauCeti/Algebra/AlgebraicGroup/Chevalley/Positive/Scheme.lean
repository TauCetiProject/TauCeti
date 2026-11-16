/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Product
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct

/-!
# Ordered positive-root multiplication as a scheme morphism

For a list of distinct positive roots, ordered root multiplication is a monomorphism
into the simply connected Chevalley scheme. The assertion is integral: it tests arbitrary
commutative rings, not just fields. It is the uniqueness part of the scheme-theoretic
positive-root factorization, and does not assert that its image is the unipotent radical
or that the multiplication is a closed immersion.

The monomorphism criterion `ChevalleyDatum.mono_rootProduct_of_injective` applies to
`list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType

/-- Ordered multiplication of distinct positive root schemes is a monomorphism into the
simply connected Chevalley scheme. The test schemes need not be affine or reduced. -/
theorem mono_rootProduct_scChevalleyDatum (t : DynkinType) (ht : t.Valid)
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    Mono ((t.scChevalleyDatum ht).rootProduct l) :=
  (t.scChevalleyDatum ht).mono_rootProduct_of_injective l fun A _ _ _ h =>
    (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A hl hpos).mp h

end TauCeti.DynkinType
