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

For a duplicate-free list of positive roots and **any** Chevalley datum `D`, ordered root
multiplication is a monomorphism into `D.groupScheme` over `ℤ`. The assertion is integral: it
tests arbitrary commutative rings, not just fields, and applies across all isogeny types. It is
the uniqueness part of the scheme-theoretic positive-root factorization, and does not assert that
its image is the unipotent radical or that the multiplication is a closed immersion.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.mono_rootProduct`: `D.rootProduct l` is a monomorphism of
  schemes over `ℤ` for every duplicate-free list `l` of positive roots.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Ordered multiplication of distinct positive root schemes is a monomorphism into the group
scheme of any Chevalley datum over `ℤ`. The test schemes need not be affine or reduced. -/
theorem mono_rootProduct (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    Mono (D.rootProduct l) :=
  D.mono_rootProduct_of_injective l fun A _ _ _ h =>
    (D.list_prod_map_rootSubgroupPoints_inj A hl hpos).mp h

end TauCeti.DynkinType.ChevalleyDatum
