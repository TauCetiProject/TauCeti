/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RingTheory.Etale.IndEtale
public import TauCeti.RingTheory.Henselization.Algebra
import TauCeti.RingTheory.Flat.Jacobson
import TauCeti.RingTheory.Henselization.Quotient

/-!
# The henselization is ind-étale

The henselization of a ring `R` along an ideal `I` is, by construction, the filtered colimit of
the étale neighbourhoods of `(R, I)`, which are étale `R`-algebras. Hence it is an ind-étale
`R`-algebra, and in particular `R → algebra I` is flat (Stacks, Lemma 15.12.2 (0AGU), flatness).
When `I` lies in the Jacobson radical of `R`, this map is even faithfully flat, because `R` and
its henselization have the same closed fibre (`TauCeti.Henselization.quotientPowEquiv`).

## Main results

* `TauCeti.Henselization.indEtale`: the henselization of `(R, I)` is an ind-étale `R`-algebra.
  The flatness of `R → algebra I` follows by `TauCeti.Algebra.IndEtale.flat`.
* `TauCeti.Henselization.faithfullyFlat_of_le_jacobson`: the henselization is faithfully flat
  over `R` when `I` lies in the Jacobson radical of `R`.

## References

* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- The henselization of `(R, I)` is an ind-étale `R`-algebra: it is the colimit of the étale
neighbourhoods of `(R, I)`, indexed by their essentially small filtered category. -/
instance indEtale (I : Ideal R) : Algebra.IndEtale R (algebra I) :=
  -- `diagram I` is indexed by a small model; reindexing along the equivalence with the small model
  -- returns to the filtered category of neighbourhoods itself.
  ⟨ObjectProperty.of_essentiallySmall_index
    (((ColimitPresentation.colimit (diagram I)).ofIso (algebraIsoColimitDiagram I).symm).reindex
      (equivSmallModel.{u} (Neighbourhood.{u, u} I)).functor)
    fun _ => ((isNeighbourhood_iff I _).mp (ObjectProperty.FullSubcategory.property _)).1⟩

-- The henselization is flat over the base ring.
example (I : Ideal R) : Module.Flat R (algebra I) := inferInstance

/-- The henselization of `(R, I)` is faithfully flat over `R` when `I` lies in the Jacobson
radical of `R`, for instance when `R` is local and `I` is proper. -/
theorem faithfullyFlat_of_le_jacobson (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) :
    Module.FaithfullyFlat R (algebra I) :=
  .of_le_jacobson_of_algHom ((Ideal.pow_le_self one_ne_zero).trans hI)
    (((quotientPowEquiv I 1).symm : _ →ₐ[R] _).comp (Ideal.Quotient.mkₐ R (extended I ^ 1)))

end TauCeti.Henselization
