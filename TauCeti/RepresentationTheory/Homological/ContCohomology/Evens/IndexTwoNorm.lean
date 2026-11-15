/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class

/-!
# The index-two Evens norm on degree-one classes

For an open subgroup `U` of index two in `G`, the graph class
`TauCeti.ContCohomology.graphClass U hU α` of `Evens/Class.lean` is a function of a continuous
homomorphism `α : U → 𝔽₂`. Through the bijection `TauCeti.ContCohomology.homClass` of
`TrivialF2/Character.lean` between continuous homomorphisms and degree-one classes, it descends to
the index-two degree-one Evens norm
```
Nᴱᵛ : H¹(U, 𝔽₂) → H²(G, 𝔽₂),
```
`evensNormIndexTwo`, whose defining equation is `evensNormIndexTwo_homClass`. The norm is a
function and not an additive map.

## Main definition

* `TauCeti.ContCohomology.evensNormIndexTwo`: the index-two degree-one Evens norm.

## Main results

* `TauCeti.ContCohomology.graphClass_representative_independent`: the graph class depends only on
  the class of the homomorphism.
* `TauCeti.ContCohomology.evensNormIndexTwo_homClass`: the norm of the class of a homomorphism is
  its graph class.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.

## Source note

The descent route, an explicit-model class of a homomorphism, its injectivity, and the graph class
of a chosen representative, follows the earlier Tau Ceti formalization in
[TauCeti PR #11157](https://github.com/TauCetiProject/TauCeti/pull/11157) by @mccorvie-agent
("feat: descend the index-two Evens norm"). The class of a homomorphism and its injectivity now
live in `TrivialF2/Character.lean`; `graphClass_representative_independent` and the definition of
`evensNormIndexTwo` through a chosen representative are adapted from it here.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section EvensNorm

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- **The graph class depends only on the class of the homomorphism:** continuous homomorphisms
`U → 𝔽₂` with the same class in `H¹(U, 𝔽₂)` have the same graph class. This is what makes
`graphClass` a function on `H¹(U, 𝔽₂)`. -/
theorem graphClass_representative_independent (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (α β : U.toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) (hβ : Continuous β)
    (hcl : homClass U.toSubgroup α hα = homClass U.toSubgroup β hβ) :
    graphClass U hU α hα = graphClass U hU β hβ := by
  obtain rfl := (homClass_inj U.toSubgroup hα hβ).1 hcl
  rfl

/-- **The index-two degree-one Evens norm** `Nᴱᵛ : H¹(U, 𝔽₂) → H²(G, 𝔽₂)` for an open subgroup
`U` of index two: the graph class of a continuous homomorphism representing the class, which
`homClass_surjective` provides and `graphClass_representative_independent` makes irrelevant. On
the class of `α` it is `graphClass U hU α` (`evensNormIndexTwo_homClass`). It is a function and not
an additive map. -/
noncomputable def evensNormIndexTwo (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    continuousCohomology 2 (trivialF2 G) :=
  graphClass U hU (homClass_surjective U.toSubgroup x).choose
    (homClass_surjective U.toSubgroup x).choose_spec.choose

/-- **The defining equation of the index-two norm:** on the class of a continuous homomorphism it
is the graph class. -/
@[simp]
theorem evensNormIndexTwo_homClass (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    evensNormIndexTwo U hU (homClass U.toSubgroup α hα) = graphClass U hU α hα :=
  graphClass_representative_independent U hU _ α _ hα
    (homClass_surjective U.toSubgroup _).choose_spec.choose_spec

end EvensNorm

end TauCeti.ContCohomology
