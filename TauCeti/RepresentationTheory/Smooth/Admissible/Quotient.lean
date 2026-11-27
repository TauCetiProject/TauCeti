/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Admissible
public import TauCeti.RepresentationTheory.Smooth.Averaging

/-!
# Quotients of admissible representations

Let `G` be a topological group and `A` a commutative ring in which every compact open subgroup of
`G` has invertible pro-order (`TauCeti.HasUnitProOrder`). A surjective intertwining map `f : V → W`
out of a smooth representation maps `V^U` onto `W^U` for every compact open subgroup `U`
(`Representation.IntertwiningMap.invariantsMap_surjective`, since `f` commutes with the averaging
projector `e_U`). Consequently a quotient of an admissible representation is admissible.

## Main results

* `Representation.IsAdmissible.of_surjective`: a representation receiving a surjective intertwining
  map from an admissible one is admissible, when every compact open subgroup has invertible
  pro-order.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §3.3, Proposition 10(2) and its proof, p. 17.
* W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, 1995, §0, conditions (a)-(b), p. 2.
-/

public section

namespace Representation

variable {A G V W : Type*} [CommRing A] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- **Quotients of admissible representations are admissible** when every compact open subgroup
has invertible pro-order: a representation receiving a surjective intertwining map from an
admissible representation is admissible. -/
theorem IsAdmissible.of_surjective [IsAdmissible ρ]
    (hA : ∀ U : OpenSubgroup G, IsCompact (U : Set G) → TauCeti.HasUnitProOrder A U)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsAdmissible σ := by
  have := IsSmooth.of_surjective f hf
  refine ⟨fun U hU ↦ ?_⟩
  have := isCompact_iff_compactSpace.1 hU
  have := IsAdmissible.finite_invariants (ρ := ρ) U hU
  have hU' : TauCeti.HasUnitProOrder A (U : Subgroup G) := hA U hU
  let g := f.res (U : Subgroup G).subtype
  have hg : Function.Surjective g := by rwa [IntertwiningMap.coe_res]
  exact Module.Finite.of_surjective _ (g.invariantsMap_surjective hU' hg)

end Representation
