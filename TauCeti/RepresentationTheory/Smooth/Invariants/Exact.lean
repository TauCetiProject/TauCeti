/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.RepresentationTheory.Smooth.Invariants
public import TauCeti.Topology.Algebra.Group.Profinite.UnitProOrder
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Exact
import TauCeti.RepresentationTheory.Smooth.Averaging

/-!
# Exactness of invariants under a compact subgroup of invertible pro-order

Let `G` be a topological group, `A` a commutative ring and `U` a compact subgroup of `G` (in
practice a compact open subgroup of a locally profinite group) with invertible pro-order in `A`
(`TauCeti.HasUnitProOrder A U`). The functor `TauCeti.SmoothRep.invariantsFunctor A U` of
`U`-invariants on smooth representations is left exact for every `U`
(`TauCeti.SmoothRep.preservesFiniteLimits_invariantsFunctor`). Under the pro-order hypothesis it
also preserves epimorphisms: a surjection `V → W` of smooth representations maps `V^U` onto `W^U`,
since it commutes with the averaging projector `e_U` onto the invariants
(`Representation.IntertwiningMap.invariantsMap_surjective`). Hence it is exact: it preserves
homology and finite colimits, and sends short exact sequences to short exact sequences.

Without the hypothesis exactness fails: for `G = U = ℤ/p` and `A = 𝔽_p`, the `U`-invariants of
the augmentation `𝔽_p[ℤ/p] → 𝔽_p` are not surjective (the Check in
`TauCeti/Examples/RepresentationTheory/Smooth/Invariants.lean`).

## Main results

* `TauCeti.SmoothRep.invariantsFunctor_map_surjective`: surjections induce surjections on
  `U`-invariants.
* `TauCeti.SmoothRep.preservesEpimorphisms_invariantsFunctor`: `invariantsFunctor A U` preserves
  epimorphisms.
* `TauCeti.SmoothRep.preservesHomology_invariantsFunctor`,
  `TauCeti.SmoothRep.preservesFiniteColimits_invariantsFunctor`: it is exact.
* `TauCeti.SmoothRep.shortExact_map_invariantsFunctor`: it preserves short exact sequences.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §3.3, Proposition 10(2) and its proof, p. 17.
-/

public section

open CategoryTheory Limits

universe w u v

namespace TauCeti

namespace SmoothRep

variable {A : Type u} [CommRing A] {G : Type v} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] (U : Subgroup G) [CompactSpace U]

/-- **Surjections are surjective on `U`-invariants** for a compact subgroup `U` of invertible
pro-order: a surjective morphism of smooth representations commutes with the averaging projector
onto `U`-invariants. -/
theorem invariantsFunctor_map_surjective (hU : HasUnitProOrder A U) {V W : SmoothRep.{w} A G}
    (f : V ⟶ W) (hf : Function.Surjective f.hom.hom) :
    Function.Surjective ((invariantsFunctor A U).map f).hom := by
  let g := f.hom.hom.res U.subtype
  have hg : Function.Surjective g := by rwa [Representation.IntertwiningMap.coe_res]
  intro w
  obtain ⟨v, hv⟩ := g.invariantsMap_surjective hU hg w
  refine ⟨v, Subtype.ext ?_⟩
  rw [coe_invariantsFunctor_map_hom_apply, ← hv,
    Representation.IntertwiningMap.coe_invariantsMap_apply]
  simp [g]

/-- **Invariants preserve epimorphisms** under a compact subgroup `U` of invertible pro-order. -/
theorem preservesEpimorphisms_invariantsFunctor (hU : HasUnitProOrder A U) :
    (invariantsFunctor.{w} A U).PreservesEpimorphisms where
  preserves f _ := (ModuleCat.epi_iff_surjective _).2
    (invariantsFunctor_map_surjective U hU f ((epi_iff_surjective f).1 inferInstance))

/-- **Invariants are exact** under a compact subgroup `U` of invertible pro-order: the functor
of `U`-invariants preserves homology, being left exact and preserving epimorphisms. -/
theorem preservesHomology_invariantsFunctor (hU : HasUnitProOrder A U) :
    (invariantsFunctor.{w} A U).PreservesHomology :=
  have := preservesEpimorphisms_invariantsFunctor.{w} U hU
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- **Invariants are right exact** under a compact subgroup `U` of invertible pro-order: the functor
of `U`-invariants preserves finite colimits. -/
theorem preservesFiniteColimits_invariantsFunctor (hU : HasUnitProOrder A U) :
    PreservesFiniteColimits (invariantsFunctor.{w} A U) :=
  have := preservesHomology_invariantsFunctor.{w} U hU
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- **Invariants preserve short exact sequences** under a compact subgroup `U` of invertible
pro-order: `0 → V₁ → V₂ → V₃ → 0` exact gives `0 → V₁^U → V₂^U → V₃^U → 0` exact. -/
theorem shortExact_map_invariantsFunctor (hU : HasUnitProOrder A U)
    {S : ShortComplex (SmoothRep.{w} A G)} (hS : S.ShortExact) :
    (S.map (invariantsFunctor A U)).ShortExact :=
  have := preservesFiniteColimits_invariantsFunctor.{w} U hU
  hS.map_of_exact _

end SmoothRep

end TauCeti
