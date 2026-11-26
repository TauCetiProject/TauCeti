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
`G` has invertible pro-order (`TauCeti.HasUnitProOrder`). Then the invariants under a compact open
subgroup `U` are exact: a surjective intertwining map `f : V → W` of smooth representations maps
`V^U` onto `W^U`, since `f (e_U v) = e_U (f v)` for the averaging projector `e_U` onto the
invariants. Consequently a quotient of an admissible representation is admissible.

## Main results

* `Representation.invariants_comp_subtype_eq_map_of_surjective`: for a surjective intertwining map
  `f` and a compact subgroup `U` of invertible pro-order, `W^U = f (V^U)`.
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

/-- **Invariants of invertible pro-order are exact on the right**: a surjective intertwining map
`f` between smooth representations maps `V^U` onto `W^U` for a compact subgroup `U` of invertible
pro-order, since `f` commutes with the averaging projector `e_U`. -/
theorem invariants_comp_subtype_eq_map_of_surjective [IsSmooth ρ] [IsSmooth σ] (U : Subgroup G)
    [CompactSpace U] (hU : TauCeti.HasUnitProOrder A U) (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) :
    invariants (σ.comp U.subtype) = (invariants (ρ.comp U.subtype)).map f.toLinearMap := by
  refine le_antisymm (fun w hw ↦ ?_) ?_
  · obtain ⟨v, rfl⟩ := hf w
    refine ⟨smoothAverage (ρ.comp U.subtype) hU v,
      smoothAverage_apply_mem_invariants _ hU v, ?_⟩
    rw [IntertwiningMap.coe_toLinearMap, ← IntertwiningMap.coe_res f U.subtype,
      IntertwiningMap.map_smoothAverage, IntertwiningMap.coe_res]
    exact smoothAverage_apply_of_mem_invariants _ hU hw
  · rintro _ ⟨v, hv, rfl⟩ u
    have h : ρ u v = v := (mem_invariants _ v).1 hv u
    change σ u (f v) = f v
    rw [← f.isIntertwining, h]

/-- **Quotients of admissible representations are admissible** when every compact open subgroup
has invertible pro-order: a representation receiving a surjective intertwining map from an
admissible representation is admissible. -/
theorem IsAdmissible.of_surjective [IsAdmissible ρ]
    (hA : ∀ U : OpenSubgroup G, IsCompact (U : Set G) → TauCeti.HasUnitProOrder A U)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsAdmissible σ := by
  have := IsSmooth.of_surjective f hf
  refine ⟨fun U hU ↦ ?_⟩
  have := isCompact_iff_compactSpace.1 hU
  have h := IsAdmissible.finite_invariants (ρ := ρ) U hU
  rw [Module.Finite.iff_fg] at h ⊢
  rw [invariants_comp_subtype_eq_map_of_surjective (U : Subgroup G) (hA U hU) f hf]
  exact h.map _

end Representation
