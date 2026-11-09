/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.Int
public import TauCeti.GroupTheory.Amenable.Prod
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Amenability of commutative groups

Every commutative topological group is amenable, with no hypothesis on its rank, its torsion or
its topology.

A finite subset `s` of a commutative group `G` is the image of the standard generators under
the homomorphism `(s → Multiplicative ℤ) →* G` sending `n` to `∏ x ∈ s, x ^ (n x).toAdd`. This
is Mathlib's `MonoidHom.noncommPiCoprod` of the maps `zpowersHom G x`, whose commutation
hypothesis holds because `G` is commutative. Its source is a finite power of the integers with
the discrete topology, so it is amenable by amenability of the integers and of finite products,
and the homomorphism is continuous for every topology on `G`. Every finite subset of `G`
therefore lies in the image of a continuous homomorphism from an amenable group, which is the
directed-union criterion `TauCeti.Amenable.of_forall_finset_subset_range`.

For an additive commutative group `A`, the instance applies to `Multiplicative A`, which carries
the topology of `A` and is a topological group when `A` is a topological additive group.

## Main results

* `TauCeti.Amenable.of_commGroup`: every commutative topological group is amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every commutative topological group is amenable, whatever its group topology. -/
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G := by
  classical
  have hcomm (s : Finset G) : Pairwise fun x y : s => ∀ m n : Multiplicative ℤ,
      Commute (zpowersHom G x m) (zpowersHom G y n) := fun _ _ _ _ _ => .all _ _
  -- For a finite set `s`, the homomorphism `n ↦ ∏ x ∈ s, x ^ (n x).toAdd` out of `s → ℤ`.
  let φ (s : Finset G) : (s → Multiplicative ℤ) →ₜ* G :=
    ⟨MonoidHom.noncommPiCoprod (fun x : s => zpowersHom G x) (hcomm s),
      continuous_of_discreteTopology⟩
  refine .of_forall_finset_subset_range φ fun s =>
    ⟨s, fun x hx => ⟨Pi.mulSingle ⟨x, hx⟩ (.ofAdd 1), ?_⟩⟩
  simp [φ, MonoidHom.noncommPiCoprod_mulSingle]

end TauCeti
