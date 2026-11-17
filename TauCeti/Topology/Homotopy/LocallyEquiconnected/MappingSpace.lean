/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.LocallyEquiconnected.Basic
public import TauCeti.Topology.MappingSpace.FreeLoop

/-!
# Mapping spaces into locally equiconnected spaces

Let `K` be a compact space and `X` a locally equiconnected space, with an equiconnecting map `l`
on a neighbourhood `W` of the diagonal. Two maps `f, g : K → X` that are pointwise `W`-close are
joined by the pointwise path `t ↦ (k ↦ l (f k, g k) t)`. By compactness of `K` the pointwise
`W`-close pairs form a neighbourhood of the diagonal of the compact-open mapping space `C(K, X)`,
and the pointwise path depends continuously on `(f, g, t)`. So `C(K, X)` is locally
equiconnected (`TauCeti.instLocallyEquiconnectedSpaceContinuousMap`), and in particular locally
path-connected and semilocally simply connected.

For the free loop space `C(S¹, X)` this makes the path components open, so the contractible free
loops `𝓛₀X` form an open subspace (`TauCeti.isOpen_contractibleLoops`), which is again locally
equiconnected. Hence `𝓛₀X` is locally path-connected and semilocally simply connected, the
hypotheses under which every subgroup of its fundamental group has a corresponding covering space
(`TauCeti.UniversalCover.subgroupCover`). Capped Floer theory uses such a covering of `𝓛₀X`,
whose fibres are the classes of caps of a loop.

## Main results

* `TauCeti.instLocallyEquiconnectedSpaceContinuousMap`: `C(K, X)` is locally equiconnected for
  compact `K` and locally equiconnected `X`.
* `TauCeti.isOpen_contractibleLoops`: the contractible free loops are open in a locally
  path-connected free loop space.
* `TauCeti.locallyEquiconnectedSpace_contractibleLoops`: the contractible free loops of a
  locally equiconnected space form a locally equiconnected space.

## References

* R. H. Fox, *On fibre spaces. II*, Bull. Amer. Math. Soc. 49 (1943), 733–735.
-/

public section

open Set Function Topology unitInterval

namespace TauCeti

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]

/-- Mapping spaces out of a compact space into a locally equiconnected space are locally
equiconnected, through pointwise connecting paths. -/
instance instLocallyEquiconnectedSpaceContinuousMap [CompactSpace K] [LocallyCompactPair K X]
    [LocallyEquiconnectedSpace X] : LocallyEquiconnectedSpace C(K, X) := by
  classical
  obtain ⟨W, l, h⟩ := LocallyEquiconnectedSpace.exists_isEquiconnecting (X := X)
  -- The pairs of maps that are pointwise `W`-close.
  let W' : Set (C(K, X) × C(K, X)) := {p | ∀ k, (p.1 k, p.2 k) ∈ W}
  have hW' : IsOpen W' := isOpen_forall_prodMk_mem continuous_id <| h.isOpen.preimage
    (by fun_prop : Continuous fun q : (C(K, X) × C(K, X)) × K => (q.1.1 q.2, q.1.2 q.2))
  -- The pointwise connecting path, as a continuous map on `W' × I`.
  have hG : Continuous fun q : (W' × I) × K => l ((q.1.1 : C(K, X) × C(K, X)).1 q.2,
      (q.1.1 : C(K, X) × C(K, X)).2 q.2) q.1.2 :=
    h.continuousOn.comp_continuous
      (f := fun q : (W' × I) × K => (((q.1.1 : C(K, X) × C(K, X)).1 q.2,
        (q.1.1 : C(K, X) × C(K, X)).2 q.2), q.1.2)) (by fun_prop)
      fun q => ⟨q.1.1.2 q.2, trivial⟩
  let L : C(W' × I, C(K, X)) := ContinuousMap.curry ⟨_, hG⟩
  refine ⟨W', fun p t => if hp : p ∈ W' then L (⟨p, hp⟩, t) else p.1,
    { isOpen := hW'
      diagonal_subset := ?_
      continuousOn := ?_
      apply_zero := fun p hp => ?_
      apply_one := fun p hp => ?_
      apply_self := fun f t => ?_ }⟩
  · rintro ⟨f, g⟩ (rfl : f = g) k
    exact h.mk_self_mem (f k)
  · refine continuousOn_iff_continuous_domRestrict.mpr ?_
    refine (L.continuous.comp (f := fun q : ↥(W' ×ˢ (univ : Set I)) => (⟨q.1.1, q.2.1⟩, q.1.2))
      (by fun_prop)).congr fun ⟨⟨p, t⟩, hp, _⟩ => ?_
    simp [Set.domRestrict, hp]
  · ext k
    simp [hp, L, h.apply_zero _ (hp k)]
  · ext k
    simp [hp, L, h.apply_one _ (hp k)]
  · have hf : (f, f) ∈ W' := fun k => h.mk_self_mem (f k)
    ext k
    simp [hf, L, h.apply_self]

variable (X) in
/-- In a locally path-connected free loop space, the contractible free loops form an open set:
they are the union of the path components of the constant loops, and path components are open. -/
theorem isOpen_contractibleLoops [LocallyPathConnectedSpace C(Circle, X)] :
    IsOpen (contractibleLoops X) := by
  have : contractibleLoops X = ⋃ x, pathComponent (ContinuousMap.const Circle x) := by
    ext γ
    simp only [mem_contractibleLoops_iff, mem_iUnion]
    exact exists_congr fun _ => ⟨Joined.symm, Joined.symm⟩
  rw [this]
  exact isOpen_iUnion fun x => IsOpen.pathComponent _

/-- The contractible free loops `𝓛₀X` of a locally equiconnected space form a locally
equiconnected space; in particular `𝓛₀X` is locally path-connected and semilocally simply
connected. -/
instance locallyEquiconnectedSpace_contractibleLoops [LocallyEquiconnectedSpace X] :
    LocallyEquiconnectedSpace (contractibleLoops X) :=
  (isOpen_contractibleLoops X).locallyEquiconnectedSpace

end TauCeti
