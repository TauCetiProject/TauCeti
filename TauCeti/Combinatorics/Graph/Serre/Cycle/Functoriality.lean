/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.PathGroup
public import TauCeti.Combinatorics.Graph.Serre.Path.Functoriality
import TauCeti.Data.Finsupp.MapDomain

/-!
# Functoriality of cycle classes

A morphism of Serre graphs `f : Γ.Hom Δ` pushes chains forward along its dart map. When the
chosen darts of `Γ` are exactly the darts sent to chosen darts of `Δ`, the pushforward of the
chain of a path is the chain of its image. This holds for orientations `O` of `Γ` and `O'` of
`Δ` with `f` carrying `O` into `O'`, since `O` is then the preimage of `O'`. For such
orientations the cycle class of closed paths therefore commutes with the homomorphism of reduced
path groups induced by `f`; this applies in particular to the inclusion of a based subgraph,
oriented by the preimage of an orientation of `Δ`.

For connected graphs `Γ` and `Δ` with orientations `O` and `O'`, and a morphism carrying `O` into
`O'`, the identification of the abelianized path group with the integral cycle lattice is
therefore natural.

## Main results

* `TauCeti.SerreGraph.Hom.mapDomain_chain`: pushing forward the chain of a path gives the chain of
  its image.
* `TauCeti.SerreGraph.PathGroup.coe_cycleClass_map`: for a morphism carrying an orientation into
  an orientation, cycle classes commute with the induced homomorphism.
* `TauCeti.SerreGraph.SpanningTree.coe_abelianizationEquivCycle_map`: for a morphism carrying an
  orientation into an orientation, the identification of the abelianized path group with the
  cycle lattice is natural.

## References

* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2 (tree loops), §2.2 (cellular
  boundaries of one-dimensional complexes) and §2.A, Theorem 2A.1 (the first homology group is
  the abelianized fundamental group).
* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
-/

public section

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {Δ : SerreGraph} (R : Type*) [Ring R] {O : Set Γ.E} {O' : Set Δ.E}

namespace Hom

variable (f : Γ.Hom Δ)

/-- If the chosen darts of the source are exactly the darts sent to chosen darts of the target,
pushing forward the chain of a dart gives the chain of its image. -/
theorem mapDomain_dartChain (hf : ∀ e, f.mapE e ∈ O' ↔ e ∈ O) (e : Γ.E) :
    Finsupp.mapDomain (fun d : O ↦ (⟨f.mapE d.1, (hf d.1).2 d.2⟩ : O')) (Γ.dartChain O R e) =
      Δ.dartChain O' R (f.mapE e) := by
  rw [dartChain_eq_subtypeDomain, dartChain_eq_subtypeDomain]
  exact (Finsupp.mapDomain_subtypeDomain hf _).trans (by simp [Finsupp.mapDomain_sub])

/-- If the chosen darts of the source are exactly the darts sent to chosen darts of the target,
pushing forward the chain of a path gives the chain of its image. -/
theorem mapDomain_chain (hf : ∀ e, f.mapE e ∈ O' ↔ e ∈ O) {a b : Γ.V} (p : Γ.Path a b) :
    Finsupp.mapDomain (fun d : O ↦ (⟨f.mapE d.1, (hf d.1).2 d.2⟩ : O')) (Path.chain Γ O R p) =
      Path.chain Δ O' R (f.toPrefunctor.mapPath p) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, Path.chain_cons, Path.chain_cons, Finsupp.mapDomain_add, ih,
      f.mapDomain_dartChain R hf, Hom.toPrefunctor_map_val]

end Hom

namespace PathGroup

variable {v : Γ.V} {w : Δ.V}

/-- Cycle classes commute with the homomorphisms of reduced path groups induced by graph
morphisms: for orientations `O` and `O'` and a morphism carrying `O` into `O'`, the cycle class
of the image of a reduced closed path is the pushforward of its cycle class. -/
theorem coe_cycleClass_map (f : Γ.Hom Δ) (hO : Γ.IsOrientation O) (hO' : Δ.IsOrientation O')
    (hf : Set.MapsTo f.mapE O O') (h : f.mapV v = w) (g : PathGroup Γ v) :
    ((cycleClass hO' R (map f h g)).toAdd : O' →₀ R) =
      Finsupp.mapDomain (fun d : O ↦ (⟨f.mapE d.1, hf d.2⟩ : O')) (cycleClass hO R g).toAdd := by
  -- Substitute `w` by the endpoint of the image path, so that the transport disappears.
  have h' : f.toPrefunctor.obj v = w := h
  subst h'
  rw [map_apply, coe_cycleClass_ofPath, Quiver.Path.cast_rfl_rfl, coe_cycleClass,
    ← f.mapDomain_chain R (f.mapE_mem_iff hO hO' hf)]

end PathGroup

namespace SpanningTree

/-- The identification of the abelianized path group with the integral cycle lattice is natural:
for orientations `O` and `O'` and a morphism carrying `O` into `O'`, the cycle of the image of an
element is the pushforward of its cycle. -/
theorem coe_abelianizationEquivCycle_map (T : Γ.SpanningTree) (T' : Δ.SpanningTree)
    {v : Γ.V} {w : Δ.V} (f : Γ.Hom Δ) (hO : Γ.IsOrientation O) (hO' : Δ.IsOrientation O')
    (hf : Set.MapsTo f.mapE O O') (h : f.mapV v = w)
    (x : Additive (Group.Abelianization (PathGroup Γ v))) :
    (T'.abelianizationEquivCycle w hO'
        ((Group.Abelianization.map (PathGroup.map f h)).toAdditive x) : O' →₀ ℤ) =
      Finsupp.mapDomain (fun d : O ↦ (⟨f.mapE d.1, hf d.2⟩ : O'))
        (T.abelianizationEquivCycle v hO x : O →₀ ℤ) := by
  -- Every element of the abelianization is the class of a reduced closed path.
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
  induction y using Quot.ind with
  | mk g => simpa using PathGroup.coe_cycleClass_map ℤ f hO hO' hf h g

end SpanningTree

end TauCeti.SerreGraph
