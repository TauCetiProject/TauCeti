/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Abelianization

/-!
# Functoriality of cycle classes

A morphism of Serre graphs `f : Γ.Hom Δ` pushes chains forward along its dart map. When the
chosen darts of `Γ` are exactly the darts sent to chosen darts of `Δ` (for instance, for
orientations `O` and `O'` with `f` carrying `O` into `O'`), the pushforward of the chain of a
path is the chain of its image. Consequently the cycle class of closed paths commutes with the
homomorphism of reduced path groups induced by `f`; this applies in particular to the inclusion
of a based subgraph.

For connected graphs these compatibilities pass to the two descriptions of the abelianized path
group:

* the identification with the integral cycle lattice does not depend on the spanning tree, and it
  is natural for graph morphisms carrying chosen darts to chosen darts;
* the identification with the free abelian group on the positive darts outside a spanning tree is
  natural for morphisms carrying the tree into a tree and positive darts outside the tree to
  positive darts outside the tree. Under a change of spanning tree from `T` to `T'`, the free
  generator of a positive dart outside `T` has as free coordinates relative to `T'` the
  coordinates of the cycle class of its `T`-loop at the positive darts outside `T'`.

## Main results

* `TauCeti.SerreGraph.Hom.mapDomain_chain`: pushing forward the chain of a path gives the chain of
  its image.
* `TauCeti.SerreGraph.PathGroup.coe_cycleClass_map`: cycle classes commute with induced
  homomorphisms.
* `TauCeti.SerreGraph.SpanningTree.abelianizationEquivCycle_eq`: the identification of the
  abelianized path group with the cycle lattice does not depend on the spanning tree.
* `TauCeti.SerreGraph.SpanningTree.coe_abelianizationEquivCycle_map`: this identification is
  natural.
* `TauCeti.SerreGraph.SpanningTree.abelianizationEquivFreeAbelianGroup_map`: the free abelian
  coordinates are natural.
* `TauCeti.SerreGraph.SpanningTree.equivFinsupp_abelianizationEquivFreeAbelianGroup_symm_of`:
  change of spanning tree in free abelian coordinates.

## References

* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2 (tree loops), §2.2 (cellular
  boundaries of one-dimensional complexes) and §2.A, Theorem 2A.1 (the first homology group is
  the abelianized fundamental group).
* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
-/

public section

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {Δ : SerreGraph} (R : Type*) [Ring R] {O : Set Γ.E} {O' : Set Δ.E}

-- The chain of a dart is the restriction to the chosen darts of the unit vector of the dart minus
-- that of its reverse.
private theorem dartChain_eq_subtypeDomain {O : Set Γ.E} (e : Γ.E) :
    Γ.dartChain O R e =
      (Finsupp.single e (1 : R) - Finsupp.single (Γ.rev e) 1).subtypeDomain (· ∈ O) := by
  ext d
  simp [dartChain_apply]

namespace Hom

variable (f : Γ.Hom Δ)

-- If the chosen darts of the source are exactly the darts sent to chosen darts of the target,
-- restricting to chosen darts commutes with pushing forward along the dart map.
private theorem mapDomain_subtypeDomain (hf : ∀ e, f.mapE e ∈ O' ↔ e ∈ O) (c : Γ.E →₀ R) :
    Finsupp.mapDomain (fun d : O ↦ (⟨f.mapE d.1, (hf d.1).2 d.2⟩ : O')) (c.subtypeDomain (· ∈ O)) =
      (Finsupp.mapDomain f.mapE c).subtypeDomain (· ∈ O') := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [Finsupp.mapDomain_add, hc, hd]
  | single a r =>
    by_cases ha : a ∈ O
    · have h₁ : (Finsupp.single a r).subtypeDomain (· ∈ O) = Finsupp.single ⟨a, ha⟩ r := by
        ext b
        simp [Finsupp.single_apply, Subtype.ext_iff]
      have h₂ : (Finsupp.single (f.mapE a) r).subtypeDomain (· ∈ O') =
          Finsupp.single ⟨f.mapE a, (hf a).2 ha⟩ r := by
        ext b
        simp [Finsupp.single_apply, Subtype.ext_iff]
      rw [h₁, Finsupp.mapDomain_single, Finsupp.mapDomain_single, h₂]
    · have h₁ : (Finsupp.single a r).subtypeDomain (· ∈ O) = 0 := by
        ext b
        simp [show a ≠ b.1 from fun hb => ha (hb ▸ b.2)]
      have h₂ : (Finsupp.single (f.mapE a) r).subtypeDomain (· ∈ O') = 0 := by
        ext b
        simp [show f.mapE a ≠ b.1 from fun hb => ha ((hf a).1 (hb ▸ b.2))]
      rw [h₁, Finsupp.mapDomain_zero, Finsupp.mapDomain_single, h₂]

/-- For orientations, a graph morphism carrying the chosen darts of the source to chosen darts
of the target sends exactly the chosen darts to chosen darts. -/
theorem mapE_mem_iff (hO : Γ.IsOrientation O) (hO' : Δ.IsOrientation O')
    (hf : Set.MapsTo f.mapE O O') (e : Γ.E) : f.mapE e ∈ O' ↔ e ∈ O := by
  refine ⟨fun he => ?_, fun he => hf he⟩
  by_contra h
  exact hO'.rev_notMem_of_mem Δ _ he (f.map_rev e ▸ hf ((hO.mem_rev_iff Γ e).mpr h))

/-- If the chosen darts of the source are exactly the darts sent to chosen darts of the target,
pushing forward the chain of a dart gives the chain of its image. -/
theorem mapDomain_dartChain (hf : ∀ e, f.mapE e ∈ O' ↔ e ∈ O) (e : Γ.E) :
    Finsupp.mapDomain (fun d : O ↦ (⟨f.mapE d.1, (hf d.1).2 d.2⟩ : O')) (Γ.dartChain O R e) =
      Δ.dartChain O' R (f.mapE e) := by
  rw [dartChain_eq_subtypeDomain, dartChain_eq_subtypeDomain, f.mapDomain_subtypeDomain R hf]
  simp [Finsupp.mapDomain_sub]

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

/-- The identification of the abelianized path group with the integral cycle lattice does not
depend on the spanning tree used to construct its inverse. -/
theorem abelianizationEquivCycle_eq (T T' : Γ.SpanningTree) (v : Γ.V)
    (hO : Γ.IsOrientation O) :
    T.abelianizationEquivCycle v hO = T'.abelianizationEquivCycle v hO :=
  AddEquiv.toAddMonoidHom_injective <| by ext; simp

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

/-- The free abelian coordinates of the abelianized path group are natural: a morphism carrying a
spanning tree `T` into a spanning tree `T'`, and the positive darts outside `T` to positive darts
outside `T'`, acts on free abelian coordinates by the induced map of generators. -/
theorem abelianizationEquivFreeAbelianGroup_map (T : Γ.SpanningTree) (T' : Δ.SpanningTree)
    {v : Γ.V} {w : Δ.V} (f : Γ.Hom Δ) (hO : Γ.IsOrientation O) (hO' : Δ.IsOrientation O')
    (hT : ∀ e ∈ T.darts, f.mapE e ∈ T'.darts)
    (hf : Set.MapsTo f.mapE (O \ T.darts) (O' \ T'.darts)) (h : f.mapV v = w)
    (x : Additive (Group.Abelianization (PathGroup Γ v))) :
    T'.abelianizationEquivFreeAbelianGroup w hO'
        ((Group.Abelianization.map (PathGroup.map f h)).toAdditive x) =
      FreeAbelianGroup.map (Set.MapsTo.restrict f.mapE _ _ hf)
        (T.abelianizationEquivFreeAbelianGroup v hO x) := by
  obtain ⟨y, rfl⟩ := (T.abelianizationEquivFreeAbelianGroup v hO).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  induction y using FreeAbelianGroup.induction_on with
  | zero => simp
  | of e =>
    simpa [T.map_loop v f T' hT h] using
      T'.abelianizationEquivFreeAbelianGroup_loop w hO' (Set.MapsTo.restrict f.mapE _ _ hf e)
  | neg _ ih => simp_all
  | add _ _ ih₁ ih₂ => simp_all

/-- Change of spanning tree in free abelian coordinates: relative to a spanning tree `T'`, the
free generator of a positive dart `e` outside a spanning tree `T` has as coordinates the
coordinates of the cycle class of the `T`-loop through `e` at the positive darts outside `T'`. -/
theorem equivFinsupp_abelianizationEquivFreeAbelianGroup_symm_of (T T' : Γ.SpanningTree)
    (v : Γ.V) (hO : Γ.IsOrientation O) (e : ↥(O \ T.darts)) :
    FreeAbelianGroup.equivFinsupp _ (T'.abelianizationEquivFreeAbelianGroup v hO
        ((T.abelianizationEquivFreeAbelianGroup v hO).symm (FreeAbelianGroup.of e))) =
      Γ.cycleChordCoordinates O T'.darts ℤ (PathGroup.cycleClass hO ℤ (T.loop v e.1)).toAdd := by
  rw [abelianizationEquivFreeAbelianGroup_symm_of, equivFinsupp_abelianizationEquivFreeAbelianGroup,
    abelianizationEquivCycle_of]

end SpanningTree

end TauCeti.SerreGraph
