/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Quotient
public import TauCeti.Topology.Homotopy.GenLoop.Contractible
public import TauCeti.Topology.Homotopy.GenLoop.Covering
public import TauCeti.Topology.Homotopy.GenLoop.Loop
public import TauCeti.Topology.PathSpace.Moore.Covering
public import TauCeti.Topology.PathSpace.Moore.Homotopy
public import Mathlib.Topology.Homotopy.Affine

/-!
# Higher loop spaces of tori are contractible

Let `L` be a discrete additive subgroup of a real topological vector space `E`, for instance a
lattice `ℤⁿ ⊆ ℝⁿ`, so that the orbit space `E / L = AddAction.orbitRel.Quotient L E` is a torus
`Tⁿ` when `L` is a full lattice. The orbit projection `E → E / L` is a covering map, so in dimension
at least two it identifies the generalized loops of `E / L` with those of `E`
(`IsCoveringMap.genLoopHomeomorph`), and these contract onto the constant loop along straight
lines. Hence, at every basepoint:

* the space `Ω^ N (E / L) x` of generalized loops is contractible for every nontrivial index type
  `N` (`AddSubgroup.contractibleSpace_genLoop_orbitRelQuotient`);
* the double loop space `Ω²(E / L) = Ω (Ω (E / L) x) (Path.refl x)` is contractible
  (`AddSubgroup.contractibleSpace_loopSpace_loopSpace_orbitRelQuotient`).

In particular `Ω²Tⁿ` is path connected, as `π₂(Tⁿ) = 0`, and it is contractible, not merely weakly
contractible: a torus is the basic aspherical space whose double loop space has the homology of a
point. These statements are for the fixed-interval loop spaces with the compact-open topology.

The same holds for the double Moore loop space `Ω_1 Ω_x (E / L)`, the strictly associative model:
the double Moore loop map of the covering `E → E / L` is a homeomorphism
(`IsCoveringMap.doubleMooreLoopSpaceHomeomorph`), and the straight-line contraction of `E` onto
`e`, which fixes `e`, contracts the double Moore loops of `E`
(`TauCeti.MooreLoopSpace.contractibleSpace_of_homotopicRel`). The single Moore loop space of a
torus is not contractible: its path components are the elements of `π₁`.

## Main results

* `AddSubgroup.contractibleSpace_genLoop_orbitRelQuotient`: `Ω^ N (E / L) x` is contractible for
  nontrivial `N`.
* `AddSubgroup.contractibleSpace_loopSpace_loopSpace_orbitRelQuotient`: `Ω²(E / L)` is
  contractible.
* `AddSubgroup.contractibleSpace_mooreLoopSpace_mooreLoopSpace_orbitRelQuotient`: the double Moore
  loop space of `E / L` is contractible.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 4.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 3.41.
-/

public section

open scoped Topology.Homotopy

namespace AddSubgroup

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] (L : AddSubgroup E) [DiscreteTopology L]

/-- **The generalized loops of a torus are contractible** in dimension at least two: for a discrete
subgroup `L` of a real topological vector space `E` and a nontrivial index type `N`, the space of
generalized loops `Ω^ N (E / L) x` is contractible at every basepoint. -/
theorem contractibleSpace_genLoop_orbitRelQuotient {N : Type*} [Nontrivial N]
    (x : AddAction.orbitRel.Quotient L E) :
    ContractibleSpace (Ω^ N (AddAction.orbitRel.Quotient L E) x) := by
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective x
  exact (L.isAddQuotientCoveringMap_quotientMk.isCoveringMap.genLoopHomeomorph e).symm
    |>.contractibleSpace

/-- **The double loop space of a torus is contractible**: for a discrete subgroup `L` of a real
topological vector space `E`, the double loop space `Ω (Ω (E / L) x) (Path.refl x)` is
contractible at every basepoint. -/
theorem contractibleSpace_loopSpace_loopSpace_orbitRelQuotient
    (x : AddAction.orbitRel.Quotient L E) :
    ContractibleSpace (Ω (Ω (AddAction.orbitRel.Quotient L E) x) (Path.refl x)) :=
  have := L.contractibleSpace_genLoop_orbitRelQuotient (N := Fin 2) x
  ((GenLoop.homeomorphOfUnique (Fin 1)).symm.trans (GenLoop.genLoopLoopHomeomorph x 1))
    |>.contractibleSpace

/-- **The double Moore loop space of a torus is contractible**: for a discrete subgroup `L` of a
real topological vector space `E`, the double Moore loop space `Ω_1 Ω_x (E / L)` is contractible at
every basepoint. -/
theorem contractibleSpace_mooreLoopSpace_mooreLoopSpace_orbitRelQuotient
    (x : AddAction.orbitRel.Quotient L E) :
    ContractibleSpace
      (TauCeti.MooreLoopSpace (TauCeti.MooreLoopSpace (AddAction.orbitRel.Quotient L E) x) 1) := by
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective x
  -- `E` contracts onto `e` along straight lines, which fix `e`; so do its double Moore loops.
  have hE : (ContinuousMap.id E).HomotopicRel (ContinuousMap.const E e) {e} :=
    ⟨{ toHomotopy := .affine _ _
       prop' t z hz := by
         rw [Set.mem_singleton_iff] at hz
         subst hz
         simp }⟩
  have := TauCeti.MooreLoopSpace.contractibleSpace_of_homotopicRel
    (TauCeti.MooreLoopSpace.homotopicRel_id_const_one hE)
  exact (IsCoveringMap.doubleMooreLoopSpaceHomeomorph (p := ⟨_, continuous_quotient_mk'⟩)
    L.isAddQuotientCoveringMap_quotientMk.isCoveringMap e).symm.contractibleSpace

end AddSubgroup
