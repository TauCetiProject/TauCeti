/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Degree
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
import TauCeti.Topology.Homotopy.MappingPath.PathFibration

/-!
# Serre's axiom on Eilenberg--Mac Lane spaces in all degrees

Let `P` be a Serre class of abelian groups closed under direct sums and `G` a group such that
every `K(G, 1)` space has its positive-degree integral homology in `P`. Then so does every
`K(G, n)` space, `n ≥ 1` (`TauCeti.IsEilenbergMacLaneSpace.prop_singularHomology_of_one`). No
hypothesis of CW type is made on the spaces.

The induction goes through the based path fibration `K(G, n + 1) → E → K(G, n + 2)`: its total
space `E`, the paths ending at the base point, is contractible, and its fibres are homotopy
equivalent to the loop space, a `K(G, n + 1)` space. The homology of the base of a Serre fibration
with contractible total space lies in `P` as soon as the homology of its fibres does
(`TauCeti.TopCat.prop_singularHomology_of_contractibleSpace`).

This is the input on Eilenberg--Mac Lane spaces of Serre's Hurewicz theorem modulo a class.

## Main results

* `CategoryTheory.ObjectProperty.SatisfiesEilenbergMacLaneAxiom`: Serre's axiom on
  Eilenberg--Mac Lane spaces through a given degree, the hypothesis on the class in Serre's
  Hurewicz theorem modulo a class, unfolded by
  `CategoryTheory.ObjectProperty.satisfiesEilenbergMacLaneAxiom_iff`.
* `TauCeti.IsEilenbergMacLaneSpace.prop_singularHomology_of_one`: for a Serre class closed under
  direct sums, Serre's axiom for `K(G, 1)` spaces gives it for all `K(G, n)` spaces.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Spectral Sequences in Algebraic Topology*, Chapter 1 (Serre classes).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace CategoryTheory.ObjectProperty

/-- **Serre's axiom on Eilenberg--Mac Lane spaces through degree `k`**, in the form taken by
Serre's Hurewicz theorem modulo `P`: for every `G ∈ P` and `m ≥ 1` there is a property `Q ≤ P`
of `ℤ`-modules, closed under isomorphisms and direct sums and containing zero, which contains
the integral homology in degrees `1, …, k` of every `K(G, m)` space. -/
def SatisfiesEilenbergMacLaneAxiom (P : ObjectProperty (ModuleCat.{0} ℤ)) (k : ℕ) : Prop :=
  ∀ (G : Type) [CommGroup G], P (ModuleCat.of ℤ (Additive G)) → ∀ m : ℕ,
    ∃ Q : ObjectProperty (ModuleCat.{0} ℤ), Q ≤ P ∧ Q.IsClosedUnderIsomorphisms ∧
      Q.ContainsZero ∧ (∀ J : Type, Q.IsClosedUnderColimitsOfShape (Discrete J)) ∧
      ∀ (Z : Type) [TopologicalSpace Z] (z : Z), TauCeti.IsEilenbergMacLaneSpace G (m + 1) Z z →
        ∀ q, q ≠ 0 → q ≤ k →
          Q (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
            (TopCat.of Z))

/-- Unfolding `ObjectProperty.SatisfiesEilenbergMacLaneAxiom`: the class `P` satisfies Serre's
axiom through degree `k` exactly when every `G ∈ P` and `m` admit a property `Q ≤ P`, closed
under isomorphisms and direct sums and containing zero, which contains the integral homology in
degrees `1, …, k` of every `K(G, m + 1)` space. -/
theorem satisfiesEilenbergMacLaneAxiom_iff (P : ObjectProperty (ModuleCat.{0} ℤ)) (k : ℕ) :
    P.SatisfiesEilenbergMacLaneAxiom k ↔
      ∀ (G : Type) [CommGroup G], P (ModuleCat.of ℤ (Additive G)) → ∀ m : ℕ,
        ∃ Q : ObjectProperty (ModuleCat.{0} ℤ), Q ≤ P ∧ Q.IsClosedUnderIsomorphisms ∧
          Q.ContainsZero ∧ (∀ J : Type, Q.IsClosedUnderColimitsOfShape (Discrete J)) ∧
          ∀ (Z : Type) [TopologicalSpace Z] (z : Z),
            TauCeti.IsEilenbergMacLaneSpace G (m + 1) Z z → ∀ q, q ≠ 0 → q ≤ k →
              Q (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
                (TopCat.of Z)) :=
  Iff.rfl

end CategoryTheory.ObjectProperty

namespace TauCeti

variable (P : ObjectProperty (ModuleCat.{0} ℤ)) [P.IsSerreClass]

/-- **Serre's axiom on Eilenberg--Mac Lane spaces, from degree one to all degrees.** Let `P` be a
Serre class closed under direct sums and `G` a group such that every `K(G, 1)` space has its
positive-degree integral homology in `P`. Then so does every `K(G, n + 1)` space. The induction
runs through the based path fibration `K(G, n + 1) → E → K(G, n + 2)`, whose total space `E` is
contractible. -/
theorem IsEilenbergMacLaneSpace.prop_singularHomology_of_one
    [∀ J : Type, P.IsClosedUnderColimitsOfShape (Discrete J)] {G : Type} [Group G]
    (h₁ : ∀ (Z : Type) [TopologicalSpace Z] (z : Z), IsEilenbergMacLaneSpace G 1 Z z →
      ∀ q, q ≠ 0 → P (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Z)))
    (n : ℕ) {Z : Type} [TopologicalSpace Z] {z : Z} (hZ : IsEilenbergMacLaneSpace G (n + 1) Z z)
    {q : ℕ} (hq : q ≠ 0) :
    P (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of Z)) := by
  induction n generalizing Z z q with
  | zero => exact h₁ Z z hZ q hq
  | succ n ih =>
    have := hZ.pathConnectedSpace
    -- The based path fibration `E → Z`, sending a path ending at `z` to its starting point.
    let p : TopCat.of (MappingPathFiber (ContinuousMap.id Z) z) ⟶ TopCat.of Z :=
      TopCat.ofHom (MappingPathFiber.proj _ z)
    have hp : TopCat.serreFibrations p :=
      (MappingPathFiber.isHurewiczFibration_proj.{0} _ _).mem_serreFibrations
    -- Every fibre is homotopy equivalent to the loop space, a `K(G, n + 1)` space.
    have hfib (b : Z) := hZ.exists_fiber_mappingPathFiberProj (ContinuousMap.id Z) z b
    exact TopCat.prop_singularHomology_of_contractibleSpace P P le_rfl hp hq
      (fun b ↦ (hfib b).choose_spec.pathConnectedSpace)
      (fun b q' hq' _ ↦ ih (hfib b).choose_spec hq')

end TauCeti
