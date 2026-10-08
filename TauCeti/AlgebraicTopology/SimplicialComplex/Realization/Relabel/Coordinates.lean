/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Basic
public import TauCeti.Topology.Algebra.Module.ExtendByZero

/-!
# Linear coordinate formulas for relabeling polyhedra

The homeomorphism of polyhedra induced by an injective vertex relabeling has ambient
continuous linear formulas in both directions: extension by zero and coordinate
restriction. These formulas apply to arbitrary ambient vertex sets and weak realizations,
including precomplexes that leave vertices unused. No global comparison between the weak
and coordinate topologies is required.

Together with `TauCeti.isPLOn_extendByZero_iff`, the formulas transport PL coordinate
maps through changes of ambient vertex sets. In particular, relabeling does not lose the
PL regularity of identifications obtained from stellar moves.

Reference: Rourke–Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

open Set

namespace PreAbstractSimplicialComplex

open AbstractSimplicialComplex

variable {α β : Type*} [DecidableEq β]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
  (P : PreAbstractSimplicialComplex α) (e : α ↪ β)
  (hK : P ≤ K.toPreAbstractSimplicialComplex)
  (hL : P.map e ≤ L.toPreAbstractSimplicialComplex)

/-- Injective relabeling of polyhedra and its inverse are restrictions of ambient
continuous linear coordinate maps. Restriction is a left inverse to extension on the
entire coordinate space; unused target coordinates are zero on the polyhedron. -/
theorem exists_continuousLinearMap_relabelingHomeomorph :
    ∃ (A : (α → ℝ) →L[ℝ] (β → ℝ)) (B : (β → ℝ) →L[ℝ] (α → ℝ)),
      Function.LeftInverse B A ∧
      (∀ x : {x : Realization K // x.1.support ∈ P},
        ((P.relabelingHomeomorph e hK hL x).1.1 : β → ℝ) = A (x.1.1 : α → ℝ)) ∧
      (∀ y : {y : Realization L // y.1.support ∈ P.map e},
        (((P.relabelingHomeomorph e hK hL).symm y).1.1 : α → ℝ) =
          B (y.1.1 : β → ℝ)) := by
  let A := Function.ExtendByZero.continuousLinearMap ℝ e
  let B : (β → ℝ) →L[ℝ] (α → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)
  refine ⟨A, B, ?_, ?_, ?_⟩
  · intro x
    ext i
    simp [A, B, e.injective]
  · intro x
    ext j
    rw [relabelingHomeomorph_val]
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      simp [A, e.injective]
    · simp [A, Finsupp.mapDomain_of_notMem_range _ _ hj,
        Function.extend_apply' _ _ _ hj]
  · intro y
    ext i
    simp [B]

end PreAbstractSimplicialComplex
