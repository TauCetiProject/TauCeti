/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Basic
public import TauCeti.Topology.Algebra.Module.ExtendByZero
public import TauCeti.Data.Finsupp.MapDomain

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

/-- Relabeling of polyhedra extends the ambient coordinate vector by zero. -/
theorem relabelingHomeomorph_coe_eq_extendByZero
    (x : {x : Realization K // x.1.support ∈ P}) :
    ((P.relabelingHomeomorph e hK hL x).1.1 : β → ℝ) =
      Function.ExtendByZero.continuousLinearMap ℝ e (x.1.1 : α → ℝ) := by
  rw [relabelingHomeomorph_val, Function.ExtendByZero.continuousLinearMap_apply]
  exact Finsupp.coe_mapDomain_eq_extend e.injective _

/-- Inverse relabeling of polyhedra restricts the ambient coordinate vector along the
vertex embedding. -/
theorem relabelingHomeomorph_symm_coe_eq_restriction
    (y : {y : Realization L // y.1.support ∈ P.map e}) :
    (((P.relabelingHomeomorph e hK hL).symm y).1.1 : α → ℝ) =
      Function.ExtendByZero.restriction ℝ e (y.1.1 : β → ℝ) := by
  ext i
  simp only [relabelingHomeomorph_symm_val, Finsupp.comapDomain_apply,
    Function.ExtendByZero.restriction_apply, Function.comp_apply]

end PreAbstractSimplicialComplex
