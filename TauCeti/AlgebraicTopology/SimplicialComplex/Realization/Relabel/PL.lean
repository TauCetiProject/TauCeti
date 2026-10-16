/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Coordinates
public import TauCeti.Topology.PL.Map

/-!
# Descending PL maps through vertex relabelings

A map between injectively relabeled polyhedra with a PL ambient coordinate formula
induces a map between the original polyhedra with a PL coordinate formula.
Extend the input by zero, apply the given formula, and restrict the output coordinates.
For a homeomorphism, applying the same result to its inverse transports the inverse
PL formula as well.

This removes the auxiliary vertex labels used to compare polyhedra by stellar moves,
so that their PL identifications can be used on the original sphere and ball links.
The polyhedra may lie in arbitrary containing weak realizations. No finiteness,
compactness, or global comparison with the coordinate topology is required, and unused
ambient vertices contribute no points.

The coordinate transport uses `relabelingHomeomorph` and its extension and restriction
formulas, together with `TauCeti.IsPLOn.comp`.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapters 1–2.
-/

public section

open Set Function TauCeti

namespace PreAbstractSimplicialComplex

open AbstractSimplicialComplex

variable {α β κ ν : Type*} [DecidableEq κ] [DecidableEq ν]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
  {A : AbstractSimplicialComplex κ} {B : AbstractSimplicialComplex ν}
  (P : PreAbstractSimplicialComplex α) (Q : PreAbstractSimplicialComplex β)
  (e : α ↪ κ) (d : β ↪ ν)
  (hK : P ≤ K.toPreAbstractSimplicialComplex)
  (hL : Q ≤ L.toPreAbstractSimplicialComplex)
  (hA : P.map e ≤ A.toPreAbstractSimplicialComplex)
  (hB : Q.map d ≤ B.toPreAbstractSimplicialComplex)

/-- A PL coordinate formula for a map of relabeled polyhedra descends to
the original polyhedra. Its explicit formula extends the input coordinates by zero
and restricts the output coordinates. For a homeomorphism, use the theorem with its
inverse and the two relabelings exchanged to descend the inverse formula. -/
theorem isPLOn_restriction_comp_extendByZero
    (h : {x : Realization A // x.1.support ∈ P.map e} →
      {y : Realization B // y.1.support ∈ Q.map d})
    (f : (κ → ℝ) → (ν → ℝ))
    (hf : IsPLOn f
      (range (fun x : {x : Realization A // x.1.support ∈ P.map e} => (x.1.1 : κ → ℝ))))
    (hcoord : ∀ x : {x : Realization A // x.1.support ∈ P.map e},
      f (x.1.1 : κ → ℝ) = (h x).1.1) :
    IsPLOn
        (Function.ExtendByZero.restriction ℝ d ∘ f ∘
          Function.ExtendByZero.continuousLinearMap ℝ e)
        (range (fun x : {x : Realization K // x.1.support ∈ P} => (x.1.1 : α → ℝ))) ∧
      ∀ x : {x : Realization K // x.1.support ∈ P},
        (Function.ExtendByZero.restriction ℝ d ∘ f ∘
          Function.ExtendByZero.continuousLinearMap ℝ e) (x.1.1 : α → ℝ) =
            (((Q.relabelingHomeomorph d hL hB).symm ∘ h ∘
              P.relabelingHomeomorph e hK hA) x).1.1 := by
  have hmap : MapsTo (Function.ExtendByZero.continuousLinearMap ℝ e)
      (range (fun x : {x : Realization K // x.1.support ∈ P} => (x.1.1 : α → ℝ)))
      (range (fun x : {x : Realization A // x.1.support ∈ P.map e} => (x.1.1 : κ → ℝ))) := by
    rw [P.range_coe_map_eq_image_extendByZero e hK hA]
    exact mapsTo_image _ _
  refine ⟨(isPLOn_continuousAffineMap
    (Function.ExtendByZero.restriction ℝ d).toContinuousAffineMap univ).comp
      (hf.comp (isPLOn_continuousAffineMap
        (Function.ExtendByZero.continuousLinearMap ℝ e).toContinuousAffineMap _) hmap)
      (fun _ _ => mem_univ _), ?_⟩
  intro x
  simp only [Function.comp_apply,
    ← relabelingHomeomorph_coe_eq_extendByZero P e hK hA x,
    hcoord, relabelingHomeomorph_symm_coe_eq_restriction]

end PreAbstractSimplicialComplex
