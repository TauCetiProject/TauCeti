/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Realization
public import TauCeti.AlgebraicTopology.Sphere.Contractible
import Mathlib.Analysis.Convex.Contractible

/-!
# Distinguishing combinatorial balls and spheres

The weak polyhedron of a combinatorial ball is contractible, whereas that of a combinatorial
sphere is not. Consequently a complex cannot be both a combinatorial ball and a combinatorial
sphere, even if the two asserted dimensions differ. This makes the ball-versus-sphere choice
in a manifold's vertex-link condition unambiguous.

The statements use the actual subpolyhedron in an arbitrary ambient weak realization.
Unused ambient vertices have no effect, and the ambient vertex type need not be finite.
The topological models are supplied by `IsCombinatorialBall.nonempty_homeomorph_closedBall`
and `IsCombinatorialSphere.nonempty_homeomorph_sphere`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (combinatorial balls, spheres, and vertex links).
-/

public section

open AbstractSimplicialComplex Metric

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {P : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {n m : ℕ}

/-- The weak polyhedron of a combinatorial ball is contractible in any ambient realization
containing the complex. This includes the one-point zero-ball. -/
theorem IsCombinatorialBall.contractibleSpace (h : IsCombinatorialBall P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    ContractibleSpace {x : Realization A // x.1.support ∈ P} := by
  obtain ⟨e⟩ := h.nonempty_homeomorph_closedBall hA
  let := Metric.contractibleSpace_closedBall
    (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1) zero_le_one
  exact e.contractibleSpace

/-- The weak polyhedron of a combinatorial sphere is not contractible, including the
two-point zero-sphere. -/
theorem IsCombinatorialSphere.not_contractibleSpace (h : IsCombinatorialSphere P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    ¬ ContractibleSpace {x : Realization A // x.1.support ∈ P} := by
  obtain ⟨e⟩ := h.nonempty_homeomorph_sphere hA
  intro hc
  let := hc
  exact TauCeti.not_contractibleSpace_sphere e.symm.contractibleSpace

/-- A combinatorial sphere cannot be a combinatorial ball of any dimension. In particular,
the spherical and ball cases of the vertex-link condition are mutually exclusive. -/
theorem IsCombinatorialSphere.not_isCombinatorialBall (h : IsCombinatorialSphere P n) :
    ¬ IsCombinatorialBall P m := by
  intro hb
  exact h.not_contractibleSpace (A := ⊤) (le_top P)
    (hb.contractibleSpace (A := ⊤) (le_top P))

end PreAbstractSimplicialComplex
