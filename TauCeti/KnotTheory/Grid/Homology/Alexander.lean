/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Homology
public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
public import TauCeti.KnotTheory.Grid.Homology.Unblocked

/-!
# The Alexander grading of unblocked grid homology

For a grid diagram `G` with an odd number of link components, the unblocked grid chain module
`GC⁻` is the internal direct sum of its Alexander pieces over the coefficient ring `R`, and the
unblocked grid differential `∂⁻` preserves the Alexander grading
(`TauCeti.OddComponentGridDiagram.alexanderChainMinusGrading`). The grading therefore descends to
the homology `ker ∂⁻ ⧸ im ∂⁻`, which is the unblocked grid homology `GH⁻`
(`TauCeti.GridDiagram.unblockedHomologyIso`): a class has Alexander degree `a` when it is the class
of a cycle all of whose monomials `V^e · x` have `A(x) - |e| = a`.

Each variable `V_c` has Alexander degree `-1` on `GC⁻` and on the concrete homology quotient.
On the grid homology of a knot every variable acts as `U`
(`TauCeti.GridDiagram.IsKnot.X_smul_unblockedHomology`). Transporting that action to the concrete
quotient will make `U` lower Alexander degree by one. The resulting graded module will support
the definition of `τ` using `TauCeti.InternalGrading.supNonTorsionDegree`.

The grading is stated on the concrete homology `ker ∂⁻ ⧸ im ∂⁻` rather than on Mathlib's
categorical homology `GH⁻`: the homogeneous pieces are modules over `R` only, since the variables
move the Alexander grading, and the concrete quotient carries its `R`-module structure.

## Main definitions

* `TauCeti.OddComponentGridDiagram.alexanderHomologyGrading`: the Alexander grading of
  `ker ∂⁻ ⧸ im ∂⁻`.

## Main results

* `TauCeti.OddComponentGridDiagram.mem_alexanderHomologyGrading_piece_iff`: a class has Alexander
  degree `a` exactly when it is the class of a cycle of Alexander degree `a`.
* `TauCeti.OddComponentGridDiagram.X_smul_mem_alexanderHomologyGrading_piece`: each variable
  `V_c` lowers the Alexander grading of grid homology by one.

## References

The Alexander grading of `GH⁻` and the action of `U` in Alexander degree `-1` are those of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4; the definition of `τ`
from them is in Chapter 6.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- **The Alexander grading of unblocked grid homology**: the grading of `ker ∂⁻ ⧸ im ∂⁻` induced
by the Alexander grading of `GC⁻`, which `∂⁻` preserves. Its degree-`a` piece consists of the
classes of the cycles of Alexander degree `a`. -/
noncomputable def alexanderHomologyGrading :
    InternalGrading R
      ((G.1.unblockedDifferential R).homology
        (G.1.unblockedDifferential_comp_self_eq_zero R)) :=
  (G.alexanderChainMinusGrading R).homology
    (G.isHomogeneous_unblockedDifferential_alexanderChainMinusGrading R)
    (G.1.unblockedDifferential_comp_self_eq_zero R)

variable {G R}

/-- A class in `ker ∂⁻ ⧸ im ∂⁻` has Alexander degree `a` exactly when it is the class of a cycle of
Alexander degree `a`. -/
theorem mem_alexanderHomologyGrading_piece_iff {a : ℤ}
    {y : (G.1.unblockedDifferential R).homology
      (G.1.unblockedDifferential_comp_self_eq_zero R)} :
    y ∈ (G.alexanderHomologyGrading R).piece a ↔
      ∃ z : LinearMap.ker (G.1.unblockedDifferential R),
        (z : GridChainMinus R n) ∈ G.alexanderChainMinusPiece R a ∧
          (G.1.unblockedDifferential R).homologyπ
            (G.1.unblockedDifferential_comp_self_eq_zero R) z = y := by
  rw [alexanderHomologyGrading, InternalGrading.mem_homology_piece_iff,
    alexanderChainMinusGrading_piece]

/-- **The variable `V_c` lowers the Alexander grading of grid homology by one.** -/
theorem X_smul_mem_alexanderHomologyGrading_piece (i : Fin n) {a : ℤ}
    {y : (G.1.unblockedDifferential R).homology
      (G.1.unblockedDifferential_comp_self_eq_zero R)}
    (hy : y ∈ (G.alexanderHomologyGrading R).piece a) :
    (X i : MvPolynomial (Fin n) R) • y ∈ (G.alexanderHomologyGrading R).piece (a - 1) := by
  rw [sub_eq_add_neg]
  refine (G.alexanderChainMinusGrading R).smul_mem_homology_piece _
    (G.1.unblockedDifferential_comp_self_eq_zero R) (fun p x hx ↦ ?_) hy
  rw [alexanderChainMinusGrading_piece] at hx ⊢
  exact G.X_smul_mem_alexanderChainMinusPiece i hx

end TauCeti.OddComponentGridDiagram
