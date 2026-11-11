/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.NonTorsion

/-!
# The invariant `τ` of a knot grid diagram

For a knot grid `G` over a commutative ring `K` of characteristic two, the unblocked grid
homology `GH⁻(G)` is a `K[U]`-module graded by the Alexander grading, on which `U` lowers the
degree by one. Its invariant `τ(G)` is minus
the largest Alexander degree of a homogeneous element that is not `K[U]`-torsion
(`GridDiagram.IsKnot.tau`). This is the definition of the
concordance invariant `τ` of Ozsváth--Stipsicz--Szabó, read on a single grid diagram. Its
independence of the diagram presenting a knot follows from the invariance of `GH⁻` under grid moves
(`GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_movesTo`), which is not part of this file.

The definition is through `InternalGrading.supNonTorsionDegree`, the supremum of the non-torsion
degrees. When `GH⁻(G)` is not a torsion module that supremum is attained
(`GridDiagram.IsKnot.isGreatest_nonTorsionDegrees_neg_tau`), so `-τ(G)` is the Alexander degree
of a homogeneous non-torsion class and every such class has degree at most `-τ(G)`
(`GridDiagram.IsKnot.le_neg_tau`). If `GH⁻(G)` were torsion the supremum would be that of the
empty set, which Mathlib takes to be `0` (`GridDiagram.IsKnot.tau_eq_zero_of_isTorsion`).

Two transfer principles are recorded, which are the algebraic content of the inequalities
satisfied by `τ` under chain maps between grid complexes. Knot grids whose homologies are
isomorphic as Alexander-graded `K[U]`-modules have the same invariant
(`GridDiagram.IsKnot.UnblockedHomologyIsomorphic.tau_eq`); this is how the invariance of `GH⁻`
descends to `τ`. A homogeneous `K[U]`-linear map of Alexander degree `δ` from `GH⁻(G)` to
`GH⁻(G')` with a left inverse up to multiplication by a power of `U` satisfies
`τ(G') ≤ τ(G) - δ`, provided `GH⁻(G)` is not torsion
(`GridDiagram.IsKnot.tau_le_tau_sub_of_comp_eq_X_pow_smul`); the crossing change maps of
Ozsváth--Stipsicz--Szabó, Chapter 6, supply such pairs of maps in degrees `0` and `-1`, and the
resulting two inequalities bound the change of `τ` under a crossing change.

Finally, over a field, when the `X`-marking state `G.X` receives an even number of counted
rectangles from every grid state and has the largest Alexander grading of any grid state,
`τ(G) = -A(G.X)`
(`GridDiagram.IsKnot.tau_eq_neg_alexanderℤ_X`). The standard torus knot grids satisfy both
hypotheses; their values of `τ` are in `TorusLink/Tau.lean`.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.tau`: minus the maximal Alexander degree of a homogeneous
  non-torsion element of `GH⁻(G)`.

## Main results

* `TauCeti.GridDiagram.IsKnot.isGreatest_nonTorsionDegrees_neg_tau` and
  `TauCeti.GridDiagram.IsKnot.le_neg_tau`: `-τ(G)` is the greatest
  non-torsion Alexander degree when `GH⁻(G)` is not torsion, and an upper bound for the
  non-torsion degrees without that hypothesis.
* `TauCeti.GridDiagram.IsKnot.tau_eq_zero_of_isTorsion`: `τ(G) = 0` when `GH⁻(G)` is torsion.
* `TauCeti.GridDiagram.IsKnot.UnblockedHomologyIsomorphic.tau_eq`: isomorphic Alexander-graded
  unblocked homologies have the same invariant.
* `TauCeti.GridDiagram.IsKnot.tau_le_tau_sub_of_comp_eq_X_pow_smul`: a
  homogeneous map of degree `δ` out of a non-torsion `GH⁻(G)` with a left inverse up to a power
  of `U` gives `τ(G') ≤ τ(G) - δ`.
* `TauCeti.GridDiagram.IsKnot.tau_eq_neg_alexanderℤ_X`: `τ(G)` from the `X`-marking state when
  that state is a parity-protected cycle of maximal Alexander grading.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Chapter 6, for the definition of `τ` as minus the maximal
  Alexander grading of a homogeneous non-torsion element of `GH⁻`, and for the crossing change
  maps whose composites are multiplication by `U`.
-/

public section

open Polynomial

namespace TauCeti

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

section Ring

variable (K : Type*) [CommRing K] [CharP K 2]

/-- **The invariant `τ` of a knot grid diagram**: minus the largest Alexander degree of a
homogeneous element of the unblocked grid homology `GH⁻(G)` that is not `K[U]`-torsion.

The supremum is attained as soon as `GH⁻(G)` is not a torsion module
(`isGreatest_nonTorsionDegrees_neg_tau`); if `GH⁻(G)` is torsion the value is `0`, the supremum
of the empty set. It is an invariant of the presented knot: knot grids connected by grid moves
have the same `τ` (`tau_eq_of_movesTo`, in `Homology/Invariance.lean`). This is the grid
definition of the concordance invariant `τ` of Ozsváth--Stipsicz--Szabó. -/
noncomputable def tau : ℤ :=
  letI := hG.unblockedHomologyModule K;
  -(hG.alexanderUnblockedHomologyGrading K).supNonTorsionDegree

/-- `τ(G)` is minus the supremal non-torsion Alexander degree of `GH⁻(G)`. -/
theorem tau_def :
    letI := hG.unblockedHomologyModule K
    hG.tau K = -(hG.alexanderUnblockedHomologyGrading K).supNonTorsionDegree :=
  (rfl)

/-- If `GH⁻(G)` is a torsion `K[U]`-module, then `τ(G) = 0`: there is no homogeneous non-torsion
class, and the supremum of the empty set of degrees is `0`. -/
theorem tau_eq_zero_of_isTorsion :
    letI := hG.unblockedHomologyModule K
    Module.IsTorsion K[X] (G.unblockedHomology K) → hG.tau K = 0 := by
  let _ := hG.unblockedHomologyModule K
  intro hT
  rw [tau_def, InternalGrading.supNonTorsionDegree_def,
    Set.not_nonempty_iff_eq_empty.mp fun h ↦
      (InternalGrading.nonTorsionDegrees_nonempty_iff _).mp h hT,
    Int.csSup_empty, neg_zero]

section Transfer

variable {m : ℕ} {G' : GridDiagram m} (hG' : G'.IsKnot)

variable {hG hG' K} in
/-- Knot grids whose unblocked homologies are isomorphic as Alexander-graded `K[U]`-modules have
the same invariant `τ`. -/
theorem UnblockedHomologyIsomorphic.tau_eq (h : hG.UnblockedHomologyIsomorphic hG' K) :
    hG.tau K = hG'.tau K := by
  let _ := hG.unblockedHomologyModule K
  let _ := hG'.unblockedHomologyModule K
  obtain ⟨e, he⟩ := unblockedHomologyIsomorphic_def.mp h
  rw [tau_def, tau_def, InternalGrading.supNonTorsionDegree_eq_of_linearEquiv e he]

/-- **Comparison of `τ` along a map with a left inverse up to a power of `U`.** Let `f` be a
`K[U]`-linear map from `GH⁻(G)` to `GH⁻(G')`, homogeneous of Alexander degree `δ`, and let `g`
be a `K[U]`-linear map back with `g ∘ f = U ^ k`. If `GH⁻(G)` is not torsion, then
`τ(G') ≤ τ(G) - δ`: the image of a homogeneous non-torsion class of degree `-τ(G)` is a
homogeneous non-torsion class of degree `-τ(G) + δ`. -/
theorem tau_le_tau_sub_of_comp_eq_X_pow_smul {δ : ℤ} (k : ℕ) :
    letI := hG.unblockedHomologyModule K
    letI := hG'.unblockedHomologyModule K
    ∀ (f : G.unblockedHomology K →ₗ[K[X]] G'.unblockedHomology K)
      (g : G'.unblockedHomology K →ₗ[K[X]] G.unblockedHomology K),
      LinearMap.IsHomogeneous f (hG.alexanderUnblockedHomologyGrading K).piece
        (hG'.alexanderUnblockedHomologyGrading K).piece δ →
      (∀ y, g (f y) = (Polynomial.X ^ k : K[X]) • y) →
      ¬Module.IsTorsion K[X] (G.unblockedHomology K) →
      hG'.tau K ≤ hG.tau K - δ := by
  let _ := hG.unblockedHomologyModule K
  let _ := hG'.unblockedHomologyModule K
  intro f g hf hgf hT
  have h := InternalGrading.supNonTorsionDegree_add_le
    ((InternalGrading.nonTorsionDegrees_nonempty_iff _).mpr hT)
    (hG'.bddAbove_nonTorsionDegrees_alexanderUnblockedHomologyGrading K) hf
    (Submodule.comap_torsion_of_comp_eq_smul (f := f) (g := g)
      (pow_mem Polynomial.X_mem_nonZeroDivisors k) hgf).le
  rw [tau_def, tau_def]
  omega

end Transfer

/-- Every Alexander degree of a homogeneous non-torsion class of `GH⁻(G)` is at most `-τ(G)`. -/
theorem le_neg_tau {a : ℤ} :
    letI := hG.unblockedHomologyModule K
    a ∈ (hG.alexanderUnblockedHomologyGrading K).nonTorsionDegrees → a ≤ -hG.tau K := by
  let _ := hG.unblockedHomologyModule K
  intro ha
  rw [tau_def, neg_neg]
  exact InternalGrading.le_supNonTorsionDegree
    (hG.bddAbove_nonTorsionDegrees_alexanderUnblockedHomologyGrading K) ha

/-- When `GH⁻(G)` is not a torsion `K[U]`-module, `-τ(G)` is the greatest Alexander degree of a
homogeneous non-torsion class: there is such a class in degree `-τ(G)`, and none in any higher
degree. -/
theorem isGreatest_nonTorsionDegrees_neg_tau :
    letI := hG.unblockedHomologyModule K
    ¬Module.IsTorsion K[X] (G.unblockedHomology K) →
      IsGreatest (hG.alexanderUnblockedHomologyGrading K).nonTorsionDegrees (-hG.tau K) := by
  let _ := hG.unblockedHomologyModule K
  intro hT
  rw [tau_def, neg_neg]
  exact InternalGrading.isGreatest_supNonTorsionDegree
    ((InternalGrading.nonTorsionDegrees_nonempty_iff _).mpr hT)
    (hG.bddAbove_nonTorsionDegrees_alexanderUnblockedHomologyGrading K)

end Ring

section Field

variable (K : Type*) [Field K] [CharP K 2]

/-- **`τ` from the `X`-marking state.** Over a field, if every grid state has an even number of
counted rectangles into the `X`-marking state `G.X`, and `G.X` has the largest Alexander grading
of any grid state, then `τ(G) = -A(G.X)`. -/
theorem tau_eq_neg_alexanderℤ_X
    (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card)
    (h : ∀ x : GridState n, hG.toOddComponentGridDiagram.alexanderℤ x ≤
      hG.toOddComponentGridDiagram.alexanderℤ G.X) :
    hG.tau K = -hG.toOddComponentGridDiagram.alexanderℤ G.X := by
  rw [tau_def, hG.supNonTorsionDegree_alexanderUnblockedHomologyGrading_eq hX h]

end Field

end GridDiagram.IsKnot

end TauCeti
