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
degree by one; it is finitely generated when `K` is Noetherian. Its invariant `τ(G)` is minus
the largest Alexander degree of a homogeneous element that is not `K[U]`-torsion
(`GridDiagram.IsKnot.tau`). This is the definition of the
concordance invariant `τ` of Ozsváth--Stipsicz--Szabó, read on a single grid diagram: the
statement that `τ(G)` does not change under grid moves is the invariance of `GH⁻`, which is not
part of this file, so nothing here is a statement about the knot a diagram presents.

The definition is through `InternalGrading.supNonTorsionDegree`, the supremum of the non-torsion
degrees. Over a Noetherian `K`, when `GH⁻(G)` is not a torsion module that supremum is attained
(`GridDiagram.IsKnot.isGreatest_nonTorsionDegrees_neg_tau`), so `-τ(G)` is the Alexander degree
of a homogeneous non-torsion class and every such class has degree at most `-τ(G)`
(`GridDiagram.IsKnot.le_neg_tau`). If `GH⁻(G)` were torsion the supremum would be that of the
empty set, which Mathlib takes to be `0`.

Two transfer principles are recorded, which are the algebraic content of the inequalities
satisfied by `τ` under chain maps between grid complexes. A graded `K[U]`-isomorphism of
Alexander degree zero between the homologies of two knot grids identifies their invariants
(`GridDiagram.IsKnot.tau_eq_of_linearEquiv`); this is how an invariance theorem for `GH⁻` will
descend to `τ`. A homogeneous `K[U]`-linear map of Alexander degree `δ` from `GH⁻(G)` to
`GH⁻(G')` with a left inverse up to multiplication by a power of `U` satisfies
`τ(G') ≤ τ(G) - δ`, provided `K` is Noetherian and `GH⁻(G)` is not torsion
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
  `TauCeti.GridDiagram.IsKnot.le_neg_tau`: over a Noetherian `K`, `-τ(G)` is the greatest
  non-torsion Alexander degree when `GH⁻(G)` is not torsion, and an upper bound for the
  non-torsion degrees without that hypothesis.
* `TauCeti.GridDiagram.IsKnot.tau_eq_of_linearEquiv`: a degree-zero graded `K[U]`-isomorphism
  of unblocked homologies identifies the invariants.
* `TauCeti.GridDiagram.IsKnot.tau_eq_of_semilinearMap`: so does a grading-preserving bijection
  that is semilinear along a ring homomorphism compatible with the evaluation `V_j ↦ U`.
* `TauCeti.GridDiagram.IsKnot.tau_le_tau_sub_of_comp_eq_X_pow_smul`: over a Noetherian `K`, a
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

Over a Noetherian `K`, the supremum is attained as soon as `GH⁻(G)` is not a torsion module
(`isGreatest_nonTorsionDegrees_neg_tau`); if `GH⁻(G)` is torsion the value is `0`, the supremum
of the empty set. This is the invariant of the diagram; it is the
concordance invariant `τ` of the presented knot once the invariance of `GH⁻` under grid moves is
available (`tau_eq_of_linearEquiv`). -/
noncomputable def tau : ℤ :=
  letI := hG.unblockedHomologyModule K;
  -(hG.alexanderUnblockedHomologyGrading K).supNonTorsionDegree

/-- `τ(G)` is minus the supremal non-torsion Alexander degree of `GH⁻(G)`. -/
theorem tau_def :
    letI := hG.unblockedHomologyModule K
    hG.tau K = -(hG.alexanderUnblockedHomologyGrading K).supNonTorsionDegree :=
  (rfl)

section Transfer

variable {m : ℕ} {G' : GridDiagram m} (hG' : G'.IsKnot)

/-- A graded `K[U]`-isomorphism of Alexander degree zero between the unblocked homologies of two
knot grids identifies their invariants `τ`. -/
theorem tau_eq_of_linearEquiv :
    letI := hG.unblockedHomologyModule K
    letI := hG'.unblockedHomologyModule K
    ∀ e : G.unblockedHomology K ≃ₗ[K[X]] G'.unblockedHomology K,
      LinearMap.IsHomogeneous e.toLinearMap (hG.alexanderUnblockedHomologyGrading K).piece
        (hG'.alexanderUnblockedHomologyGrading K).piece 0 →
      hG.tau K = hG'.tau K := by
  let _ := hG.unblockedHomologyModule K
  let _ := hG'.unblockedHomologyModule K
  intro e he
  rw [tau_def, tau_def, InternalGrading.supNonTorsionDegree_eq_of_linearEquiv e he]

/-- A bijection between the unblocked homologies of two knot grids identifies their invariants
`τ` if it preserves the Alexander grading and is semilinear along a ring homomorphism `σ` of the
polynomial rings that commutes with the evaluation `V_j ↦ U`, such as a renaming of the variables.
Such a map is then a graded `K[U]`-isomorphism of degree zero. -/
theorem tau_eq_of_semilinearMap {σ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin m) K}
    (hσ : ∀ p, MvPolynomial.aeval (fun _ ↦ (Polynomial.X : K[X])) (σ p) =
      MvPolynomial.aeval (fun _ ↦ (Polynomial.X : K[X])) p)
    (f : G.unblockedHomology K →ₛₗ[σ] G'.unblockedHomology K) (hf : Function.Bijective f)
    (hA : ∀ a y, y ∈ (hG.alexanderUnblockedHomologyGrading K).piece a →
      f y ∈ (hG'.alexanderUnblockedHomologyGrading K).piece a) :
    hG.tau K = hG'.tau K := by
  let _ := hG.unblockedHomologyModule K
  let _ := hG'.unblockedHomologyModule K
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩⟩
  let f' : G.unblockedHomology K →ₗ[K[X]] G'.unblockedHomology K :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun q y ↦ by
        obtain ⟨p, rfl⟩ := MvPolynomial.aeval_const_X_surjective (Fin n) K q
        rw [hG.aeval_smul_unblockedHomology, LinearMap.map_smulₛₗ, RingHom.id_apply, ← hσ,
          hG'.aeval_smul_unblockedHomology] }
  refine hG.tau_eq_of_linearEquiv K hG' (LinearEquiv.ofBijective f' hf)
    (LinearMap.isHomogeneous_def.mpr fun a y hy ↦ ?_)
  rw [add_zero]
  exact hA a y hy

variable [IsNoetherianRing K]

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
    (Submodule.comap_torsion_le_of_comp_eq_smul (pow_mem Polynomial.X_mem_nonzeroDivisors k) hgf)
  rw [tau_def, tau_def]
  omega

end Transfer

variable [IsNoetherianRing K]

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
