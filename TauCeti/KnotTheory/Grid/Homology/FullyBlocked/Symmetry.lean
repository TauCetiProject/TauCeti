/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.Conjugation
public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Differential.Symmetry
public import TauCeti.KnotTheory.Grid.Grading.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Grading.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.FullyBlocked.Bigraded
public import TauCeti.KnotTheory.Grid.Homology.Symmetry

/-!
# Symmetries of fully blocked grid homology

For a grid diagram `G` with an odd number of components, a cyclic permutation of the rows or of
the columns, the diagonal reflection and the half-turn each relabel grid states, intertwine the
fully blocked differentials and preserve the `(O-Maslov, Alexander)` bidegree of every state. So
they preserve the Poincaré series `P(G)` of the fully blocked grid homology `GH~(G)`.

Exchanging the `O`- and `X`-markings leaves the fully blocked differential unchanged but does not
preserve bidegrees: it moves a state of bidegree `(m, a)` to bidegree `(m - 2a - (n - 1),
-a - (n - 1))`. So it acts on `P(G)` by the conjugation symmetry `TauCeti.Bigraded.conjugate`,
followed by a shift.

## Main results

* `OddComponentGridDiagram.coeff_bigradedFullyBlockedHomologyPoincareSeries_of_intertwining`: a
  relabeling of grid states that intertwines the fully blocked differentials and moves bidegrees
  along an injective map `φ` identifies the coefficients of `P(G)` at `g` and of `P(G')` at `φ g`.
* `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining`: a
  relabeling of grid states that intertwines the fully blocked differentials and preserves
  bidegrees identifies the Poincaré series of `GH~`.
* `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_relabelRows_finRotate`,
  `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_relabelColumns_finRotate`,
  `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_transpose`,
  `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_rotate`: the cyclic
  permutations, the diagonal reflection and the half-turn preserve the Poincaré series of `GH~`.
* `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_swapMarkings`: the
  marking swap conjugates the Poincaré series of `GH~` and shifts it by `(1 - n, 1 - n)`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapters 3 and 4, and Section 7.1 for the marking swap.
-/

public section

namespace TauCeti.OddComponentGridDiagram

open GridDiagram

variable {n : ℕ}

local notation "F" => ZMod 2
local notation "P" => bigradedFullyBlockedHomologyPoincareSeries


/-- A linear equivalence of grid chains that intertwines the fully blocked differentials and moves
each grid state to a grid state whose bidegree is the image of the original bidegree under an
injective map `φ` identifies the coefficient of the Poincaré series of `GH~` in bidegree `g` with
the coefficient of the target series in bidegree `φ g`. -/
theorem coeff_bigradedFullyBlockedHomologyPoincareSeries_of_intertwining
    (G G' : OddComponentGridDiagram n) (e : GridChain F n ≃ₗ[F] GridChain F n)
    (he : ∀ c, G'.val.fullyBlockedDifferential (e c) = e (G.val.fullyBlockedDifferential c))
    (σ : GridState n → GridState n) (heσ : ∀ x, e (Finsupp.single x 1) = Finsupp.single (σ x) 1)
    {φ : ℤ × ℤ → ℤ × ℤ} (hφ : Function.Injective φ)
    (hσ : ∀ x, G'.bidegree (σ x) = φ (G.bidegree x)) (g : ℤ × ℤ) :
    (P G').coeff (φ g) = (P G).coeff g := by
  refine G.coeff_bigradedFullyBlockedHomologyPoincareSeries_of_linearEquiv
    (G.val.fullyBlockedHomologyEquivOfIntertwining G'.val e he) φ (fun g y => ?_) g
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    rw [bigradedFullyBlockedHomologyProjection_mk, fullyBlockedHomologyEquivOfIntertwining_apply_mk,
      fullyBlockedHomologyEquivOfIntertwining_apply_mk, bigradedFullyBlockedHomologyProjection_mk]
    congr 1
    ext1
    simp only [fullyBlockedCyclesEquivOfIntertwining_apply]
    exact G.map_bigradedChainInclusion_bigradedChainProjection_of_injective G' e.toLinearMap hφ
      (fun x y hy => by
        rw [LinearEquiv.coe_coe, heσ, Finsupp.single_apply, ite_eq_right_iff]
        rintro rfl
        exact absurd (hσ x) hy)
      g z

/-- A linear equivalence of grid chains that intertwines the fully blocked differentials and moves
each grid state to a grid state of the same bidegree identifies the Poincaré series of fully
blocked homology. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining
    (G G' : OddComponentGridDiagram n) (e : GridChain F n ≃ₗ[F] GridChain F n)
    (he : ∀ c, G'.val.fullyBlockedDifferential (e c) = e (G.val.fullyBlockedDifferential c))
    (σ : GridState n → GridState n) (heσ : ∀ x, e (Finsupp.single x 1) = Finsupp.single (σ x) 1)
    (hσ : ∀ x, G'.bidegree (σ x) = G.bidegree x) :
    P G = P G' :=
  AddMonoidAlgebra.coeff_injective (Finsupp.ext fun g =>
    (coeff_bigradedFullyBlockedHomologyPoincareSeries_of_intertwining G G' e he σ heσ
      Function.injective_id hσ g).symm)

variable (G : OddComponentGridDiagram n)

/-- A cyclic permutation of the rows preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_relabelRows_finRotate :
    P (G.relabelRows (finRotate n)) = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.relabelRowsEquiv (finRotate n))
    (by simpa only [val_relabelRows] using
      G.val.fullyBlockedDifferential_relabelRows_finRotate_apply) _
    (fun x => GridChain.relabelRowsEquiv_single _ x 1)
    (G.bidegree_relabelRows_finRotate)).symm

/-- A cyclic permutation of the columns preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_relabelColumns_finRotate :
    P (G.relabelColumns (finRotate n)) = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.relabelColumnsEquiv (finRotate n))
    (by simpa only [val_relabelColumns] using
      G.val.fullyBlockedDifferential_relabelColumns_finRotate_apply) _
    (fun x => GridChain.relabelColumnsEquiv_single _ x 1)
    (G.bidegree_relabelColumns_finRotate)).symm

/-- The diagonal reflection preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_transpose : P G.transpose = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.transposeEquiv F n)
    (LinearMap.congr_fun G.val.fullyBlockedDifferential_transpose) _
    (fun x => GridChain.transposeEquiv_single x 1) G.bidegree_transpose).symm

/-- The half-turn preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_rotate : P G.rotate = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.halfTurnEquiv F) G.val.fullyBlockedDifferential_rotate_halfTurnEquiv _
    (fun x => GridChain.halfTurnEquiv_single F x 1) G.bidegree_rotate_halfTurn).symm

/-- **Conjugation symmetry of `GH~` under the marking swap.** Exchanging the `O`- and
`X`-markings of a grid of size `n` leaves the fully blocked complex unchanged, and moves a grid
state of bidegree `(m, a)` to bidegree `(m - 2a - (n - 1), -a - (n - 1))`. So the Poincaré series
of `GH~` of the swapped diagram is the conjugate series `(m, a) ↦ (m - 2a, -a)`, shifted by
`(1 - n, 1 - n)`. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_swapMarkings :
    P G.swapMarkings =
      AddMonoidAlgebra.single (1 - (n : ℤ), 1 - (n : ℤ)) 1 * Bigraded.conjugate (P G) := by
  set c : ℤ × ℤ := (1 - (n : ℤ), 1 - (n : ℤ))
  have key := coeff_bigradedFullyBlockedHomologyPoincareSeries_of_intertwining G G.swapMarkings
    (LinearEquiv.refl F _) (fun d => by rw [val_swapMarkings,
      GridDiagram.fullyBlockedDifferential_swapMarkings]; rfl) id (fun _ => rfl)
    ((add_left_injective c).comp Bigraded.conjugationEquiv.injective) (fun x => by
      rw [id, bidegree_swapMarkings]
      ext <;> simp [c] <;> ring)
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun h => ?_)
  have hh := key (Bigraded.conjugationEquiv (h - c))
  simp only [Function.comp_apply, Bigraded.conjugationEquiv_conjugationEquiv,
    sub_add_cancel] at hh
  rw [hh, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, Bigraded.coeff_conjugate,
    neg_add_eq_sub]

end TauCeti.OddComponentGridDiagram
