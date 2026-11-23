/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Homology
public import TauCeti.KnotTheory.Grid.Homology.FullyBlockedBigraded
public import TauCeti.KnotTheory.Grid.Homology.HatBigrading
public import TauCeti.KnotTheory.Grid.Homology.PartiallyBlocked.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import TauCeti.KnotTheory.Grid.XHomotopy.Grading

/-!
# The bigrading of partially blocked grid homology

For a grid diagram `G` with an odd number of components and a set `S` of columns, the chains of
`GC⁻` blocked for `S` form a homogeneous submodule for the `(O-Maslov, Alexander)` bigrading
(`TauCeti.OddComponentGridDiagram.isHomogeneous_blockedChains`), so the partially blocked grid
homology `TauCeti.GridDiagram.partiallyBlockedHomology S` inherits the bigrading
(`TauCeti.OddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading`).

Blocking one more column `t` on the component of a blocked column `i` splits the homology along a
homotopy from `V_t` to `V_i`, which has bidegree `(-1, -1)`; so the bidegree-`g` piece after
blocking `t` has the rank of the bidegree-`g` piece plus that of the bidegree-`(g + (1, 1))`
piece before
(`TauCeti.OddComponentGridDiagram.rank_bigradedPartiallyBlockedHomologyGrading_piece_insert`).

The identifications of partially blocked homology with fully blocked homology `GH~` (every column
blocked) and, for a knot, with simply blocked homology `G-hat` (one column blocked) have degree
zero for these bigradings.

## Main definitions

* `TauCeti.OddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading`: the
  `(O-Maslov, Alexander)` grading of partially blocked grid homology.

## Main results

* `TauCeti.OddComponentGridDiagram.mem_bigradedPartiallyBlockedHomologyGrading_piece_iff`: a class
  is homogeneous of bidegree `g` exactly when it is the class of a chain of bidegree `g`.
* `TauCeti.OddComponentGridDiagram.rank_bigradedPartiallyBlockedHomologyGrading_piece_insert`:
  the graded doubling when one more column of a blocked component is blocked.
* `TauCeti.OddComponentGridDiagram.isHomogeneous_partiallyBlockedHomologyUnivEquiv`: the
  identification with `GH~` has degree zero.
* `TauCeti.GridDiagram.IsKnot.isHomogeneous_partiallyBlockedHomologySingletonEquiv`: for a knot,
  the identification with `G-hat` has degree zero.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 4.6.
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), Section 2.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

local notation "F" => ZMod 2

/-! ### Blocked chains form a homogeneous submodule -/

/-- The chains blocked for a set of columns form a homogeneous submodule of `GC⁻`: a monomial
involves a blocked variable whatever its bidegree. -/
theorem isHomogeneous_blockedChains (R : Type*) [CommRing R] (S : Finset (Fin n)) :
    DirectSum.SetLike.IsHomogeneous (G.bigradedChainMinusGrading R).piece
      (GridDiagram.blockedChains R S) := by
  intro g c hc
  rw [GridDiagram.mem_blockedChains_iff] at hc ⊢
  intro x
  rw [mem_ideal_span_X_image]
  exact fun m hm => mem_ideal_span_X_image.mp (hc x) m
    (G.support_decompose_bigradedChainMinusGrading_subset R c g x hm)

/-! ### The bigrading of partially blocked homology -/

/-- Over `𝔽₂`, the unblocked differential, viewed as an `𝔽₂`-linear map, has bidegree
`(-1, 0)`. -/
private theorem isHomogeneous_restrictScalars_unblockedDifferential :
    LinearMap.IsHomogeneous ((G.val.unblockedDifferential F).restrictScalars F)
      (G.bigradedChainMinusGrading F).piece (G.bigradedChainMinusGrading F).piece (-(1, 0)) :=
  LinearMap.isHomogeneous_def.2 fun _ _ hc =>
    (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading F).map_mem hc

private theorem isHomogeneous_restrictScalars_blockedChains (S : Finset (Fin n)) :
    DirectSum.SetLike.IsHomogeneous (G.bigradedChainMinusGrading F).piece
      ((GridDiagram.blockedChains F S).restrictScalars F) :=
  fun g _ hc => G.isHomogeneous_blockedChains F S g hc

/-- The internal `(O-Maslov, Alexander)` grading of the partially blocked grid homology of the
columns `S`: its bidegree-`g` piece consists of the classes of the chains of `GC⁻` of bidegree
`g` whose boundaries are blocked. -/
noncomputable def bigradedPartiallyBlockedHomologyGrading (S : Finset (Fin n)) :
    InternalGrading F (G.val.partiallyBlockedHomology S) (ℤ × ℤ) :=
  (G.bigradedChainMinusGrading F).quotientHomology
    G.isHomogeneous_restrictScalars_unblockedDifferential
    G.val.restrictScalars_unblockedDifferential_comp_self_eq_zero
    (G.val.blockedChains_le_comap_unblockedDifferential S)
    (G.isHomogeneous_restrictScalars_blockedChains S)

/-- A class of partially blocked homology is homogeneous of bidegree `g` exactly when it is the
class of a chain of bidegree `g` whose boundary is blocked. -/
theorem mem_bigradedPartiallyBlockedHomologyGrading_piece_iff {S : Finset (Fin n)} {g : ℤ × ℤ}
    {y : G.val.partiallyBlockedHomology S} :
    y ∈ (G.bigradedPartiallyBlockedHomologyGrading S).piece g ↔
      ∃ c ∈ G.bigradedChainMinusPiece F g,
        ∃ hc : G.val.unblockedDifferential F c ∈ GridDiagram.blockedChains F S,
          Submodule.Quotient.mk
            ⟨Submodule.Quotient.mk c, (Submodule.mk_mem_ker_mapQ_iff c).mpr hc⟩ = y := by
  rw [bigradedPartiallyBlockedHomologyGrading, InternalGrading.mem_quotientHomology_piece_iff,
    bigradedChainMinusGrading_piece]
  simp only [LinearMap.quotientHomologyClass_def]
  -- The `𝔽₂`-linear restrictions of the differential and of the blocked chains have the same
  -- values and members as the polynomial-linear originals.
  rfl

/-- **Blocking one more column of a blocked component, bigraded.** If the column `i` is blocked,
`t` is not, and `t` and `i` lie on the same link component, then the bidegree-`g` piece of the
partially blocked homology after blocking `t` has the rank of the bidegree-`g` piece plus that of
the bidegree-`(g + (1, 1))` piece before. The second copy is the image of a homotopy from `V_t` to
`V_i` of bidegree `(-1, -1)`. -/
theorem rank_bigradedPartiallyBlockedHomologyGrading_piece_insert {S : Finset (Fin n)}
    {i t : Fin n} (hti : G.val.componentPerm.SameCycle t i) (hi : i ∈ S) (ht : t ∉ S) (g : ℤ × ℤ) :
    Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading (insert t S)).piece g) =
      Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading S).piece g) +
        Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading S).piece (g + (1, 1))) := by
  obtain ⟨H, hH, hHg⟩ := G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle F hti
  have e := (G.bigradedChainMinusGrading F).quotientHomologyProdPieceEquiv
    (h := H.restrictScalars F) (v := DistribSMul.toLinearMap F (GridChainMinus F n) (X t))
    (s := -(1, 1)) G.isHomogeneous_restrictScalars_unblockedDifferential
    G.val.restrictScalars_unblockedDifferential_comp_self_eq_zero
    (G.val.blockedChains_le_comap_unblockedDifferential S)
    (G.isHomogeneous_restrictScalars_blockedChains S)
    (G.val.blockedChains_le_comap_unblockedDifferential (insert t S))
    (G.isHomogeneous_restrictScalars_blockedChains (insert t S))
    (GridDiagram.blockedChains_mono (Finset.subset_insert t S))
    (fun m => GridDiagram.X_smul_mem_blockedChains (Finset.mem_insert_self t S) m)
    (fun _ hx => GridDiagram.exists_sub_X_smul_mem_blockedChains hx)
    (fun _ hm => GridDiagram.map_mem_blockedChains _ hm)
    (fun m => (G.val.unblockedDifferential F).map_smul _ m)
    (fun _ hm => GridDiagram.mem_blockedChains_of_X_smul_mem ht hm)
    (fun m => by
      have hm : G.val.unblockedDifferential F (H m) + H (G.val.unblockedDifferential F m) =
          (X t + X i : MvPolynomial (Fin n) F) • m := congr($hH m)
      simp only [LinearMap.restrictScalars_apply, DistribSMul.toLinearMap_apply,
        Submodule.restrictScalars_mem]
      rw [hm, add_smul, add_sub_cancel_left]
      exact GridDiagram.X_smul_mem_blockedChains hi m)
    (LinearMap.isHomogeneous_def.2 fun _ _ hc => by
      rw [bigradedChainMinusGrading_piece] at hc ⊢
      simpa only [sub_eq_add_neg, LinearMap.restrictScalars_apply] using hHg hc) g
  unfold bigradedPartiallyBlockedHomologyGrading
  rw [← e.rank_eq, rank_prod', sub_neg_eq_add]

/-! ### Comparison with fully blocked homology -/

/-- The identification of the partially blocked homology of every column with fully blocked
grid homology `GH~` has degree zero for the `(O-Maslov, Alexander)` bigradings. -/
theorem isHomogeneous_partiallyBlockedHomologyUnivEquiv :
    LinearMap.IsHomogeneous G.val.partiallyBlockedHomologyUnivEquiv.toLinearMap
      (G.bigradedPartiallyBlockedHomologyGrading Finset.univ).piece
      G.bigradedFullyBlockedHomologyGrading.piece 0 :=
  InternalGrading.isHomogeneous_of_quotientHomologyClass _ _ _ _ _ fun _ c hcp hc => by
    rw [bigradedChainMinusGrading_piece] at hcp
    rw [add_zero, LinearEquiv.coe_coe, LinearMap.quotientHomologyClass_def,
      GridDiagram.partiallyBlockedHomologyUnivEquiv_mk _ c hc,
      bigradedFullyBlockedHomologyGrading_piece]
    exact G.mem_bigradedFullyBlockedHomologyPiece_iff_exists.2
      ⟨_, G.mapRange_constantCoeff_mem_range_bigradedChainInclusion hcp, rfl⟩

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

local notation "F" => ZMod 2

/-- For a knot grid, the identification of the partially blocked homology of one column `i` with
simply blocked grid homology `G-hat` has degree zero for the `(O-Maslov, Alexander)`
bigradings. -/
theorem isHomogeneous_partiallyBlockedHomologySingletonEquiv (i : Fin n) :
    LinearMap.IsHomogeneous (hG.partiallyBlockedHomologySingletonEquiv i).toLinearMap
      (hG.toOddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading {i}).piece
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading F i).piece 0 :=
  InternalGrading.isHomogeneous_of_quotientHomologyClass _ _ _ _ _ fun _ c hcp hc => by
    rw [bigradedChainMinusGrading_piece] at hcp
    rw [add_zero, LinearEquiv.coe_coe, LinearMap.quotientHomologyClass_def,
      hG.partiallyBlockedHomologySingletonEquiv_mk i c hc,
      bigradedHatHomologyGrading_piece]
    refine oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece _ F i ?_
    rw [LinearEquiv.apply_symm_apply]
    exact hG.toOddComponentGridDiagram.simplyBlockedSpecialization_mem_bigradedChainHatPiece i hcp

end TauCeti.GridDiagram.IsKnot
