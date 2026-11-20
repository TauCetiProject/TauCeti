/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.Stabilization
public import TauCeti.Algebra.Module.GradedModule.Homology
public import TauCeti.KnotTheory.Grid.Homology.FullyBlockedBigraded
public import TauCeti.KnotTheory.Grid.Homology.PartiallyBlocked
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
import TauCeti.KnotTheory.Grid.XHomotopy.Grading
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# The bigraded series of fully blocked knot-grid homology

For a knot grid `G` of size `n`, fully blocked grid homology is simply blocked grid homology
tensored with `n - 1` copies of the two-dimensional bigraded space `W`, which has one generator
in bidegree `(0, 0)` and one in bidegree `(-1, -1)`. At the level of Poincaré series this reads

`P(GH~(G)) = P(G-hat(G)) * W ^ (n - 1)`

(`TauCeti.GridDiagram.IsKnot.bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_pow`), with both
series in the `(O-Maslov, Alexander)` bidegrees over `𝔽₂`. It refines the dimension count
`dim GH~ = 2 ^ (n - 1) dim G-hat` (`TauCeti.GridDiagram.IsKnot.finrank_fullyBlockedHomology`) to
each bidegree. In particular the two series have the same class modulo `W`-stabilization
(`TauCeti.Bigraded.stableMk_mul_W_pow`).

The proof grades the partially blocked complexes of `TauCeti.GridDiagram.partiallyBlockedHomology`,
which interpolate between `G-hat` (one blocked column) and `GH~` (every column blocked). The
chains blocked for a set of columns form a homogeneous submodule of `GC⁻`
(`TauCeti.OddComponentGridDiagram.isHomogeneous_blockedChains`), so partially blocked homology
inherits the bigrading (`TauCeti.OddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading`).
Blocking one more column `t` on the component of a blocked column `i` splits the homology along a
homotopy from `V_t` to `V_i`, which has bidegree `(-1, -1)`; so the bidegree-`g` piece after
blocking `t` has the rank of the bidegree-`g` piece plus that of the bidegree-`(g + (1, 1))`
piece before
(`TauCeti.OddComponentGridDiagram.rank_bigradedPartiallyBlockedHomologyGrading_piece_insert`).
This is the coefficient formula `(P * W)(g) = P(g) + P(g + (1, 1))` of `TauCeti.Bigraded.W`.

## Main definitions

* `TauCeti.OddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading`: the
  `(O-Maslov, Alexander)` grading of partially blocked grid homology.

## Main results

* `TauCeti.OddComponentGridDiagram.mem_bigradedPartiallyBlockedHomologyGrading_piece_iff`: a class
  is homogeneous of bidegree `g` exactly when it is the class of a chain of bidegree `g`.
* `TauCeti.OddComponentGridDiagram.rank_bigradedPartiallyBlockedHomologyGrading_piece_insert`:
  the graded doubling when one more column of a blocked component is blocked.
* `TauCeti.GridDiagram.IsKnot.bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_pow`: the
  Poincaré series of `GH~` of a knot grid of size `n` is that of `G-hat` times `W ^ (n - 1)`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 4.6 (Proposition 4.6.15: `GH~ ≅ G-hat ⊗ W ^ (n - 1)` as
  bigraded vector spaces).
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), Section 2.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

local notation "F" => ZMod 2

/-! ### Blocked chains form a homogeneous submodule -/

/-- Every monomial of a homogeneous component of a chain of `GC⁻` is a monomial of the chain. -/
private theorem support_decompose_bigradedChainMinusGrading_subset (R : Type*) [CommRing R]
    (c : GridChainMinus R n) (g : ℤ × ℤ) (x : GridState n) :
    ((DirectSum.decompose (G.bigradedChainMinusGrading R).piece c g : GridChainMinus R n)
      x).support ⊆ (c x).support := by
  classical
  intro e he
  have hmem (q : ℤ × ℤ) {f : Fin n →₀ ℕ}
      (hf : f ∈ ((DirectSum.decompose (G.bigradedChainMinusGrading R).piece c q :
        GridChainMinus R n) x).support) : G.monomialBidegree x f = q := by
    have hq : (DirectSum.decompose (G.bigradedChainMinusGrading R).piece c q :
        GridChainMinus R n) ∈ G.bigradedChainMinusPiece R q := by
      rw [← bigradedChainMinusGrading_piece]
      exact (DirectSum.decompose (G.bigradedChainMinusGrading R).piece c q).2
    rw [mem_bigradedChainMinusPiece] at hq
    exact hq x f hf
  rw [MvPolynomial.mem_support_iff] at he ⊢
  rw [← DirectSum.sum_support_decompose (G.bigradedChainMinusGrading R).piece c,
    Finsupp.finsetSum_apply, MvPolynomial.coeff_sum,
    Finset.sum_eq_single_of_mem g (DFinsupp.mem_support_iff.mpr fun h0 => he (by simp [h0]))]
  · exact he
  · intro q _ hqg
    by_contra hne
    exact hqg ((hmem q (MvPolynomial.mem_support_iff.mpr hne)).symm.trans
      (hmem g (MvPolynomial.mem_support_iff.mpr he)))

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
    LinearMap.IsHomogeneous ((G.1.unblockedDifferential F).restrictScalars F)
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
    InternalGrading F (G.1.partiallyBlockedHomology S) (ℤ × ℤ) :=
  (G.bigradedChainMinusGrading F).quotientHomology
    G.isHomogeneous_restrictScalars_unblockedDifferential
    G.1.restrictScalars_unblockedDifferential_comp_self_eq_zero
    (G.1.blockedChains_le_comap_unblockedDifferential S)
    (G.isHomogeneous_restrictScalars_blockedChains S)

/-- A class of partially blocked homology is homogeneous of bidegree `g` exactly when it is the
class of a chain of bidegree `g` whose boundary is blocked. -/
theorem mem_bigradedPartiallyBlockedHomologyGrading_piece_iff {S : Finset (Fin n)} {g : ℤ × ℤ}
    {y : G.1.partiallyBlockedHomology S} :
    y ∈ (G.bigradedPartiallyBlockedHomologyGrading S).piece g ↔
      ∃ c ∈ G.bigradedChainMinusPiece F g,
        ∃ hc : G.1.unblockedDifferential F c ∈ GridDiagram.blockedChains F S,
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
    {i t : Fin n} (hti : G.1.componentPerm.SameCycle t i) (hi : i ∈ S) (ht : t ∉ S) (g : ℤ × ℤ) :
    Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading (insert t S)).piece g) =
      Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading S).piece g) +
        Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading S).piece (g + (1, 1))) := by
  obtain ⟨H, hH, hHg⟩ := G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle F hti
  have e := (G.bigradedChainMinusGrading F).quotientHomologyProdPieceEquiv
    (h := H.restrictScalars F) (v := DistribSMul.toLinearMap F (GridChainMinus F n) (X t))
    (s := -(1, 1)) G.isHomogeneous_restrictScalars_unblockedDifferential
    G.1.restrictScalars_unblockedDifferential_comp_self_eq_zero
    (G.1.blockedChains_le_comap_unblockedDifferential S)
    (G.isHomogeneous_restrictScalars_blockedChains S)
    (G.1.blockedChains_le_comap_unblockedDifferential (insert t S))
    (G.isHomogeneous_restrictScalars_blockedChains (insert t S))
    (GridDiagram.blockedChains_mono (Finset.subset_insert t S))
    (fun m => GridDiagram.X_smul_mem_blockedChains (Finset.mem_insert_self t S) m)
    (fun _ hx => GridDiagram.exists_sub_X_smul_mem_blockedChains hx)
    (fun _ hm => GridDiagram.map_mem_blockedChains _ hm)
    (fun m => (G.1.unblockedDifferential F).map_smul _ m)
    (fun _ hm => GridDiagram.mem_blockedChains_of_X_smul_mem ht hm)
    (fun m => by
      have hm : G.1.unblockedDifferential F (H m) + H (G.1.unblockedDifferential F m) =
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

/-! ### The extreme cases: simply blocked and fully blocked homology -/

/-- A chain of `GC⁻` of bidegree `g` has constant coefficients of bidegree `g`. -/
private theorem mapRange_constantCoeff_mem_range_bigradedChainInclusion {g : ℤ × ℤ}
    {c : GridChainMinus F n} (hc : c ∈ G.bigradedChainMinusPiece F g) :
    c.mapRange constantCoeff (map_zero _) ∈ LinearMap.range (G.bigradedChainInclusion F g) := by
  refine ⟨G.bigradedChainProjection F g (c.mapRange constantCoeff (map_zero _)), ?_⟩
  ext x
  rw [bigradedChainInclusion_apply]
  split_ifs with hx
  · rw [bigradedChainProjection_apply]
  · rw [Finsupp.mapRange_apply, eq_comm]
    by_contra h
    refine hx ?_
    rw [← G.monomialBidegree_zero]
    rw [mem_bigradedChainMinusPiece] at hc
    exact hc x 0 (by rwa [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq])

/-- Blocking every column: the bidegree pieces of partially blocked homology are those of fully
blocked homology. -/
private theorem rank_bigradedPartiallyBlockedHomologyGrading_piece_univ (g : ℤ × ℤ) :
    Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading Finset.univ).piece g) =
      G.bigradedFullyBlockedHomologyPoincareSeries.coeff g := by
  have he : LinearMap.IsHomogeneous G.1.partiallyBlockedHomologyUnivEquiv.toLinearMap
      (G.bigradedPartiallyBlockedHomologyGrading Finset.univ).piece
      G.bigradedFullyBlockedHomologyGrading.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p y hy
    obtain ⟨c, hcp, hc, rfl⟩ := (G.mem_bigradedPartiallyBlockedHomologyGrading_piece_iff).1 hy
    rw [add_zero, LinearEquiv.coe_coe, GridDiagram.partiallyBlockedHomologyUnivEquiv_mk _ c hc,
      bigradedFullyBlockedHomologyGrading_piece]
    exact G.mem_bigradedFullyBlockedHomologyPiece_iff_exists.2
      ⟨_, G.mapRange_constantCoeff_mem_range_bigradedChainInclusion hcp, rfl⟩
  rw [(he.pieceEquiv g).rank_eq, bigradedFullyBlockedHomologyGrading_piece,
    coeff_bigradedFullyBlockedHomologyPoincareSeries, Module.finrank_eq_rank]

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

local notation "F" => ZMod 2

/-- Blocking one column: the bidegree pieces of partially blocked homology are those of
simply blocked homology. -/
private theorem rank_bigradedPartiallyBlockedHomologyGrading_piece_singleton (i : Fin n)
    (g : ℤ × ℤ) :
    Module.rank F
        ((hG.toOddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading {i}).piece g) =
      (hG.bigradedSimplyBlockedHomologyPoincareSeries F i).coeff g := by
  have he : LinearMap.IsHomogeneous (hG.partiallyBlockedHomologySingletonEquiv i).toLinearMap
      (hG.toOddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading {i}).piece
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading F i).piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p y hy
    obtain ⟨c, hcp, hc, rfl⟩ :=
      (hG.toOddComponentGridDiagram.mem_bigradedPartiallyBlockedHomologyGrading_piece_iff).1 hy
    rw [add_zero, LinearEquiv.coe_coe, hG.partiallyBlockedHomologySingletonEquiv_mk i c hc,
      bigradedHatHomologyGrading_piece]
    refine oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece _ F i ?_
    rw [LinearEquiv.apply_symm_apply]
    exact hG.toOddComponentGridDiagram.simplyBlockedSpecialization_mem_bigradedChainHatPiece i hcp
  have := hG.finite_restrictScalars_simplyBlockedHomology F i
  rw [(he.pieceEquiv g).rank_eq, bigradedHatHomologyGrading_piece,
    coeff_bigradedSimplyBlockedHomologyPoincareSeries, Module.finrank_eq_rank]

/-- Blocking the columns of `T` in addition to the column `i` multiplies the Poincaré series of
simply blocked homology by `W ^ |T|`, bidegree by bidegree. -/
private theorem rank_bigradedPartiallyBlockedHomologyGrading_piece_insert_eq (i : Fin n)
    {T : Finset (Fin n)} (hiT : i ∉ T) (g : ℤ × ℤ) :
    Module.rank F
        ((hG.toOddComponentGridDiagram.bigradedPartiallyBlockedHomologyGrading
          (insert i T)).piece g) =
      (hG.bigradedSimplyBlockedHomologyPoincareSeries F i * Bigraded.W ^ T.card).coeff g := by
  induction T using Finset.induction_on generalizing g with
  | empty =>
    rw [LawfulSingleton.insert_empty_eq, Finset.card_empty, pow_zero, mul_one]
    exact hG.rank_bigradedPartiallyBlockedHomologyGrading_piece_singleton i g
  | insert t T htT ih =>
    have hit : i ≠ t := fun h => hiT (h ▸ Finset.mem_insert_self t T)
    have hiT' : i ∉ T := fun h => hiT (Finset.mem_insert_of_mem h)
    rw [Finset.insert_comm, rank_bigradedPartiallyBlockedHomologyGrading_piece_insert _
      (hG.sameCycle_componentPerm t i) (Finset.mem_insert_self i T) (by simp [Ne.symm hit, htT]),
      ih hiT' g, ih hiT' (g + (1, 1)), Finset.card_insert_of_notMem htT, pow_succ, ← mul_assoc,
      Bigraded.coeff_mul_W, Nat.cast_add]

/-- **Fully blocked grid homology is `G-hat ⊗ W ^ (n - 1)`, bigraded.** For a knot grid of size
`n` and any blocked column `i`, the `(O-Maslov, Alexander)` Poincaré series of fully blocked grid
homology `GH~` is that of simply blocked grid homology `G-hat` times `W ^ (n - 1)`, where `W` has
one generator in bidegree `(0, 0)` and one in bidegree `(-1, -1)`. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_pow (i : Fin n) :
    hG.toOddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries =
      hG.bigradedSimplyBlockedHomologyPoincareSeries F i * Bigraded.W ^ (n - 1) := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  have h := hG.rank_bigradedPartiallyBlockedHomologyGrading_piece_insert_eq i
    (Finset.notMem_erase i Finset.univ) g
  rw [Finset.insert_erase (Finset.mem_univ i), Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin,
    hG.toOddComponentGridDiagram.rank_bigradedPartiallyBlockedHomologyGrading_piece_univ] at h
  exact_mod_cast h

end TauCeti.GridDiagram.IsKnot
