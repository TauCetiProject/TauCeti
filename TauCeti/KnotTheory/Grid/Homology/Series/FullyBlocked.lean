/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.Stabilization
public import TauCeti.KnotTheory.Grid.Homology.PartiallyBlocked.Bigraded
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked

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
At the two ends, the identifications of partially blocked homology with `G-hat` and `GH~` have
degree zero (`TauCeti.GridDiagram.IsKnot.isHomogeneous_partiallyBlockedHomologySingletonEquiv`,
`TauCeti.OddComponentGridDiagram.isHomogeneous_partiallyBlockedHomologyUnivEquiv`).

## Main results

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

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

local notation "F" => ZMod 2

/-- Blocking every column: the bidegree pieces of partially blocked homology are those of fully
blocked homology. -/
private theorem rank_bigradedPartiallyBlockedHomologyGrading_piece_univ (g : ℤ × ℤ) :
    Module.rank F ((G.bigradedPartiallyBlockedHomologyGrading Finset.univ).piece g) =
      G.bigradedFullyBlockedHomologyPoincareSeries.coeff g := by
  rw [(G.isHomogeneous_partiallyBlockedHomologyUnivEquiv.pieceEquiv g).rank_eq,
    bigradedFullyBlockedHomologyGrading_piece,
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
  have := hG.finite_restrictScalars_simplyBlockedHomology F i
  rw [((hG.isHomogeneous_partiallyBlockedHomologySingletonEquiv i).pieceEquiv g).rank_eq,
    bigradedHatHomologyGrading_piece,
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
