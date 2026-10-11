/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Alexander
public import TauCeti.RingTheory.FittingIdeal.Corner

/-!
# The Burau presentation ideal

The codimension-one minors of the unreduced Burau matrix minus the identity generate the
principal ideal of the Burau--Alexander corner determinant. Equivalently, the first
Fitting ideal of its cokernel is that principal ideal. These formulas compare the
determinant algorithm with the presentation-ideal algorithm for Alexander invariants.

Both formulas hold over arbitrary commutative rings at any unit parameter, for links
as well as knots, and include the trivial one-strand braid.

Reference: J. Birman, *Braids, Links, and Mapping Class Groups*, Theorem 3.11.
-/

public section

noncomputable section

namespace TauCeti.MarkovBraid

open Matrix KnotTheory LinearMap

variable {R : Type*} [CommRing R]

/-- The codimension-one minors of `burau β - 1` generate the ideal of its Alexander
corner determinant. -/
theorem minorsIdeal_range_burau_sub_one_eq_span_burauAlexander (β : MarkovBraid) (t : Rˣ) :
    (range ((burau (β.predStrands + 1) t β.braid :
      Matrix (Fin (β.predStrands + 1)) (Fin (β.predStrands + 1)) R) - 1).mulVecLin).minorsIdeal
        β.predStrands = Ideal.span {β.burauAlexander t} := by
  rw [burauAlexander_def]
  exact Matrix.minorsIdeal_range_eq_span_det_submatrix_castSucc _
    (burau_sub_one_mulVec_one t β.braid) (geom_vecMul_burau_sub_one t β.braid)
    (by simp) (by simpa using t.isUnit.pow β.predStrands)

/-- The first Fitting ideal of the unreduced Burau cokernel is the principal
Alexander ideal, including for the one-strand unknot. -/
@[simp]
theorem fittingIdeal_coker_burau_sub_one_one_eq_span_burauAlexander (β : MarkovBraid) (t : Rˣ) :
    fittingIdeal R ((Fin (β.predStrands + 1) → R) ⧸
      range ((burau (β.predStrands + 1) t β.braid :
        Matrix (Fin (β.predStrands + 1)) (Fin (β.predStrands + 1)) R) - 1).mulVecLin) 1 =
      Ideal.span {β.burauAlexander t} := by
  nontriviality R
  rw [fittingIdeal_eq_minorsIdeal_ker (Submodule.mkQ_surjective _),
    Submodule.ker_mkQ, Module.finrank_fin_fun]
  simpa only [Nat.add_sub_cancel] using β.minorsIdeal_range_burau_sub_one_eq_span_burauAlexander t

end TauCeti.MarkovBraid
