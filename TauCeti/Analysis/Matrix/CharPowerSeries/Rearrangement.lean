/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Basic
public import TauCeti.Topology.Order.DecreasingRearrangement

/-!
# Ordered row bounds for Fredholm coefficients

For a bounded row majorant `r` satisfying `‖A i j‖ ≤ r i` on an arbitrary index type,
the norm of the `n`-th principal-minor coefficient is at most the product of the first `n`
terms of the decreasing rearrangement of `r`. For a null majorant, positive rearranged
terms are attained entries, with multiplicities retained and zeros padding finite support.
This is the coefficient estimate used to compare Fredholm Newton polygons with ordered
row bounds.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
-/

public section

open Finset

namespace Matrix

variable {ι R : Type*} [DecidableEq ι] [SeminormedCommRing R] [NormOneClass R]
  [IsUltrametricDist R] {A : Matrix ι ι R} {r : ι → ℝ}

/-- The product of the first `n` terms of the decreasing rearrangement of a bounded row
majorant bounds the `n`-th Fredholm coefficient.
No enumeration of the row indices or infinitude of the positive row bounds is assumed. -/
theorem norm_charCoeff_le_prod_decreasingRearrangement
    (hr : BddAbove (Set.range r)) (hA : ∀ i j, ‖A i j‖ ≤ r i) (n : ℕ) :
    ‖A.charCoeff n‖ ≤ ∏ k ∈ range n, TauCeti.decreasingRearrangement r k := by
  apply norm_charCoeff_le hA
    (prod_nonneg fun k _ ↦ TauCeti.decreasingRearrangement_nonneg hr k)
  intro s hs
  exact hs ▸ TauCeti.prod_le_prod_decreasingRearrangement
    (fun i ↦ (norm_nonneg (A i i)).trans (hA i i)) hr s

end Matrix
