/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.Geometry.Manifold.LocallyFlat.Finite
public import TauCeti.Geometry.Manifold.LocallyFlat.Sphere

/-!
# Brown's bicollaring theorem for spheres

Every locally flat embedding `Sⁿ → Sⁿ⁺¹` has a global bicollar, in every dimension `n`.
For positive-dimensional source spheres, Jordan–Brouwer separation supplies the disconnected
complement needed by the bicollaring theorem for separating spheres. The zero-dimensional
source is discrete and compact, so finite bicollaring handles its two points directly.

The global product neighbourhood is the structural input to the annulus theorem; local
flatness is essential, since a wild embedded sphere need not have a bicollar.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75
  (1962), 331–341.
* A. Hatcher, *Algebraic Topology*, Section 2.B, Corollary 2B.2 (Jordan–Brouwer separation).
-/

public section

open Metric Set Topology
open scoped EuclideanSpace

namespace TauCeti

/-- **Brown's bicollaring theorem:** every locally flat embedding of the standard `n`-sphere
in the standard `(n + 1)`-sphere is globally bicollared, including `n = 0`. -/
theorem brownBicollaring (n : ℕ) : BrownBicollaring n := by
  refine brownBicollaring_iff.2 fun f hf => ?_
  by_cases hn : n = 0
  · subst n
    have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0))
      (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    have := finite_of_compact_of_discrete
      (X := sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    exact hf.isLocallyBicollared.isBicollared_of_finite hf.injective
  · apply hf.isBicollared_of_not_isPreconnected_compl_range hn
    intro hconn
    have hclosed : IsClosed (range f) := by
      simpa using (isCompact_univ.image hf.continuous).isClosed
    have := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    have := hclosed.isOpen_compl.locallyPathConnectedSpace
    have := isPreconnected_iff_preconnectedSpace.1 hconn
    have hcard := natCard_zerothHomotopy_sphere_compl_range_eq_two
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) + 1) hf.continuous hf.injective
    have hle : Nat.card (ZerothHomotopy ↥(range f)ᶜ) ≤ 1 := by
      rw [← Nat.card_congr connectedComponentsEquivZerothHomotopy]
      simpa using Nat.card_le_card_of_injective
        (f := fun _ : ConnectedComponents ↥(range f)ᶜ => ())
        (fun _ _ _ => Subsingleton.elim _ _)
    omega

end TauCeti
