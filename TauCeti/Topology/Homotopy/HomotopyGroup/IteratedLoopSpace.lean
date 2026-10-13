/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.IteratedLoopSpace

/-!
# Homotopy groups of iterated loop spaces

The shift of homotopy groups along the `k`-fold iterated loop space
`TauCeti.BasedTopologicalSpace.iteratedLoopSpace` of a based space,
`π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`, by iterating
`HomotopyGroup.pathLoopSpaceMulEquiv`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.piIteratedLoopSpaceMulEquiv`:
  `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`.
-/

public section

universe u

namespace TauCeti

open HomotopyGroup
open scoped Topology

namespace BasedTopologicalSpace

/-- Shifting the degree by one more loop reindexes `m + 1 + 1 + k` as `m + 1 + (k + 1)`. -/
theorem add_succ_add_succ_eq (m k : ℕ) : m + 1 + 1 + k = m + 1 + (k + 1) := by
  omega

/-- **The homotopy groups of the `k`-fold loop space are the homotopy groups of the space,
shifted by `k`**: `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`. -/
noncomputable def piIteratedLoopSpaceMulEquiv (X : BasedTopologicalSpace.{u}) :
    (k m : ℕ) →
      π_ (m + 1) (X.iteratedLoopSpace k).carrier (X.iteratedLoopSpace k).basepoint ≃*
        π_ (m + 1 + k) X.carrier X.basepoint
  | 0, _ => MulEquiv.refl _
  | k + 1, m =>
    (pathLoopSpaceMulEquiv (X := (X.iteratedLoopSpace k).carrier)
        (x := (X.iteratedLoopSpace k).basepoint) m).trans
      ((X.piIteratedLoopSpaceMulEquiv k (m + 1)).trans
        (congrMulEquiv (finCongr (add_succ_add_succ_eq m k))))

/-- In degree `k = 0` the shift is the identity. -/
@[simp]
theorem piIteratedLoopSpaceMulEquiv_zero (X : BasedTopologicalSpace.{u}) (m : ℕ) :
    X.piIteratedLoopSpaceMulEquiv 0 m = MulEquiv.refl _ := by
  rw [piIteratedLoopSpaceMulEquiv.eq_1]

/-- The shift along `k + 1` loops is the one-loop shift `pathLoopSpaceMulEquiv` followed by the
shift along `k` loops, reindexed. -/
@[simp]
theorem piIteratedLoopSpaceMulEquiv_succ (X : BasedTopologicalSpace.{u}) (k m : ℕ) :
    X.piIteratedLoopSpaceMulEquiv (k + 1) m =
      (pathLoopSpaceMulEquiv (X := (X.iteratedLoopSpace k).carrier)
          (x := (X.iteratedLoopSpace k).basepoint) m).trans
        ((X.piIteratedLoopSpaceMulEquiv k (m + 1)).trans
          (congrMulEquiv (finCongr (add_succ_add_succ_eq m k)))) := by
  rw [piIteratedLoopSpaceMulEquiv.eq_2]

end BasedTopologicalSpace

end TauCeti
