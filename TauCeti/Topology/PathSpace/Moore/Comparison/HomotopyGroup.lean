/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv

/-!
# The homotopy-group shift for Moore loops

Normalizing a Moore loop to the unit interval induces the usual loop-space shift on higher
homotopy groups. This identifies `πₖ(ΩᴹX, 1)` with `πₖ₊₁(X, x)` for positive `k`, and
shows that the double Moore loop space is path connected when `π₂(X, x)` vanishes.

The comparison uses the specified Moore/fixed-interval homotopy equivalence. The basepoint
is the Moore loop of duration zero, which normalizes to the constant fixed-interval loop.

* A. Hatcher, *Algebraic Topology*, §4.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

noncomputable section

namespace TauCeti.MooreLoopSpace

open scoped Topology Topology.Homotopy
open HomotopyGroup

variable {X : Type*} [TopologicalSpace X]

/-- The positive homotopy groups of Moore loops are the higher homotopy groups of the
original space, via normalization to the unit interval and the loop-space shift. -/
def homotopyGroupMulEquiv (x : X) (n : ℕ) :
    π_ (n + 1) (MooreLoopSpace X x) 1 ≃* π_ (n + 2) X x :=
  (mulEquivOfHomotopyEquiv (homotopyEquivPath x) 1).trans
    ((homeomorphMulEquivOfEq (Homeomorph.refl (Ω X x))
      (by simpa only [Homeomorph.refl_apply, id_eq, homotopyEquivPath_apply]
        using toPath_one)).trans
      (pathLoopSpaceMulEquiv n))

/-- The Moore loop-space shift applies the map induced by normalization and then the
fixed-interval loop-space shift. -/
@[simp]
theorem homotopyGroupMulEquiv_apply (x : X) (n : ℕ)
    (a : π_ (n + 1) (MooreLoopSpace X x) 1) :
    homotopyGroupMulEquiv x n a = pathLoopSpaceMulEquiv n
      (HomotopyGroup.map (homotopyEquivPath x).toFun
        (by simpa only [homotopyEquivPath_apply] using toPath_one) a) := by
  simp only [homotopyGroupMulEquiv, MulEquiv.trans_apply, mulEquivOfHomotopyEquiv_apply,
    homeomorphMulEquivOfEq_apply, HomotopyGroup.map_comp_apply]
  congr 1

/-- The double Moore loop space is path connected when the second homotopy group
of the original space vanishes. -/
theorem pathConnectedSpace_double (x : X) [Subsingleton (π_ 2 X x)] :
    PathConnectedSpace (MooreLoopSpace (MooreLoopSpace X x) 1) := by
  apply (pathConnectedSpace_iff (1 : MooreLoopSpace X x)).2
  exact (pi1MulEquivFundamentalGroup.symm.trans (homotopyGroupMulEquiv x 0)).injective.subsingleton

end TauCeti.MooreLoopSpace
