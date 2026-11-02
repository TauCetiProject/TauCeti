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

/-- The Moore loop space `MooreLoopSpace X x` is path connected if and only if `π_ 1 X x` is
trivial. -/
theorem pathConnectedSpace_iff_subsingleton_pi1 (x : X) :
    PathConnectedSpace (MooreLoopSpace X x) ↔ Subsingleton (π_ 1 X x) :=
  (pathConnectedSpace_iff x).trans pi1MulEquivFundamentalGroup.symm.toEquiv.subsingleton_congr

/-- The double Moore loop space `MooreLoopSpace (MooreLoopSpace X x) 1` is path connected if and
only if `π_ 2 X x` is trivial. -/
theorem pathConnectedSpace_double_iff (x : X) :
    PathConnectedSpace (MooreLoopSpace (MooreLoopSpace X x) 1) ↔ Subsingleton (π_ 2 X x) :=
  (pathConnectedSpace_iff_subsingleton_pi1 (1 : MooreLoopSpace X x)).trans
    (homotopyGroupMulEquiv x 0).toEquiv.subsingleton_congr

/-- The double Moore loop space is path connected when the second homotopy group
of the original space vanishes. -/
theorem pathConnectedSpace_double (x : X) [Subsingleton (π_ 2 X x)] :
    PathConnectedSpace (MooreLoopSpace (MooreLoopSpace X x) 1) :=
  (pathConnectedSpace_double_iff x).mpr inferInstance

/-- All homotopy groups `π_ k (MooreLoopSpace X x) 1` (including `k = 0`) are trivial if and only
if `π_ (n + 1) X x` is trivial for every `n : ℕ`. -/
theorem forall_subsingleton_homotopyGroup_iff (x : X) :
    (∀ k : ℕ, Subsingleton (π_ k (MooreLoopSpace X x) 1)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 1) X x) := by
  constructor
  · intro h n
    cases n with
    | zero =>
      exact (pathConnectedSpace_iff_subsingleton_pi1 x).mp
        ((pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (1 : MooreLoopSpace X x)).mpr
          (h 0))
    | succ m =>
      exact (homotopyGroupMulEquiv x m).toEquiv.subsingleton_congr.mp (h (m + 1))
  · intro h k
    cases k with
    | zero =>
      exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (1 : MooreLoopSpace X x)).mp
        ((pathConnectedSpace_iff_subsingleton_pi1 x).mpr (h 0))
    | succ m =>
      exact (homotopyGroupMulEquiv x m).toEquiv.subsingleton_congr.mpr (h (m + 1))

/-- All homotopy groups of the double Moore loop space `MooreLoopSpace (MooreLoopSpace X x) 1`
(including `k = 0`) are trivial if and only if `π_ (n + 2) X x` is trivial for every `n : ℕ`. -/
theorem forall_subsingleton_homotopyGroup_double_iff (x : X) :
    (∀ k : ℕ, Subsingleton (π_ k (MooreLoopSpace (MooreLoopSpace X x) 1) 1)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 2) X x) :=
  (forall_subsingleton_homotopyGroup_iff (1 : MooreLoopSpace X x)).trans
    (forall_congr' fun n ↦ (homotopyGroupMulEquiv x n).toEquiv.subsingleton_congr)

end TauCeti.MooreLoopSpace
