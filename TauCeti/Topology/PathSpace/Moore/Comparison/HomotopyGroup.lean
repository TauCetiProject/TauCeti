/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
import TauCeti.Topology.PathSpace.Moore.Between.Equiv

/-!
# The homotopy-group shift for Moore loops

Normalizing a Moore loop to the unit interval induces the usual loop-space shift on higher
homotopy groups. This identifies `πₖ(ΩᴹX, 1)` with `πₖ₊₁(X, x)` for positive `k`, and
shows that the double Moore loop space is path connected when `π₂(X, x)` vanishes.

The unit is not special: concatenation in front with a Moore loop `γ` is a homotopy equivalence
of the Moore loop space carrying the unit to `γ`, so the positive homotopy groups of `ΩᴹX` at
`γ` vanish exactly when the corresponding higher homotopy groups of `X` do
(`TauCeti.MooreLoopSpace.subsingleton_homotopyGroup_succ_iff`). In particular every path component
of the Moore loop space of an aspherical space is weakly contractible.

The comparison uses the specified Moore/fixed-interval homotopy equivalence. The basepoint
is the Moore loop of duration zero, which normalizes to the constant fixed-interval loop.

* A. Hatcher, *Algebraic Topology*, §4.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

noncomputable section

namespace TauCeti.MooreLoopSpace

open scoped Topology Topology.Homotopy ContinuousMap
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

/-- The homotopy group `π_ k (MooreLoopSpace X x) 1` (including `k = 0`) is trivial if and only if
`π_ (k + 1) X x` is trivial. -/
theorem subsingleton_homotopyGroup_iff (x : X) (k : ℕ) :
    Subsingleton (π_ k (MooreLoopSpace X x) 1) ↔ Subsingleton (π_ (k + 1) X x) := by
  cases k with
  | zero =>
    exact
      (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (1 : MooreLoopSpace X x)).symm.trans
        (pathConnectedSpace_iff_subsingleton_pi1 x)
  | succ m => exact (homotopyGroupMulEquiv x m).toEquiv.subsingleton_congr

/-- All homotopy groups `π_ k (MooreLoopSpace X x) 1` (including `k = 0`) are trivial if and only
if `π_ (n + 1) X x` is trivial for every `n : ℕ`. -/
theorem forall_subsingleton_homotopyGroup_iff (x : X) :
    (∀ k : ℕ, Subsingleton (π_ k (MooreLoopSpace X x) 1)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 1) X x) :=
  forall_congr' (subsingleton_homotopyGroup_iff x)

/-- All homotopy groups of the double Moore loop space `MooreLoopSpace (MooreLoopSpace X x) 1`
(including `k = 0`) are trivial if and only if `π_ (n + 2) X x` is trivial for every `n : ℕ`. -/
theorem forall_subsingleton_homotopyGroup_double_iff (x : X) :
    (∀ k : ℕ, Subsingleton (π_ k (MooreLoopSpace (MooreLoopSpace X x) 1) 1)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 2) X x) :=
  (forall_subsingleton_homotopyGroup_iff (1 : MooreLoopSpace X x)).trans
    (forall_congr' fun n ↦ (homotopyGroupMulEquiv x n).toEquiv.subsingleton_congr)

/-- At every Moore loop `γ`, not only at the unit, the homotopy group `π_ (n + 1)` of the Moore
loop space is trivial exactly when `π_ (n + 2) X x` is. Concatenation in front with `γ` is a
homotopy equivalence of the Moore loop space, with homotopy inverse concatenation in front with the
reversal of `γ`, and it carries the unit to `γ`. -/
theorem subsingleton_homotopyGroup_succ_iff {x : X} (γ : MooreLoopSpace X x) (n : ℕ) :
    Subsingleton (π_ (n + 1) (MooreLoopSpace X x) γ) ↔ Subsingleton (π_ (n + 2) X x) := by
  let E : MooreLoopSpace X x ≃ₕ MooreLoopSpace X x :=
    (MoorePathBetween.loopPrependHomotopyEquiv (MoorePathBetween.loopHomeomorph x γ)).trans
      (MoorePathBetween.loopHomeomorph x).symm.toHomotopyEquiv
  have hE : E.toFun 1 = γ := by
    simp [E, ContinuousMap.HomotopyEquiv.trans_apply, -Homeomorph.symm_toHomotopyEquiv,
      Homeomorph.coe_toHomotopyEquiv, MoorePathBetween.rightAct_one]
  rw [← (homotopyGroupMulEquiv x n).toEquiv.subsingleton_congr, ← hE]
  exact (mulEquivOfHomotopyEquiv E 1).toEquiv.subsingleton_congr.symm

end TauCeti.MooreLoopSpace
