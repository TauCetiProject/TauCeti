/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Algebra.Group.Action.LeftToRight

/-!
# Topological structure on left-to-right group action conversions

When `X` is a topological space, the type copy `TauCeti.LeftToRightAction G X` inherits the
topology of `X` and is canonically homeomorphic to `X` via `TauCeti.LeftToRightAction.homeomorph`.
In particular, `LeftToRightAction G X` inherits Hausdorffness (`T2Space`), and when `G` is a
topological group with continuous inversion acting continuously on the left on `X`, the converted
right action `MulOpposite.op g • y = g⁻¹ • y` is jointly continuous (`ContinuousSMul`).

## Main definitions

* `TauCeti.LeftToRightAction.homeomorph G X`: the canonical homeomorphism
  `X ≃ₜ LeftToRightAction G X`.

## Main results

* `TauCeti.LeftToRightAction.instT2Space`: `LeftToRightAction G X` is Hausdorff when `X` is.
* `TauCeti.LeftToRightAction.instContinuousSMul`: converting a jointly continuous left action of a
  group with continuous inversion yields a jointly continuous right action.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.2 and §10.6 (conversion between left and right principal actions via inversion).
-/

public section

open MulOpposite

namespace TauCeti.LeftToRightAction

variable {G X : Type*} [TopologicalSpace X]

/-- `LeftToRightAction G X` carries the topology of `X`. -/
instance instTopologicalSpace : TopologicalSpace (LeftToRightAction G X) :=
  inferInstanceAs (TopologicalSpace X)

variable (G X) in
/-- The identity homeomorphism from `X` to `LeftToRightAction G X`. -/
def homeomorph : X ≃ₜ LeftToRightAction G X where
  toEquiv := equiv G X
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem homeomorph_toEquiv : (homeomorph G X).toEquiv = equiv G X :=
  (rfl)

@[simp]
theorem coe_homeomorph : ⇑(homeomorph G X) = equiv G X :=
  (rfl)

@[simp]
theorem coe_homeomorph_symm : ⇑(homeomorph G X).symm = (equiv G X).symm :=
  (rfl)

/-- `LeftToRightAction G X` inherits Hausdorffness from `X`. -/
instance instT2Space [T2Space X] : T2Space (LeftToRightAction G X) :=
  (homeomorph G X).t2Space

/-- Converting a jointly continuous left action of a topological group with continuous inversion
produces a jointly continuous right action on `LeftToRightAction G X`. -/
instance instContinuousSMul [Group G] [TopologicalSpace G] [ContinuousInv G]
    [MulAction G X] [ContinuousSMul G X] :
    ContinuousSMul Gᵐᵒᵖ (LeftToRightAction G X) where
  continuous_smul := by
    have hfun : (fun p : Gᵐᵒᵖ × LeftToRightAction G X ↦ p.1 • p.2) =
        fun p ↦ homeomorph G X (p.1.unop⁻¹ • (homeomorph G X).symm p.2) := by
      funext ⟨g, y⟩
      obtain ⟨x, rfl⟩ := (equiv G X).surjective y
      simp only [coe_homeomorph, coe_homeomorph_symm, Equiv.symm_apply_apply, smul_equiv]
    rw [hfun]
    exact (homeomorph G X).continuous.comp
      (((continuous_unop.comp continuous_fst).inv).smul
        ((homeomorph G X).symm.continuous.comp continuous_snd))

end TauCeti.LeftToRightAction
