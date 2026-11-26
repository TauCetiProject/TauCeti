/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# An element acting by a scalar

Let `z` act on `M` in the same way as a scalar `r`, in the sense that `z • m = r • m` for every
`m : M`. If the action of `r` commutes with an action of `G`, then so does the action of `z`; and
if `r` lies in a ring with `r - 1` a unit, then `m ↦ z • m - m` is bijective. These are the two
hypotheses of Sah's lemma `groupCohomology.IsCocycle₁.isCoboundary₁_of_bijective` when `z` acts by
a scalar.

## Main results

* `TauCeti.smul_comm_of_smul_eq`: if `z` acts by a scalar `r` commuting with `G`, then
  `z • g • m = g • z • m`.
* `TauCeti.bijective_smul_sub_of_smul_eq`: if `z` acts by a scalar `r` with `r - 1` a unit, then
  `m ↦ z • m - m` is bijective.
-/

public section

namespace TauCeti

variable {G R M : Type*} [SMul G M]

/-- If `z` acts on `M` by a scalar `r` whose action commutes with that of `G`, then the action
of `z` commutes with that of `G`. -/
theorem smul_comm_of_smul_eq [SMul R M] [SMulCommClass G R M] {z : G} {r : R}
    (hzr : ∀ m : M, z • m = r • m) (g : G) (m : M) : z • g • m = g • z • m := by
  rw [hzr, hzr, smul_comm g r m]

/-- If `z` acts on `M` by a scalar `r` of a ring with `r - 1` a unit, then `m ↦ z • m - m` is
bijective. -/
theorem bijective_smul_sub_of_smul_eq [Ring R] [AddCommGroup M] [Module R M] {z : G} {r : R}
    (hzr : ∀ m : M, z • m = r • m) (hr : IsUnit (r - 1)) :
    Function.Bijective fun m : M => z • m - m := by
  simpa only [hzr, sub_smul, one_smul] using hr.smul_bijective (β := M)

end TauCeti
