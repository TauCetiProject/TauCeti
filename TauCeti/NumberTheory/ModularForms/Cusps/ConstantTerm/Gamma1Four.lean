/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Gamma1

/-!
# The constant terms of odd weight at the irregular cusp of `Γ₁(4)`

The cusp `1/2` of `Γ₁(4)`, represented by every `γ ∈ SL(2, ℤ)` whose lower-left entry is `2`
modulo `4`, is irregular: `Γ₁(4)` contains `γ (-T) γ⁻¹`
(`TauCeti.mul_neg_T_mul_inv_mem_Gamma1_four`). So in odd weight every modular form on `Γ₁(4)`
has constant term zero there (`ModularForm.constantTermAt_eq_zero_of_odd`). This is what makes
the irregular cusp drop out of the dimension bounds of `M_k(Γ₁(4))` in odd weight.

## Main results

* `ModularForm.constantTermAt_eq_zero_of_odd_of_Gamma1_four`: in odd weight, a modular form on
  `Γ₁(4)` has constant term zero at every `γ` whose lower-left entry is `2` modulo `4`.
-/

public section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ModularForm

/-- In odd weight, a modular form on `Γ₁(4)` has constant term zero at the irregular cusp `1/2`,
that is, at every `γ` whose lower-left entry is `2` modulo `4`. -/
theorem constantTermAt_eq_zero_of_odd_of_Gamma1_four {γ : SL(2, ℤ)}
    (hγ : ((γ 1 0 : ℤ) : ZMod 4) = 2) {k : ℤ} (hk : Odd k)
    (f : ModularForm ((Gamma1 4).map (mapGL ℝ)) k) : constantTermAt γ f = 0 :=
  constantTermAt_eq_zero_of_odd
    (Subgroup.mem_map_of_mem _ (TauCeti.mul_neg_T_mul_inv_mem_Gamma1_four hγ))
    (by simp [ModularGroup.coe_T]) (by simp [ModularGroup.coe_T]) hk f

end ModularForm
