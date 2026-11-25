/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commensurable

/-!
# Subgroups commensurated by the whole group

The commensurator of a subgroup `H` of `G` is all of `G` exactly when every conjugate `g H g⁻¹`
meets `H` in a subgroup of finite index in `H`. Commensurability of `g H g⁻¹` with `H` also asks
that `H ∩ g H g⁻¹` have finite index in `g H g⁻¹`, but this second condition is the first one for
`g⁻¹`, conjugated by `g`, so only one direction has to be checked for each element.

This is the form in which the commensurator of `GL_n(ℤ_p)` in `GL_n(ℚ_p)` is computed: for each `g`
one exhibits a congruence subgroup of `GL_n(ℤ_p)` inside `g GL_n(ℤ_p) g⁻¹`.

## Main results

* `Subgroup.Commensurable.commensurator_eq_top_iff`: `commensurator H = ⊤` if and only if
  `g H g⁻¹ ∩ H` has finite index in `H` for every `g`.
-/

public section

open scoped Pointwise

namespace Subgroup.Commensurable

variable {G : Type*} [Group G] {H : Subgroup G}

/-- **The commensurator of `H` is the whole group** exactly when, for every `g`, the conjugate
`g H g⁻¹` meets `H` in a subgroup of finite index in `H`. The other half of commensurability,
finite index in `g H g⁻¹`, follows by applying the condition to `g⁻¹`. -/
theorem commensurator_eq_top_iff :
    commensurator H = ⊤ ↔ ∀ g : G, (MulAut.conj g • H).IsFiniteRelIndex H := by
  refine ⟨fun h g ↦ ((commensurator_mem_iff H g).mp (h ▸ mem_top g)).1, fun h ↦ ?_⟩
  refine eq_top_iff.mpr fun g _ ↦ (commensurator_mem_iff H g).mpr ⟨h g, ?_⟩
  have hg := h g⁻¹
  rw [isFiniteRelIndex_iff_relIndex_ne_zero] at hg ⊢
  rwa [← relIndex_pointwise_smul (MulAut.conj g)⁻¹, inv_smul_smul, ← map_inv]

end Subgroup.Commensurable
