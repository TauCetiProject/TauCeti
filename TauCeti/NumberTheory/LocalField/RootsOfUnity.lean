/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Roots of unity in a valued field

Every root of unity of nonzero order in a valued field has valuation one. Consequently,
inclusion of the integer ring into the field identifies their groups of roots of unity of any
nonzero order.

## Main results

* `TauCeti.map_rootsOfUnity_integer`: inclusion maps the roots of unity in the integer ring onto
  the roots of unity in the field.
* `TauCeti.rootsOfUnityIntegerEquiv`: the resulting multiplicative equivalence.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K]

/-- **The roots of unity of a valued field are those of its integer ring**: a root of nonzero
order has valuation one, so it is a unit of `𝒪[K]`. -/
theorem map_rootsOfUnity_integer {n : ℕ} (hn : n ≠ 0) :
    (rootsOfUnity n 𝒪[K]).map (Units.map (Subring.subtype 𝒪[K]).toMonoidHom) =
      rootsOfUnity n K := by
  refine le_antisymm (map_rootsOfUnity _ n) fun ζ hζ ↦ ?_
  have hvalpow : valuation K (ζ : K) ^ n = 1 := by
    rw [← map_pow, (mem_rootsOfUnity' n ζ).mp hζ, map_one]
  have hval : valuation K (ζ : K) = 1 :=
    (pow_eq_one_iff_of_nonneg (bot_le : 0 ≤ valuation K (ζ : K)) hn).mp hvalpow
  have hu : IsUnit (⟨(ζ : K), (Valuation.mem_integer_iff (valuation K) (ζ : K)).mpr hval.le⟩
      : 𝒪[K]) := (Valuation.integer.integers (valuation K)).isUnit_of_one' hval
  have hcoe : ((hu.unit : 𝒪[K]) : K) = (ζ : K) := congrArg Subtype.val hu.unit_spec
  refine ⟨hu.unit, ?_, Units.ext hcoe⟩
  rw [SetLike.mem_coe, mem_rootsOfUnity']
  apply Subtype.ext
  push_cast [hcoe]
  exact_mod_cast (mem_rootsOfUnity' n ζ).mp hζ

/-- The `n`-th roots of unity of `𝒪[K]` and of `K` agree, for `n ≠ 0`. -/
def rootsOfUnityIntegerEquiv {n : ℕ} (hn : n ≠ 0) :
    rootsOfUnity n 𝒪[K] ≃* rootsOfUnity n K :=
  (Subgroup.equivMapOfInjective _ _
      (Units.map_injective (f := (Subring.subtype 𝒪[K]).toMonoidHom) Subtype.val_injective)).trans
    (MulEquiv.subgroupCongr (map_rootsOfUnity_integer K hn))

/-- The equivalence between roots of unity in `𝒪[K]` and `K` is induced by inclusion. -/
@[simp]
theorem coe_rootsOfUnityIntegerEquiv {n : ℕ} (hn : n ≠ 0) (ζ : rootsOfUnity n 𝒪[K]) :
    (((rootsOfUnityIntegerEquiv K hn ζ : rootsOfUnity n K) : Kˣ) : K) =
      (((ζ : 𝒪[K]ˣ) : 𝒪[K]) : K) := by
  rw [rootsOfUnityIntegerEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply, Units.coe_map]
  rfl

end TauCeti
