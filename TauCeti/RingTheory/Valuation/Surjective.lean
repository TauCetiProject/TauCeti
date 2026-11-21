/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Surjective valuations and valuations with a common value group

Normalized valuations, such as the valuation of a place of a function field, are surjective onto
their value group with zero. This file records the consequences of surjectivity that hold for a
valuation with values in any linearly ordered commutative group with zero `Γ₀`, and the rigidity of
equivalent valuations with the same cyclic value group.

## Main results

* `Valuation.isNontrivial_of_surjective`: a surjective valuation is nontrivial when `Γ₀ˣ` is.
* `Valuation.valueGroup_eq_top_of_surjective`: a surjective valuation has full value group.
* `Valuation.valuationSubring_isDiscreteValuationRing_of_surjective`: when `Γ₀ˣ` is nontrivial
  and cyclic, the valuation ring of a surjective valuation on a field is a discrete valuation ring.
* `Valuation.eq_of_isEquiv_of_valueGroup_eq`: two equivalent valuations with the same cyclic value
  group are equal.
* `Valuation.eq_of_isEquiv_of_surjective`: when `Γ₀ˣ` is cyclic, two equivalent surjective
  valuations are equal.
-/

public section

open MonoidWithZeroHom LinearOrderedCommGroup

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Ring

variable {R : Type*} [Ring R]

/-- **A surjective valuation is nontrivial** once `Γ₀` has a unit other than `1`. Surjectivity is
the form the hypothesis usually arrives in — a place carries it by definition — while results
about valuation rings are stated for a nontrivial valuation, and this converts one to the
other. -/
theorem isNontrivial_of_surjective [Nontrivial Γ₀ˣ] {v : Valuation R Γ₀}
    (hv : Function.Surjective v) : v.IsNontrivial where
  exists_val_nontrivial := by
    obtain ⟨γ, hγ⟩ := exists_ne (1 : Γ₀ˣ)
    obtain ⟨x, hx⟩ := hv γ
    exact ⟨x, hx ▸ γ.ne_zero, hx ▸ Units.val_eq_one.not.mpr hγ⟩

/-- Surjectivity of `v` makes its value group the whole of `Γ₀ˣ`. -/
theorem valueGroup_eq_top_of_surjective (v : Valuation R Γ₀) (hv : Function.Surjective v) :
    v.valueGroup = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun γ ↦ mem_valueGroup _ (hv γ)

/-- A surjective valuation has nontrivial value group once `Γ₀ˣ` is nontrivial. -/
theorem nontrivial_valueGroup_of_surjective [Nontrivial Γ₀ˣ] (v : Valuation R Γ₀)
    (hv : Function.Surjective v) : Nontrivial v.valueGroup :=
  have := isNontrivial_of_surjective hv
  inferInstance

/-- In a nontrivial cyclic subgroup `H`, the generator below one of `H` regarded as a group is the
generator below one of `H` as a subgroup. -/
private theorem coe_genLTOne_top {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    (H : Subgroup G) [Nontrivial H] [IsCyclic H] :
    (((⊤ : Subgroup H).genLTOne : H) : G) = H.genLTOne :=
  H.genLTOne_unique (Subtype.coe_lt_coe.mpr (⊤ : Subgroup H).genLTOne_lt_one) <| by
    rw [← H.coe_subtype, ← MonoidHom.map_zpowers, Subgroup.genLTOne_zpowers_eq_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **Equivalent valuations with the same cyclic value group are equal.** Equivalence induces an
order-preserving isomorphism between the value groups. On a common cyclic value group it sends the
generator below one to itself, so it is the identity, and the two valuations agree.

Cyclicity cannot be dropped: a valuation and its square are equivalent and, for a surjective
valuation onto `ℝ≥0`, share the value group, without being equal. -/
theorem eq_of_isEquiv_of_valueGroup_eq {v w : Valuation R Γ₀} [IsCyclic v.valueGroup]
    (h : v.IsEquiv w) (hvw : v.valueGroup = w.valueGroup) : v = w := by
  refine Valuation.ext fun x ↦ ?_
  rcases eq_or_ne (v x) 0 with hx | hx
  · rw [hx, h.eq_zero.mp hx]
  have hwx : w x ≠ 0 := h.eq_zero.ne.mp hx
  have h1 : v 1 ≠ 0 := by simp
  have hw1 : w 1 ≠ 0 := by simp
  rcases v.valueGroup.bot_or_nontrivial with hbot | hnt
  · -- A trivial common value group forces both values to be `1`.
    have hv1 : Units.mk0 (v x) hx ∈ v.valueGroup := mem_valueGroup _ ⟨x, rfl⟩
    have hw1' : Units.mk0 (w x) hwx ∈ w.valueGroup := mem_valueGroup _ ⟨x, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hv1
    rw [← hvw, hbot, Subgroup.mem_bot] at hw1'
    simpa using congrArg Units.val (hv1.trans hw1'.symm)
  have : Nontrivial w.valueGroup := hvw ▸ hnt
  have : IsCyclic w.valueGroup := hvw ▸ ‹IsCyclic v.valueGroup›
  -- The two value groups have the same generator below one, and the isomorphism of value
  -- groups induced by `h` fixes it.
  have hgen : v.valueGroup.genLTOne = w.valueGroup.genLTOne :=
    Subgroup.genLTOne_unique_of_zpowers_eq (Subgroup.genLTOne_lt_one _)
      (Subgroup.genLTOne_lt_one _) (by simp [hvw])
  have hmap := OrderMonoidIso.map_genLTOne h.orderMonoidIso
  -- Write the class of `v x` as a power of the generator and transport it along `h`.
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (Subgroup.genLTOne_zpowers_eq_top (⊤ : Subgroup v.valueGroup) ▸
      Subgroup.mem_top (valueGroup.mk (v : R →*₀ Γ₀) 1 x h1 hx))
  have key : (valueGroup.mk (w : R →*₀ Γ₀) 1 x hw1 hwx : Γ₀ˣ) =
      valueGroup.mk (v : R →*₀ Γ₀) 1 x h1 hx := by
    rw [← h.orderMonoidIso_spec h1 hx, ← hk, map_zpow, hmap, SubgroupClass.coe_zpow,
      SubgroupClass.coe_zpow, coe_genLTOne_top, coe_genLTOne_top, hgen]
  simpa using (congrArg Units.val key).symm

/-- **Equivalent surjective valuations are equal** when `Γ₀ˣ` is cyclic, for instance for
normalized `ℤᵐ⁰`-valuations. -/
theorem eq_of_isEquiv_of_surjective [IsCyclic Γ₀ˣ] {v w : Valuation R Γ₀}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w :=
  eq_of_isEquiv_of_valueGroup_eq h <| by
    rw [valueGroup_eq_top_of_surjective v hv, valueGroup_eq_top_of_surjective w hw]

end Ring

section Field

variable {K : Type*} [Field K]

/-- The valuation ring of a surjective valuation is a proper subring once `Γ₀ˣ` is nontrivial. -/
theorem valuationSubring_ne_top_of_surjective [Nontrivial Γ₀ˣ] (v : Valuation K Γ₀)
    (hv : Function.Surjective v) : v.valuationSubring ≠ ⊤ :=
  fun h ↦ (valuationSubring_eq_top_iff v).mp h (isNontrivial_of_surjective hv)

/-- The valuation ring of a surjective valuation is a discrete valuation ring once `Γ₀ˣ` is
nontrivial and cyclic. -/
theorem valuationSubring_isDiscreteValuationRing_of_surjective [IsCyclic Γ₀ˣ] [Nontrivial Γ₀ˣ]
    (v : Valuation K Γ₀) (hv : Function.Surjective v) :
    IsDiscreteValuationRing v.valuationSubring :=
  have := nontrivial_valueGroup_of_surjective v hv
  valuationSubring_isDiscreteValuationRing v

end Field

end Valuation
