/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Surjective valuations and valuations with equal value groups

Normalized valuations, such as the valuation of a place of a function field, are surjective onto
their value group with zero. This file records the consequences of surjectivity that do not involve
an additive order. A surjective monoid-with-zero homomorphism has full value group, with no
condition on the codomain. A surjective valuation is nontrivial exactly when its target has an
element other than `0` and `1`, for instance a unit other than `1`; on a field its valuation ring
is then a proper subring, and a discrete valuation ring if moreover the units of the target form a
cyclic group. Finally, two equivalent valuations whose value groups are the same cyclic subgroup of
the units of the target are equal. That the value groups are isomorphic as ordered groups is not
enough: equivalence always provides such an isomorphism.

## Main results

* `MonoidWithZeroHom.valueGroup_eq_top_of_surjective`: a surjective monoid-with-zero homomorphism
  has full value group.
* `Valuation.isNontrivial_iff_of_surjective`: a surjective valuation is nontrivial exactly when
  `Γ₀` has an element other than `0` and `1`.
* `Valuation.isNontrivial_of_surjective`: a surjective valuation is nontrivial when `Γ₀ˣ` is.
* `Valuation.valuationSubring_isDiscreteValuationRing_of_surjective`: when `Γ₀ˣ` is nontrivial
  and cyclic, the valuation ring of a surjective valuation on a field is a discrete valuation ring.
* `Valuation.eq_of_isEquiv_of_valueGroup_eq`: two equivalent valuations whose value groups are
  equal and cyclic, as subgroups of `Γ₀ˣ`, are equal.
* `Valuation.eq_of_isEquiv_of_surjective`: when `Γ₀ˣ` is cyclic, two equivalent surjective
  valuations are equal.
-/

public section

open MonoidWithZeroHom LinearOrderedCommGroup

namespace MonoidWithZeroHom

variable {A B : Type*} [MonoidWithZero A] [MonoidWithZero B]

/-- Surjectivity of `f` makes its value group the whole of `Bˣ`. -/
theorem valueGroup_eq_top_of_surjective (f : A →*₀ B) (hf : Function.Surjective f) :
    f.valueGroup = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun γ ↦ mem_valueGroup _ (hf γ)

/-- A surjective monoid-with-zero homomorphism has nontrivial value group once `Bˣ` is
nontrivial. -/
theorem nontrivial_valueGroup_of_surjective [Nontrivial Bˣ] (f : A →*₀ B)
    (hf : Function.Surjective f) : Nontrivial f.valueGroup :=
  (Subgroup.nontrivial_iff_ne_bot _).mpr <| valueGroup_eq_top_of_surjective f hf ▸ top_ne_bot

end MonoidWithZeroHom

namespace Valuation

section Monoid

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] {R : Type*} [Ring R]

/-- **A surjective valuation is nontrivial exactly when `Γ₀` has an element other than `0` and
`1`.** Such an element need not be a unit: `Γ₀` may be `{0, ε, 1}` with `ε ^ 2 = 0`. -/
theorem isNontrivial_iff_of_surjective {v : Valuation R Γ₀} (hv : Function.Surjective v) :
    v.IsNontrivial ↔ ∃ γ : Γ₀, γ ≠ 0 ∧ γ ≠ 1 :=
  ⟨fun h ↦ let ⟨x, hx⟩ := h.exists_val_nontrivial; ⟨v x, hx⟩,
    fun ⟨γ, hγ⟩ ↦ let ⟨x, hx⟩ := hv γ; ⟨x, hx ▸ hγ⟩⟩

/-- **A surjective valuation is nontrivial** once `Γ₀` has a unit other than `1`. Surjectivity is
the form the hypothesis usually arrives in — a place carries it by definition — while results
about valuation rings are stated for a nontrivial valuation, and this converts one to the
other. -/
theorem isNontrivial_of_surjective [Nontrivial Γ₀ˣ] {v : Valuation R Γ₀}
    (hv : Function.Surjective v) : v.IsNontrivial := by
  obtain ⟨γ, hγ⟩ := exists_ne (1 : Γ₀ˣ)
  have hγ1 : (γ : Γ₀) ≠ 1 := Units.val_eq_one.not.mpr hγ
  have : Nontrivial Γ₀ := ⟨_, _, hγ1⟩
  exact (isNontrivial_iff_of_surjective hv).mpr ⟨γ, γ.ne_zero, hγ1⟩

end Monoid

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Ring

variable {R : Type*} [Ring R]

/-- In a nontrivial cyclic subgroup `H`, the generator below one of `H` regarded as a group is the
generator below one of `H` as a subgroup. -/
private theorem coe_genLTOne_top {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    (H : Subgroup G) [Nontrivial H] [IsCyclic H] :
    (((⊤ : Subgroup H).genLTOne : H) : G) = H.genLTOne :=
  H.genLTOne_unique (Subtype.coe_lt_coe.mpr (⊤ : Subgroup H).genLTOne_lt_one) <| by
    simpa [Subgroup.genLTOne_zpowers_eq_top, ← MonoidHom.range_eq_map] using
      (MonoidHom.map_zpowers H.subtype (⊤ : Subgroup H).genLTOne).symm

/-- **Equivalent valuations with equal cyclic value groups are equal.** The value groups must be
equal as subgroups of `Γ₀ˣ`. Equivalence always induces an order-preserving isomorphism between
them, so isomorphic value groups would not suffice: the `p`-adic valuation and its square are
equivalent and not equal. When the two subgroups are equal and cyclic, that isomorphism is the
identity, so the two valuations agree.

Cyclicity cannot be dropped: a valuation and its square are equivalent and, for a surjective
valuation onto `ℝ≥0`, share the value group, without being equal. -/
theorem eq_of_isEquiv_of_valueGroup_eq {v w : Valuation R Γ₀} [IsCyclic v.valueGroup]
    (h : v.IsEquiv w) (hvw : v.valueGroup = w.valueGroup) : v = w := by
  -- The isomorphism of value groups induced by `h`, followed by the inclusion of `w.valueGroup`,
  -- is the inclusion of `v.valueGroup`.
  have key : w.valueGroup.subtype.comp (h.orderMonoidIso : v.valueGroup →* w.valueGroup) =
      v.valueGroup.subtype := by
    rcases subsingleton_or_nontrivial v.valueGroup with _ | hnt
    · exact MonoidHom.ext fun x ↦ by rw [Subsingleton.elim x 1, map_one, map_one]
    have : Nontrivial w.valueGroup := hvw ▸ hnt
    have : IsCyclic w.valueGroup := hvw ▸ ‹IsCyclic v.valueGroup›
    -- Both homomorphisms send the generator below one of `v.valueGroup` to itself: the
    -- isomorphism sends it to the generator below one of `w.valueGroup`, which is the same.
    have hgen : v.valueGroup.genLTOne = w.valueGroup.genLTOne :=
      Subgroup.genLTOne_unique_of_zpowers_eq (Subgroup.genLTOne_lt_one _)
        (Subgroup.genLTOne_lt_one _) (by simp [hvw])
    refine (MonoidHom.eq_iff_eq_on_generator (fun x ↦
      (⊤ : Subgroup v.valueGroup).genLTOne_zpowers_eq_top ▸ Subgroup.mem_top x) _ _).mpr ?_
    simp [OrderMonoidIso.map_genLTOne, coe_genLTOne_top, hgen]
  -- Adjoining zero to both sides of `key` and evaluating at `v.restrict x` gives `v x = w x`,
  -- since `h.orderMonoidIso₀` sends `v.restrict x` to `w.restrict x`.
  refine Valuation.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun (congrArg WithZero.map' key) (v.restrict x)
  rw [WithZero.map'_comp] at hx
  rw [← v.embedding_restrict, ← w.embedding_restrict, ← h.orderMonoidIso₀_spec]
  exact congrArg WithZero.withZeroUnitsEquiv hx.symm

/-- **Equivalent surjective valuations are equal** when `Γ₀ˣ` is cyclic, for instance for
normalized `ℤᵐ⁰`-valuations. -/
theorem eq_of_isEquiv_of_surjective [IsCyclic Γ₀ˣ] {v w : Valuation R Γ₀}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w :=
  eq_of_isEquiv_of_valueGroup_eq h <| by
    rw [v.valueGroup_eq_top_of_surjective hv, w.valueGroup_eq_top_of_surjective hw]

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
  have := v.nontrivial_valueGroup_of_surjective hv
  valuationSubring_isDiscreteValuationRing v

end Field

end Valuation
