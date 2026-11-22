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
condition on the codomain; between groups with zero, for instance for a valuation from a division
ring into an ordered group with zero, full value group conversely means surjectivity, so such a map
is surjective as soon as it attains a generator of the units of its codomain. A surjective
valuation is nontrivial exactly when its target has an element other than `0` and `1`, for
instance a unit other than `1`. For a surjective valuation from a field into a linearly ordered
commutative group with zero whose units are nontrivial, the valuation ring is a proper subring,
and a discrete valuation ring if moreover those units form a cyclic group. Finally, two
equivalent valuations into a linearly ordered commutative group with zero whose value groups are
the same cyclic subgroup of the units of the target are equal. That the value groups are
isomorphic as ordered groups is not enough: equivalence always provides such an isomorphism.

## Main results

* `MonoidWithZeroHom.valueGroup_eq_top_of_surjective`: a surjective monoid-with-zero homomorphism
  has full value group.
* `MonoidWithZeroHom.valueGroup_eq_top_iff_surjective`: between groups with zero, the converse
  holds as well.
* `MonoidWithZeroHom.surjective_of_mem_range_of_zpowers_eq_top`: between groups with zero, a map
  that attains a generator of the units of its codomain is surjective.
* `Valuation.isNontrivial_iff_of_surjective`: a surjective valuation is nontrivial exactly when
  `Γ₀` has an element other than `0` and `1`.
* `Valuation.isNontrivial_of_surjective`: a surjective valuation is nontrivial when `Γ₀ˣ` is.
* `Valuation.valuationSubring_ne_top_of_surjective`: for a surjective valuation from a field into
  a linearly ordered commutative group with zero `Γ₀` with `Γ₀ˣ` nontrivial, the valuation ring is
  a proper subring.
* `Valuation.valuationSubring_isDiscreteValuationRing_of_surjective`: for a surjective valuation
  from a field into a linearly ordered commutative group with zero `Γ₀` with `Γ₀ˣ` nontrivial and
  cyclic, the valuation ring is a discrete valuation ring.
* `Valuation.eq_of_isEquiv_of_valueGroup_eq`: two equivalent valuations into a linearly ordered
  commutative group with zero `Γ₀` whose value groups are equal and cyclic, as subgroups of `Γ₀ˣ`,
  are equal.
* `Valuation.eq_of_isEquiv_of_surjective`: two equivalent surjective valuations into a linearly
  ordered commutative group with zero `Γ₀` with `Γ₀ˣ` cyclic are equal.
-/

public section

open MonoidWithZeroHom LinearOrderedCommGroup

namespace MonoidWithZeroHom

section MonoidWithZero

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

end MonoidWithZero

section GroupWithZero

variable {A B : Type*} [GroupWithZero A] [GroupWithZero B]

/-- **Between groups with zero, full value group means surjectivity.** The nonzero values of `f`
are closed under inverses, so they already form the value group. On a ring this fails: the
`t`-adic valuation on `k[t², t³]` has full value group in `ℤᵐ⁰` without attaining `exp (-1)`. -/
theorem valueGroup_eq_top_iff_surjective (f : A →*₀ B) :
    f.valueGroup = ⊤ ↔ Function.Surjective f := by
  classical
  refine ⟨fun h ↦ ?_, valueGroup_eq_top_of_surjective f⟩
  -- `f` factors as `ValueGroup₀.restrict₀ f`, which is onto, followed by
  -- `ValueGroup₀.embedding`, which is onto once the value group is full.
  have hs : Function.Surjective f.valueGroup.subtype := by
    rw [← MonoidHom.range_eq_top, Subgroup.range_subtype, h]
  have he : Function.Surjective (ValueGroup₀.embedding (f := f)) :=
    WithZero.withZeroUnitsEquiv.surjective.comp (WithZero.map'_surjective hs)
  convert he.comp (ValueGroup₀.restrict₀_surjective f) using 1
  exact funext fun a ↦ (ValueGroup₀.embedding_restrict₀ a).symm

/-- **Between groups with zero, a map that attains a generator of the units of its codomain is
surjective**: the value group contains that generator, so it is full. -/
theorem surjective_of_mem_range_of_zpowers_eq_top (f : A →*₀ B) {u : Bˣ}
    (hu : (u : B) ∈ Set.range f) (hzu : Subgroup.zpowers u = ⊤) : Function.Surjective f :=
  (valueGroup_eq_top_iff_surjective f).mp <| top_unique <|
    hzu ▸ Subgroup.zpowers_le.mpr (mem_valueGroup _ hu)

end GroupWithZero

end MonoidWithZeroHom

namespace Valuation

section Monoid

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] {R : Type*} [Ring R]

/-- **A surjective valuation is nontrivial exactly when `Γ₀` has an element other than `0` and
`1`.** Such an element need not be a unit: `Γ₀` may be the multiplicative submonoid
`{0} ∪ {2⁻ⁿ | n : ℕ}` of `ℝ≥0`, in which `1 / 2` is a nonzero nonunit. -/
theorem isNontrivial_iff_of_surjective {v : Valuation R Γ₀} (hv : Function.Surjective v) :
    v.IsNontrivial ↔ ∃ γ : Γ₀, γ ≠ 0 ∧ γ ≠ 1 :=
  (⟨fun h ↦ h.exists_val_nontrivial, fun h ↦ ⟨h⟩⟩ : v.IsNontrivial ↔ _).trans
    (hv.exists (p := fun γ ↦ γ ≠ 0 ∧ γ ≠ 1)).symm

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

/-- **Equivalent valuations with equal cyclic value groups are equal**, for valuations into a
linearly ordered commutative group with zero `Γ₀`. The value groups must be equal as subgroups of
`Γ₀ˣ`. Equivalence always induces an order-preserving isomorphism between
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
    · exact Subsingleton.elim _ _
    have : Nontrivial w.valueGroup := hvw ▸ hnt
    have : IsCyclic w.valueGroup := hvw ▸ ‹IsCyclic v.valueGroup›
    -- `IsRankOneDiscrete.generator' v` is the generator below one of `v.valueGroup` regarded as
    -- a group, so the isomorphism sends it to `generator' w`. Both are the generator below one
    -- of the common value group.
    have hv : IsRankOneDiscrete.generator' v = (⊤ : Subgroup v.valueGroup).genLTOne :=
      (⊤ : Subgroup v.valueGroup).genLTOne_unique (IsRankOneDiscrete.generator'_lt_one v)
        (IsRankOneDiscrete.generator'_zpowers_eq_top v)
    have hw : IsRankOneDiscrete.generator' w = (⊤ : Subgroup w.valueGroup).genLTOne :=
      (⊤ : Subgroup w.valueGroup).genLTOne_unique (IsRankOneDiscrete.generator'_lt_one w)
        (IsRankOneDiscrete.generator'_zpowers_eq_top w)
    have hgen : IsRankOneDiscrete.generator w = IsRankOneDiscrete.generator v := by
      rw [← IsRankOneDiscrete.valueGroup_genLTOne_eq_generator w,
        ← IsRankOneDiscrete.valueGroup_genLTOne_eq_generator v]
      congr 1
      exact hvw.symm
    refine (MonoidHom.eq_iff_eq_on_generator (fun x ↦
      IsRankOneDiscrete.generator'_zpowers_eq_top v ▸ Subgroup.mem_top x) _ _).mpr ?_
    change ((h.orderMonoidIso (IsRankOneDiscrete.generator' v) : w.valueGroup) : Γ₀ˣ) =
      IsRankOneDiscrete.generator v
    rw [hv, OrderMonoidIso.map_genLTOne, ← hw]
    exact hgen
  -- Adjoining zero to both sides of `key` and evaluating at `v.restrict x` gives `v x = w x`,
  -- since `h.orderMonoidIso₀` sends `v.restrict x` to `w.restrict x`.
  refine Valuation.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun (congrArg WithZero.map' key) (v.restrict x)
  rw [WithZero.map'_comp] at hx
  rw [← v.embedding_restrict, ← w.embedding_restrict, ← h.orderMonoidIso₀_spec]
  exact congrArg WithZero.withZeroUnitsEquiv hx.symm

/-- **Equivalent surjective valuations are equal** when they take values in a linearly ordered
commutative group with zero `Γ₀` with `Γ₀ˣ` cyclic, for instance for normalized
`ℤᵐ⁰`-valuations. -/
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
