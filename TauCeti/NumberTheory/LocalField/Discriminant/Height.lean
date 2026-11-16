/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.AlgEquiv
public import TauCeti.NumberTheory.LocalField.Different.Wild
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic

/-!
# The height and the mean of an extension of local fields

Let `L/K` be a finite separable extension of nonarchimedean local fields, with ramification index
`e = e(L/K)`, inertia degree `f = f(L/K)` and discriminant exponent `c = δ(L/K)`. Dedekind's
different theorem gives `f (e - 1) ≤ c`, with equality exactly in the tame case, so the
discriminant exponent is `f (e - 1)` plus a correction that measures wild ramification. This file
names that correction:

* the **height** `H(L/K) = c / f + 1 - e`, a natural number;
* the **mean** `m(L/K) = H(L/K) / e`, a nonnegative rational number;

so that `c = f (e - 1 + H(L/K)) = f (e - 1 + e m(L/K))`. In particular a totally ramified `L/K`
has `c = e - 1 + H(L/K)`.

Since `c = f · d(L/K)` for the different exponent `d(L/K)`
(`TauCeti.discriminantExponent_eq_inertiaDegree_mul_differentExponent`), the height is also
`d(L/K) + 1 - e`, and it extends Serre's wild exponent `c(L) = d(L) + 1 - [L : K]` of a totally
ramified extension, `IntermediateField.wildExponent`, to every finite separable extension
(`IntermediateField.wildExponent_eq_height`). It vanishes exactly in the tame case, is bounded by
`v_L(e)` when `e` is nonzero in `L` (the upper half of Dedekind's different theorem), and both the
height and the mean are invariants of the `K`-isomorphism class that are unchanged by passing to
the top step `M/L` of a tower `M/L/K` with `L/K` unramified, in particular to the totally ramified
top step `L/L₀` of the canonical tower `K ⊆ L₀ ⊆ L`.

## Main definitions

* `TauCeti.height`: the height `H(L/K) = c / f + 1 - e` of a separable extension.
* `TauCeti.mean`: the mean `m(L/K) = H(L/K) / e`.

## Main results

* `TauCeti.height_eq_differentExponent_add_one_sub` and
  `TauCeti.height_add_ramificationIndex`: `H = d + 1 - e`, read without truncation as
  `H + e = d + 1`.
* `TauCeti.discriminantExponent_eq_inertiaDegree_mul_add_height`: `c = f (e - 1) + f H`, and
  its rational form `TauCeti.natCast_height`, `H = c / f - e + 1` in `ℚ`.
* `TauCeti.height_eq_zero_iff`: the height vanishes exactly for tamely ramified extensions.
* `TauCeti.height_le_natCastValuation`: `H ≤ v_L(e)` when `e` is nonzero in `L`.
* `TauCeti.height_eq_of_algEquiv`: the height is a `K`-isomorphism invariant.
* `TauCeti.IsUnramified.height_tower_eq` and `TauCeti.height_unramifiedExtension_inertiaDegree`:
  over an unramified base the height is that of the top step, in particular of the totally
  ramified top step of the canonical tower.
* `TauCeti.ramificationIndex_mul_mean` and
  `TauCeti.natCast_discriminantExponent_eq_inertiaDegree_mul_mean`: `e m = H` and
  `c = f (e - 1 + e m)`.
* `TauCeti.mean_eq_zero_iff`, `TauCeti.mean_le_natCastValuation`, `TauCeti.mean_eq_of_algEquiv`,
  `TauCeti.IsUnramified.mean_tower_eq` and `TauCeti.mean_unramifiedExtension_inertiaDegree`: the
  corresponding facts for the mean, the bound reading `m ≤ v_K(e)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, Proposition 13.
* The LMFDB Collaboration, *The L-functions and modular forms database*, the section on `p`-adic
  fields, whose conventions for the height and the mean are followed here.
-/

public section
noncomputable section

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsSeparable K L]

/-- The **height** `H(L/K) = c / f + 1 - e` of a separable extension `L/K` of nonarchimedean
local fields, where `c` is the discriminant exponent, `f` the inertia degree and `e` the
ramification index of `L/K`.

Since `c = f · d(L/K)` for the different exponent `d(L/K)` and `e - 1 ≤ d(L/K)`, neither the
division nor the truncated subtraction loses anything: `H(L/K) = d(L/K) + 1 - e` is the excess of
the different exponent over its tame value `e - 1` (`TauCeti.height_add_ramificationIndex`), and
`c = f (e - 1) + f H(L/K)`. For a totally ramified extension it is Serre's wild exponent
(`IntermediateField.wildExponent_eq_height`). -/
def height : ℕ :=
  discriminantExponent K L / inertiaDegree K L + 1 - ramificationIndex K L

/-- The defining formula of `height`: `H(L/K) = c / f + 1 - e`. -/
theorem height_def :
    height K L = discriminantExponent K L / inertiaDegree K L + 1 - ramificationIndex K L :=
  (rfl)

/-- The height is the excess of the different exponent over its tame value:
`H(L/K) = d(L/K) + 1 - e`. -/
theorem height_eq_differentExponent_add_one_sub :
    height K L = differentExponent K L + 1 - ramificationIndex K L := by
  rw [height_def, discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    Nat.mul_div_cancel_left _ inertiaDegree_pos]

/-- **The height without truncation**: `H(L/K) + e = d(L/K) + 1`. -/
theorem height_add_ramificationIndex :
    height K L + ramificationIndex K L = differentExponent K L + 1 := by
  have := ramificationIndex_sub_one_le_differentExponent K L
  have := ramificationIndex_pos (K := K) (L := L)
  rw [height_eq_differentExponent_add_one_sub]
  omega

/-- The different exponent is its tame value `e - 1` plus the height:
`d(L/K) = e - 1 + H(L/K)`. -/
theorem differentExponent_eq_ramificationIndex_sub_one_add_height :
    differentExponent K L = ramificationIndex K L - 1 + height K L := by
  have := height_add_ramificationIndex K L
  have := ramificationIndex_pos (K := K) (L := L)
  omega

/-- **The discriminant exponent in terms of the height**: `c = f (e - 1) + f H(L/K)`. -/
theorem discriminantExponent_eq_inertiaDegree_mul_add_height :
    discriminantExponent K L =
      inertiaDegree K L * (ramificationIndex K L - 1) + inertiaDegree K L * height K L := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    differentExponent_eq_ramificationIndex_sub_one_add_height, Nat.mul_add]

/-- The height in `ℚ`, without division in `ℕ` or truncated subtraction:
`H(L/K) = c / f - e + 1`. -/
theorem natCast_height :
    (height K L : ℚ) =
      discriminantExponent K L / inertiaDegree K L - ramificationIndex K L + 1 := by
  have hf : (inertiaDegree K L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 inertiaDegree_pos.ne'
  have he : 1 ≤ ramificationIndex K L := ramificationIndex_pos
  rw [discriminantExponent_eq_inertiaDegree_mul_add_height, ← Nat.mul_add, Nat.cast_mul,
    mul_div_cancel_left₀ _ hf]
  push_cast [he]
  ring

/-- **The height vanishes exactly in the tame case**: `H(L/K) = 0` if and only if `L/K` is
tamely ramified. -/
@[simp]
theorem height_eq_zero_iff : height K L = 0 ↔ IsTamelyRamified K L := by
  rw [← differentExponent_eq_ramificationIndex_sub_one_iff,
    differentExponent_eq_ramificationIndex_sub_one_add_height]
  omega

/-- The height is positive exactly in the wild case. -/
theorem height_pos_iff : 0 < height K L ↔ IsWildlyRamified K L := by
  rw [Nat.pos_iff_ne_zero, ne_eq, height_eq_zero_iff, not_isTamelyRamified_iff]

/-- **The wild upper bound on the height**: if the ramification index `e` is nonzero in `L`, then
`H(L/K) ≤ v_L(e)`. This is the upper half `d(L/K) ≤ e - 1 + v_L(e)` of Dedekind's different
theorem. -/
theorem height_le_natCastValuation (he : (ramificationIndex K L : L) ≠ 0) :
    height K L ≤ natCastValuation L (ramificationIndex K L) he := by
  have := differentExponent_le_ramificationIndex_sub_one_add_natCastValuation he
  rw [differentExponent_eq_ramificationIndex_sub_one_add_height] at this
  omega

/-- **The height is an invariant of the `K`-isomorphism class.** -/
theorem height_eq_of_algEquiv (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) :
    height K L = height K M := by
  have := finite_of_valuativeExtension K L
  have := finite_of_valuativeExtension K M
  rw [height_eq_differentExponent_add_one_sub, height_eq_differentExponent_add_one_sub,
    differentExponent_eq_of_algEquiv K L M e, ramificationIndex_eq_of_algEquiv K L M e]

/-- The **mean** `m(L/K) = H(L/K) / e` of a separable extension `L/K` of nonarchimedean local
fields: the height divided by the ramification index. The discriminant exponent is
`c = f (e - 1 + e m(L/K))` (`TauCeti.natCast_discriminantExponent_eq_inertiaDegree_mul_mean`). -/
def mean : ℚ :=
  height K L / ramificationIndex K L

/-- The defining formula of `mean`: `m(L/K) = H(L/K) / e`. -/
theorem mean_def : mean K L = height K L / ramificationIndex K L :=
  (rfl)

/-- The height is the ramification index times the mean: `e m(L/K) = H(L/K)`. -/
theorem ramificationIndex_mul_mean :
    (ramificationIndex K L : ℚ) * mean K L = height K L := by
  rw [mean_def, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 ramificationIndex_pos.ne')]

/-- **The discriminant exponent in terms of the mean**: `c = f (e - 1 + e m(L/K))`. -/
theorem natCast_discriminantExponent_eq_inertiaDegree_mul_mean :
    (discriminantExponent K L : ℚ) =
      inertiaDegree K L * (ramificationIndex K L - 1 + ramificationIndex K L * mean K L) := by
  have he : 1 ≤ ramificationIndex K L := ramificationIndex_pos
  rw [ramificationIndex_mul_mean, discriminantExponent_eq_inertiaDegree_mul_add_height]
  push_cast [he]
  ring

/-- The mean is nonnegative. -/
theorem mean_nonneg : 0 ≤ mean K L := by
  rw [mean_def]
  positivity

/-- **The mean vanishes exactly in the tame case.** -/
@[simp]
theorem mean_eq_zero_iff : mean K L = 0 ↔ IsTamelyRamified K L := by
  rw [mean_def, div_eq_zero_iff, Nat.cast_eq_zero, Nat.cast_eq_zero, height_eq_zero_iff,
    or_iff_left ramificationIndex_pos.ne']

/-- The mean is positive exactly in the wild case. -/
theorem mean_pos_iff : 0 < mean K L ↔ IsWildlyRamified K L := by
  rw [(mean_nonneg K L).lt_iff_ne', ne_eq, mean_eq_zero_iff, not_isTamelyRamified_iff]

/-- **The wild upper bound on the mean**: if the ramification index `e` is nonzero in `K`, then
`m(L/K) ≤ v_K(e)`. Over `ℚ_p` the bound is `v_p(e)`, the exponent of the wild ramification
index. -/
theorem mean_le_natCastValuation (he : (ramificationIndex K L : K) ≠ 0) :
    mean K L ≤ natCastValuation K (ramificationIndex K L) he := by
  have heL : (ramificationIndex K L : L) ≠ 0 := by
    simpa using (map_ne_zero (algebraMap K L)).2 he
  have hepos : (0 : ℚ) < ramificationIndex K L := Nat.cast_pos.2 ramificationIndex_pos
  have h := height_le_natCastValuation K L heL
  rw [natCastValuation_eq_ramificationIndex_mul (L := L) _ he] at h
  rw [mean_def, div_le_iff₀ hepos, mul_comm]
  exact_mod_cast h

/-- **The mean is an invariant of the `K`-isomorphism class.** -/
theorem mean_eq_of_algEquiv (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) :
    mean K L = mean K M := by
  rw [mean_def, mean_def, height_eq_of_algEquiv K L M e, ramificationIndex_eq_of_algEquiv K L M e]

section Tower

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M] [ValuativeExtension K M] [Algebra.IsSeparable K M]

omit [Algebra.IsSeparable K L] in
/-- **The height over an unramified base.** In a tower `M/L/K` with `L/K` unramified,
`H(M/L) = H(M/K)`. -/
theorem IsUnramified.height_tower_eq [IsUnramified K L] :
    haveI := Algebra.isSeparable_tower_top_of_isSeparable K L M
    height L M = height K M := by
  have := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [height_eq_differentExponent_add_one_sub, height_eq_differentExponent_add_one_sub,
    IsUnramified.ramificationIndex_tower_eq K L M, ← IsUnramified.differentExponent_tower_eq K L M]

omit [Algebra.IsSeparable K L] in
/-- **The mean over an unramified base.** In a tower `M/L/K` with `L/K` unramified,
`m(M/L) = m(M/K)`. -/
theorem IsUnramified.mean_tower_eq [IsUnramified K L] :
    haveI := Algebra.isSeparable_tower_top_of_isSeparable K L M
    mean L M = mean K M := by
  have := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [mean_def, mean_def, IsUnramified.height_tower_eq K L M,
    IsUnramified.ramificationIndex_tower_eq K L M]

end Tower

section TotallyRamified

variable [ValuativeRel (unramifiedExtension K L (inertiaDegree K L))]
  [TopologicalSpace (unramifiedExtension K L (inertiaDegree K L))]
  [IsNonarchimedeanLocalField (unramifiedExtension K L (inertiaDegree K L))]
  [ValuativeExtension K (unramifiedExtension K L (inertiaDegree K L))]

/-- **The height is that of the totally ramified step of the canonical tower.** For the maximal
unramified subextension `L₀` of `L/K`, `H(L/L₀) = H(L/K)`. -/
@[simp]
theorem height_unramifiedExtension_inertiaDegree :
    height (unramifiedExtension K L (inertiaDegree K L)) L = height K L :=
  have := isUnramified_unramifiedExtension_inertiaDegree K L
  IsUnramified.height_tower_eq K _ L

/-- **The mean is that of the totally ramified step of the canonical tower.** For the maximal
unramified subextension `L₀` of `L/K`, `m(L/L₀) = m(L/K)`. -/
@[simp]
theorem mean_unramifiedExtension_inertiaDegree :
    mean (unramifiedExtension K L (inertiaDegree K L)) L = mean K L :=
  have := isUnramified_unramifiedExtension_inertiaDegree K L
  IsUnramified.mean_tower_eq K _ L

end TotallyRamified

end TauCeti
