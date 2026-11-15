/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.NumberTheory.LocalField.Unramified.Factorization
import TauCeti.NumberTheory.LocalField.Different.Tower
import TauCeti.NumberTheory.LocalField.Different.Wild

/-!
# Height and mean of a separable extension of local fields

Let `L/K` be a separable extension of nonarchimedean local fields with compatible valuations, of
ramification index `e = e(L/K)`, inertia degree `f = f(L/K)`, different exponent `d = d(L/K)`, and
discriminant exponent `δ = δ(L/K) = f · d`. By Dedekind's different theorem, `e - 1 ≤ d`, with
equality if and only if `L/K` is tamely ramified.

This file introduces the nonnegative integer excess over the tame bound, the **height**

`H(L/K) = δ / f + 1 - e = d + 1 - e : ℕ`,

together with its normalized rational counterpart, the **mean**

`m(L/K) = H(L/K) / e : ℚ`.

When `L/K` is totally ramified (`f = 1`, `e = [L : K]`), the height is Serre's wild exponent
`δ + 1 - [L : K]` from the local mass formula (`IntermediateField.wildExponent`). Defining `H` via
`δ / f + 1 - e` extends that invariant to arbitrary finite separable extensions so that the
discriminant exponent is recovered as `δ = f · (e - 1) + f · H = f · (e - 1 + e · m)`, and passing
to the totally ramified top step `L/L₀` over the maximal unramified subextension `L₀` leaves both
`H` and `m` unchanged.

## Main definitions

* `TauCeti.height K L`: the height `H(L/K) = δ(L/K) / f(L/K) + 1 - e(L/K)` of a separable
  extension of nonarchimedean local fields.
* `TauCeti.mean K L`: the mean `m(L/K) = H(L/K) / e(L/K) ∈ ℚ`.

## Main results

* `TauCeti.height_eq_differentExponent_add_one_sub_ramificationIndex` and
  `TauCeti.differentExponent_eq_ramificationIndex_sub_one_add_height`: `H = d + 1 - e` and the
  faithful recovery `d = e - 1 + H`.
* `TauCeti.discriminantExponent_eq_inertiaDegree_mul_add_height` and
  `TauCeti.ratCast_discriminantExponent_eq_mul_mean`: `δ = f · (e - 1) + f · H` and its rational
  form `δ = f · (e - 1 + e · m)`.
* `TauCeti.height_eq_zero_iff`, `TauCeti.mean_eq_zero_iff`, `TauCeti.height_pos_iff`, and
  `TauCeti.mean_pos_iff`: `H` and `m` vanish if and only if `L/K` is tamely ramified, and are
  strictly positive if and only if `L/K` is wildly ramified.
* `TauCeti.height_le_natCastValuation`: when `(e(L/K) : L) ≠ 0`, `H(L/K) ≤ v_L(e(L/K))`.
* `TauCeti.height_eq_of_algEquiv` and `TauCeti.mean_eq_of_algEquiv`: invariance under
  `K`-algebra equivalence.
* `TauCeti.height_tower` and `TauCeti.mean_tower`: in a finite separable tower `M/L/K`,
  `H(M/K) = H(M/L) + e(M/L) · H(L/K)` and `m(M/K) = m(L/K) + m(M/L) / e(L/K)`.
* `TauCeti.height_unramifiedExtension_inertiaDegree` and
  `TauCeti.mean_unramifiedExtension_inertiaDegree`: invariance under passage to the totally
  ramified step over the maximal unramified subextension.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §§4 and 6.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and C. Sinclair, *Enumerating extensions of `(π)`-adic fields with given invariants*,
  Int. J. Number Theory **13** (2017), 2007–2038.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsSeparable K L]

/-- The **height** `H(L/K) = δ(L/K) / f(L/K) + 1 - e(L/K)` of a separable extension `L/K` of
nonarchimedean local fields: the excess of the different exponent `d(L/K) = δ(L/K) / f(L/K)` over
the tame bound `e(L/K) - 1`. For a totally ramified extension this agrees with Serre's wild
exponent `δ(L/K) + 1 - [L : K]`. -/
def height (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Algebra.IsSeparable K L] : ℕ :=
  discriminantExponent K L / inertiaDegree K L + 1 - ramificationIndex K L

/-- The **mean** `m(L/K) = H(L/K) / e(L/K)` of a separable extension `L/K` of nonarchimedean local
fields: the height divided by the ramification index. -/
def mean (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Algebra.IsSeparable K L] : ℚ :=
  (height K L : ℚ) / ramificationIndex K L

/-- The defining formula for `height`. -/
theorem height_def :
    height K L = discriminantExponent K L / inertiaDegree K L + 1 - ramificationIndex K L := (rfl)

/-- The defining formula for `mean`. -/
theorem mean_def :
    mean K L = (height K L : ℚ) / ramificationIndex K L := (rfl)

/-- Since `δ(L/K) = f(L/K) · d(L/K)` and `f(L/K) > 0`, the height is
`d(L/K) + 1 - e(L/K)`. -/
theorem height_eq_differentExponent_add_one_sub_ramificationIndex :
    height K L = differentExponent K L + 1 - ramificationIndex K L := by
  rw [height_def, discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    Nat.mul_div_right _ (inertiaDegree_pos (K := K) (L := L))]

/-- **Faithfulness of the height**: `d(L/K) = e(L/K) - 1 + H(L/K)`. Because `e(L/K) - 1 ≤ d(L/K)`,
the truncated subtraction in `height` loses no information. -/
theorem differentExponent_eq_ramificationIndex_sub_one_add_height :
    differentExponent K L = ramificationIndex K L - 1 + height K L := by
  have hd := ramificationIndex_sub_one_le_differentExponent K L
  have he := ramificationIndex_pos (K := K) (L := L)
  rw [height_eq_differentExponent_add_one_sub_ramificationIndex]
  omega

/-- Equivalent additive form of faithfulness in `ℕ`: `H(L/K) + e(L/K) = d(L/K) + 1`. -/
theorem height_add_ramificationIndex :
    height K L + ramificationIndex K L = differentExponent K L + 1 := by
  have hd := ramificationIndex_sub_one_le_differentExponent K L
  have he := ramificationIndex_pos (K := K) (L := L)
  rw [height_eq_differentExponent_add_one_sub_ramificationIndex]
  omega

/-- Cast to `ℤ`, the height is `d(L/K) - e(L/K) + 1`. -/
theorem natCast_height :
    (height K L : ℤ) = differentExponent K L - ramificationIndex K L + 1 := by
  have := height_add_ramificationIndex K L
  omega

/-- **Recovery of the discriminant exponent from the height**:
`δ(L/K) = f(L/K) · (e(L/K) - 1) + f(L/K) · H(L/K)`. -/
theorem discriminantExponent_eq_inertiaDegree_mul_add_height :
    discriminantExponent K L =
      inertiaDegree K L * (ramificationIndex K L - 1) + inertiaDegree K L * height K L := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    differentExponent_eq_ramificationIndex_sub_one_add_height, mul_add]

/-- Factored form of the discriminant-exponent identity:
`δ(L/K) = f(L/K) · (e(L/K) - 1 + H(L/K))`. -/
theorem discriminantExponent_eq_inertiaDegree_mul_ramificationIndex_sub_one_add_height :
    discriminantExponent K L =
      inertiaDegree K L * (ramificationIndex K L - 1 + height K L) := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    differentExponent_eq_ramificationIndex_sub_one_add_height]

variable {K L} in
/-- For a totally ramified separable extension, the height is `δ(L/K) + 1 - [L : K]`. -/
theorem IsTotallyRamified.height_eq (h : IsTotallyRamified K L) :
    height K L = discriminantExponent K L + 1 - Module.finrank K L := by
  rw [height_def, h.inertiaDegree_eq_one, Nat.div_one,
    (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 h]

/-- Multiplying the mean by the ramification index recovers the height in `ℚ`. -/
@[simp]
theorem ramificationIndex_mul_mean :
    (ramificationIndex K L : ℚ) * mean K L = height K L := by
  have he : (ramificationIndex K L : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ramificationIndex_pos (K := K) (L := L)).ne'
  rw [mean_def, mul_div_cancel₀ _ he]

/-- Rational form of the discriminant formula in terms of the mean:
`δ(L/K) = f(L/K) · (e(L/K) - 1 + e(L/K) · m(L/K))`. -/
theorem ratCast_discriminantExponent_eq_mul_mean :
    (discriminantExponent K L : ℚ) =
      inertiaDegree K L * (ramificationIndex K L - 1 + ramificationIndex K L * mean K L) := by
  have he : 1 ≤ ramificationIndex K L := ramificationIndex_pos (K := K) (L := L)
  rw [ramificationIndex_mul_mean,
    discriminantExponent_eq_inertiaDegree_mul_ramificationIndex_sub_one_add_height]
  push_cast [he]
  ring

/-- The mean of a separable extension of local fields is nonnegative. -/
theorem mean_nonneg : 0 ≤ mean K L := by
  rw [mean_def]
  positivity

/-- **The tame criterion for the height**: `H(L/K) = 0` if and only if `L/K` is tamely
ramified. -/
@[simp]
theorem height_eq_zero_iff : height K L = 0 ↔ IsTamelyRamified K L := by
  have hd := ramificationIndex_sub_one_le_differentExponent K L
  have he := ramificationIndex_pos (K := K) (L := L)
  rw [height_eq_differentExponent_add_one_sub_ramificationIndex,
    ← differentExponent_eq_ramificationIndex_sub_one_iff]
  omega

/-- **The wild criterion for the height**: `0 < H(L/K)` if and only if `L/K` is wildly
ramified. -/
@[simp]
theorem height_pos_iff : 0 < height K L ↔ IsWildlyRamified K L := by
  rw [Nat.pos_iff_ne_zero, ne_eq, height_eq_zero_iff, not_isTamelyRamified_iff]

/-- **The tame criterion for the mean**: `m(L/K) = 0` if and only if `L/K` is tamely ramified. -/
@[simp]
theorem mean_eq_zero_iff : mean K L = 0 ↔ IsTamelyRamified K L := by
  have he : (ramificationIndex K L : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ramificationIndex_pos (K := K) (L := L)).ne'
  rw [mean_def, div_eq_zero_iff, or_iff_left he, Nat.cast_eq_zero, height_eq_zero_iff]

/-- **The wild criterion for the mean**: `0 < m(L/K)` if and only if `L/K` is wildly ramified. -/
@[simp]
theorem mean_pos_iff : 0 < mean K L ↔ IsWildlyRamified K L := by
  rw [lt_iff_le_and_ne, and_iff_right (mean_nonneg K L), ne_comm, ne_eq, mean_eq_zero_iff,
    not_isTamelyRamified_iff]

variable {K L} in
/-- A tamely ramified extension has height `0`. -/
theorem IsTamelyRamified.height_eq_zero (h : IsTamelyRamified K L) : height K L = 0 :=
  (height_eq_zero_iff K L).2 h

variable {K L} in
/-- A tamely ramified extension has mean `0`. -/
theorem IsTamelyRamified.mean_eq_zero (h : IsTamelyRamified K L) : mean K L = 0 :=
  (mean_eq_zero_iff K L).2 h

/-- An unramified extension has height `0`. -/
theorem IsUnramified.height_eq_zero [IsUnramified K L] : height K L = 0 :=
  (IsUnramified.isTamelyRamified K L).height_eq_zero

/-- An unramified extension has mean `0`. -/
theorem IsUnramified.mean_eq_zero [IsUnramified K L] : mean K L = 0 :=
  (IsUnramified.isTamelyRamified K L).mean_eq_zero

variable {K L} in
/-- **The wild upper bound for the height**: if the ramification index `e(L/K)` is nonzero in `L`
(in particular in mixed characteristic), then `H(L/K) ≤ v_L(e(L/K))`. -/
theorem height_le_natCastValuation (he : (ramificationIndex K L : L) ≠ 0) :
    height K L ≤ natCastValuation L (ramificationIndex K L) he := by
  have h := differentExponent_le_ramificationIndex_sub_one_add_natCastValuation (K := K) he
  rw [differentExponent_eq_ramificationIndex_sub_one_add_height] at h
  omega

section AlgEquiv

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]

/-- The height is invariant under `K`-algebra equivalence of extensions. -/
theorem height_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    height K L =
      (let _ : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
       height K M) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  let _ : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
  rw [height_def, height_def, discriminantExponent_eq_of_algEquiv K L M e,
    inertiaDegree_eq_of_algEquiv K L M e, ramificationIndex_eq_of_algEquiv K L M e]

/-- The mean is invariant under `K`-algebra equivalence of extensions. -/
theorem mean_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    mean K L =
      (let _ : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
       mean K M) := by
  let _ : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
  rw [mean_def, mean_def, height_eq_of_algEquiv K L M e, ramificationIndex_eq_of_algEquiv K L M e]

end AlgEquiv

section Tower

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M] [Algebra.IsSeparable K M]

omit [Algebra.IsSeparable K L] in
/-- **Transitivity of height in towers**: for a tower `M/L/K` of separable extensions of
nonarchimedean local fields, `H(M/K) = H(M/L) + e(M/L) · H(L/K)`. -/
theorem height_tower :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    height K M = height L M + ramificationIndex L M * height K L := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  let _ : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  have heKL : 1 ≤ ramificationIndex K L := ramificationIndex_pos (K := K) (L := L)
  have heLM : 1 ≤ ramificationIndex L M := ramificationIndex_pos (K := L) (L := M)
  have heKM : 1 ≤ ramificationIndex K L * ramificationIndex L M := Nat.mul_pos heKL heLM
  have hd := differentExponent_tower K L M
  rw [differentExponent_eq_ramificationIndex_sub_one_add_height K M,
    differentExponent_eq_ramificationIndex_sub_one_add_height L M,
    differentExponent_eq_ramificationIndex_sub_one_add_height K L,
    ramificationIndex_tower (K := K) (L := L) M] at hd
  zify [heKL, heLM, heKM] at hd ⊢
  linarith

omit [Algebra.IsSeparable K L] in
/-- **Transitivity of mean in towers**: for a tower `M/L/K` of separable extensions of
nonarchimedean local fields, `m(M/K) = m(L/K) + m(M/L) / e(L/K)`. -/
theorem mean_tower :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    mean K M = mean K L + mean L M / ramificationIndex K L := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  let _ : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  have heKL : (ramificationIndex K L : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ramificationIndex_pos (K := K) (L := L)).ne'
  have heLM : (ramificationIndex L M : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ramificationIndex_pos (K := L) (L := M)).ne'
  rw [mean_def, mean_def, mean_def, height_tower K L M,
    ramificationIndex_tower (K := K) (L := L) M]
  push_cast
  field_simp
  ring

omit [Algebra.IsSeparable K L] in
variable {K L} in
/-- When the bottom step `L/K` of a separable tower `M/L/K` is tamely ramified,
`H(M/K) = H(M/L)`. -/
theorem IsTamelyRamified.height_tower_eq (h : IsTamelyRamified K L) :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    height K M = height L M := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  let _ : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [height_tower K L M, h.height_eq_zero, mul_zero, add_zero]

omit [Algebra.IsSeparable K L] in
variable {L M} in
/-- When the top step `M/L` of a separable tower `M/L/K` is tamely ramified,
`m(M/K) = m(L/K)`. -/
theorem IsTamelyRamified.mean_tower_eq (h : IsTamelyRamified L M) :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
    mean K M = mean K L := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  let _ : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [mean_tower K L M, h.mean_eq_zero, zero_div, add_zero]

omit [Algebra.IsSeparable K L] in
/-- When the bottom step `L/K` of a separable tower `M/L/K` is unramified, `H(M/K) = H(M/L)`. -/
theorem IsUnramified.height_tower_eq [IsUnramified K L] :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    height K M = height L M :=
  (IsUnramified.isTamelyRamified K L).height_tower_eq M

omit [Algebra.IsSeparable K L] in
/-- When the bottom step `L/K` of a separable tower `M/L/K` is unramified, `m(M/K) = m(M/L)`. -/
theorem IsUnramified.mean_tower_eq [IsUnramified K L] :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    mean K M = mean L M := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  let _ : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [mean_tower K L M, IsUnramified.mean_eq_zero K L,
    IsUnramified.ramificationIndex_eq_one (K := K) (L := L), Nat.cast_one, div_one, zero_add]

end Tower

section CanonicalTower

variable [ValuativeRel (unramifiedExtension K L (inertiaDegree K L))]
  [TopologicalSpace (unramifiedExtension K L (inertiaDegree K L))]
  [IsNonarchimedeanLocalField (unramifiedExtension K L (inertiaDegree K L))]
  [ValuativeExtension K (unramifiedExtension K L (inertiaDegree K L))]

/-- The height of the totally ramified top step over the maximal unramified subextension equals the
height of `L/K`. -/
@[simp]
theorem height_unramifiedExtension_inertiaDegree :
    letI : Algebra.IsSeparable (unramifiedExtension K L (inertiaDegree K L)) L :=
      Algebra.isSeparable_tower_top_of_isSeparable K _ L
    height (unramifiedExtension K L (inertiaDegree K L)) L = height K L := by
  have := isUnramified_unramifiedExtension_inertiaDegree K L
  exact (IsUnramified.height_tower_eq K (unramifiedExtension K L (inertiaDegree K L)) L).symm

/-- The mean of the totally ramified top step over the maximal unramified subextension equals the
mean of `L/K`. -/
@[simp]
theorem mean_unramifiedExtension_inertiaDegree :
    letI : Algebra.IsSeparable (unramifiedExtension K L (inertiaDegree K L)) L :=
      Algebra.isSeparable_tower_top_of_isSeparable K _ L
    mean (unramifiedExtension K L (inertiaDegree K L)) L = mean K L := by
  have := isUnramified_unramifiedExtension_inertiaDegree K L
  exact (IsUnramified.mean_tower_eq K (unramifiedExtension K L (inertiaDegree K L)) L).symm

end CanonicalTower

end TauCeti
