/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.FormalSeries
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Formal-group height of ordinary and supersingular elliptic curves

Let `W` be an elliptic curve over a field `K`, with formal group `Ê = formalGroup W` in the
canonical parameter `T = -x / y` at infinity. For a nonzero integer `n`, the formal expansion of the
multiplication-by-`n` isogeny `[n] : W → W` is the formal-group `n`-series `[n]_Ê(T)`
(`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`), and the order of an isogeny's formal
series is its inseparable degree (`TauCeti.Isogeny.order_formalSeries`). Combining the two shows
that `[n]_Ê(T)` has order `deg_i [n]` and is therefore nonzero (`order_zsmulSeries_formalGroup`,
`zsmulSeries_formalGroup_ne_zero`).

When `K` has prime characteristic `p`, `[p]` has total degree `deg_s [p] · deg_i [p] = p²`, while
`W` is ordinary when `deg_s [p] = p` and supersingular when `deg_s [p] = 1`
(`WeierstrassCurve.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq`,
`WeierstrassCurve.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one`). Reading the
exponent of `p` in `ord_T [p]_Ê(T) = deg_i [p]` proves Silverman V.3.1(a)/(c) and IV.7.5 in every
prime characteristic, including `p = 2` and `p = 3`:

* `W` is ordinary if and only if `Ê` has height `1` (`isOrdinary_iff_height_formalGroup_eq_one`),
  equivalently if and only if the Hasse invariant — the coefficient of `Tᵖ⁻¹` in the invariant
  differential — is nonzero (`isOrdinary_iff_coeff_invariantDifferential_ne_zero`).
* `W` is supersingular if and only if `Ê` has height `2`
  (`isSupersingular_iff_height_formalGroup_eq_two`), equivalently if and only if the Hasse
  invariant vanishes (`isSupersingular_iff_coeff_invariantDifferential_eq_zero`), in which case the
  coefficient `v₂` of `T^(p²)` in `[p]_Ê(T)` is nonzero
  (`coeff_nsmulSeries_sq_formalGroup_ne_zero_of_isSupersingular`).
* In particular, `Ê` always has height `1` or `2` (`height_formalGroup_eq_one_or_eq_two`,
  `height_formalGroup_le_two`), and `(formalGroup W).height n ≠ ⊤` for every `n ≠ 0` over any
  field (`height_formalGroup_ne_top`).

## Main results

* `WeierstrassCurve.order_zsmulSeries_formalGroup`,
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: for `n ≠ 0`, `[n]_Ê` has order `deg_i [n]`.
* `WeierstrassCurve.zsmulSeries_formalGroup_ne_zero`,
  `WeierstrassCurve.nsmulSeries_formalGroup_ne_zero`,
  `WeierstrassCurve.height_formalGroup_ne_top`: for `n ≠ 0`, `[n]_Ê ≠ 0` and `height n ≠ ⊤`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`: `W` is ordinary iff `Ê` has height
  `1`.
* `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: `W` is supersingular iff `Ê`
  has height `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two`,
  `WeierstrassCurve.height_formalGroup_le_two`: in characteristic `p`, `Ê` has height `1` or `2`.
* `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero`,
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`: the Hasse-invariant
  criteria for ordinarity and supersingularity in every prime characteristic.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.3, IV.7.5, V.3.1, and
  V.4.1.
-/

public section

open TauCeti.Isogeny

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The order of `[n]_Ê(T)` is the inseparable degree of `[n]`** (Silverman IV.4.3). -/
theorem order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero W hn, order_formalSeries]

/-- For every nonzero integer `n`, the formal-group `n`-series `[n]_Ê(T)` of an elliptic curve over
a field is nonzero. -/
theorem zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  rw [Ne, ← PowerSeries.order_eq_top.not, W.order_zsmulSeries_formalGroup hn]
  exact ENat.natCast_ne_top _

/-- **The order of `[n]_Ê(T)` for a nonzero natural `n` is the inseparable degree of `[n]`.** -/
theorem order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine (Nat.cast_ne_zero.mpr hn)).inseparableDegree := by
  rw [← FormalGroup.zsmulSeries_natCast, W.order_zsmulSeries_formalGroup]

/-- For every nonzero natural `n`, the formal-group `n`-series `[n]_Ê(T)` of an elliptic curve over
a field is nonzero. -/
theorem nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← FormalGroup.zsmulSeries_natCast]
  exact W.zsmulSeries_formalGroup_ne_zero (Nat.cast_ne_zero.mpr hn)

/-- **The formal group of an elliptic curve over a field has finite height at every nonzero `n`.**
-/
theorem height_formalGroup_ne_top {n : ℕ} (hn : n ≠ 0) : (formalGroup W).height n ≠ ⊤ := by
  rw [Ne, FormalGroup.height_eq_top_iff]
  exact W.nsmulSeries_formalGroup_ne_zero hn

section CharP

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- **An elliptic curve in characteristic `p` is ordinary if and only if its formal group has
height `1`** (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have hn : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hdeg := (mulByIntIsogenyOfNeZero W.toAffine hn).separableDegree_mul_inseparableDegree
  rw [degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast, sq] at hdeg
  have hh : (formalGroup W).height p = 1 ↔
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree = p := by
    rw [← Nat.cast_one, FormalGroup.height_eq_natCast_iff, pow_one,
      W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj]
  rw [W.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p hp.out, hh]
  exact ⟨fun hs ↦ mul_left_cancel₀ hp.out.ne_zero (by rwa [hs] at hdeg),
    fun hi ↦ mul_right_cancel₀ hp.out.ne_zero (by rwa [hi] at hdeg)⟩

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height `2`** (Silverman V.3.1, IV.7.5). -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have hn : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hdeg := (mulByIntIsogenyOfNeZero W.toAffine hn).separableDegree_mul_inseparableDegree
  rw [degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast] at hdeg
  have hh : (formalGroup W).height p = 2 ↔
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree = p ^ 2 := by
    rw [← Nat.cast_ofNat (R := ℕ∞), FormalGroup.height_eq_natCast_iff,
      W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj]
  rw [W.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p, hh]
  exact ⟨fun hs ↦ by rwa [hs, one_mul] at hdeg,
    fun hi ↦ mul_right_cancel₀ (pow_ne_zero 2 hp.out.ne_zero)
      ((by rwa [hi] at hdeg : _ * p ^ 2 = p ^ 2).trans (one_mul _).symm)⟩

/-- **The formal group of an elliptic curve in characteristic `p` has height `1` or `2`**
(Silverman IV.7.5). -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsOrdinary p
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp h)
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp (not_isOrdinary.mp h))

/-- **The formal group of an elliptic curve in characteristic `p` has height at most `2`.** -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h <;> rw [h]
  exact one_le_two

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height greater than `1`.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, W.isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **Hasse-invariant criterion for ordinarity**: in characteristic `p`, an elliptic curve is
ordinary if and only if the coefficient of `Tᵖ⁻¹` in its invariant differential is nonzero
(Silverman V.4.1). -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rw [W.isOrdinary_iff_height_formalGroup_eq_one, W.height_formalGroup_eq_one_iff]

/-- **Hasse-invariant criterion for supersingularity**: in characteristic `p`, an elliptic curve is
supersingular if and only if the coefficient of `Tᵖ⁻¹` in its invariant differential vanishes
(Silverman V.4.1). -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, W.isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_not]

/-- On a supersingular elliptic curve in characteristic `p`, Landweber's `v₂` — the coefficient of
`T^(p²)` in `[p]_Ê(T)` — is nonzero. -/
theorem coeff_nsmulSeries_sq_formalGroup_ne_zero_of_isSupersingular (hW : W.IsSupersingular p) :
    PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p) ≠ 0 :=
  (formalGroup W).coeff_nsmulSeries_ne_zero_of_height_eq (h := 2)
    (by exact_mod_cast W.isSupersingular_iff_height_formalGroup_eq_two.mp hW)

end CharP

end WeierstrassCurve

end
