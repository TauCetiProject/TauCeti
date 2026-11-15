/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Hom
-- Proof-only: the domain of an isogeny to an elliptic curve is elliptic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
-- Proof-only: `deg [n] = n²`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
-- Proof-only: supersingularity and ordinarity in terms of the separable degree of `[p]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Formal-group height of ordinary and supersingular elliptic curves

Let `W` be an elliptic curve over a field `K`, with formal group law `Ê = formalGroup W`. For every
nonzero integer `n`, the formal power series at infinity of multiplication by `n` is the
multiplication-by-`n` series `[n]_Ê(T)` (`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`),
whose order of vanishing equals the inseparable degree of `[n] : W → W`
(`TauCeti.Isogeny.order_formalSeries`). In particular `[n]_Ê ≠ 0`, so `Ê` never has infinite height
at a nonzero integer (`WeierstrassCurve.height_formalGroup_ne_top`).

When `K` has prime characteristic `p`, the isogeny `[p] : W → W` has degree `p²`, factored into its
separable and inseparable degrees:

* `W` is ordinary if and only if `[p]` has separable degree `p`, hence inseparable degree `p`, so
  `[p]_Ê(T)` has order `p` and `Ê` has height `1`
  (`WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`).
* `W` is supersingular if and only if `[p]` is purely inseparable (has separable degree `1`), hence
  has inseparable degree `p²`, so `[p]_Ê(T)` has order `p²` and `Ê` has height `2`
  (`WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`).

Consequently, the formal group of an elliptic curve in characteristic `p` has height `1` or `2`,
and in particular height at most `2` (`WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
`WeierstrassCurve.height_formalGroup_le_two`), including in characteristics `2` and `3` without
coordinate normalization. Combining with `WeierstrassCurve.height_formalGroup_eq_one_iff` gives the
Hasse-invariant criterion at every prime: `W` is supersingular if and only if the coefficient of
`Tᵖ⁻¹` in the invariant differential of `Ê` vanishes
(`WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero`). Finally,
since an isogeny preserves the height of the formal group (`TauCeti.Isogeny.height_formalGroup_eq`),
isogenous elliptic curves are simultaneously supersingular and simultaneously ordinary
(`TauCeti.Isogeny.isSupersingular_iff` and `TauCeti.Isogeny.isOrdinary_iff`).

## Main results

* `WeierstrassCurve.zsmulSeries_formalGroup_ne_zero` and
  `WeierstrassCurve.nsmulSeries_formalGroup_ne_zero`: `[n]_Ê ≠ 0` for every nonzero `n` on an
  elliptic curve over a field.
* `WeierstrassCurve.order_zsmulSeries_formalGroup` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: the order of `[n]_Ê` is the inseparable degree
  of `[n]`.
* `WeierstrassCurve.height_formalGroup_ne_top`: `(formalGroup W).height p ≠ ⊤` for `p ≠ 0`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`: in characteristic `p`, `W` is
  ordinary if and only if `(formalGroup W).height p = 1`.
* `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: in characteristic `p`, `W` is
  supersingular if and only if `(formalGroup W).height p = 2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the height of `formalGroup W` is `1` or `2`, hence
  at most `2`.
* `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero` and
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero`: the
  Hasse-invariant criterion for ordinarity and supersingularity in every prime characteristic.
* `TauCeti.Isogeny.isSupersingular_iff` and `TauCeti.Isogeny.isOrdinary_iff`: supersingularity and
  ordinarity are invariant under isogenies.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, IV.7 and V.3.1.
-/

public section

open TauCeti.Isogeny

namespace WeierstrassCurve

section ArbitraryField

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- On an elliptic curve over a field, the formal-group multiplication series `[n]_Ê` is nonzero for
every nonzero `n : ℤ`. -/
theorem zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero W hn]
  exact (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries_ne_zero

/-- On an elliptic curve over a field, the formal-group multiplication series `[n]_Ê` is nonzero for
every nonzero `n : ℕ`. -/
theorem nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← (formalGroup W).zsmulSeries_natCast n]
  exact W.zsmulSeries_formalGroup_ne_zero (Nat.cast_ne_zero.mpr hn)

/-- The order of vanishing of `[n]_Ê(T)` is the inseparable degree of `[n] : W → W`. -/
theorem order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero W hn, order_formalSeries]

/-- The order of vanishing of `[n]_Ê(T)` for `n : ℕ` (`n ≠ 0`) is the inseparable degree of
`[n] : W → W`. -/
theorem order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine (Nat.cast_ne_zero.mpr hn)).inseparableDegree := by
  rw [← (formalGroup W).zsmulSeries_natCast n, order_zsmulSeries_formalGroup]

/-- The formal group of an elliptic curve over a field never has infinite height at `p ≠ 0`. -/
theorem height_formalGroup_ne_top {p : ℕ} (hp : p ≠ 0) : (formalGroup W).height p ≠ ⊤ :=
  (formalGroup W).height_eq_top_iff.not.mpr (W.nsmulSeries_formalGroup_ne_zero hp)

end ArbitraryField

section PrimeChar

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
  {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- **An elliptic curve in characteristic `p` is ordinary if and only if its formal group has height
one** (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have hn : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let φ := mulByIntIsogenyOfNeZero W.toAffine hn
  have hdeg : φ.separableDegree * φ.inseparableDegree = p * p := by
    rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast, sq]
  rw [isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p W hp.out,
    ← Nat.cast_one (R := ℕ∞), (formalGroup W).height_eq_natCast_iff, pow_one,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  exact ⟨fun h ↦ Nat.eq_of_mul_eq_mul_left hp.out.pos (by rwa [h] at hdeg),
    fun h ↦ Nat.eq_of_mul_eq_mul_right hp.out.pos (by rwa [h] at hdeg)⟩

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height two** (Silverman V.3.1). -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have hn : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let φ := mulByIntIsogenyOfNeZero W.toAffine hn
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast]
  rw [isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p W,
    ← Nat.cast_ofNat (R := ℕ∞), (formalGroup W).height_eq_natCast_iff,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  exact ⟨fun h ↦ by rwa [h, one_mul] at hdeg,
    fun h ↦ (Nat.mul_eq_right (pow_ne_zero 2 hp.out.ne_zero)).mp (by rwa [h] at hdeg)⟩

/-- **The formal group of an elliptic curve in characteristic `p` has height `1` or `2`**
(Silverman IV.7.5). -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  rcases em (W.IsSupersingular p) with h | h
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp h)
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp (not_isSupersingular.mp h))

/-- **The formal group of an elliptic curve in characteristic `p` has height at most `2`**. -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h <;> rw [h]
  exact one_le_two

/-- In characteristic `p`, an elliptic curve is supersingular if and only if its formal group has
height greater than one. -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **Hasse-invariant criterion for ordinarity**: over a field of characteristic `p`, an elliptic
curve is ordinary if and only if the coefficient of `Tᵖ⁻¹` in the invariant differential of its
formal group is nonzero. -/
theorem isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 :=
  W.isOrdinary_iff_height_formalGroup_eq_one.trans W.height_formalGroup_eq_one_iff

/-- **Hasse-invariant criterion for supersingularity**: over a field of characteristic `p`, an
elliptic curve is supersingular if and only if the coefficient of `Tᵖ⁻¹` in the invariant
differential of its formal group vanishes. -/
theorem isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero, not_not]

end PrimeChar

end WeierstrassCurve

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- **Supersingularity is invariant under isogeny**: if there is an isogeny `φ : W₁ → W₂` of
elliptic curves over a field of exponential characteristic `p`, then `W₁` is supersingular if and
only if `W₂` is. -/
theorem isSupersingular_iff {p : ℕ} [ExpChar K p] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.IsSupersingular p ↔ W₂.IsSupersingular p := by
  classical
  have : W₁.IsElliptic := φ.isElliptic
  rcases ‹ExpChar K p› with _ | hprime
  · simp [WeierstrassCurve.isSupersingular_iff_forall]
  · have : Fact p.Prime := ⟨hprime⟩
    rw [W₁.isSupersingular_iff_height_formalGroup_eq_two,
      W₂.isSupersingular_iff_height_formalGroup_eq_two, φ.height_formalGroup_eq]

/-- **Ordinarity is invariant under isogeny**: if there is an isogeny `φ : W₁ → W₂` of elliptic
curves over a field of exponential characteristic `p`, then `W₁` is ordinary if and only if `W₂`
is. -/
theorem isOrdinary_iff {p : ℕ} [ExpChar K p] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.IsOrdinary p ↔ W₂.IsOrdinary p := by
  rw [← WeierstrassCurve.not_isSupersingular, ← WeierstrassCurve.not_isSupersingular,
    φ.isSupersingular_iff]

end TauCeti.Isogeny
