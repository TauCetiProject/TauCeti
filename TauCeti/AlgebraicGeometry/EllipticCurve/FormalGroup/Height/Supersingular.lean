/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.InseparableDegree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Ordinary height one and supersingular height two of elliptic formal groups at every prime

Let `W` be an elliptic curve over a field `K`, with formal group `Ê = formalGroup W`. For every
nonzero integer `n`, the formal series of `[n] : W → W` is `[n]_Ê`
(`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`), and the order of an isogeny's formal
series is its inseparable degree (`TauCeti.Isogeny.order_formalSeries`). Hence

`ord([n]_Ê) = deg_i([n])`

over every field (`order_zsmulSeries_formalGroup`, `order_nsmulSeries_formalGroup`), and `[n]_Ê ≠ 0`
for `n ≠ 0` (`zsmulSeries_formalGroup_ne_zero`).

When `K` has prime characteristic `p`, multiplication by `p` on `W` has degree `p²`
(`TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero`), and `W` is ordinary (resp. supersingular)
exactly when `[p]` has separable degree `p` (resp. `1`), by
`isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq` and
`isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one` (Silverman V.3.1). Reading
`deg_s([p]) · deg_i([p]) = p²` against `ord([p]_Ê) = deg_i([p])` yields the complete height
stratification of elliptic formal groups at every prime `p`, including `p = 2` and `p = 3`:

* `height_formalGroup_eq_one_or_eq_two` and `height_formalGroup_le_two`: the formal group of an
  elliptic curve in characteristic `p` has height `1` or `2` (Silverman IV.7.5).
* `isOrdinary_iff_height_formalGroup_eq_one` and `isSupersingular_iff_height_formalGroup_eq_two`:
  `W` is ordinary if and only if `Ê` has height `1`, and supersingular if and only if `Ê` has
  height `2` (Silverman V.3.1(a)(iii)).
* `isOrdinary_iff_coeff_invariantDifferential_ne_zero` and
  `isSupersingular_iff_coeff_invariantDifferential_eq_zero`: `W` is supersingular if and only if
  the Hasse invariant — the coefficient of `Tᵖ⁻¹` in `(formalGroup W).invariantDifferential` —
  vanishes (Silverman V.4.1).
* `isOrdinary_iff_heightIdeal_formalGroup_two_eq_top`,
  `isSupersingular_iff_heightIdeal_formalGroup_two_eq_bot`, and
  `heightIdeal_formalGroup_eq_top_of_three_le`: in terms of Landweber's height ideals `I_n(Ê)`,
  `I₂(Ê)` is `⊤` on the ordinary locus and `⊥` on the supersingular locus, while `I_n(Ê) = ⊤` for
  all `n ≥ 3` on every elliptic curve.

## Main results

* `WeierstrassCurve.order_zsmulSeries_formalGroup`,
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: `ord([n]_Ê) = deg_i([n])` for `n ≠ 0`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`,
  `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: ordinary height `1` and
  supersingular height `2` at every prime `p`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two`,
  `WeierstrassCurve.height_formalGroup_le_two`: `(formalGroup W).height p ∈ {1, 2}`.
* `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`: Hasse-invariant
  criterion for supersingularity at every prime `p`.
* `WeierstrassCurve.isOrdinary_iff_heightIdeal_formalGroup_two_eq_top`,
  `WeierstrassCurve.isSupersingular_iff_heightIdeal_formalGroup_two_eq_bot`,
  `WeierstrassCurve.heightIdeal_formalGroup_eq_top_of_three_le`: Landweber height-ideal dictionary.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7.5, V.3.1, and V.4.1.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
-/

public section

namespace WeierstrassCurve

section Field

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The order of `[n]_Ê` (`n ≠ 0`) equals the inseparable degree of `[n] : W → W`.** -/
theorem order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero W hn,
    TauCeti.Isogeny.order_formalSeries]

/-- **The order of `[n]_Ê` for a nonzero natural number `n` equals the inseparable degree of
`[n] : W → W`.** -/
theorem order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine
        (Nat.cast_ne_zero.mpr hn)).inseparableDegree := by
  rw [← (formalGroup W).zsmulSeries_natCast, order_zsmulSeries_formalGroup]

/-- **For every nonzero integer `n`, multiplication by `n` on `formalGroup W` is nonzero**
(Silverman IV.7.5). -/
theorem zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  rw [Ne, ← PowerSeries.order_eq_top, order_zsmulSeries_formalGroup W hn]
  exact ENat.natCast_ne_top _

/-- **For every nonzero natural number `n`, `[n]_Ê` is nonzero on an elliptic curve**
(Silverman IV.7.5). -/
theorem nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← (formalGroup W).zsmulSeries_natCast]
  exact W.zsmulSeries_formalGroup_ne_zero (Nat.cast_ne_zero.mpr hn)

/-- **For every nonzero `p : ℕ`, the `p`-height of `formalGroup W` over any field is finite**
(Silverman IV.7.5: `[p]_Ê ≠ 0`). -/
theorem height_formalGroup_ne_top {p : ℕ} (hp : p ≠ 0) : (formalGroup W).height p ≠ ⊤ := by
  rw [Ne, FormalGroup.height_eq_top_iff]
  exact W.nsmulSeries_formalGroup_ne_zero hp

end Field

section PrimeChar

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **An elliptic curve in characteristic `p` is ordinary if and only if its formal group has
height `1`** (Silverman V.3.1, including `p = 2, 3`). -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have : ExpChar K p := .prime hp.out
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hp0
  have hdeg : φ.separableDegree * φ.inseparableDegree = p * p := by
    rw [φ.separableDegree_mul_inseparableDegree,
      TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast, sq]
  rw [W.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p hp.out,
    show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, (formalGroup W).height_eq_natCast_iff,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, pow_one, Nat.cast_inj (R := ℕ∞)]
  exact ⟨fun hs ↦ mul_left_cancel₀ hp.out.ne_zero (by rwa [hs] at hdeg),
    fun hi ↦ mul_right_cancel₀ hp.out.ne_zero (by rwa [hi] at hdeg)⟩

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height `2`** (Silverman V.3.1, including `p = 2, 3`). -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have : ExpChar K p := .prime hp.out
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hp0
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree,
      TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast]
  rw [W.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p,
    show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl, (formalGroup W).height_eq_natCast_iff,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  refine ⟨fun hs ↦ ?_, fun hi ↦ ?_⟩
  · rwa [hs, one_mul] at hdeg
  · exact mul_right_cancel₀ (pow_ne_zero 2 hp.out.ne_zero) (by rw [one_mul]; rwa [hi] at hdeg)

/-- **The formal group of an elliptic curve in characteristic `p` has height `1` or `2`**
(Silverman IV.7.5). -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsSupersingular p
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp h)
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp (W.not_isSupersingular.mp h))

/-- **The formal group of an elliptic curve in characteristic `p` has height at most `2`**
(Silverman IV.7.5). -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h <;> simp [h]

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height strictly greater than `1`.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← W.not_isOrdinary, W.isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **Hasse-invariant criterion for ordinarity**: in characteristic `p`, an elliptic curve is
ordinary if and only if the coefficient of `Tᵖ⁻¹` in the invariant differential of its formal group
is nonzero (Silverman V.4.1). -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rw [W.isOrdinary_iff_height_formalGroup_eq_one, W.height_formalGroup_eq_one_iff]

/-- **Hasse-invariant criterion for supersingularity**: in characteristic `p`, an elliptic curve is
supersingular if and only if the coefficient of `Tᵖ⁻¹` in the invariant differential of its formal
group vanishes (Silverman V.4.1). -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← W.not_isOrdinary, W.isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_not]

/-- **In characteristic `p`, an elliptic curve is ordinary if and only if its second Landweber
height ideal `I₂(Ê)` is the unit ideal.** -/
theorem isOrdinary_iff_heightIdeal_formalGroup_two_eq_top :
    W.IsOrdinary p ↔ (formalGroup W).heightIdeal p 2 = ⊤ := by
  rw [(formalGroup W).heightIdeal_eq_top_iff_height_lt, W.isOrdinary_iff_height_formalGroup_eq_one]
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h <;> simp [h]

/-- **In characteristic `p`, an elliptic curve is supersingular if and only if its second
Landweber height ideal `I₂(Ê)` vanishes.** -/
theorem isSupersingular_iff_heightIdeal_formalGroup_two_eq_bot :
    W.IsSupersingular p ↔ (formalGroup W).heightIdeal p 2 = ⊥ := by
  rw [(formalGroup W).heightIdeal_eq_bot_iff_le_height,
    W.isSupersingular_iff_height_formalGroup_eq_two]
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h <;> simp [h]

/-- **Every Landweber height ideal `I_n(Ê)` with `n ≥ 3` of an elliptic curve in characteristic `p`
is the unit ideal**, because `(formalGroup W).height p ≤ 2 < n`. -/
theorem heightIdeal_formalGroup_eq_top_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ := by
  rw [(formalGroup W).heightIdeal_eq_top_iff_height_lt]
  exact W.height_formalGroup_le_two.trans_lt (by exact_mod_cast (by omega : 2 < n))

@[simp]
theorem heightIdeal_formalGroup_three_eq_top : (formalGroup W).heightIdeal p 3 = ⊤ :=
  W.heightIdeal_formalGroup_eq_top_of_three_le le_rfl

end PrimeChar

end WeierstrassCurve

namespace TauCeti.Isogeny

/-- **Isogenous elliptic curves over a field have the same formal-group `p`-height.** -/
theorem height_formalGroup_eq {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) :
    (WeierstrassCurve.formalGroup W₁).height p = (WeierstrassCurve.formalGroup W₂).height p :=
  φ.formalGroupHom.height_eq (φ.formalGroupHom_toPowerSeries.symm ▸ φ.formalSeries_ne_zero) p

end TauCeti.Isogeny

end
