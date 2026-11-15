/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Height of the formal group of an elliptic curve at every prime

Let `W` be an elliptic curve over a field `K`, with formal group law `Ê = formalGroup W` in the
parameter `z = -x/y` at infinity. For any nonzero integer `n`, the order of the `n`-multiplication
series `[n]_Ê` equals the inseparable degree of `[n] : W → W`
(`WeierstrassCurve.order_zsmulSeries_formalGroup`).

Over a field `K` of prime characteristic `p`, multiplication by `p` has degree `p²`, and its
separable degree is `p` when `W` is ordinary and `1` when `W` is supersingular
(`WeierstrassCurve.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq`,
`WeierstrassCurve.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one`). Hence
`[p]_Ê` has order `p` when `W` is ordinary and `p²` when `W` is supersingular, which proves in
every prime characteristic (including `p = 2` and `p = 3`):

* `W` is ordinary if and only if `Ê` has height `1`
  (`WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`), and if and only if the Hasse
  invariant (the coefficient of `Tᵖ⁻¹` in the invariant differential of `Ê`) is nonzero
  (`WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero`);
* `W` is supersingular if and only if `Ê` has height `2`
  (`WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`), and if and only if the Hasse
  invariant vanishes (`WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`);
* the height of `Ê` is always `1` or `2` (`WeierstrassCurve.height_formalGroup_eq_one_or_eq_two`),
  in particular at most `2` (`WeierstrassCurve.height_formalGroup_le_two`).

## Main results

* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`: `W` is ordinary iff `Ê` has
  height `1`.
* `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: `W` is supersingular iff `Ê`
  has height `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the height of `Ê` is `1` or `2`, hence at most `2`.
* `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero` and
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`: the
  formal-differential Hasse-invariant criteria for ordinarity and supersingularity in every prime
  characteristic.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, IV.7, V.3.1, and V.4.
-/

public section

namespace WeierstrassCurve

section Field

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **An elliptic curve in characteristic `p` is ordinary if and only if its formal group has height
one** (Silverman V.3.1), for every prime `p` including `2` and `3`. -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have : ExpChar K p := .prime hp.out
  have hpz : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hpz
  have hφ (h : (p : ℤ) ≠ 0) : TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine h = φ := rfl
  have hdeg : φ.separableDegree * φ.inseparableDegree = p * p := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast, sq]
  rw [W.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p hp.out, ← Nat.cast_one,
    FormalGroup.height_eq_natCast_iff, pow_one, W.order_nsmulSeries_formalGroup hp.out.ne_zero,
    Nat.cast_inj (R := ℕ∞)]
  simp only [hφ]
  exact ⟨fun hs ↦ Nat.mul_left_cancel hp.out.pos (hs ▸ hdeg),
    fun hi ↦ Nat.mul_right_cancel hp.out.pos (hi ▸ hdeg)⟩

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height two** (Silverman V.3.1), for every prime `p` including `2` and `3`. -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have : ExpChar K p := .prime hp.out
  have hpz : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hpz
  have hφ (h : (p : ℤ) ≠ 0) : TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine h = φ := rfl
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  rw [W.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p,
    ← Nat.cast_ofNat (R := ℕ∞), FormalGroup.height_eq_natCast_iff,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  simp only [hφ]
  exact ⟨fun hs ↦ by rwa [hs, one_mul] at hdeg,
    fun hi ↦ Nat.mul_right_cancel (pow_pos hp.out.pos 2) (by rw [hi] at hdeg; linarith)⟩

/-- **The formal group of an elliptic curve in characteristic `p` has height `1` or `2`**
(Silverman IV.7.5 and V.3.1). -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsOrdinary p
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp h)
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp (not_isOrdinary.mp h))

/-- **The formal group of an elliptic curve in characteristic `p` has height at most two.** -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two with h | h <;> rw [h]
  exact one_le_two

/-- The formal group of an elliptic curve in characteristic `p` has finite height. -/
theorem height_formalGroup_ne_top : (formalGroup W).height p ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) W.height_formalGroup_le_two

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height strictly greater than one.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, W.isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **Formal-differential Hasse-invariant criterion for ordinarity**: an elliptic curve in
characteristic `p` is ordinary if and only if the coefficient of `Tᵖ⁻¹` in the invariant
differential of its formal group is nonzero (Silverman IV.4, IV.7, V.3.1, and V.4). -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero :
    W.IsOrdinary p ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rw [W.isOrdinary_iff_height_formalGroup_eq_one, W.height_formalGroup_eq_one_iff]

/-- **Formal-differential Hasse-invariant criterion for supersingularity**: an elliptic curve in
characteristic `p` is supersingular if and only if the coefficient of `Tᵖ⁻¹` in the invariant
differential of its formal group vanishes (Silverman IV.4, IV.7, V.3.1, and V.4). -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero :
    W.IsSupersingular p ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, W.isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_not]

/-- Over a field of characteristic `p`, the formal group of an elliptic curve has height two if and
only if the coefficient of `Tᵖ⁻¹` in its invariant differential vanishes. -/
theorem height_formalGroup_eq_two_iff :
    (formalGroup W).height p = 2 ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← W.isSupersingular_iff_height_formalGroup_eq_two,
    W.isSupersingular_iff_coeff_invariantDifferential_eq_zero]

end Field

end WeierstrassCurve

end
