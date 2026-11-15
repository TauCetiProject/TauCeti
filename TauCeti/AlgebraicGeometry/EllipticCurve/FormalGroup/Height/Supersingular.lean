/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange

/-!
# The height-one and height-two strata of the formal group of an elliptic curve

Let `W` be an elliptic curve over a field `K`. Multiplication by any nonzero `n : ℕ` on `W` induces
the formal power series `(formalGroup W).nsmulSeries n` on the formal group `Ê = formalGroup W`
(`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero_natCast`), which is therefore nonzero (more
generally over every nontrivial commutative ring) and has order equal to the inseparable degree of
`[n]` (`WeierstrassCurve.order_nsmulSeries_formalGroup_eq_inseparableDegree`). Consequently `Ê` has
finite height at every nonzero `p`, and isogenous elliptic curves have formal groups of equal
height.

When `K` has prime characteristic `p`, `[p]` has degree `p² = deg_s [p] · deg_i [p]`:
* `W` is **supersingular** if and only if `(formalGroup W).height p = 2`;
* `W` is **ordinary** if and only if `(formalGroup W).height p = 1`, equivalently the `(p - 1)`-st
  coefficient of `(formalGroup W).invariantDifferential` is nonzero.

Consequently the formal group of every elliptic curve over a field of prime characteristic `p` has
height `1` or `2` (in particular at most `2`), complementing the explicit characteristic `2` and `3`
height-two criteria of `TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Char.Two` and
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Char.Three`.

## Main results

* `TauCeti.Isogeny.height_formalGroup_eq`: isogenous elliptic curves have formal groups of equal
  height.
* `WeierstrassCurve.nsmulSeries_formalGroup_ne_zero` and
  `WeierstrassCurve.zsmulSeries_formalGroup_ne_zero`: `[n]_Ê ≠ 0` for `n ≠ 0` over any nontrivial
  commutative ring.
* `WeierstrassCurve.height_formalGroup_ne_top`: over any field, `Ê` has finite height at every
  nonzero `p`.
* `WeierstrassCurve.order_nsmulSeries_formalGroup_eq_inseparableDegree`: the order of `[n]_Ê` is
  the inseparable degree of `[n]`.
* `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: an elliptic curve in
  characteristic `p` is supersingular if and only if its formal group has height `2`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`: an elliptic curve in prime
  characteristic `p` is ordinary if and only if its formal group has height `1`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the formal group of an elliptic curve in prime
  characteristic `p` has height `1` or `2`, hence at most `2`.
* `WeierstrassCurve.isSupersingular_iff_one_lt_height_formalGroup`,
  `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero` and
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero`:
  characterisations of ordinarity and supersingularity via `1 < height` and the `(p - 1)`-st
  coefficient of the formal-group invariant differential.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7.4, IV.7.5, V.3.1 and
  V.4.1.
-/

public section

open TauCeti.Isogeny

/-! ### Invariance of height under isogenies -/

namespace TauCeti.Isogeny

/-- **Isogenous elliptic curves have formal groups of the same height.** -/
theorem height_formalGroup_eq {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) :
    (WeierstrassCurve.formalGroup W₁).height p = (WeierstrassCurve.formalGroup W₂).height p :=
  φ.formalGroupHom.height_eq (by simpa using φ.formalSeries_ne_zero) p

end TauCeti.Isogeny

/-! ### Nonvanishing of `[n]_Ê`, order of `[n]_Ê`, and the height strata -/

namespace WeierstrassCurve

section Ring

variable {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- For every nonzero natural number `n`, the `[n]`-series of the formal group of an elliptic curve
over a nontrivial commutative ring is nonzero. -/
theorem nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  -- Reduce modulo a maximal ideal of `R` to a field, where `[n]_Ê` is the formal series of `[n]`.
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let _ : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let π : R →+* R ⧸ 𝔪 := Ideal.Quotient.mk 𝔪
  have : (W.map π).IsElliptic := ⟨by simpa using W.isUnit_Δ.map π⟩
  have hnz : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  intro h0
  have hmap := congrArg (PowerSeries.map π) h0
  rw [map_zero, FormalGroup.map_nsmulSeries, ← map_formalGroup,
    ← formalSeries_mulByIntIsogenyOfNeZero_natCast (W.map π) hnz] at hmap
  exact (mulByIntIsogenyOfNeZero (W.map π).toAffine hnz).formalSeries_ne_zero hmap

/-- For every nonzero integer `n`, the `[n]`-series of the formal group of an elliptic curve over a
nontrivial commutative ring is nonzero. -/
theorem zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa [FormalGroup.zsmulSeries_natCast] using
      W.nsmulSeries_formalGroup_ne_zero (Int.natCast_ne_zero.mp hn)
  · intro h0
    have hneg : (k : ℤ) = -1 * -(k : ℤ) := by ring
    have hk : (formalGroup W).nsmulSeries k = 0 := by
      rw [← FormalGroup.zsmulSeries_natCast, hneg, FormalGroup.zsmulSeries_mul, h0,
        PowerSeries.subst_zero_of_constantCoeff_zero
          ((formalGroup W).constantCoeff_zsmulSeries _)]
    exact W.nsmulSeries_formalGroup_ne_zero (by omega) hk

end Ring

section Field

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- The formal group of an elliptic curve over a field has finite height at every nonzero `p`. -/
theorem height_formalGroup_ne_top {p : ℕ} (hp : p ≠ 0) :
    (formalGroup W).height p ≠ ⊤ :=
  (formalGroup W).height_eq_top_iff.not.mpr (W.nsmulSeries_formalGroup_ne_zero hp)

/-- **The order of `[n]_Ê` is the inseparable degree of `[n]`** (Silverman IV.7.4). -/
theorem order_nsmulSeries_formalGroup_eq_inseparableDegree {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      ((mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree : ℕ∞) := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero_natCast W hn, order_formalSeries_eq_inseparableDegree]

private theorem separableDegree_mul_inseparableDegree_mulByIntIsogenyOfNeZero_natCast
    {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).separableDegree *
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree = n ^ 2 := by
  rw [(mulByIntIsogenyOfNeZero W.toAffine hn).separableDegree_mul_inseparableDegree,
    degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast]

private theorem not_isSupersingular_zero : ¬W.IsSupersingular 0 := by
  classical
  obtain ⟨P, hP⟩ := exists_ne (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
  rw [W.isSupersingular_iff_forall, not_forall]
  exact ⟨P, fun h ↦ hP (h (zero_nsmul P))⟩

/-- **An elliptic curve over a field of characteristic `p` is supersingular if and only if its
formal group has height `2`** (Silverman V.3.1). -/
theorem isSupersingular_iff_height_formalGroup_eq_two {p : ℕ} [CharP K p] :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · -- In prime characteristic `p`, `deg_s [p] · deg_i [p] = p²`, so `deg_s [p] = 1` iff
    -- `deg_i [p] = p²`, i.e. `[p]_Ê` has order `p²`.
    have : ExpChar K p := .prime hp
    have hpz : (p : ℤ) ≠ 0 := mod_cast expChar_ne_zero K p
    have hdeg := W.separableDegree_mul_inseparableDegree_mulByIntIsogenyOfNeZero_natCast hpz
    rw [isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p W,
      ← Nat.cast_ofNat (R := ℕ∞) (n := 2), (formalGroup W).height_eq_natCast_iff,
      W.order_nsmulSeries_formalGroup_eq_inseparableDegree hpz, Nat.cast_inj (R := ℕ∞)]
    refine ⟨fun hs ↦ ?_, fun hi ↦ ?_⟩
    · rwa [hs, one_mul] at hdeg
    · rw [hi] at hdeg
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) (hdeg.trans (one_mul _).symm)
  · have hz : (formalGroup W).height 0 = ⊤ := (formalGroup W).height_eq_top_iff.mpr (by simp)
    exact iff_of_false W.not_isSupersingular_zero (by simp [hz])

/-- **An elliptic curve over a field of prime characteristic `p` is ordinary if and only if its
formal group has height `1`** (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one {p : ℕ} [hp : Fact p.Prime] [CharP K p] :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  -- `deg_s [p] · deg_i [p] = p²`, so `deg_s [p] = p` iff `deg_i [p] = p`.
  have : ExpChar K p := .prime hp.out
  have hpz : (p : ℤ) ≠ 0 := mod_cast expChar_ne_zero K p
  have hdeg := W.separableDegree_mul_inseparableDegree_mulByIntIsogenyOfNeZero_natCast hpz
  rw [isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p W hp.out,
    ← Nat.cast_one (R := ℕ∞), (formalGroup W).height_eq_natCast_iff, pow_one,
    W.order_nsmulSeries_formalGroup_eq_inseparableDegree hpz, Nat.cast_inj (R := ℕ∞)]
  refine ⟨fun hs ↦ ?_, fun hi ↦ ?_⟩
  · rw [hs, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hdeg
  · rw [hi, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos hdeg

/-- **The formal group of an elliptic curve over a field of prime characteristic `p` has height
`1` or `2`** (Silverman IV.7.5). -/
theorem height_formalGroup_eq_one_or_two {p : ℕ} [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsSupersingular p
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp h)
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp (not_isSupersingular.mp h))

/-- **The formal group of an elliptic curve over a field of prime characteristic `p` has height at
most `2`** (Silverman IV.7.5). -/
theorem height_formalGroup_le_two {p : ℕ} [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_two (p := p) with h | h <;> simp [h]

/-- **An elliptic curve over a field of prime characteristic `p` is supersingular if and only if
its formal group has height strictly greater than `1`.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup {p : ℕ} [Fact p.Prime] [CharP K p] :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, W.isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **An elliptic curve over a field of characteristic `p` is ordinary if and only if the
`(p - 1)`-st coefficient of its formal-group invariant differential is nonzero**
(Silverman V.4.1(a)). -/
theorem isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero {p : ℕ} [CharP K p] :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    exact W.isOrdinary_iff_height_formalGroup_eq_one.trans W.height_formalGroup_eq_one_iff
  · have hc0 : PowerSeries.coeff (0 - 1) (formalGroup W).invariantDifferential ≠ 0 := by
      simp [PowerSeries.coeff_zero_eq_constantCoeff,
        (formalGroup W).constantCoeff_invariantDifferential]
    exact iff_of_true (not_isSupersingular.mp W.not_isSupersingular_zero) hc0

/-- **An elliptic curve over a field of characteristic `p` is supersingular if and only if the
`(p - 1)`-st coefficient of its formal-group invariant differential vanishes**
(Silverman V.4.1(a)). -/
theorem isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero {p : ℕ} [CharP K p] :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, W.isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero, not_not]

end Field

end WeierstrassCurve
