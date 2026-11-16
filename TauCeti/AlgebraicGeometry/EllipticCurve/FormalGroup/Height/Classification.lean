/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
-- Proof-only: height of an elliptic curve via the inseparable degree of `[p]`.
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.MulByInt
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Order
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Classification of Weierstrass formal group heights at every prime

Let `W` be a Weierstrass curve over a field `K` of prime characteristic `p`, and let `Ê` be its
formal group law. This file classifies the height of `Ê` for every Weierstrass curve, smooth or
singular, in every prime characteristic including `2` and `3`:

* If `W` is elliptic (`Δ ≠ 0`), then `Ê` has height `1` or `2`: height `1` exactly when `W` is
  ordinary (equivalently, the Hasse invariant `coeff (p - 1) ω` is nonzero), and height `2`
  exactly when `W` is supersingular (equivalently, the Hasse invariant vanishes).
* If `W` is nodal (`Δ = 0` and `c₄ ≠ 0`), then `Ê` has height `1`, and its Hasse invariant is
  nonzero.
* If `W` is cuspidal (`Δ = 0` and `c₄ = 0`), then `Ê` has height `⊤`.

In particular, `Ê` has height `1`, `2`, or `⊤`; it has height at most `2` exactly when `W` is
smooth or nodal (`c₄ ≠ 0 ∨ Δ ≠ 0`), and infinite height exactly at a cusp (`Δ = 0 ∧ c₄ = 0`).

## Strategy

For an elliptic curve `W`, the multiplication-by-`p` series `[p]_Ê` is the formal power series of
the isogeny `[p]` (`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`), whose order equals the
inseparable degree `deg_i [p]` (`TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree`). Since
`deg_s [p] * deg_i [p] = deg [p] = p²`, the characterizations of ordinarity (`deg_s [p] = p`) and
supersingularity (`deg_s [p] = 1`) from `Isogeny.RelativeFrobenius.Supersingular` immediately give
`deg_i [p] = p` (height `1`) and `deg_i [p] = p²` (height `2`).

For a singular curve (`Δ = 0`), passing to `AlgebraicClosure K` preserves the formal-group height
and supplies a singular point `(x, y)` together with a root `α` of the tangent quadratic. The
change of variables `⟨1, x, α, y⟩` brings the curve to `y² + (a₁ + 2 α) x y = x³`
(`WeierstrassCurve.Affine.variableChange_eq_of_isSingular`), where `(a₁ + 2 α) ^ 4 = c₄`, leaving
the height unchanged (`WeierstrassCurve.VariableChange.height_formalGroup_variableChange`). By
`FormalGroup.Multiplicative`, this cubic has height `1` when `c₄ ≠ 0` and `⊤` when `c₄ = 0`.

## Main results

* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one` and
  `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: an elliptic curve in prime
  characteristic `p` is ordinary iff its formal group has height `1`, and supersingular iff its
  formal group has height `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the formal group of an elliptic curve has height
  `1` or `2`.
* `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero` and
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`: ordinarity and
  supersingularity characterized by the Hasse invariant in every prime characteristic.
* `WeierstrassCurve.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero` and
  `WeierstrassCurve.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero`: nodal cubics have
  height `1` and cuspidal cubics have height `⊤`.
* `WeierstrassCurve.height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero` and
  `WeierstrassCurve.coeff_invariantDifferential_formalGroup_ne_zero_iff_c₄_ne_zero_of_Δ_eq_zero`:
  for a singular Weierstrass curve, height `1`, nonzero Hasse invariant, and `c₄ ≠ 0` coincide.
* `WeierstrassCurve.height_formalGroup_eq_top_iff`,
  `WeierstrassCurve.height_formalGroup_le_two_iff`, and
  `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two_or_eq_top`: complete trichotomy for
  arbitrary Weierstrass curves over fields of prime characteristic.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.7 and V.3.1.
-/

public section

namespace WeierstrassCurve

section Elliptic

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- Over a field of prime characteristic `p`, the formal group of an elliptic curve has finite
height `h` exactly when the isogeny `[p]` has inseparable degree `p ^ h`. -/
private theorem height_formalGroup_eq_natCast_iff_inseparableDegree {h : ℕ} :
    (formalGroup W).height p = h ↔
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine
        (mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)).inseparableDegree = p ^ h := by
  rw [(formalGroup W).height_eq_natCast_iff, ← FormalGroup.zsmulSeries_natCast,
    ← TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero W,
    TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree, Nat.cast_inj]

/-- **In prime characteristic `p`, an elliptic curve is ordinary exactly when its formal group has
height `1`** (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have : ExpChar K p := .prime hp.out
  have hpZ : (p : ℤ) ≠ 0 := mod_cast hp.out.ne_zero
  set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hpZ
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  rw [isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p W hp.out, ← Nat.cast_one,
    W.height_formalGroup_eq_natCast_iff_inseparableDegree, pow_one]
  constructor
  · intro hs
    rw [hs, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hdeg
  · intro hi
    rw [hi, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos hdeg

/-- **In prime characteristic `p`, an elliptic curve is supersingular exactly when its formal group
has height `2`** (Silverman V.3.1). -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have : ExpChar K p := .prime hp.out
  have hpZ : (p : ℤ) ≠ 0 := mod_cast hp.out.ne_zero
  set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hpZ
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  rw [isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p W,
    ← Nat.cast_ofNat (n := 2), W.height_formalGroup_eq_natCast_iff_inseparableDegree]
  constructor
  · intro hs
    rw [hs, one_mul] at hdeg
    exact hdeg
  · intro hi
    rw [hi] at hdeg
    exact (Nat.mul_eq_right (pow_ne_zero 2 hp.out.ne_zero)).mp hdeg

/-- **The formal group of an elliptic curve over a field of prime characteristic has height `1` or
`2`.** -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsOrdinary p
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp h)
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp (not_isOrdinary.mp h))

/-- **The formal group of an elliptic curve over a field of prime characteristic has height at most
`2`.** -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two with h | h
  · rw [h]; decide
  · exact h.le

/-- **Ordinarity from the Hasse invariant**: in prime characteristic `p`, an elliptic curve is
ordinary exactly when the coefficient of `Tᵖ⁻¹` in the invariant differential of its formal group
is nonzero. -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rw [W.isOrdinary_iff_height_formalGroup_eq_one, W.height_formalGroup_eq_one_iff]

/-- **Supersingularity from the Hasse invariant**: in prime characteristic `p`, an elliptic curve is
supersingular exactly when the coefficient of `Tᵖ⁻¹` in the invariant differential of its formal
group vanishes. -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, W.isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_not]

end Elliptic

section Singular

variable {K : Type*} [Field K] {p : ℕ} [CharP K p] (W : WeierstrassCurve K)

omit [CharP K p] in
/-- Over the algebraic closure, a singular Weierstrass curve (`Δ = 0`) can be transformed by a
change of variables into `y² + a x y = x³` with `a⁴ = c₄`, preserving the height of its formal
group. -/
private theorem exists_height_formalGroup_eq_of_Δ_eq_zero (hΔ : W.Δ = 0) :
    ∃ a : AlgebraicClosure K, a ^ 4 = algebraMap K (AlgebraicClosure K) W.c₄ ∧
      (formalGroup W).height p =
        (formalGroup (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K))).height p := by
  let Ω := AlgebraicClosure K
  let ι : K →+* Ω := algebraMap K Ω
  let W₁ : WeierstrassCurve Ω := W.map ι
  have hΔ₁ : W₁.toAffine.Δ = 0 := by rw [map_Δ, hΔ, map_zero]
  obtain ⟨x, y, hxy⟩ := W₁.toAffine.exists_isSingular_of_Δ_eq_zero hΔ₁
  let f : Polynomial Ω :=
    Polynomial.X ^ 2 + Polynomial.C W₁.a₁ * Polynomial.X - Polynomial.C (3 * x + W₁.a₂)
  have hf2 : f.coeff 2 ≠ 0 := by
    simp [f, Polynomial.coeff_X_pow]
  have hdeg : f.degree ≠ 0 := by
    intro h0
    have hle : (2 : WithBot ℕ) ≤ f.degree := Polynomial.le_degree_of_ne_zero hf2
    rw [h0] at hle
    exact absurd hle (by decide)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root f hdeg
  have hα' : α ^ 2 + W₁.a₁ * α - (3 * x + W₁.a₂) = 0 := by
    simpa [f, Polynomial.IsRoot] using hα
  refine ⟨W₁.a₁ + 2 * α, ?_, ?_⟩
  · have hc₄ := Affine.c₄_eq_of_isSingular hxy hα'
    rw [map_c₄] at hc₄
    rw [add_comm, ← hc₄]
  · have hV := Affine.variableChange_eq_of_isSingular hxy hα'
    calc
      (formalGroup W).height p = ((formalGroup W).map ι).height p :=
        ((formalGroup W).height_map ι p).symm
      _ = (formalGroup W₁).height p := by rw [map_formalGroup]
      _ = (formalGroup (VariableChange.mk 1 x α y • W₁)).height p :=
        (VariableChange.height_formalGroup_variableChange _ W₁ p).symm
      _ = (formalGroup (⟨W₁.a₁ + 2 * α, 0, 0, 0, 0⟩ : WeierstrassCurve Ω)).height p := by
        rw [hV]

/-- **A nodal Weierstrass curve has formal-group height `1`.** Over a field of prime characteristic
`p`, if `Δ = 0` and `c₄ ≠ 0`, then the formal group of `W` has height `1`. -/
theorem height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero [Fact p.Prime] (hΔ : W.Δ = 0)
    (hc₄ : W.c₄ ≠ 0) : (formalGroup W).height p = 1 := by
  obtain ⟨a, ha, hht⟩ := W.exists_height_formalGroup_eq_of_Δ_eq_zero hΔ
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at ha
    exact hc₄ ((map_eq_zero_iff (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).mp ha.symm)
  rw [hht]
  exact height_formalGroup_eq_one (W := (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K)))
    ha0 rfl rfl rfl rfl

/-- **A cuspidal Weierstrass curve has infinite formal-group height.** Over a field of
characteristic `p`, if `Δ = 0` and `c₄ = 0`, then the formal group of `W` has height `⊤`. -/
theorem height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    (formalGroup W).height p = ⊤ := by
  obtain ⟨a, ha, hht⟩ := W.exists_height_formalGroup_eq_of_Δ_eq_zero hΔ
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have ha0 : a = 0 := by
    rw [hc₄, map_zero] at ha
    exact (pow_eq_zero_iff (by decide)).mp ha
  rw [hht]
  exact height_formalGroup_eq_top (W := (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K)))
    ha0 rfl rfl rfl rfl

/-- Over a field of prime characteristic `p`, a singular Weierstrass curve (`Δ = 0`) has
formal-group height `1` exactly when `c₄ ≠ 0` (i.e., when the singularity is a node rather than a
cusp). -/
theorem height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero [Fact p.Prime] (hΔ : W.Δ = 0) :
    (formalGroup W).height p = 1 ↔ W.c₄ ≠ 0 := by
  refine ⟨fun h hc₄ ↦ ?_, W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ⟩
  rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄] at h
  exact ENat.top_ne_one h

/-- Over a field of prime characteristic `p`, the Hasse invariant of a singular Weierstrass curve
(`Δ = 0`) is nonzero exactly when `c₄ ≠ 0`. -/
theorem coeff_invariantDifferential_formalGroup_ne_zero_iff_c₄_ne_zero_of_Δ_eq_zero [Fact p.Prime]
    (hΔ : W.Δ = 0) :
    PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 ↔ W.c₄ ≠ 0 := by
  rw [← W.height_formalGroup_eq_one_iff, W.height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero hΔ]

/-- **Smooth or nodal Weierstrass curves have formal-group height `1` or `2`.** Over a field of
prime characteristic `p`, whenever `c₄ ≠ 0 ∨ Δ ≠ 0`, the formal group of `W` has height `1` or `2`.
-/
theorem height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero [Fact p.Prime]
    (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases hΔ : W.Δ = 0
  · exact Or.inl (W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ
      (h.resolve_right (not_not.mpr hΔ)))
  · have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
    exact W.height_formalGroup_eq_one_or_eq_two

/-- **Trichotomy of formal-group heights for Weierstrass curves.** Over a field of prime
characteristic `p`, the formal group of any Weierstrass curve has height `1`, `2`, or `⊤`. -/
theorem height_formalGroup_eq_one_or_eq_two_or_eq_top [Fact p.Prime] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 ∨ (formalGroup W).height p = ⊤ := by
  by_cases h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0
  · rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero h with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · push Not at h
    exact Or.inr (Or.inr (W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero h.2 h.1))

/-- **Characterization of infinite formal-group height.** Over a field of prime characteristic `p`,
a Weierstrass curve has formal group of height `⊤` exactly when it is cuspidal (`Δ = 0 ∧ c₄ = 0`).
-/
theorem height_formalGroup_eq_top_iff [Fact p.Prime] :
    (formalGroup W).height p = ⊤ ↔ W.Δ = 0 ∧ W.c₄ = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hΔ, hc₄⟩ ↦ W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄⟩
  by_contra hne
  have hor : W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
    rw [not_and_or] at hne
    exact hne.symm
  rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero hor with h1 | h2
  · rw [h1] at h; exact ENat.one_ne_top h
  · rw [h2] at h; exact ENat.natCast_ne_top 2 h

/-- **Characterization of formal-group height at most `2`.** Over a field of prime characteristic
`p`, a Weierstrass curve has formal group of height at most `2` exactly when it is smooth or nodal
(`c₄ ≠ 0 ∨ Δ ≠ 0`). -/
theorem height_formalGroup_le_two_iff [Fact p.Prime] :
    (formalGroup W).height p ≤ 2 ↔ W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hne.2 hne.1] at h
    exact absurd h (by decide)
  · intro h
    rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero h with h | h
    · rw [h]; decide
    · exact h.le

end Singular

end WeierstrassCurve
