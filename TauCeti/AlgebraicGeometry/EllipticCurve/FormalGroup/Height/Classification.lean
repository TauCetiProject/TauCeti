/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange

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
smooth or nodal (`c₄ ≠ 0 ∨ Δ ≠ 0`), height `2` exactly when `W` is smooth with vanishing Hasse
invariant (`Δ ≠ 0 ∧ coeff (p - 1) ω = 0`), and infinite height exactly at a cusp
(`Δ = 0 ∧ c₄ = 0`).

This field-level classification characterizes the ordinary and supersingular strata at every prime
`p` and supplies the residue-field input for ring-level height-ideal bounds, Landweber's `v₂`-unit
condition, and the nodal Hasse-invariant unit condition in
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Bound`.

## Strategy

For an elliptic curve `W`, the ordinary and supersingular strata are characterized by height `1`
and `2` in `TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular`, via the
inseparable degree of `[p]`; this file adds the Hasse-invariant description of height `2`.

For a singular curve (`Δ = 0`), passing to `AlgebraicClosure K` preserves the formal-group height
and supplies a singular point `(x, y)` together with a root `α` of the tangent quadratic
(`WeierstrassCurve.Affine.exists_isSingular_and_tangent_root_of_Δ_eq_zero`). The change of
variables `⟨1, x, α, y⟩` brings the curve to `y² + (a₁ + 2 α) x y = x³`
(`WeierstrassCurve.Affine.variableChange_eq_of_isSingular`), where `(a₁ + 2 α) ^ 4 = c₄`, leaving
the height unchanged (`WeierstrassCurve.VariableChange.height_formalGroup_variableChange`). By
`WeierstrassCurve.height_formalGroup_eq_one` and `WeierstrassCurve.height_formalGroup_eq_top`, this
cubic has height `1` when `c₄ ≠ 0` and `⊤` when `c₄ = 0`.

## Main results

* `WeierstrassCurve.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero`:
  an elliptic curve in characteristic `p` has formal group of height `2` exactly when the
  coefficient of `T ^ (p - 1)` in its invariant differential vanishes.
* `WeierstrassCurve.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero` and
  `WeierstrassCurve.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero`: nodal cubics have
  height `1` and cuspidal cubics have height `⊤`.
* `WeierstrassCurve.height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero` and
  `WeierstrassCurve.coeff_invariantDifferential_formalGroup_ne_zero_iff_c₄_ne_zero_of_Δ_eq_zero`:
  for a singular Weierstrass curve, height `1`, nonzero Hasse invariant, and `c₄ ≠ 0` coincide.
* `WeierstrassCurve.height_formalGroup_eq_two_iff`,
  `WeierstrassCurve.height_formalGroup_eq_top_iff`,
  `WeierstrassCurve.height_formalGroup_le_two_iff`,
  `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two_iff`, and
  `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two_or_eq_top`: complete `{1, 2, ⊤}` trichotomy
  and exact characterizations of each height stratum for arbitrary Weierstrass curves (with the
  `{1, 2, ⊤}` trichotomy, cuspidal `⊤`, and height-`2` characterizations holding in characteristic
  `p = 0` as well).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.7 and V.3.1.
-/

public section

namespace WeierstrassCurve

section Elliptic

variable {K : Type*} [Field K] {p : ℕ} [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **Height two from the Hasse invariant**: in characteristic `p`, an elliptic curve has formal
group of height `2` at `p` exactly when the coefficient of `T ^ (p - 1)` in the invariant
differential of its formal group vanishes. -/
theorem height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero :
    (formalGroup W).height p = 2 ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← W.isSupersingular_iff_height_formalGroup_eq_two,
    W.isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero]

end Elliptic

section Singular

variable {K : Type*} [Field K] {p : ℕ} (W : WeierstrassCurve K)

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
  obtain ⟨x, y, α, hxy, hα'⟩ :=
    W₁.toAffine.exists_isSingular_and_tangent_root_of_Δ_eq_zero (by rw [map_Δ, hΔ, map_zero])
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

variable [CharP K p]

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

/-- **Trichotomy of formal-group heights for Weierstrass curves.** Over a field of characteristic
`p`, the formal group of any Weierstrass curve has `p`-height `1`, `2`, or `⊤`. -/
theorem height_formalGroup_eq_one_or_eq_two_or_eq_top :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 ∨ (formalGroup W).height p = ⊤ := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    by_cases h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0
    · rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · push Not at h
      exact Or.inr (Or.inr (W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero h.2 h.1))
  · exact Or.inr (Or.inr ((formalGroup W).height_eq_top_iff.mpr (by simp)))

/-- **Characterization of formal-group height `2`.** Over a field of characteristic `p`, a
Weierstrass curve has formal group of height `2` at `p` exactly when it is elliptic (`Δ ≠ 0`) and
the coefficient of `T ^ (p - 1)` in its invariant differential vanishes. -/
theorem height_formalGroup_eq_two_iff :
    (formalGroup W).height p = 2 ↔
      W.Δ ≠ 0 ∧ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    constructor
    · intro h
      have hΔ : W.Δ ≠ 0 := by
        intro hΔ0
        by_cases hc₄ : W.c₄ = 0
        · rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ0 hc₄] at h
          exact ENat.natCast_ne_top 2 h.symm
        · rw [W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ0 hc₄] at h
          exact absurd h (by decide)
      have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
      exact ⟨hΔ,
        W.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero.mp h⟩
    · rintro ⟨hΔ, hH⟩
      have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
      exact W.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero.mpr hH
  · rw [(formalGroup W).height_eq_top_iff.mpr (by simp)]
    exact iff_of_false (ENat.top_ne_natCast 2) (by simp)

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

/-- **Characterization of formal-group height `1` or `2`.** Over a field of prime characteristic
`p`, `(formalGroup W).height p` is `1` or `2` if and only if `W.c₄ ≠ 0` or `W.Δ ≠ 0`. -/
theorem height_formalGroup_eq_one_or_eq_two_iff [Fact p.Prime] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 ↔ W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
  refine ⟨fun h ↦ W.height_formalGroup_le_two_iff.mp ?_,
    W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero⟩
  rcases h with h | h
  · rw [h]; decide
  · exact h.le

end Singular

end WeierstrassCurve
