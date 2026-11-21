/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular
import Mathlib.Algebra.CharP.Algebra

/-!
# Classification of Weierstrass formal group heights at every prime

Let `W` be a Weierstrass curve over a field `K` of characteristic `p`, and let `Ê = formalGroup W`
be its formal group law. Building on the elliptic height stratification in
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular` and the
multiplication-series order bounds in `TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Order`,
this file classifies the height of `Ê` for every Weierstrass curve, smooth or singular:

* In prime characteristic `p`, if `W` is elliptic (`Δ ≠ 0`), then `Ê` has height `1` or `2`: height
  `1` exactly when `W` is ordinary (equivalently, the Hasse invariant `coeff (p - 1) ω` is
  nonzero), and height `2` exactly when `W` is supersingular (equivalently, the Hasse invariant
  vanishes).
* If `W` is nodal (`Δ = 0` and `c₄ ≠ 0`), then in prime characteristic `p`, `Ê` has height `1` and
  nonzero Hasse invariant.
* If `W` is cuspidal (`Δ = 0` and `c₄ = 0`), then `Ê` has height `⊤` whenever `(p : K) = 0`.
* At `p = 0` (in characteristic zero), `[0]_Ê = 0`, so every Weierstrass curve has height `⊤`.

In any characteristic `p` (prime or zero), `Ê` has height `1`, `2`, or `⊤`. In prime characteristic
`p`, `Ê` has height at most `2` iff `c₄ ≠ 0 ∨ Δ ≠ 0` (smooth or nodal), height `2` iff
`Δ ≠ 0 ∧ coeff (p - 1) ω = 0`, and infinite height iff `Δ = 0 ∧ c₄ = 0` (more generally,
`height p Ê = ⊤ ↔ Δ = 0 ∧ c₄ = 0` whenever `p ≠ 0` and `(p : K) = 0`). For any `p ≠ 0` over any
field, a smooth or nodal curve has finite `p`-height.

## Strategy

For an elliptic curve `W`, the ordinary and supersingular strata are characterized by height `1`
and `2` in `TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular`, via the
inseparable degree of `[p]`; this file adds the Hasse-invariant description of height `2`.

For a nodal curve (`Δ = 0` and `c₄ ≠ 0`) in prime characteristic `p`, the order bound
`WeierstrassCurve.order_nsmulSeries_formalGroup_le_of_Δ_eq_zero_of_c₄_ne_zero` forces
`ord [p]_Ê ≤ p`, which together with `FormalGroup.exists_order_nsmulSeries_eq_pow` gives height
`1`. For a cuspidal curve (`Δ = 0` and `c₄ = 0`) with `(p : K) = 0`,
`WeierstrassCurve.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero` gives `[p]_Ê = 0` and
hence height `⊤`.

## Main results

* `WeierstrassCurve.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero`:
  an elliptic curve in prime characteristic `p` has formal group of height `2` exactly when its
  Hasse invariant vanishes.
* `WeierstrassCurve.height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero`: for any `p ≠ 0` over
  any field, a smooth or nodal Weierstrass curve has finite formal-group height.
* `WeierstrassCurve.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero`: nodal cubics in prime
  characteristic `p` have height `1`.
* `WeierstrassCurve.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero` and
  `WeierstrassCurve.height_formalGroup_eq_top_iff`: whenever `(p : K) = 0`, cuspidal cubics have
  height `⊤`, and for `p ≠ 0` with `(p : K) = 0` (in particular, in prime characteristic `p`),
  infinite height characterizes the cuspidal locus `Δ = 0 ∧ c₄ = 0`.
* `WeierstrassCurve.height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero` and
  `WeierstrassCurve.coeff_invariantDifferential_formalGroup_ne_zero_iff_c₄_ne_zero_of_Δ_eq_zero`:
  for a singular Weierstrass curve in prime characteristic `p`, height `1`, nonzero Hasse invariant,
  and `c₄ ≠ 0` coincide.
* `WeierstrassCurve.height_formalGroup_eq_two_iff` and
  `WeierstrassCurve.height_formalGroup_le_two_iff`: exact characterizations of height `2` and
  height at most `2` for arbitrary Weierstrass curves over a field of prime characteristic `p`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two_or_eq_top`: trichotomy `(1, 2, ⊤)` in any
  characteristic `p` (where at `p = 0` every curve has height `⊤`).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.7 and V.3.1.
-/

public section

namespace WeierstrassCurve

section Elliptic

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **Height two from the Hasse invariant**: in prime characteristic `p`, an elliptic curve has
formal group of height `2` exactly when the coefficient of `Tᵖ⁻¹` in the invariant differential of
its formal group vanishes. -/
theorem height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero :
    (formalGroup W).height p = 2 ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← W.isSupersingular_iff_height_formalGroup_eq_two,
    W.isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero]

end Elliptic

section Singular

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- Over any field and for any `p ≠ 0`, a smooth or nodal Weierstrass curve (`c₄ ≠ 0 ∨ Δ ≠ 0`) has
finite formal-group height. -/
theorem height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero {p : ℕ} (hp : p ≠ 0)
    (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) : (formalGroup W).height p ≠ ⊤ := by
  rw [ne_eq, FormalGroup.height_eq_top_iff]
  intro h0
  have hord := W.order_nsmulSeries_formalGroup_le_sq hp h
  simp [h0] at hord

/-- **A cuspidal Weierstrass curve has infinite formal-group height** whenever `(p : K) = 0`:
if `Δ = 0`, `c₄ = 0`, and `(p : K) = 0`, then the formal group of `W` has height `⊤`. -/
theorem height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero {p : ℕ}
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) (hp : (p : K) = 0) : (formalGroup W).height p = ⊤ :=
  ((formalGroup W).height_eq_top_iff).mpr
    (W.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ hp)

/-- **Characterization of infinite formal-group height.** Over a field with `p ≠ 0` and
`(p : K) = 0` (in particular, in prime characteristic `p`), the formal group of a Weierstrass curve
has height `⊤` exactly when the curve is cuspidal (`Δ = 0 ∧ c₄ = 0`). -/
theorem height_formalGroup_eq_top_iff {p : ℕ} (hp : p ≠ 0) (hpK : (p : K) = 0) :
    (formalGroup W).height p = ⊤ ↔ W.Δ = 0 ∧ W.c₄ = 0 := by
  refine ⟨fun htop ↦ ?_, fun ⟨hΔ, hc₄⟩ ↦
    W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ hpK⟩
  by_contra h
  rw [not_and_or, or_comm] at h
  exact W.height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero hp h htop

variable {p : ℕ} [CharP K p]

/-- **A nodal Weierstrass curve has formal-group height `1`.** Over a field of prime characteristic
`p`, if `Δ = 0` and `c₄ ≠ 0`, then the formal group of `W` has height `1`. -/
theorem height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero [hp : Fact p.Prime] (hΔ : W.Δ = 0)
    (hc₄ : W.c₄ ≠ 0) : (formalGroup W).height p = 1 := by
  have hle := W.order_nsmulSeries_formalGroup_le_of_Δ_eq_zero_of_c₄_ne_zero hp.out.ne_zero hΔ hc₄
  have h0 : (formalGroup W).nsmulSeries p ≠ 0 := fun h0 ↦ by simp [h0] at hle
  obtain ⟨h, hh0, hh⟩ :=
    (formalGroup W).exists_order_nsmulSeries_eq_pow hp.out (CharP.cast_eq_zero K p) h0
  rw [hh, Nat.cast_le] at hle
  have hh1 : h = 1 := le_antisymm
    ((Nat.pow_le_pow_iff_right hp.out.one_lt).mp (by simpa using hle))
    (Nat.one_le_iff_ne_zero.mpr hh0)
  rw [← Nat.cast_one, FormalGroup.height_eq_natCast_iff, hh, hh1, pow_one]

/-- Over a field of prime characteristic `p`, a singular Weierstrass curve (`Δ = 0`) has
formal-group height `1` exactly when `c₄ ≠ 0` (i.e., when the singularity is a node rather than a
cusp). -/
theorem height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero [Fact p.Prime] (hΔ : W.Δ = 0) :
    (formalGroup W).height p = 1 ↔ W.c₄ ≠ 0 := by
  refine ⟨fun h hc₄ ↦ ?_, W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ⟩
  rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ (CharP.cast_eq_zero K p)] at h
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
`p` (including `p = 0`, where every curve has height `⊤`), the formal group of any Weierstrass
curve has height `1`, `2`, or `⊤`. -/
theorem height_formalGroup_eq_one_or_eq_two_or_eq_top :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 ∨ (formalGroup W).height p = ⊤ := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    by_cases h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0
    · rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · push Not at h
      exact Or.inr (Or.inr
        (W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero h.2 h.1 (CharP.cast_eq_zero K p)))
  · exact Or.inr (Or.inr (((formalGroup W).height_eq_top_iff).mpr (by simp)))

/-- **Characterization of formal-group height `2`.** Over a field of prime characteristic `p`,
a Weierstrass curve has formal group of height `2` exactly when it is elliptic (`Δ ≠ 0`) and its
Hasse invariant vanishes. -/
theorem height_formalGroup_eq_two_iff [Fact p.Prime] :
    (formalGroup W).height p = 2 ↔
      W.Δ ≠ 0 ∧ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  constructor
  · intro h
    have hΔ : W.Δ ≠ 0 := by
      intro hΔ0
      by_cases hc₄ : W.c₄ = 0
      · rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ0 hc₄
          (CharP.cast_eq_zero K p)] at h
        exact ENat.natCast_ne_top 2 h.symm
      · rw [W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ0 hc₄] at h
        exact absurd h (by decide)
    have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
    exact ⟨hΔ,
      W.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero.mp h⟩
  · rintro ⟨hΔ, hH⟩
    have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
    exact W.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero.mpr hH

/-- **Characterization of formal-group height at most `2`.** Over a field of prime characteristic
`p`, a Weierstrass curve has formal group of height at most `2` exactly when it is smooth or nodal
(`c₄ ≠ 0 ∨ Δ ≠ 0`). -/
theorem height_formalGroup_le_two_iff [Fact p.Prime] :
    (formalGroup W).height p ≤ 2 ↔ W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hne.2 hne.1
      (CharP.cast_eq_zero K p)] at h
    exact absurd h (by decide)
  · intro h
    rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero h with h | h
    · rw [h]; decide
    · exact h.le

end Singular

end WeierstrassCurve

end
