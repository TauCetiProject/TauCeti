/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The discriminant in the cubic normal form of Tate's algorithm

In the normal form with `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄` and `ϖ³ ∣ a₆`, write
`a₂ = ϖ A₂`, `a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆`. The discriminant is divisible by `ϖ⁶`, and its
quotient reduces to sixteen times the discriminant of the residue cubic
`T³ + A₂ T² + A₄ T + A₆`. Consequently, its valuation is exactly six if and only if the residue
characteristic is not two and that cubic has nonzero discriminant.

This connects the cubic test of Tate's algorithm with the discriminant valuation used in its
algorithmic Ogg exponent. In residue characteristic two the quotient always vanishes; a cubic
with distinct roots therefore need not give discriminant valuation six. No perfectness,
Henselianity or minimality assumption is needed for these discriminant computations.

## Main results

* `WeierstrassCurve.exists_Δ_eq_pow_six_mul`: the factorization and congruence over any
  commutative ring.
* `WeierstrassCurve.six_le_addVal_Δ_of_pow_dvd`: the valuation bound in the cubic normal form.
* `WeierstrassCurve.addVal_Δ_eq_six_iff`: the exact valuation test, in every residue
  characteristic.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9,
  Step 6 of Tate's algorithm.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R]

/-- In the cubic normal form, `Δ = ϖ⁶ d` where `d` is congruent modulo `ϖ` to sixteen times
the discriminant of `T³ + A₂ T² + A₄ T + A₆`. This identity holds over any commutative ring. -/
theorem exists_Δ_eq_pow_six_mul (W : WeierstrassCurve R) (ϖ A₂ A₄ A₆ : R)
    (h₁ : ϖ ∣ W.a₁) (h₂ : W.a₂ = ϖ * A₂) (h₃ : ϖ ^ 2 ∣ W.a₃)
    (h₄ : W.a₄ = ϖ ^ 2 * A₄) (h₆ : W.a₆ = ϖ ^ 3 * A₆) :
    ∃ d : R, W.Δ = ϖ ^ 6 * d ∧ ϖ ∣ d - 16 * (Cubic.mk 1 A₂ A₄ A₆).discr := by
  obtain ⟨A₁, h₁⟩ := h₁
  obtain ⟨A₃, h₃⟩ := h₃
  let d := -(4 * A₂ + ϖ * A₁ ^ 2) ^ 2 *
      (4 * A₂ * A₆ - A₄ ^ 2 + ϖ * (A₁ ^ 2 * A₆ - A₁ * A₃ * A₄ + A₂ * A₃ ^ 2)) -
    8 * (2 * A₄ + ϖ * A₁ * A₃) ^ 3 - 27 * (4 * A₆ + ϖ * A₃ ^ 2) ^ 2 +
    9 * (4 * A₂ + ϖ * A₁ ^ 2) * (2 * A₄ + ϖ * A₁ * A₃) * (4 * A₆ + ϖ * A₃ ^ 2)
  refine ⟨d, ?_, ?_⟩
  · simp only [Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃, h₄, h₆]
    dsimp [d]
    ring
  · -- Compute the quotient in `R / (ϖ)` to avoid choosing representatives of the error term.
    have hϖ : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    apply Ideal.mem_span_singleton.1
    apply Ideal.Quotient.eq_zero_iff_mem.1
    simp only [map_sub, map_mul, map_ofNat, map_add, map_neg, map_pow, d, Cubic.discr,
      hϖ, zero_mul, add_zero, map_one]
    ring

/-- The discriminant in the cubic normal form is divisible by the sixth power of the
parameter. The parameter need not be a uniformiser or even a nonzero element. -/
theorem pow_six_dvd_Δ_of_pow_dvd (W : WeierstrassCurve R) (ϖ : R)
    (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ∣ W.a₂) (h₃ : ϖ ^ 2 ∣ W.a₃)
    (h₄ : ϖ ^ 2 ∣ W.a₄) (h₆ : ϖ ^ 3 ∣ W.a₆) : ϖ ^ 6 ∣ W.Δ := by
  obtain ⟨A₂, h₂⟩ := h₂
  obtain ⟨A₄, h₄⟩ := h₄
  obtain ⟨A₆, h₆⟩ := h₆
  obtain ⟨d, hd, _⟩ := W.exists_Δ_eq_pow_six_mul ϖ A₂ A₄ A₆ h₁ h₂ h₃ h₄ h₆
  exact ⟨d, hd⟩

end CommRing

section DiscreteValuationRing

open IsLocalRing IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

/-- The discriminant valuation in the cubic normal form is at least six. -/
theorem six_le_addVal_Δ_of_pow_dvd (hϖ : Irreducible ϖ) (W : WeierstrassCurve R)
    (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ∣ W.a₂) (h₃ : ϖ ^ 2 ∣ W.a₃)
    (h₄ : ϖ ^ 2 ∣ W.a₄) (h₆ : ϖ ^ 3 ∣ W.a₆) : 6 ≤ addVal R W.Δ := by
  have h := addVal_le_iff_dvd.2 (W.pow_six_dvd_Δ_of_pow_dvd ϖ h₁ h₂ h₃ h₄ h₆)
  simpa only [hϖ.addVal_pow, Nat.cast_ofNat] using h

/-- The residue of any quotient `Δ / ϖ⁶` is sixteen times the discriminant of the residue
cubic. The statement is independent of the choices of divisible-coefficient witnesses. -/
theorem residue_Δ_div_pow_six (hϖ : Irreducible ϖ) (W : WeierstrassCurve R)
    (A₂ A₄ A₆ d : R) (h₁ : ϖ ∣ W.a₁) (h₂ : W.a₂ = ϖ * A₂) (h₃ : ϖ ^ 2 ∣ W.a₃)
    (h₄ : W.a₄ = ϖ ^ 2 * A₄) (h₆ : W.a₆ = ϖ ^ 3 * A₆) (hd : W.Δ = ϖ ^ 6 * d) :
    residue R d = 16 * (Cubic.mk 1 (residue R A₂) (residue R A₄) (residue R A₆)).discr := by
  obtain ⟨d', hd', hcongr⟩ := W.exists_Δ_eq_pow_six_mul ϖ A₂ A₄ A₆ h₁ h₂ h₃ h₄ h₆
  have heq : d' = d := mul_left_cancel₀ (pow_ne_zero 6 hϖ.ne_zero) (hd'.symm.trans hd)
  rw [heq] at hcongr
  have hzero : residue R (d - 16 * (Cubic.mk 1 A₂ A₄ A₆).discr) = 0 := by
    rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact hcongr
  simpa [Cubic.discr, sub_eq_zero, map_ofNat] using hzero

/-- The discriminant valuation in the cubic normal form is exactly six precisely when two
is nonzero in the residue field and the residue cubic has nonzero discriminant. -/
theorem addVal_Δ_eq_six_iff (hϖ : Irreducible ϖ) (W : WeierstrassCurve R)
    (A₂ A₄ A₆ : R) (h₁ : ϖ ∣ W.a₁) (h₂ : W.a₂ = ϖ * A₂) (h₃ : ϖ ^ 2 ∣ W.a₃)
    (h₄ : W.a₄ = ϖ ^ 2 * A₄) (h₆ : W.a₆ = ϖ ^ 3 * A₆) :
    addVal R W.Δ = 6 ↔ (2 : ResidueField R) ≠ 0 ∧
      (Cubic.mk 1 (residue R A₂) (residue R A₄) (residue R A₆)).discr ≠ 0 := by
  obtain ⟨d, hd, _⟩ := W.exists_Δ_eq_pow_six_mul ϖ A₂ A₄ A₆ h₁ h₂ h₃ h₄ h₆
  have hr := W.residue_Δ_div_pow_six hϖ A₂ A₄ A₆ d h₁ h₂ h₃ h₄ h₆ hd
  rw [hd, AddValuation.map_mul, hϖ.addVal_pow, Nat.cast_ofNat]
  have hv : (6 : ℕ∞) + addVal R d = 6 ↔ addVal R d = 0 := by
    simp
  rw [hv, addVal_eq_zero_iff, ← residue_ne_zero_iff_isUnit, hr, mul_ne_zero_iff]
  have h16 : (16 : ResidueField R) = 2 ^ 4 := by norm_num
  rw [h16, pow_ne_zero_iff (by norm_num : (4 : ℕ) ≠ 0)]

end DiscreteValuationRing

end WeierstrassCurve
