/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.FieldTheory.Perfect
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic

/-!
# Tate's algorithm: the additive normal form and the non-minimality test

Let `R` be a discrete valuation ring with uniformiser `ϖ` and perfect residue field `k`. Once
Step 2 of Tate's algorithm has moved the singular point of the reduction to the origin
(`WeierstrassCurve.exists_map_residue_variableChange_isSingular_zero`), the reduction is additive
exactly when `ϖ ∣ b₂`, and the algorithm then runs three divisibility tests:

* Step 3: if `ϖ² ∤ a₆`, the reduction symbol is `II`;
* Step 4: if `ϖ³ ∤ b₈`, it is `III`;
* Step 5: if `ϖ³ ∤ b₆`, it is `IV`.

If all three fail, Step 6 changes coordinates over `R` so that

  `ϖ ∣ a₁`, `ϖ ∣ a₂`, `ϖ² ∣ a₃`, `ϖ² ∣ a₄`, `ϖ³ ∣ a₆`,

which is the normal form from which the cubic `T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³` of Steps 6–8 is
read. This file proves that Step 6 succeeds, with a change of variables `y ↦ y + s x + t` fixing
`x`. Each of its two halves completes a square modulo `ϖ`: first `T² + a₁ T − a₂`, whose
discriminant is `b₂`, then `T² + (a₃/ϖ) T − a₆/ϖ²`, whose discriminant is `b₆/ϖ²`. A quadratic with
vanishing discriminant over the perfect field `k` has a double root in `k`
(`Polynomial.exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero`); in
characteristic `2` this is a square root, which is where perfectness enters. The conditions on
`a₃` and `a₄` that Step 2 provides are not needed as hypotheses: `ϖ ∣ a₃` follows from
`b₆ = a₃² + 4 a₆`, and `ϖ² ∣ a₄` in the normal form from `b₈ ≡ −a₄² (mod ϖ³)`.

The algorithm stops at Step 11 when `ϖⁱ ∣ aᵢ` for every `i`. The substitution `x ↦ ϖ² x`,
`y ↦ ϖ³ y` then divides each `aᵢ` by `ϖⁱ` and the discriminant by `ϖ¹²`, so the equation was not
minimal; `WeierstrassCurve.not_isMinimal_baseChange_of_pow_dvd` records this.

## Main results

* `WeierstrassCurve.exists_variableChange_dvd_a₁_a₂_a₃_a₄_a₆`: **Step 6 of Tate's algorithm**.
  If `ϖ ∣ b₂`, `ϖ² ∣ a₆`, `ϖ³ ∣ b₆` and `ϖ³ ∣ b₈`, a change of variables `y ↦ y + s x + t` over `R`
  produces `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄` and `ϖ³ ∣ a₆`.
* `WeierstrassCurve.not_isMinimal_baseChange_of_pow_dvd`: **Step 11 of Tate's algorithm**. An
  equation over `R` with nonzero discriminant and `ϖⁱ ∣ aᵢ` for `i = 1, 2, 3, 4, 6` is not minimal
  over the fraction field.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9,
  Steps 3 to 6 and Step 11 of Tate's algorithm.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

/-- A double root of `T² + a T − b` modulo `ϖ`, lifted from the residue field: if `ϖ` divides the
discriminant `a² + 4 b`, some `s ∈ R` has `ϖ ∣ a + 2 s` and `ϖ ∣ b − s a − s²`. For a Weierstrass
equation these are the new `a₁` and `a₂` after `y ↦ y + s x`. -/
private theorem exists_dvd_add_two_mul_and_dvd_sub_mul_sub_sq [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) {a b : R} (h : ϖ ∣ a ^ 2 + 4 * b) :
    ∃ s : R, ϖ ∣ a + 2 * s ∧ ϖ ∣ b - s * a - s ^ 2 := by
  have key (x : R) : residue R x = 0 ↔ ϖ ∣ x := by
    rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hd : discrim 1 (residue R a) (-residue R b) = 0 := by
    rw [discrim, ← (key _).2 h]
    simp only [map_add, map_pow, map_mul, map_ofNat]
    ring
  obtain ⟨x, hx, hx'⟩ :=
    exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero one_ne_zero hd
  obtain ⟨s, rfl⟩ := residue_surjective x
  refine ⟨s, (key _).1 ?_, (key _).1 ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    linear_combination hx'
  · simp only [map_sub, map_mul, map_pow]
    linear_combination -hx

/-- **Tate's algorithm, Step 6.** Over a discrete valuation ring with uniformiser `ϖ` and perfect
residue field, let `W` be a Weierstrass equation over `R` on which Steps 3–5 do not stop:
`ϖ ∣ b₂`, `ϖ² ∣ a₆`, `ϖ³ ∣ b₈` and `ϖ³ ∣ b₆`. (After Step 2, `ϖ ∣ b₂` says the reduction is
additive; the normal form of Step 2 itself is not assumed.) Then a change of variables
`y ↦ y + s x + t` with `s, t ∈ R` carries `W` to an equation with `ϖ ∣ a₁`, `ϖ ∣ a₂`, `ϖ² ∣ a₃`,
`ϖ² ∣ a₄` and `ϖ³ ∣ a₆`. -/
theorem exists_variableChange_dvd_a₁_a₂_a₃_a₄_a₆ [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) (hb₂ : ϖ ∣ W.b₂) (ha₆ : ϖ ^ 2 ∣ W.a₆)
    (hb₆ : ϖ ^ 3 ∣ W.b₆) (hb₈ : ϖ ^ 3 ∣ W.b₈) :
    ∃ s t : R, ϖ ∣ (VariableChange.mk 1 0 s t • W).a₁ ∧ ϖ ∣ (VariableChange.mk 1 0 s t • W).a₂ ∧
      ϖ ^ 2 ∣ (VariableChange.mk 1 0 s t • W).a₃ ∧ ϖ ^ 2 ∣ (VariableChange.mk 1 0 s t • W).a₄ ∧
      ϖ ^ 3 ∣ (VariableChange.mk 1 0 s t • W).a₆ := by
  have hp : Prime ϖ := hϖ.prime
  -- First half: `s` clears `a₁` and `a₂` modulo `ϖ`, since `b₂ = a₁² + 4 a₂`.
  obtain ⟨s, hs₁, hs₂⟩ := exists_dvd_add_two_mul_and_dvd_sub_mul_sub_sq hϖ (a := W.a₁) (b := W.a₂)
    (by rwa [b₂] at hb₂)
  -- `b₆ = a₃² + 4 a₆` and `ϖ² ∣ a₆` give `ϖ ∣ a₃`; write `a₃ = ϖ α` and `a₆ = ϖ² β`.
  obtain ⟨α, hα⟩ : ϖ ∣ W.a₃ := hp.dvd_of_dvd_pow (n := 2) <| by
    have : W.a₃ ^ 2 = W.b₆ - 4 * W.a₆ := by rw [b₆]; ring
    rw [this]
    exact dvd_sub ((dvd_pow_self ϖ three_ne_zero).trans hb₆)
      (((dvd_pow_self ϖ two_ne_zero).trans ha₆).mul_left 4)
  obtain ⟨β, hβ⟩ := ha₆
  -- Second half: `ϖ ∣ α² + 4 β = b₆ / ϖ²`, so `t = ϖ τ` clears `a₃ / ϖ` and `a₆ / ϖ²` modulo `ϖ`.
  have hαβ : ϖ ∣ α ^ 2 + 4 * β := by
    have h : ϖ ^ 2 * ϖ ∣ ϖ ^ 2 * (α ^ 2 + 4 * β) := by
      rw [← pow_succ]
      convert hb₆ using 1
      rw [b₆, hα, hβ]
      ring
    rwa [mul_dvd_mul_iff_left (pow_ne_zero 2 hp.ne_zero)] at h
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_dvd_add_two_mul_and_dvd_sub_mul_sub_sq hϖ hαβ
  refine ⟨s, ϖ * τ, ?_⟩
  set V := VariableChange.mk 1 0 s (ϖ * τ) • W with hV
  have hV₁ : V.a₁ = W.a₁ + 2 * s := by simp [hV, variableChange_a₁]
  have hV₂ : V.a₂ = W.a₂ - s * W.a₁ - s ^ 2 := by simp [hV, variableChange_a₂]
  have hV₃ : V.a₃ = ϖ * (α + 2 * τ) := by simp [hV, variableChange_a₃, hα]; ring
  have hV₆ : V.a₆ = ϖ ^ 2 * (β - τ * α - τ ^ 2) := by
    simp [hV, variableChange_a₆, hα, hβ]; ring
  have hV₈ : V.b₈ = W.b₈ := by simp [hV, variableChange_b₈]
  have h₁ : ϖ ∣ V.a₁ := hV₁ ▸ hs₁
  have h₂ : ϖ ∣ V.a₂ := hV₂ ▸ hs₂
  have h₃ : ϖ ^ 2 ∣ V.a₃ := by rw [hV₃, sq]; exact mul_dvd_mul_left ϖ hτ₁
  have h₆ : ϖ ^ 3 ∣ V.a₆ := by rw [hV₆, pow_succ ϖ 2]; exact mul_dvd_mul_left _ hτ₂
  refine ⟨h₁, h₂, h₃, ?_, h₆⟩
  -- `b₈ = a₁² a₆ + 4 a₂ a₆ − a₁ a₃ a₄ + a₂ a₃² − a₄²`, and every term but `a₄²` is divisible by
  -- `ϖ³`, so `ϖ³ ∣ a₄²`. Then `ϖ ∣ a₄`, and writing `a₄ = ϖ c` gives `ϖ ∣ c²`, so `ϖ ∣ c`.
  have h₄ : ϖ ^ 2 * ϖ ∣ V.a₄ ^ 2 := by
    obtain ⟨x₁, hx₁⟩ := h₁
    obtain ⟨x₂, hx₂⟩ := h₂
    obtain ⟨x₃, hx₃⟩ := h₃
    obtain ⟨x₆, hx₆⟩ := h₆
    obtain ⟨y, hy⟩ := hb₈
    refine ⟨ϖ ^ 2 * x₁ ^ 2 * x₆ + 4 * ϖ * x₂ * x₆ - x₁ * x₃ * V.a₄ + ϖ ^ 2 * x₂ * x₃ ^ 2 - y, ?_⟩
    have hb := hV₈
    rw [b₈, hy, hx₁, hx₂, hx₃, hx₆] at hb
    linear_combination -hb
  obtain ⟨c, hc⟩ := hp.dvd_of_dvd_pow (dvd_trans (dvd_mul_left ϖ _) h₄)
  rw [hc, mul_pow, mul_dvd_mul_iff_left (pow_ne_zero 2 hp.ne_zero)] at h₄
  rw [hc, sq ϖ]
  exact mul_dvd_mul_left ϖ (hp.dvd_of_dvd_pow h₄)

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum in
/-- **Tate's algorithm, Step 11.** If a Weierstrass equation over a discrete valuation ring `R` has
nonzero discriminant and `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`, `ϖ⁴ ∣ a₄`, `ϖ⁶ ∣ a₆`, then its base change
to the fraction field `K` is not minimal over `R`: the substitution `x ↦ ϖ² x`, `y ↦ ϖ³ y` divides
each `aᵢ` by `ϖⁱ`, so the result is again integral, and divides the discriminant by `ϖ¹²`. -/
theorem not_isMinimal_baseChange_of_pow_dvd (hϖ : Irreducible ϖ) (W : WeierstrassCurve R)
    (hΔ : W.Δ ≠ 0) (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂) (h₃ : ϖ ^ 3 ∣ W.a₃) (h₄ : ϖ ^ 4 ∣ W.a₄)
    (h₆ : ϖ ^ 6 ∣ W.a₆) : ¬ IsMinimal R (W.baseChange K) := by
  intro hmin
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c₃, hc₃⟩ := h₃
  obtain ⟨c₄, hc₄⟩ := h₄
  obtain ⟨c₆, hc₆⟩ := h₆
  have hϖ₀ : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hϖ.ne_zero
  let C : VariableChange K := ⟨Units.mk0 _ hϖ₀, 0, 0, 0⟩
  -- The scaled equation is the base change of `⟨c₁, c₂, c₃, c₄, c₆⟩`, hence integral.
  have hC : C • W.baseChange K = (⟨c₁, c₂, c₃, c₄, c₆⟩ : WeierstrassCurve R).baseChange K := by
    ext <;> simp [C, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, baseChange, hc₁, hc₂, hc₃, hc₄, hc₆] <;> field_simp
  have : IsIntegral R (C • W.baseChange K) := ⟨⟨_, hC⟩⟩
  have hle := valuation_Δ_le_of_isMinimal_smul R (W₁ := W.baseChange K) C rfl
  rw [variableChange_Δ, map_mul, map_pow] at hle
  have hvΔ : valuation K (maximalIdeal R) (W.baseChange K).Δ ≠ 0 := by
    rw [Valuation.ne_zero_iff, baseChange, map_Δ]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hΔ
  have hv : valuation K (maximalIdeal R) (algebraMap R K ϖ) < 1 :=
    (valuation_lt_one_iff_mem _ _).2 ((mem_maximalIdeal _).2 hϖ.not_isUnit)
  have hv' : 1 < valuation K (maximalIdeal R) ↑(C.u⁻¹) := by
    simp only [C, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
    exact one_lt_inv_iff₀.2 ⟨(Valuation.pos_iff _).2 hϖ₀, hv⟩
  have := mul_lt_mul_of_pos_right (one_lt_pow₀ hv' (by norm_num : (12 : ℕ) ≠ 0))
    (zero_lt_iff.2 hvΔ)
  rw [one_mul] at this
  exact (this.trans_le hle).false

end WeierstrassCurve

end
