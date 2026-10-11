/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.FieldTheory.Perfect
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

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
vanishing discriminant over the perfect field `k` has a double root in `k`, which lifts to `R`
(`TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal`);
in characteristic `2` this is a square root, which is where perfectness enters. The conditions on
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

* `WeierstrassCurve.pow_three_dvd_Δ_of_dvd_b₂_of_dvd_a₃_of_dvd_a₄_of_sq_dvd_a₆`,
  `WeierstrassCurve.pow_four_dvd_Δ_of_dvd_b₂_of_sq_dvd_b₆_of_pow_three_dvd_b₈`, and
  `WeierstrassCurve.pow_five_dvd_Δ_of_dvd_b₂_of_pow_three_dvd_b₆_of_pow_three_dvd_b₈`:
  discriminant bounds at the early additive tests;
  `WeierstrassCurve.sq_dvd_b₄_of_dvd_b₂_of_sq_dvd_b₆_of_pow_three_dvd_b₈` supplies the Step 4 bound.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9,
  Steps 3 to 6 and Step 11 of Tate's algorithm.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

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
  have key (x : R) : x ∈ maximalIdeal R ↔ ϖ ∣ x := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  -- First half: `s` clears `a₁` and `a₂` modulo `ϖ`, since `b₂ = a₁² + 4 a₂`.
  obtain ⟨s, hs₁, hs₂⟩ :=
    TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal
      (a := W.a₁) (b := W.a₂) ((key _).2 (by rwa [b₂] at hb₂))
  rw [key] at hs₁ hs₂
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
  obtain ⟨τ, hτ₁, hτ₂⟩ :=
    TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal
      ((key _).2 hαβ)
  rw [key] at hτ₁ hτ₂
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

namespace TauCeti

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ϖ : R)

/-- If the Step 3 test fails (`ϖ² ∣ a₆`), the discriminant is divisible by `ϖ³`.
The coefficient conditions are those of the Step 2 normal form. -/
theorem _root_.WeierstrassCurve.pow_three_dvd_Δ_of_dvd_b₂_of_dvd_a₃_of_dvd_a₄_of_sq_dvd_a₆
    (hb₂ : ϖ ∣ W.b₂) (h₃ : ϖ ∣ W.a₃) (h₄ : ϖ ∣ W.a₄) (h₆ : ϖ ^ 2 ∣ W.a₆) :
    ϖ ^ 3 ∣ W.Δ := by
  have h₆one : ϖ ∣ W.a₆ := (dvd_pow_self ϖ (by decide : 2 ≠ 0)).trans h₆
  have hb₈ : ϖ ^ 2 ∣ W.b₈ :=
    (W.dvd_b₄_and_dvd_b₆_and_sq_dvd_b₈_of_dvd_b₂_of_dvd_a₃_of_dvd_a₄_of_dvd_a₆
      ϖ hb₂ h₃ h₄ h₆one).2.2
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨A₃, hA₃⟩ := h₃
  obtain ⟨A₄, hA₄⟩ := h₄
  obtain ⟨A₆, hA₆⟩ := h₆
  have hB₄ : W.b₄ = ϖ * (W.a₁ * A₃ + 2 * A₄) := by
    rw [WeierstrassCurve.b₄, hA₃, hA₄]; ring
  have hB₆ : W.b₆ = ϖ ^ 2 * (A₃ ^ 2 + 4 * A₆) := by
    rw [WeierstrassCurve.b₆, hA₃, hA₆]; ring
  obtain ⟨B₈, hB₈⟩ := hb₈
  refine ⟨-ϖ * B₂ ^ 2 * B₈ - 8 * (W.a₁ * A₃ + 2 * A₄) ^ 3 -
    27 * ϖ * (A₃ ^ 2 + 4 * A₆) ^ 2 +
    9 * ϖ * B₂ * (W.a₁ * A₃ + 2 * A₄) * (A₃ ^ 2 + 4 * A₆), ?_⟩
  rw [WeierstrassCurve.Δ, hB₂, hB₄, hB₆, hB₈]
  ring

/-- At Step 4, the failed `b₈` test forces `ϖ² ∣ b₄` from
`4 b₈ = b₂ b₆ - b₄²`. No restriction on the residue characteristic is needed. -/
theorem _root_.WeierstrassCurve.sq_dvd_b₄_of_dvd_b₂_of_sq_dvd_b₆_of_pow_three_dvd_b₈
    [IsDomain R]
    (hϖ : Prime ϖ) (hb₂ : ϖ ∣ W.b₂) (hb₆ : ϖ ^ 2 ∣ W.b₆)
    (hb₈ : ϖ ^ 3 ∣ W.b₈) : ϖ ^ 2 ∣ W.b₄ := by
  have heq : W.b₄ ^ 2 = W.b₂ * W.b₆ - 4 * W.b₈ := by
    linear_combination W.b_relation
  have hsq : ϖ ^ 3 ∣ W.b₄ ^ 2 := by
    rw [heq]
    obtain ⟨B₂, hB₂⟩ := hb₂
    obtain ⟨B₆, hB₆⟩ := hb₆
    obtain ⟨B₈, hB₈⟩ := hb₈
    refine ⟨B₂ * B₆ - 4 * B₈, ?_⟩
    rw [hB₂, hB₆, hB₈]
    ring
  have hp : ϖ ∣ W.b₄ := hϖ.dvd_of_dvd_pow
    ((dvd_pow_self ϖ (by decide : 3 ≠ 0)).trans hsq)
  obtain ⟨B₄, hB₄⟩ := hp
  have hB₄sq : ϖ ∣ B₄ ^ 2 := by
    rw [hB₄, mul_pow] at hsq
    rw [pow_succ ϖ 2] at hsq
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ.ne_zero)).1 hsq
  obtain ⟨C₄, hC₄⟩ := hϖ.dvd_of_dvd_pow hB₄sq
  exact ⟨C₄, by rw [hB₄, hC₄]; ring⟩

/-- If the Step 4 test fails (`ϖ³ ∣ b₈`), then `ϖ⁴` divides the discriminant.
The `ϖ² ∣ b₆` hypothesis already follows from the failed Step 3 test. -/
theorem _root_.WeierstrassCurve.pow_four_dvd_Δ_of_dvd_b₂_of_sq_dvd_b₆_of_pow_three_dvd_b₈
    [IsDomain R]
    (hϖ : Prime ϖ) (hb₂ : ϖ ∣ W.b₂) (hb₆ : ϖ ^ 2 ∣ W.b₆)
    (hb₈ : ϖ ^ 3 ∣ W.b₈) : ϖ ^ 4 ∣ W.Δ := by
  have hb₄ := W.sq_dvd_b₄_of_dvd_b₂_of_sq_dvd_b₆_of_pow_three_dvd_b₈ ϖ hϖ hb₂ hb₆ hb₈
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨B₄, hB₄⟩ := hb₄
  obtain ⟨B₆, hB₆⟩ := hb₆
  obtain ⟨B₈, hB₈⟩ := hb₈
  refine ⟨-ϖ * B₂ ^ 2 * B₈ - 8 * ϖ ^ 2 * B₄ ^ 3 - 27 * B₆ ^ 2 +
    9 * ϖ * B₂ * B₄ * B₆, ?_⟩
  rw [WeierstrassCurve.Δ, hB₂, hB₄, hB₆, hB₈]
  ring

/-- If the Step 5 test also fails (`ϖ³ ∣ b₆`), then `ϖ⁵` divides the discriminant.
This is the discriminant bound at the entry to Step 6, before its normalising change of
variables. -/
theorem _root_.WeierstrassCurve.pow_five_dvd_Δ_of_dvd_b₂_of_pow_three_dvd_b₆_of_pow_three_dvd_b₈
    [IsDomain R] (hϖ : Prime ϖ) (hb₂ : ϖ ∣ W.b₂) (hb₆ : ϖ ^ 3 ∣ W.b₆)
    (hb₈ : ϖ ^ 3 ∣ W.b₈) : ϖ ^ 5 ∣ W.Δ := by
  have hb₆two : ϖ ^ 2 ∣ W.b₆ :=
    (pow_dvd_pow ϖ (by decide : 2 ≤ 3)).trans hb₆
  have hb₄ := W.sq_dvd_b₄_of_dvd_b₂_of_sq_dvd_b₆_of_pow_three_dvd_b₈ ϖ hϖ hb₂ hb₆two hb₈
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨B₄, hB₄⟩ := hb₄
  obtain ⟨B₆, hB₆⟩ := hb₆
  obtain ⟨B₈, hB₈⟩ := hb₈
  refine ⟨-B₂ ^ 2 * B₈ - 8 * ϖ * B₄ ^ 3 - 27 * ϖ * B₆ ^ 2 +
    9 * ϖ * B₂ * B₄ * B₆, ?_⟩
  rw [WeierstrassCurve.Δ, hB₂, hB₄, hB₆, hB₈]
  ring

end TauCeti

end
