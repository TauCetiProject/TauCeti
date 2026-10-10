/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Additive
import TauCeti.Algebra.Polynomial.CubicTripleRoot
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

/-!
# Tate's algorithm: the triple-root branch

Let `R` be a discrete valuation ring with uniformiser `ϖ` and perfect residue field `k`. Step 6 of
Tate's algorithm (`WeierstrassCurve.exists_variableChange_dvd_a₁_a₂_a₃_a₄_a₆`) brings an equation
with additive reduction to the normal form `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆`, and reads off it
the residue cubic

  `P(T) = T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³` over `k`.

This file treats the branch of the algorithm in which `P` has a triple root (Steps 8 to 10):

* Step 8: translate `x ↦ x + r` so that the triple root is `T = 0`. Then `ϖ² ∣ a₂`, `ϖ³ ∣ a₄`
  and `ϖ⁴ ∣ a₆`. If the quadratic `Y² + (a₃/ϖ²) Y − a₆/ϖ⁴` has distinct roots, that is if
  `ϖ⁵ ∤ b₆`, the reduction symbol is `IV*`.
* Step 9: otherwise translate `y ↦ y + t` so that its double root is `Y = 0`. Then `ϖ³ ∣ a₃` and
  `ϖ⁵ ∣ a₆`. If `ϖ⁴ ∤ a₄`, the reduction symbol is `III*`.
* Step 10: otherwise, if `ϖ⁶ ∤ a₆`, the reduction symbol is `II*`.

If all three tests fail, then `ϖⁱ ∣ aᵢ` for every `i` and the equation was not minimal (Step 11,
`WeierstrassCurve.not_isMinimal_baseChange_of_pow_dvd`). So on a minimal equation this branch
always stops at Step 8, 9 or 10.

The triple-root condition is stated on the coefficients of `W`, without dividing by `ϖ`: by
`Polynomial.exists_cubic_eq_X_sub_C_pow_three_iff`, a monic cubic `T³ + b T² + c T + d` over the
perfect field `k` is a cube exactly when `b² = 3c`, `c² = 3bd` and `bc = 9d`. For `P` these
conditions read `ϖ³ ∣ a₂² − 3 a₄`, `ϖ⁵ ∣ a₄² − 3 a₂ a₆` and `ϖ⁴ ∣ a₂ a₄ − 9 a₆`. Perfectness of `k`
enters twice: to find the triple root, a cube root in characteristic `3`, and to complete the
square in Step 9, a square root in characteristic `2`.

## Main results

* `WeierstrassCurve.exists_variableChange_pow_dvd_a₂_a₄_a₆`: **Step 8 of Tate's algorithm**. If
  the residue cubic has a triple root, a translation `x ↦ x + r` over `R` produces `ϖ ∣ a₁`,
  `ϖ² ∣ a₂, a₃`, `ϖ³ ∣ a₄` and `ϖ⁴ ∣ a₆`.
* `WeierstrassCurve.exists_variableChange_pow_dvd_a₃_a₆`: **Step 9 of Tate's algorithm**. If
  moreover `ϖ⁵ ∣ b₆`, a translation `y ↦ y + t` over `R` produces in addition `ϖ³ ∣ a₃` and
  `ϖ⁵ ∣ a₆`.
* `WeierstrassCurve.exists_variableChange_not_pow_dvd_b₆_or_a₄_or_a₆`: **the triple-root branch
  terminates.** On a minimal equation with nonzero discriminant whose residue cubic has a triple
  root, a change of variables over `R` reaches the normal form of Step 8 and one of
  `ϖ⁵ ∤ b₆` (Step 8, `IV*`), `ϖ⁴ ∤ a₄` (Step 9, `III*`) or `ϖ⁶ ∤ a₆` (Step 10, `II*`) holds,
  the last two in the normal form of Step 9.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9,
  Steps 8 to 10 of Tate's algorithm.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

/-- **Tate's algorithm, Step 8.** Over a discrete valuation ring with uniformiser `ϖ` and perfect
residue field, let `W` be an equation in the normal form of Step 6, `ϖ ∣ a₁`, `ϖ² ∣ a₃, a₄`,
`ϖ³ ∣ a₆`, whose residue cubic `T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³` has a triple root:
`ϖ³ ∣ a₂² − 3 a₄`, `ϖ⁵ ∣ a₄² − 3 a₂ a₆` and `ϖ⁴ ∣ a₂ a₄ − 9 a₆`
(`Polynomial.exists_cubic_eq_X_sub_C_pow_three_iff`). Then a translation `x ↦ x + r` with `r ∈ R`
moves the triple root to `0`: the new equation has `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ² ∣ a₃`, `ϖ³ ∣ a₄` and
`ϖ⁴ ∣ a₆`. (The condition `ϖ ∣ a₂` of the Step 6 normal form follows from the others.) -/
theorem exists_variableChange_pow_dvd_a₂_a₄_a₆ [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) (h₁ : ϖ ∣ W.a₁) (h₃ : ϖ ^ 2 ∣ W.a₃)
    (h₄ : ϖ ^ 2 ∣ W.a₄) (h₆ : ϖ ^ 3 ∣ W.a₆) (hb : ϖ ^ 3 ∣ W.a₂ ^ 2 - 3 * W.a₄)
    (hc : ϖ ^ 5 ∣ W.a₄ ^ 2 - 3 * W.a₂ * W.a₆) (hd : ϖ ^ 4 ∣ W.a₂ * W.a₄ - 9 * W.a₆) :
    ∃ r : R, ϖ ∣ (VariableChange.mk 1 r 0 0 • W).a₁ ∧ ϖ ^ 2 ∣ (VariableChange.mk 1 r 0 0 • W).a₂ ∧
      ϖ ^ 2 ∣ (VariableChange.mk 1 r 0 0 • W).a₃ ∧ ϖ ^ 3 ∣ (VariableChange.mk 1 r 0 0 • W).a₄ ∧
      ϖ ^ 4 ∣ (VariableChange.mk 1 r 0 0 • W).a₆ := by
  have hp : Prime ϖ := hϖ.prime
  have hϖ₀ : ϖ ≠ 0 := hp.ne_zero
  have key (x : R) : residue R x = 0 ↔ ϖ ∣ x := by
    rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  -- Write `a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆`; then `ϖ ∣ a₂`, say `a₂ = ϖ A₂`, since `ϖ² ∣ a₂²`.
  obtain ⟨A₄, hA₄⟩ := h₄
  obtain ⟨A₆, hA₆⟩ := h₆
  obtain ⟨A₂, hA₂⟩ : ϖ ∣ W.a₂ := hp.dvd_of_dvd_pow (n := 2) <| by
    have : W.a₂ ^ 2 = (W.a₂ ^ 2 - 3 * W.a₄) + 3 * W.a₄ := by ring
    rw [this]
    exact dvd_add ((dvd_pow_self ϖ three_ne_zero).trans hb)
      (by rw [hA₄]; exact ⟨3 * ϖ * A₄, by ring⟩)
  -- The three conditions say that the residue cubic `T³ + A₂ T² + A₄ T + A₆` is a cube.
  have hcancel {n : ℕ} {x : R} (h : ϖ ^ n * ϖ ∣ ϖ ^ n * x) : residue R x = 0 :=
    (key x).2 ((mul_dvd_mul_iff_left (pow_ne_zero n hϖ₀)).1 h)
  have hb' : residue R A₂ ^ 2 = 3 * residue R A₄ := by
    rw [← sub_eq_zero, ← map_pow, ← map_ofNat (residue R) 3, ← map_mul, ← map_sub]
    refine hcancel (n := 2) ?_
    rw [← pow_succ]
    convert hb using 1
    rw [hA₂, hA₄]
    ring
  have hc' : residue R A₄ ^ 2 = 3 * residue R A₂ * residue R A₆ := by
    rw [← sub_eq_zero, ← map_pow, ← map_ofNat (residue R) 3, ← map_mul, ← map_mul, ← map_sub]
    refine hcancel (n := 4) ?_
    rw [← pow_succ]
    convert hc using 1
    rw [hA₂, hA₄, hA₆]
    ring
  have hd' : residue R A₂ * residue R A₄ = 9 * residue R A₆ := by
    rw [← sub_eq_zero, ← map_mul, ← map_ofNat (residue R) 9, ← map_mul, ← map_sub]
    refine hcancel (n := 3) ?_
    rw [← pow_succ]
    convert hd using 1
    rw [hA₂, hA₄, hA₆]
    ring
  obtain ⟨ρ', hρ'⟩ := exists_cubic_eq_X_sub_C_pow_three_iff.2 ⟨hb', hc', hd'⟩
  obtain ⟨ρ, rfl⟩ := residue_surjective ρ'
  obtain ⟨hρ₂, hρ₄, hρ₆⟩ := cubic_eq_X_sub_C_pow_three_iff.1 hρ'
  -- Lift the triple root to `ρ ∈ R`; then `x ↦ x + ϖ ρ` moves it to `0`.
  have e₂ : ϖ ∣ A₂ + 3 * ρ := (key _).1 (by
    simp only [map_add, map_mul, map_ofNat, hρ₂]; ring)
  have e₄ : ϖ ∣ A₄ + 2 * ρ * A₂ + 3 * ρ ^ 2 := (key _).1 (by
    simp only [map_add, map_mul, map_pow, map_ofNat, hρ₂, hρ₄]; ring)
  have e₆ : ϖ ∣ A₆ + ρ * A₄ + ρ ^ 2 * A₂ + ρ ^ 3 := (key _).1 (by
    simp only [map_add, map_mul, map_pow, hρ₂, hρ₄, hρ₆]; ring)
  refine ⟨ϖ * ρ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [variableChange_a₁] using h₁
  · have : (VariableChange.mk 1 (ϖ * ρ) 0 0 • W).a₂ = ϖ * (A₂ + 3 * ρ) := by
      simp [variableChange_a₂, hA₂]; ring
    rw [this, sq]
    exact mul_dvd_mul_left ϖ e₂
  · have : (VariableChange.mk 1 (ϖ * ρ) 0 0 • W).a₃ = W.a₃ + ϖ * ρ * W.a₁ := by
      simp [variableChange_a₃]
    rw [this, sq]
    exact dvd_add (sq ϖ ▸ h₃) (by rw [mul_assoc]; exact mul_dvd_mul_left ϖ (h₁.mul_left ρ))
  · have : (VariableChange.mk 1 (ϖ * ρ) 0 0 • W).a₄ = ϖ ^ 2 * (A₄ + 2 * ρ * A₂ + 3 * ρ ^ 2) := by
      simp [variableChange_a₄, hA₂, hA₄]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ e₄
  · have : (VariableChange.mk 1 (ϖ * ρ) 0 0 • W).a₆ =
        ϖ ^ 3 * (A₆ + ρ * A₄ + ρ ^ 2 * A₂ + ρ ^ 3) := by
      simp [variableChange_a₆, hA₂, hA₄, hA₆]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ e₆

/-- **Tate's algorithm, Step 9.** Over a discrete valuation ring with uniformiser `ϖ` and perfect
residue field, let `W` be an equation in the normal form of Step 8, `ϖ ∣ a₁`, `ϖ² ∣ a₂`,
`ϖ³ ∣ a₄`, `ϖ⁴ ∣ a₆`, on which Step 8 does not stop: the quadratic `Y² + (a₃/ϖ²) Y − a₆/ϖ⁴` has
a double root, that is `ϖ⁵ ∣ b₆`. Then a translation `y ↦ y + t` with `t ∈ R` moves the double
root to `0`: the new equation has `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`, `ϖ³ ∣ a₄` and `ϖ⁵ ∣ a₆`. (The
condition `ϖ² ∣ a₃` of the Step 8 normal form follows from `b₆ = a₃² + 4 a₆`.) -/
theorem exists_variableChange_pow_dvd_a₃_a₆ [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂)
    (h₄ : ϖ ^ 3 ∣ W.a₄) (h₆ : ϖ ^ 4 ∣ W.a₆) (hb₆ : ϖ ^ 5 ∣ W.b₆) :
    ∃ t : R, ϖ ∣ (VariableChange.mk 1 0 0 t • W).a₁ ∧ ϖ ^ 2 ∣ (VariableChange.mk 1 0 0 t • W).a₂ ∧
      ϖ ^ 3 ∣ (VariableChange.mk 1 0 0 t • W).a₃ ∧ ϖ ^ 3 ∣ (VariableChange.mk 1 0 0 t • W).a₄ ∧
      ϖ ^ 5 ∣ (VariableChange.mk 1 0 0 t • W).a₆ := by
  have hp : Prime ϖ := hϖ.prime
  have hϖ₀ : ϖ ^ 4 ≠ 0 := pow_ne_zero 4 hp.ne_zero
  have key (x : R) : x ∈ maximalIdeal R ↔ ϖ ∣ x := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  -- `b₆ = a₃² + 4 a₆` gives `ϖ² ∣ a₃`; write `a₃ = ϖ² α` and `a₆ = ϖ⁴ β`.
  obtain ⟨β, hβ⟩ := h₆
  have h₃ : ϖ ^ 4 ∣ W.a₃ ^ 2 := by
    have : W.a₃ ^ 2 = W.b₆ - 4 * W.a₆ := by rw [b₆]; ring
    rw [this]
    exact dvd_sub ((pow_dvd_pow ϖ (show 4 ≤ 5 by norm_num)).trans hb₆)
      (by rw [hβ]; exact ⟨4 * β, by ring⟩)
  obtain ⟨c, hc⟩ := hp.dvd_of_dvd_pow ((dvd_pow_self ϖ four_ne_zero).trans h₃)
  rw [hc, mul_pow, show ϖ ^ 4 = ϖ ^ 2 * ϖ ^ 2 by ring,
    mul_dvd_mul_iff_left (pow_ne_zero 2 hp.ne_zero)] at h₃
  obtain ⟨α, hα⟩ : ϖ ^ 2 ∣ W.a₃ := by
    rw [hc, sq ϖ]
    exact mul_dvd_mul_left ϖ (hp.dvd_of_dvd_pow ((dvd_pow_self ϖ two_ne_zero).trans h₃))
  -- `ϖ ∣ α² + 4 β = b₆ / ϖ⁴`, so `t = ϖ² τ` completes the square modulo `ϖ⁵`.
  have hαβ : ϖ ∣ α ^ 2 + 4 * β := by
    have h : ϖ ^ 4 * ϖ ∣ ϖ ^ 4 * (α ^ 2 + 4 * β) := by
      rw [← pow_succ]
      convert hb₆ using 1
      rw [b₆, hα, hβ]
      ring
    rwa [mul_dvd_mul_iff_left hϖ₀] at h
  obtain ⟨τ, hτ₁, hτ₂⟩ :=
    TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal
      ((key _).2 hαβ)
  rw [key] at hτ₁ hτ₂
  refine ⟨ϖ ^ 2 * τ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [variableChange_a₁] using h₁
  · simpa [variableChange_a₂] using h₂
  · have : (VariableChange.mk 1 0 0 (ϖ ^ 2 * τ) • W).a₃ = ϖ ^ 2 * (α + 2 * τ) := by
      simp [variableChange_a₃, hα]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ hτ₁
  · have : (VariableChange.mk 1 0 0 (ϖ ^ 2 * τ) • W).a₄ = W.a₄ - ϖ ^ 2 * τ * W.a₁ := by
      simp [variableChange_a₄]
    rw [this, pow_succ]
    exact dvd_sub (pow_succ ϖ 2 ▸ h₄) (by rw [mul_assoc]; exact mul_dvd_mul_left _ (h₁.mul_left τ))
  · have : (VariableChange.mk 1 0 0 (ϖ ^ 2 * τ) • W).a₆ = ϖ ^ 4 * (β - τ * α - τ ^ 2) := by
      simp [variableChange_a₆, hα, hβ]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ hτ₂

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The triple-root branch of Tate's algorithm terminates.** Over a discrete valuation ring with
uniformiser `ϖ`, perfect residue field and fraction field `K`, let `W` be an equation with nonzero
discriminant, minimal over `K`, in the normal form of Step 6 (`ϖ ∣ a₁`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆`)
and whose residue cubic has a triple root (`ϖ³ ∣ a₂² − 3 a₄`, `ϖ⁵ ∣ a₄² − 3 a₂ a₆`,
`ϖ⁴ ∣ a₂ a₄ − 9 a₆`). Then a change of variables `x ↦ x + r`, `y ↦ y + t` over `R` produces an
equation in the normal form of Step 8 (`ϖ ∣ a₁`, `ϖ² ∣ a₂, a₃`, `ϖ³ ∣ a₄`, `ϖ⁴ ∣ a₆`) on which
the algorithm stops at Step 8 (`ϖ⁵ ∤ b₆`, symbol `IV*`), or reaches the normal form of Step 9
(`ϖ³ ∣ a₃`, `ϖ⁵ ∣ a₆`) and stops at Step 9 (`ϖ⁴ ∤ a₄`, symbol `III*`) or at Step 10
(`ϖ⁶ ∤ a₆`, symbol `II*`). -/
theorem exists_variableChange_not_pow_dvd_b₆_or_a₄_or_a₆ [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) (hΔ : W.Δ ≠ 0)
    [IsMinimal R (W.baseChange K)] (h₁ : ϖ ∣ W.a₁) (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : ϖ ^ 2 ∣ W.a₄)
    (h₆ : ϖ ^ 3 ∣ W.a₆) (hb : ϖ ^ 3 ∣ W.a₂ ^ 2 - 3 * W.a₄)
    (hc : ϖ ^ 5 ∣ W.a₄ ^ 2 - 3 * W.a₂ * W.a₆) (hd : ϖ ^ 4 ∣ W.a₂ * W.a₄ - 9 * W.a₆) :
    ∃ r t : R, ϖ ∣ (VariableChange.mk 1 r 0 t • W).a₁ ∧
      ϖ ^ 2 ∣ (VariableChange.mk 1 r 0 t • W).a₂ ∧ ϖ ^ 2 ∣ (VariableChange.mk 1 r 0 t • W).a₃ ∧
      ϖ ^ 3 ∣ (VariableChange.mk 1 r 0 t • W).a₄ ∧ ϖ ^ 4 ∣ (VariableChange.mk 1 r 0 t • W).a₆ ∧
      (¬ ϖ ^ 5 ∣ (VariableChange.mk 1 r 0 t • W).b₆ ∨
        ϖ ^ 3 ∣ (VariableChange.mk 1 r 0 t • W).a₃ ∧ ϖ ^ 5 ∣ (VariableChange.mk 1 r 0 t • W).a₆ ∧
          (¬ ϖ ^ 4 ∣ (VariableChange.mk 1 r 0 t • W).a₄ ∨
            ¬ ϖ ^ 6 ∣ (VariableChange.mk 1 r 0 t • W).a₆)) := by
  obtain ⟨r, g₁, g₂, g₃, g₄, g₆⟩ :=
    exists_variableChange_pow_dvd_a₂_a₄_a₆ hϖ W h₁ h₃ h₄ h₆ hb hc hd
  set V := VariableChange.mk 1 r 0 0 • W with hV
  by_cases hb₆ : ϖ ^ 5 ∣ V.b₆
  · obtain ⟨t, k₁, k₂, k₃, k₄, k₆⟩ := exists_variableChange_pow_dvd_a₃_a₆ hϖ V g₁ g₂ g₄ g₆ hb₆
    -- `x ↦ x + r` followed by `y ↦ y + t` is the single change of variables `(1, r, 0, t)`.
    have hC : VariableChange.mk 1 r 0 t • W = VariableChange.mk 1 0 0 t • V := by
      rw [hV, smul_smul]
      congr 1
      ext <;> simp [VariableChange.mul_def]
    refine ⟨r, t, ?_⟩
    rw [hC]
    refine ⟨k₁, k₂, (pow_dvd_pow ϖ (by norm_num)).trans k₃, k₄,
      (pow_dvd_pow ϖ (by norm_num)).trans k₆, Or.inr ⟨k₃, k₆, ?_⟩⟩
    -- If both tests failed, `ϖⁱ ∣ aᵢ` for every `i` (Step 11), against minimality.
    by_contra! h
    refine not_isMinimal_baseChange_of_pow_dvd (K := K) hϖ _ ?_ k₁ k₂ k₃ h.1 h.2 ?_
    · simpa [variableChange_Δ, hV] using hΔ
    · rw [← hC, baseChange, ← map_variableChange]
      exact isMinimal_baseChange_smul R (W.baseChange K) _
  · exact ⟨r, 0, g₁, g₂, g₃, g₄, g₆, Or.inl hb₆⟩

end WeierstrassCurve

end
