/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

/-!
# Tate's algorithm: the double-root branch

Let `R` be a discrete valuation ring with uniformiser `ϖ` and perfect residue field `k`. Step 6 of
Tate's algorithm (`WeierstrassCurve.exists_variableChange_dvd_a₁_a₂_a₃_a₄_a₆`) brings an equation
with additive reduction to the normal form `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆`, and reads off it
the residue cubic

  `P(T) = T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³` over `k`.

This file treats the branch of the algorithm in which `P` has a double root that is not a triple
root (Step 7), where the reduction symbol is `Iₙ*` for some `n ≥ 1`.

Translating `x ↦ x + r` moves the double root to `T = 0`
(`WeierstrassCurve.exists_variableChange_not_sq_dvd_a₂_and_pow_dvd_a₄_a₆`). Then `ϖ` divides `a₂`
exactly once, written `ϖ ∥ a₂` below, because the simple root `-a₂/ϖ` of `P` is nonzero, and the
equation is in the normal form of stage `n = 1` of the following subprocedure. At stage `n` the
equation satisfies `ϖ ∣ a₁`, `ϖ ∥ a₂` and

* for `n = 2k + 1` odd: `ϖ^(k+2) ∣ a₃`, `ϖ^(k+3) ∣ a₄`, `ϖ^(2k+4) ∣ a₆`. If the quadratic
  `Y² + (a₃/ϖ^(k+2)) Y − a₆/ϖ^(2k+4)` has distinct roots, that is if `ϖ^(2k+5) ∤ b₆`, the reduction
  symbol is `Iₙ*`. Otherwise a translation `y ↦ y + t` moves its double root to `0`
  (`WeierstrassCurve.exists_pow_dvd_and_variableChange_pow_dvd_a₃_a₆`) and gives stage `n + 1`;
* for `n = 2k + 2` even: `ϖ^(k+3) ∣ a₃`, `ϖ^(k+3) ∣ a₄`, `ϖ^(2k+5) ∣ a₆`. If the quadratic
  `(a₂/ϖ) X² + (a₄/ϖ^(k+3)) X + a₆/ϖ^(2k+5)` has distinct roots, that is if
  `ϖ^(2k+7) ∤ discrim a₂ a₄ a₆ = a₄² − 4 a₂ a₆`, the reduction symbol is `Iₙ*`. Otherwise a
  translation `x ↦ x + r` moves its double root to `0`
  (`WeierstrassCurve.exists_pow_dvd_and_variableChange_pow_dvd_a₄_a₆`) and gives stage `n + 1`.

Each stage forces `ϖ^(n+6) ∣ Δ`, and translations do not change `Δ`, so the subprocedure stops
at some stage `n` with `n + 6 ≤ v(Δ)` whenever `Δ ≠ 0`
(`WeierstrassCurve.exists_variableChange_not_pow_dvd_b₆_or_discrim`). No minimality hypothesis is
needed for this. Perfectness of `k` is used to find the double roots of the quadratics, which in
characteristic `2` are square roots.

## Main results

* `WeierstrassCurve.exists_variableChange_not_sq_dvd_a₂_and_pow_dvd_a₄_a₆`: **Step 7 of Tate's
  algorithm, the translation.** If the residue cubic of an equation in the normal form of Step 6
  has a double root that is not a triple root, a translation `x ↦ x + r` over `R` produces
  `ϖ ∣ a₁`, `ϖ ∥ a₂`, `ϖ² ∣ a₃`, `ϖ³ ∣ a₄` and `ϖ⁴ ∣ a₆`.
* `WeierstrassCurve.exists_pow_dvd_and_variableChange_pow_dvd_a₃_a₆`: completing the square in
  `y`. If `ϖ^m ∣ a₃`, `ϖ^(2m) ∣ a₆` and `ϖ^(2m+1) ∣ b₆`, a translation `y ↦ y + t` with `ϖ^m ∣ t`
  produces `ϖ^(m+1) ∣ a₃` and `ϖ^(2m+1) ∣ a₆`.
* `WeierstrassCurve.exists_pow_dvd_and_variableChange_pow_dvd_a₄_a₆`: completing the square in
  `x`. If `m ≥ 2`, `ϖ ∥ a₂`, `ϖ^(m+1) ∣ a₄`, `ϖ^(2m+1) ∣ a₆` and `ϖ^(2m+3) ∣ discrim a₂ a₄ a₆`, a
  translation `x ↦ x + r` with `ϖ^m ∣ r` produces `ϖ^(m+2) ∣ a₄` and `ϖ^(2m+2) ∣ a₆`.
* `WeierstrassCurve.exists_variableChange_not_pow_dvd_b₆_or_discrim`: **the `Iₙ*` subprocedure
  of Tate's algorithm terminates.** From the normal form of Step 7 and `Δ ≠ 0`, a translation
  over `R` reaches stage `n = 2k + 1` with `ϖ^(2k+5) ∤ b₆`, or stage `n = 2k + 2` with
  `ϖ^(2k+7) ∤ discrim a₂ a₄ a₆`, and in either case `ϖ^(n+6) ∣ Δ`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9, Step 7
  of Tate's algorithm.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing

variable {R : Type*} [CommRing R] {ϖ : R}

/-- The equation is at an odd stage `n = 2k + 1` of the `Iₙ*` subprocedure of Tate's algorithm. -/
private def IsOddStage (ϖ : R) (k : ℕ) (W : WeierstrassCurve R) : Prop :=
  ϖ ∣ W.a₁ ∧ ϖ ∣ W.a₂ ∧ ¬ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ (k + 2) ∣ W.a₃ ∧ ϖ ^ (k + 3) ∣ W.a₄ ∧
    ϖ ^ (2 * k + 4) ∣ W.a₆

/-- The equation is at an even stage `n = 2k + 2` of the `Iₙ*` subprocedure of Tate's
algorithm. -/
private def IsEvenStage (ϖ : R) (k : ℕ) (W : WeierstrassCurve R) : Prop :=
  ϖ ∣ W.a₁ ∧ ϖ ∣ W.a₂ ∧ ¬ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ (k + 3) ∣ W.a₃ ∧ ϖ ^ (k + 3) ∣ W.a₄ ∧
    ϖ ^ (2 * k + 5) ∣ W.a₆

/-- At stage `n = 2k + 1`, `ϖ^(n+6) ∣ Δ`. -/
private theorem IsOddStage.pow_dvd_Δ {k : ℕ} {W : WeierstrassCurve R}
    (hW : IsOddStage ϖ k W) : ϖ ^ (2 * k + 7) ∣ W.Δ := by
  obtain ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩, -, ⟨x₃, h₃⟩, ⟨x₄, h₄⟩, ⟨x₆, h₆⟩⟩ := hW
  have hb₂ : W.b₂ = ϖ * (ϖ * x₁ ^ 2 + 4 * x₂) := by rw [b₂, h₁, h₂]; ring
  have hb₄ : W.b₄ = ϖ ^ (k + 3) * (x₁ * x₃ + 2 * x₄) := by rw [b₄, h₁, h₃, h₄]; ring
  have hb₆ : W.b₆ = ϖ ^ (2 * k + 4) * (x₃ ^ 2 + 4 * x₆) := by rw [b₆, h₃, h₆]; ring
  have hb₈ : W.b₈ = ϖ ^ (2 * k + 5) *
      (ϖ * x₁ ^ 2 * x₆ + 4 * x₂ * x₆ - ϖ * x₁ * x₃ * x₄ + x₂ * x₃ ^ 2 - ϖ * x₄ ^ 2) := by
    rw [b₈, h₁, h₂, h₃, h₄, h₆]; ring
  refine ⟨-(ϖ * x₁ ^ 2 + 4 * x₂) ^ 2 *
      (ϖ * x₁ ^ 2 * x₆ + 4 * x₂ * x₆ - ϖ * x₁ * x₃ * x₄ + x₂ * x₃ ^ 2 - ϖ * x₄ ^ 2) -
    8 * ϖ ^ (k + 2) * (x₁ * x₃ + 2 * x₄) ^ 3 - 27 * ϖ ^ (2 * k + 1) * (x₃ ^ 2 + 4 * x₆) ^ 2 +
    9 * ϖ ^ (k + 1) * (ϖ * x₁ ^ 2 + 4 * x₂) * (x₁ * x₃ + 2 * x₄) * (x₃ ^ 2 + 4 * x₆), ?_⟩
  rw [Δ, hb₂, hb₄, hb₆, hb₈]
  ring

/-- At stage `n = 2k + 2`, `ϖ^(n+6) ∣ Δ`. -/
private theorem IsEvenStage.pow_dvd_Δ {k : ℕ} {W : WeierstrassCurve R}
    (hW : IsEvenStage ϖ k W) : ϖ ^ (2 * k + 8) ∣ W.Δ := by
  obtain ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩, -, ⟨x₃, h₃⟩, ⟨x₄, h₄⟩, ⟨x₆, h₆⟩⟩ := hW
  have hb₂ : W.b₂ = ϖ * (ϖ * x₁ ^ 2 + 4 * x₂) := by rw [b₂, h₁, h₂]; ring
  have hb₄ : W.b₄ = ϖ ^ (k + 3) * (ϖ * x₁ * x₃ + 2 * x₄) := by rw [b₄, h₁, h₃, h₄]; ring
  have hb₆ : W.b₆ = ϖ ^ (2 * k + 5) * (ϖ * x₃ ^ 2 + 4 * x₆) := by rw [b₆, h₃, h₆]; ring
  have hb₈ : W.b₈ = ϖ ^ (2 * k + 6) *
      (ϖ * x₁ ^ 2 * x₆ + 4 * x₂ * x₆ - ϖ * x₁ * x₃ * x₄ + ϖ * x₂ * x₃ ^ 2 - x₄ ^ 2) := by
    rw [b₈, h₁, h₂, h₃, h₄, h₆]; ring
  refine ⟨-(ϖ * x₁ ^ 2 + 4 * x₂) ^ 2 *
      (ϖ * x₁ ^ 2 * x₆ + 4 * x₂ * x₆ - ϖ * x₁ * x₃ * x₄ + ϖ * x₂ * x₃ ^ 2 - x₄ ^ 2) -
    8 * ϖ ^ (k + 1) * (ϖ * x₁ * x₃ + 2 * x₄) ^ 3 -
    27 * ϖ ^ (2 * k + 2) * (ϖ * x₃ ^ 2 + 4 * x₆) ^ 2 +
    9 * ϖ ^ (k + 1) * (ϖ * x₁ ^ 2 + 4 * x₂) * (ϖ * x₁ * x₃ + 2 * x₄) * (ϖ * x₃ ^ 2 + 4 * x₆), ?_⟩
  rw [Δ, hb₂, hb₄, hb₆, hb₈]
  ring

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **Tate's algorithm, Step 7: moving the double root to `0`.** Over a discrete valuation ring
with uniformiser `ϖ`, let `W` be an equation in the normal form of Step 6, with `ϖ ∣ a₁`,
`ϖ² ∣ a₃`, `a₂ = ϖ A₂`, `a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆`, and let `ρ` be a double root of the residue
cubic `P(T) = T³ + A₂ T² + A₄ T + A₆` which is not a triple root: `P(ρ) = 0`, `P'(ρ) = 0` and
`3 ρ + A₂ ≠ 0`, the last saying that the third root `-A₂ - 2 ρ` of `P` differs from `ρ`. Then a
translation `x ↦ x + r` with `r ∈ R` produces an equation with `ϖ ∣ a₁`, `ϖ ∣ a₂` but `ϖ² ∤ a₂`,
`ϖ² ∣ a₃`, `ϖ³ ∣ a₄` and `ϖ⁴ ∣ a₆`. -/
theorem exists_variableChange_not_sq_dvd_a₂_and_pow_dvd_a₄_a₆ (hϖ : Irreducible ϖ)
    (W : WeierstrassCurve R) (h₁ : ϖ ∣ W.a₁) (h₃ : ϖ ^ 2 ∣ W.a₃) {A₂ A₄ A₆ : R}
    (hA₂ : W.a₂ = ϖ * A₂) (hA₄ : W.a₄ = ϖ ^ 2 * A₄) (hA₆ : W.a₆ = ϖ ^ 3 * A₆)
    (ρ : ResidueField R)
    (hρ : ρ ^ 3 + residue R A₂ * ρ ^ 2 + residue R A₄ * ρ + residue R A₆ = 0)
    (hρ' : 3 * ρ ^ 2 + 2 * residue R A₂ * ρ + residue R A₄ = 0)
    (hρ'' : 3 * ρ + residue R A₂ ≠ 0) :
    ∃ r : R, ϖ ∣ (VariableChange.mk 1 r 0 0 • W).a₁ ∧ ϖ ∣ (VariableChange.mk 1 r 0 0 • W).a₂ ∧
      ¬ ϖ ^ 2 ∣ (VariableChange.mk 1 r 0 0 • W).a₂ ∧
      ϖ ^ 2 ∣ (VariableChange.mk 1 r 0 0 • W).a₃ ∧ ϖ ^ 3 ∣ (VariableChange.mk 1 r 0 0 • W).a₄ ∧
      ϖ ^ 4 ∣ (VariableChange.mk 1 r 0 0 • W).a₆ := by
  have hϖ₀ : ϖ ≠ 0 := hϖ.ne_zero
  have key (x : R) : residue R x = 0 ↔ ϖ ∣ x := by
    rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  -- Lift the double root to `ρ₀ ∈ R`; then `x ↦ x + ϖ ρ₀` moves it to `0`.
  obtain ⟨ρ₀, rfl⟩ := residue_surjective ρ
  have e₂ : ¬ ϖ ∣ A₂ + 3 * ρ₀ := by
    rw [← key]
    simp only [map_add, map_mul, map_ofNat]
    exact fun h ↦ hρ'' (by linear_combination h)
  have e₄ : ϖ ∣ A₄ + 2 * A₂ * ρ₀ + 3 * ρ₀ ^ 2 := (key _).1 (by
    simp only [map_add, map_mul, map_pow, map_ofNat]; linear_combination hρ')
  have e₆ : ϖ ∣ A₆ + ρ₀ * A₄ + ρ₀ ^ 2 * A₂ + ρ₀ ^ 3 := (key _).1 (by
    simp only [map_add, map_mul, map_pow]; linear_combination hρ)
  have hV₂ : (VariableChange.mk 1 (ϖ * ρ₀) 0 0 • W).a₂ = ϖ * (A₂ + 3 * ρ₀) := by
    simp [variableChange_a₂, hA₂]; ring
  refine ⟨ϖ * ρ₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [variableChange_a₁] using h₁
  · rw [hV₂]
    exact dvd_mul_right _ _
  · rw [hV₂, sq, mul_dvd_mul_iff_left hϖ₀]
    exact e₂
  · have : (VariableChange.mk 1 (ϖ * ρ₀) 0 0 • W).a₃ = W.a₃ + ϖ * ρ₀ * W.a₁ := by
      simp [variableChange_a₃]
    rw [this, sq]
    exact dvd_add (sq ϖ ▸ h₃) (by rw [mul_assoc]; exact mul_dvd_mul_left ϖ (h₁.mul_left ρ₀))
  · have : (VariableChange.mk 1 (ϖ * ρ₀) 0 0 • W).a₄ =
        ϖ ^ 2 * (A₄ + 2 * A₂ * ρ₀ + 3 * ρ₀ ^ 2) := by
      simp [variableChange_a₄, hA₂, hA₄]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ e₄
  · have : (VariableChange.mk 1 (ϖ * ρ₀) 0 0 • W).a₆ =
        ϖ ^ 3 * (A₆ + ρ₀ * A₄ + ρ₀ ^ 2 * A₂ + ρ₀ ^ 3) := by
      simp [variableChange_a₆, hA₂, hA₄, hA₆]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ e₆

/-- **Completing the square in `y`.** Over a discrete valuation ring with uniformiser `ϖ` and
perfect residue field, let `W` be an equation with `ϖ^m ∣ a₃` and `ϖ^(2m) ∣ a₆` whose quadratic
`Y² + (a₃/ϖ^m) Y − a₆/ϖ^(2m)` has a double root modulo `ϖ`, that is `ϖ^(2m+1) ∣ b₆`. Then a
translation `y ↦ y + t` with `ϖ^m ∣ t` moves the double root to `0`: the new equation has
`ϖ^(m+1) ∣ a₃` and `ϖ^(2m+1) ∣ a₆`. The translation fixes `a₁` and `a₂` and changes `a₄` to
`a₄ − t a₁`. -/
theorem exists_pow_dvd_and_variableChange_pow_dvd_a₃_a₆ [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) {m : ℕ} (h₃ : ϖ ^ m ∣ W.a₃)
    (h₆ : ϖ ^ (2 * m) ∣ W.a₆) (hb₆ : ϖ ^ (2 * m + 1) ∣ W.b₆) :
    ∃ t : R, ϖ ^ m ∣ t ∧ ϖ ^ (m + 1) ∣ (VariableChange.mk 1 0 0 t • W).a₃ ∧
      ϖ ^ (2 * m + 1) ∣ (VariableChange.mk 1 0 0 t • W).a₆ := by
  have key (x : R) : x ∈ maximalIdeal R ↔ ϖ ∣ x := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  obtain ⟨α, hα⟩ := h₃
  obtain ⟨β, hβ⟩ := h₆
  -- `b₆ = a₃² + 4 a₆ = ϖ^(2m) (α² + 4 β)`, so `ϖ ∣ α² + 4 β`.
  have hαβ : ϖ ∣ α ^ 2 + 4 * β := by
    have h : ϖ ^ (2 * m) * ϖ ∣ ϖ ^ (2 * m) * (α ^ 2 + 4 * β) := by
      rw [← pow_succ]
      convert hb₆ using 1
      rw [b₆, hα, hβ]
      ring
    rwa [mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)] at h
  obtain ⟨τ, hτ₁, hτ₂⟩ :=
    TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal
      ((key _).2 hαβ)
  rw [key] at hτ₁ hτ₂
  refine ⟨ϖ ^ m * τ, dvd_mul_right _ _, ?_, ?_⟩
  · have : (VariableChange.mk 1 0 0 (ϖ ^ m * τ) • W).a₃ = ϖ ^ m * (α + 2 * τ) := by
      simp [variableChange_a₃, hα]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ hτ₁
  · have : (VariableChange.mk 1 0 0 (ϖ ^ m * τ) • W).a₆ = ϖ ^ (2 * m) * (β - τ * α - τ ^ 2) := by
      simp [variableChange_a₆, hα, hβ]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul_left _ hτ₂

/-- **Completing the square in `x`.** Over a discrete valuation ring with uniformiser `ϖ` and
perfect residue field, let `m ≥ 2` and let `W` be an equation with `ϖ ∣ a₂` but `ϖ² ∤ a₂`,
`ϖ^(m+1) ∣ a₄` and `ϖ^(2m+1) ∣ a₆`, whose quadratic `(a₂/ϖ) X² + (a₄/ϖ^(m+1)) X + a₆/ϖ^(2m+1)`
has a double root modulo `ϖ`, that is `ϖ^(2m+3) ∣ discrim a₂ a₄ a₆ = a₄² − 4 a₂ a₆`. Then a
translation `x ↦ x + r` with `ϖ^m ∣ r` moves the double root to `0`: the new equation has
`ϖ^(m+2) ∣ a₄` and `ϖ^(2m+2) ∣ a₆`. The translation fixes `a₁`, changes `a₂` to `a₂ + 3 r` and
`a₃` to `a₃ + r a₁`. -/
theorem exists_pow_dvd_and_variableChange_pow_dvd_a₄_a₆ [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) {m : ℕ} (hm : 2 ≤ m) (h₂ : ϖ ∣ W.a₂)
    (h₂' : ¬ ϖ ^ 2 ∣ W.a₂) (h₄ : ϖ ^ (m + 1) ∣ W.a₄) (h₆ : ϖ ^ (2 * m + 1) ∣ W.a₆)
    (hd : ϖ ^ (2 * m + 3) ∣ discrim W.a₂ W.a₄ W.a₆) :
    ∃ r : R, ϖ ^ m ∣ r ∧ ϖ ^ (m + 2) ∣ (VariableChange.mk 1 r 0 0 • W).a₄ ∧
      ϖ ^ (2 * m + 2) ∣ (VariableChange.mk 1 r 0 0 • W).a₆ := by
  have key (x : R) : residue R x = 0 ↔ ϖ ∣ x := by
    rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  obtain ⟨A, hA⟩ := h₂
  obtain ⟨B, hB⟩ := h₄
  obtain ⟨C, hC⟩ := h₆
  -- The leading coefficient `A = a₂ / ϖ` is a unit, and
  -- `discrim a₂ a₄ a₆ = ϖ^(2m+2) discrim A B C`.
  have hA' : residue R A ≠ 0 := by
    rw [ne_eq, key]
    rintro ⟨A', rfl⟩
    exact h₂' ⟨A', by rw [hA]; ring⟩
  have hd' : discrim (residue R A) (residue R B) (residue R C) = 0 := by
    have h : ϖ ^ (2 * (n + 2) + 2) * ϖ ∣ ϖ ^ (2 * (n + 2) + 2) * discrim A B C := by
      rw [← pow_succ]
      convert hd using 1
      rw [discrim, discrim, hA, hB, hC]
      ring
    rw [mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero), ← key] at h
    simpa [discrim, map_ofNat] using h
  -- Lift the double root to `ρ ∈ R`; then `x ↦ x + ϖ^m ρ` moves it to `0`.
  obtain ⟨x, hx, hx'⟩ :=
    Polynomial.exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero hA' hd'
  obtain ⟨ρ, rfl⟩ := residue_surjective x
  obtain ⟨u, hu⟩ : ϖ ∣ B + 2 * A * ρ := (key _).1 (by
    simp only [map_add, map_mul, map_ofNat]; linear_combination hx')
  obtain ⟨v, hv⟩ : ϖ ∣ C + ρ * B + ρ ^ 2 * A := (key _).1 (by
    simp only [map_add, map_mul, map_pow]; linear_combination hx)
  refine ⟨ϖ ^ (n + 2) * ρ, dvd_mul_right _ _, ⟨u + 3 * ϖ ^ n * ρ ^ 2, ?_⟩,
    ⟨v + ϖ ^ n * ρ ^ 3, ?_⟩⟩
  · simp only [variableChange_a₄, hA, hB]
    simp only [inv_one, Units.val_one, one_pow, one_mul, zero_mul, sub_zero, add_zero, mul_zero]
    linear_combination ϖ ^ (n + 3) * hu
  · simp only [variableChange_a₆, hA, hB, hC]
    simp only [inv_one, Units.val_one, one_pow, one_mul, zero_mul, sub_zero, mul_zero]
    linear_combination ϖ ^ (2 * n + 5) * hv

/-- If the quadratic of an odd stage `2k + 1` has a double root, a translation `y ↦ y + t` reaches
the even stage `2k + 2`. -/
private theorem IsOddStage.exists_isEvenStage [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) {k : ℕ} {W : WeierstrassCurve R} (hW : IsOddStage ϖ k W)
    (hb₆ : ϖ ^ (2 * k + 5) ∣ W.b₆) : ∃ t : R, IsEvenStage ϖ k (VariableChange.mk 1 0 0 t • W) := by
  obtain ⟨h₁, h₂, h₂', h₃, h₄, h₆⟩ := hW
  obtain ⟨t, ht, h₃', h₆'⟩ := exists_pow_dvd_and_variableChange_pow_dvd_a₃_a₆ hϖ W (m := k + 2) h₃
    (by rwa [show 2 * (k + 2) = 2 * k + 4 by ring])
    (by rwa [show 2 * (k + 2) + 1 = 2 * k + 5 by ring])
  refine ⟨t, by simpa [variableChange_a₁] using h₁, by simpa [variableChange_a₂] using h₂,
    by simpa [variableChange_a₂] using h₂', h₃', ?_,
    by rwa [show 2 * k + 5 = 2 * (k + 2) + 1 by ring]⟩
  have : (VariableChange.mk 1 0 0 t • W).a₄ = W.a₄ - t * W.a₁ := by simp [variableChange_a₄]
  rw [this]
  exact dvd_sub h₄ (pow_succ ϖ (k + 2) ▸ mul_dvd_mul ht h₁)

/-- If the quadratic of an even stage `2k + 2` has a double root, a translation `x ↦ x + r`
reaches the odd stage `2k + 3`. -/
private theorem IsEvenStage.exists_isOddStage [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) {k : ℕ} {W : WeierstrassCurve R} (hW : IsEvenStage ϖ k W)
    (hd : ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆) :
    ∃ r : R, IsOddStage ϖ (k + 1) (VariableChange.mk 1 r 0 0 • W) := by
  obtain ⟨h₁, h₂, h₂', h₃, h₄, h₆⟩ := hW
  obtain ⟨r, hr, h₄', h₆'⟩ := exists_pow_dvd_and_variableChange_pow_dvd_a₄_a₆ hϖ W (m := k + 2)
    (by omega) h₂ h₂' h₄ (by rwa [show 2 * (k + 2) + 1 = 2 * k + 5 by ring])
    (by rwa [show 2 * (k + 2) + 3 = 2 * k + 7 by ring])
  have h3r : ϖ ^ 2 ∣ 3 * r := ((pow_dvd_pow ϖ (by omega)).trans hr).mul_left 3
  have hV₂ : (VariableChange.mk 1 r 0 0 • W).a₂ = W.a₂ + 3 * r := by simp [variableChange_a₂]
  have hV₃ : (VariableChange.mk 1 r 0 0 • W).a₃ = W.a₃ + r * W.a₁ := by simp [variableChange_a₃]
  refine ⟨r, by simpa [variableChange_a₁] using h₁, ?_, ?_, ?_, h₄',
    by rwa [show 2 * (k + 1) + 4 = 2 * (k + 2) + 2 by ring]⟩
  · rw [hV₂]
    exact dvd_add h₂ ((dvd_pow_self ϖ two_ne_zero).trans h3r)
  · rw [hV₂]
    exact fun h ↦ h₂' ((dvd_add_left h3r).1 h)
  · rw [hV₃]
    exact dvd_add h₃ (pow_succ ϖ (k + 2) ▸ mul_dvd_mul hr h₁)

/-- **The `Iₙ*` subprocedure of Tate's algorithm terminates.** Over a discrete valuation ring with
uniformiser `ϖ` and perfect residue field, let `W` be an equation with nonzero discriminant in the
normal form of Step 7: `ϖ ∣ a₁`, `ϖ ∣ a₂` but `ϖ² ∤ a₂`, `ϖ² ∣ a₃`, `ϖ³ ∣ a₄` and `ϖ⁴ ∣ a₆`. Then
a translation `x ↦ x + r`, `y ↦ y + t` over `R` produces an equation with `ϖ ∣ a₁`, `ϖ ∣ a₂` and
`ϖ² ∤ a₂` on which the subprocedure stops, at an odd stage `n = 2k + 1`:
`ϖ^(k+2) ∣ a₃`, `ϖ^(k+3) ∣ a₄`, `ϖ^(2k+4) ∣ a₆` and `ϖ^(2k+5) ∤ b₆`; or at an even stage
`n = 2k + 2`: `ϖ^(k+3) ∣ a₃`, `ϖ^(k+3) ∣ a₄`, `ϖ^(2k+5) ∣ a₆` and
`ϖ^(2k+7) ∤ discrim a₂ a₄ a₆`. In both cases the reduction symbol is `Iₙ*`, and `ϖ^(n+6) ∣ Δ`. -/
theorem exists_variableChange_not_pow_dvd_b₆_or_discrim [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) (hΔ : W.Δ ≠ 0) (h₁ : ϖ ∣ W.a₁)
    (h₂ : ϖ ∣ W.a₂) (h₂' : ¬ ϖ ^ 2 ∣ W.a₂) (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : ϖ ^ 3 ∣ W.a₄)
    (h₆ : ϖ ^ 4 ∣ W.a₆) :
    ∃ r t : R, ∃ k : ℕ, ϖ ∣ (VariableChange.mk 1 r 0 t • W).a₁ ∧
      ϖ ∣ (VariableChange.mk 1 r 0 t • W).a₂ ∧ ¬ ϖ ^ 2 ∣ (VariableChange.mk 1 r 0 t • W).a₂ ∧
      (ϖ ^ (k + 2) ∣ (VariableChange.mk 1 r 0 t • W).a₃ ∧
          ϖ ^ (k + 3) ∣ (VariableChange.mk 1 r 0 t • W).a₄ ∧
          ϖ ^ (2 * k + 4) ∣ (VariableChange.mk 1 r 0 t • W).a₆ ∧
          ¬ ϖ ^ (2 * k + 5) ∣ (VariableChange.mk 1 r 0 t • W).b₆ ∧ ϖ ^ (2 * k + 7) ∣ W.Δ ∨
        ϖ ^ (k + 3) ∣ (VariableChange.mk 1 r 0 t • W).a₃ ∧
          ϖ ^ (k + 3) ∣ (VariableChange.mk 1 r 0 t • W).a₄ ∧
          ϖ ^ (2 * k + 5) ∣ (VariableChange.mk 1 r 0 t • W).a₆ ∧
          ¬ ϖ ^ (2 * k + 7) ∣ discrim (VariableChange.mk 1 r 0 t • W).a₂
            (VariableChange.mk 1 r 0 t • W).a₄ (VariableChange.mk 1 r 0 t • W).a₆ ∧
          ϖ ^ (2 * k + 8) ∣ W.Δ) := by
  have hΔV (r t : R) : (VariableChange.mk 1 r 0 t • W).Δ = W.Δ := by simp [variableChange_Δ]
  -- Two translations compose to a translation.
  have hC (r t r' t' : R) : VariableChange.mk 1 r' 0 t' • VariableChange.mk 1 r 0 t • W =
      VariableChange.mk 1 (r + r') 0 (t + t') • W := by
    rw [smul_smul]
    congr 1
    ext <;> simp [VariableChange.mul_def, add_comm]
  -- The `ϖ`-adic valuation of `Δ ≠ 0` is finite: `ϖ^(N+1) ∤ Δ` for some `N`. Since every stage
  -- `2k + 1` forces `ϖ^(2k+7) ∣ Δ`, induct on a bound `M` with `ϖ^(2k+M) ∤ Δ`.
  obtain ⟨N, hN⟩ := FiniteMultiplicity.of_not_isUnit hϖ.not_isUnit hΔ
  obtain ⟨k, r, t, hM, hW⟩ : ∃ (k : ℕ) (r t : R), ¬ ϖ ^ (2 * k + (N + 1)) ∣ W.Δ ∧
      IsOddStage ϖ k (VariableChange.mk 1 r 0 t • W) := by
    refine ⟨0, 0, 0, by simpa using hN, ?_⟩
    rw [show (VariableChange.mk 1 0 0 0 : VariableChange R) = 1 from rfl, one_smul]
    exact ⟨h₁, h₂, h₂', h₃, h₄, h₆⟩
  clear hN
  generalize N + 1 = M at hM
  induction M generalizing k r t with
  | zero =>
    exact absurd ((pow_dvd_pow ϖ (by omega)).trans (hΔV r t ▸ hW.pow_dvd_Δ)) hM
  | succ M ih =>
    by_cases hb₆ : ϖ ^ (2 * k + 5) ∣ (VariableChange.mk 1 r 0 t • W).b₆
    · obtain ⟨t', hW'⟩ := hW.exists_isEvenStage hϖ hb₆
      simp only [hC, add_zero] at hW'
      by_cases hd : ϖ ^ (2 * k + 7) ∣ discrim (VariableChange.mk 1 r 0 (t + t') • W).a₂
          (VariableChange.mk 1 r 0 (t + t') • W).a₄ (VariableChange.mk 1 r 0 (t + t') • W).a₆
      · obtain ⟨r', hW''⟩ := hW'.exists_isOddStage hϖ hd
        simp only [hC, add_zero] at hW''
        exact ih (k + 1) (r + r') (t + t') hW'' (fun h ↦ hM ((pow_dvd_pow ϖ (by omega)).trans h))
      · obtain ⟨g₁, g₂, g₂', g₃, g₄, g₆⟩ := hW'
        exact ⟨r, t + t', k, g₁, g₂, g₂', Or.inr ⟨g₃, g₄, g₆, hd,
          hΔV r (t + t') ▸ IsEvenStage.pow_dvd_Δ ⟨g₁, g₂, g₂', g₃, g₄, g₆⟩⟩⟩
    · obtain ⟨g₁, g₂, g₂', g₃, g₄, g₆⟩ := hW
      exact ⟨r, t, k, g₁, g₂, g₂', Or.inl ⟨g₃, g₄, g₆, hb₆,
        hΔV r t ▸ IsOddStage.pow_dvd_Δ ⟨g₁, g₂, g₂', g₃, g₄, g₆⟩⟩⟩

end WeierstrassCurve

end
