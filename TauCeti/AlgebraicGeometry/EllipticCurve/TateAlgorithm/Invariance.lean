/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Discriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Tate's algorithm: the output does not depend on the choices

Tate's algorithm reads the reduction symbol of a Weierstrass equation over a discrete valuation
ring `R` with uniformiser `ϖ` by alternating changes of variables over `R` with divisibility tests
(`WeierstrassCurve.IsTateTerminal`, `WeierstrassCurve.exists_isTateTerminal`). The changes of
variables are not unique: at each step any one moving the singular point, or the multiple root of
the residue polynomial, to the origin will do. This file proves that the symbol does not depend on
these choices, nor on the uniformiser, except possibly for the index `n` of a symbol `Iₙ*` with
`n ≥ 1`. If `W` and `C • W` are equations over `R`, related by a change of variables `C` over `R`,
on which the algorithm stops with symbols `s` and `s'`, then `s = s'`, or both are of the form
`Iₙ*` with `n ≥ 1`. Since two minimal equations of one elliptic curve over the fraction field are
related by a change of variables over `R`, the symbol at which the algorithm stops on a minimal
equation is an invariant of the curve, up to the same proviso. No minimality is needed for the
first statement.

## Main results

* `WeierstrassCurve.dvd_r_and_dvd_t_of_dvd_a₃_a₄_a₆`: a change of variables between two
  equations whose reductions modulo a prime are singular at the origin fixes the origin modulo
  that prime.
* `WeierstrassCurve.IsTateTerminal.eq_of_smul`: if the algorithm stops on `W` with a symbol `s`
  other than `Iₙ*` with `n ≥ 1`, then it stops on every `C • W`, for `C` over `R`, with `s` only.
* `WeierstrassCurve.IsTateTerminal.exists_eq_IStar_of_smul`: if it stops on `W` with `Iₙ*`,
  `n ≥ 1`, then it stops on every `C • W` with some `Iₘ*`, `m ≥ 1`.
* `WeierstrassCurve.isTateTerminal_iff_of_associated`: the stopping conditions do not depend on
  the uniformiser.
* `WeierstrassCurve.IsTateTerminal.eq_of_isMinimal_smul` and
  `WeierstrassCurve.IsTateTerminal.exists_eq_IStar_of_isMinimal_smul`: the same statements for
  two minimal equations of one elliptic curve over the fraction field, with any uniformisers.

## Implementation notes

The algorithm applies its tests in a fixed order, and each test is invariant under the changes of
variables between two equations which have passed the earlier tests and are in the normal form the
test is read on:

* `ϖ ∣ Δ` is invariant because `Δ` changes by a unit;
* if both equations reduce to curves singular at the origin, `C` fixes the origin modulo `ϖ`
  (`WeierstrassCurve.dvd_r_and_dvd_t_of_dvd_a₃_a₄_a₆`), since the reduction of `W` has only one
  singular point (`WeierstrassCurve.Affine.eq_of_isSingular_of_isSingular`). Then `b₂`, `a₆`
  modulo `ϖ²`, `b₈` modulo `ϖ³` and `b₆` modulo `ϖ³` change by units, which gives invariance of
  the tests of Steps 2 to 5;
* if both equations are in the normal form of Step 6, then `ϖ ∣ s` and `ϖ² ∣ t`, and the residue
  cubic of `C • W` is `v⁶ P (v⁻² T + ρ)`, where `P` is that of `W`, `v` is the reduction of `u⁻¹`
  and `ρ` that of `r / ϖ`. So the discriminant of the residue cubic `T³ + b T² + c T + d`, and
  `b² - 3c`, change by units. The first is the test of `I₀*`; the second vanishes on the residue
  cubic `T³` of Steps 8 to 10 and not on the residue cubics `T³ + b T²`, `b ≠ 0`, of the `Iₙ*`
  branch;
* if both equations are in the normal form of Step 8, so that both residue cubics are `T³`, then
  `ρ = 0`. This makes `b₆` modulo `ϖ⁵` invariant, which is the test of `IV*`, and on the normal
  form of Step 9 also `ϖ³ ∣ t`, which makes `a₄` modulo `ϖ⁴` invariant, the test of `III*`.

If the algorithm stopped on `W` at an earlier test than on `C • W`, then `W` would fail a test
that `C • W` passes, which invariance rules out. So it stops on both at the same test, and the
symbol is determined by the test, except for the index of `Iₙ`, which is the valuation of `Δ`, and
the index of `Iₙ*`, which is read off the subprocedure of Step 7 and is not treated here.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing IsDiscreteValuationRing TauCeti

section CommRing

variable {R : Type*} [CommRing R] {ϖ : R}

/-- **A change of variables fixes the singular point of the reduction.** If the reductions modulo a
prime `ϖ` of `W` and of `C • W` are both singular at the origin, that is `ϖ` divides `a₃`, `a₄` and
`a₆` of both equations, then `C` maps the origin to the origin modulo `ϖ`: `ϖ ∣ r` and `ϖ ∣ t`. -/
theorem dvd_r_and_dvd_t_of_dvd_a₃_a₄_a₆ (hϖ : Prime ϖ) {W : WeierstrassCurve R}
    {C : VariableChange R} (h₃ : ϖ ∣ W.a₃) (h₄ : ϖ ∣ W.a₄) (h₆ : ϖ ∣ W.a₆)
    (h₃' : ϖ ∣ (C • W).a₃) (h₄' : ϖ ∣ (C • W).a₄) (h₆' : ϖ ∣ (C • W).a₆) :
    ϖ ∣ C.r ∧ ϖ ∣ C.t := by
  have := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ
  set π := Ideal.Quotient.mk (Ideal.span {ϖ})
  have key (x : R) : π x = 0 ↔ ϖ ∣ x := Ideal.Quotient.eq_zero_iff_dvd ϖ x
  rw [variableChange_a₃, (C.u⁻¹.isUnit.pow 3).dvd_mul_left, ← key] at h₃'
  rw [variableChange_a₄, (C.u⁻¹.isUnit.pow 4).dvd_mul_left, ← key] at h₄'
  rw [variableChange_a₆, (C.u⁻¹.isUnit.pow 6).dvd_mul_left, ← key] at h₆'
  rw [← key] at h₃ h₄ h₆
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at h₃' h₄' h₆'
  -- Modulo `ϖ`, the translation of `W` by `(r, t)` differs from `C • W` by `(u, 0, s, 0)`, so it
  -- is singular at the origin too: `W` is singular modulo `ϖ` at `(r, t)` as well as at `(0, 0)`.
  have hrt : (W.map π).toAffine.IsSingular (π C.r) (π C.t) := by
    rw [Affine.isSingular_iff_variableChange, Affine.isSingular_zero]
    simp only [variableChange_a₃, variableChange_a₄, variableChange_a₆, map_a₁, map_a₂, map_a₃,
      map_a₄, map_a₆, inv_one, Units.val_one, one_pow, one_mul, zero_mul, sub_zero, mul_zero,
      add_zero]
    exact ⟨by linear_combination h₆', by linear_combination h₄' + π C.s * h₃',
      by linear_combination h₃'⟩
  have h₀ : (W.map π).toAffine.IsSingular 0 0 := by simp [h₃, h₄, h₆]
  obtain ⟨hr, ht⟩ := Affine.eq_of_isSingular_of_isSingular hrt h₀
  exact ⟨(key _).1 hr, (key _).1 ht⟩

/-- The tests of Tate's algorithm, in the order in which it applies them: the algorithm goes on
past the test `k` exactly when `tateTest ϖ W k` holds. -/
private def tateTest (ϖ : R) (W : WeierstrassCurve R) : ℕ → Prop
  | 0 => ϖ ∣ W.Δ
  | 1 => ϖ ∣ W.b₂
  | 2 => ϖ ^ 2 ∣ W.a₆
  | 3 => ϖ ^ 3 ∣ W.b₈
  | 4 => ϖ ^ 3 ∣ W.b₆
  | 5 => ϖ ^ 7 ∣ (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr
  | 6 => ϖ ^ 3 ∣ W.a₂ ^ 2 - 3 * W.a₄
  | 7 => ϖ ^ 5 ∣ W.b₆
  | 8 => ϖ ^ 4 ∣ W.a₄
  | _ => False

/-- The test at which Tate's algorithm stops with a given symbol. -/
private def chainIndex : ReductionSymbol → ℕ
  | .I 0 => 0
  | .I (_ + 1) => 1
  | .II => 2
  | .III => 3
  | .IV => 4
  | .IStar 0 => 5
  | .IStar (_ + 1) => 6
  | .IVStar => 7
  | .IIIStar => 8
  | .IIStar => 9

/-- An equation on which Tate's algorithm reaches the test `i`: it passes the earlier tests and is
in the normal form on which the test `i` is read. -/
private def TateContext (ϖ : R) (i : ℕ) (W : WeierstrassCurve R) : Prop :=
  (∀ k < i, tateTest ϖ W k) ∧ (1 ≤ i → ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ∣ W.a₆) ∧
    (5 ≤ i → ϖ ∣ W.a₁ ∧ ϖ ∣ W.a₂ ∧ ϖ ^ 2 ∣ W.a₃ ∧ ϖ ^ 2 ∣ W.a₄ ∧ ϖ ^ 3 ∣ W.a₆) ∧
    (7 ≤ i → ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ 3 ∣ W.a₄ ∧ ϖ ^ 4 ∣ W.a₆) ∧
    (8 ≤ i → ϖ ^ 3 ∣ W.a₃ ∧ ϖ ^ 5 ∣ W.a₆)

private theorem TateContext.mono {i j : ℕ} {W : WeierstrassCurve R} (h : TateContext ϖ j W)
    (hij : i ≤ j) : TateContext ϖ i W :=
  ⟨fun k hk ↦ h.1 k (hk.trans_le hij), fun hi ↦ h.2.1 (hi.trans hij),
    fun hi ↦ h.2.2.1 (hi.trans hij), fun hi ↦ h.2.2.2.1 (hi.trans hij),
    fun hi ↦ h.2.2.2.2 (hi.trans hij)⟩

/-- The normal form of Step 6 passes the tests of Steps 1 to 5. -/
private theorem tateTest_of_stepSix {W : WeierstrassCurve R} (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ∣ W.a₂)
    (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : ϖ ^ 2 ∣ W.a₄) (h₆ : ϖ ^ 3 ∣ W.a₆) : ∀ k < 5, tateTest ϖ W k := by
  have hΔ := W.pow_six_dvd_Δ_of_pow_dvd ϖ h₁ h₂ h₃ h₄ h₆
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  obtain ⟨x₃, hx₃⟩ := h₃
  obtain ⟨x₄, hx₄⟩ := h₄
  obtain ⟨x₆, hx₆⟩ := h₆
  intro k hk
  interval_cases k
  · exact (dvd_pow_self ϖ (by norm_num)).trans hΔ
  · exact ⟨ϖ * x₁ ^ 2 + 4 * x₂, by rw [b₂, hx₁, hx₂]; ring⟩
  · exact ⟨ϖ * x₆, by rw [hx₆]; ring⟩
  · exact ⟨ϖ ^ 2 * x₁ ^ 2 * x₆ + 4 * ϖ * x₂ * x₆ - ϖ ^ 2 * x₁ * x₃ * x₄ + ϖ ^ 2 * x₂ * x₃ ^ 2 -
      ϖ * x₄ ^ 2, by rw [b₈, hx₁, hx₂, hx₃, hx₄, hx₆]; ring⟩
  · exact ⟨ϖ * x₃ ^ 2 + 4 * x₆, by rw [b₆, hx₃, hx₆]; ring⟩

/-- The normal form of Step 9 passes the test of `IV*`. -/
private theorem tateTest_seven_of_stepNine {W : WeierstrassCurve R} (h₃ : ϖ ^ 3 ∣ W.a₃)
    (h₆ : ϖ ^ 5 ∣ W.a₆) : tateTest ϖ W 7 := by
  obtain ⟨z₃, hz₃⟩ := h₃
  obtain ⟨z₆, hz₆⟩ := h₆
  exact ⟨ϖ * z₃ ^ 2 + 4 * z₆, by rw [b₆, hz₃, hz₆]; ring⟩

/-- **The stopping conditions of Tate's algorithm do not depend on the uniformiser.** -/
theorem isTateTerminal_iff_of_associated {W : WeierstrassCurve R} {ϖ' : R} (hϖ : Associated ϖ ϖ')
    {s : ReductionSymbol} : W.IsTateTerminal ϖ s ↔ W.IsTateTerminal ϖ' s := by
  have h (n : ℕ) (x : R) : ϖ ^ n ∣ x ↔ ϖ' ^ n ∣ x := hϖ.pow_pow.dvd_iff_dvd_left
  have h₁ (x : R) : ϖ ∣ x ↔ ϖ' ∣ x := hϖ.dvd_iff_dvd_left
  rcases s with (_ | n) | _ | _ | _ | (_ | n) | _ | _ | _ <;>
    simp only [isTateTerminal_I_zero, isTateTerminal_I_add_one, isTateTerminal_II,
      isTateTerminal_III, isTateTerminal_IV, isTateTerminal_IStar_zero,
      isTateTerminal_IStar_add_one, isTateTerminal_IVStar, isTateTerminal_IIIStar,
      isTateTerminal_IIStar, isTateOddStage_iff, isTateEvenStage_iff, h, h₁]

end CommRing

section DiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  {W : WeierstrassCurve R}

private theorem residue_eq_zero_iff_dvd (hϖ : Irreducible ϖ) (x : R) :
    residue R x = 0 ↔ ϖ ∣ x := by
  rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]

/-- The test separating the double-root branch (Step 7) from the triple-root branch (Step 8) is the
residue-cubic test `b² = 3c`: if `a₂ = ϖ A₂` and `a₄ = ϖ² A₄`, then `ϖ³ ∣ a₂² - 3 a₄` exactly when
`A₂² - 3 A₄` vanishes in the residue field. -/
private theorem pow_three_dvd_sq_sub_iff (hϖ : Irreducible ϖ) {A₂ A₄ : R} (hA₂ : W.a₂ = ϖ * A₂)
    (hA₄ : W.a₄ = ϖ ^ 2 * A₄) :
    ϖ ^ 3 ∣ W.a₂ ^ 2 - 3 * W.a₄ ↔ residue R A₂ ^ 2 - 3 * residue R A₄ = 0 := by
  rw [hA₂, hA₄, show (ϖ * A₂) ^ 2 - 3 * (ϖ ^ 2 * A₄) = ϖ ^ 2 * (A₂ ^ 2 - 3 * A₄) by ring,
    pow_succ, mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ.ne_zero), ← residue_eq_zero_iff_dvd hϖ]
  simp [map_ofNat]

/-- Between two equations in the normal form of Step 6, a change of variables has `ϖ ∣ r`,
`ϖ ∣ s` and `ϖ² ∣ t`. -/
private theorem dvd_r_s_t_of_stepSix (hϖ : Irreducible ϖ) {C : VariableChange R}
    (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ∣ W.a₂) (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : ϖ ^ 2 ∣ W.a₄) (h₆ : ϖ ^ 3 ∣ W.a₆)
    (h₂' : ϖ ∣ (C • W).a₂) (h₃' : ϖ ^ 2 ∣ (C • W).a₃) (h₄' : ϖ ^ 2 ∣ (C • W).a₄)
    (h₆' : ϖ ^ 3 ∣ (C • W).a₆) : ϖ ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ 2 ∣ C.t := by
  have hp (n : ℕ) {x : R} (h : ϖ ^ (n + 1) ∣ x) : ϖ ∣ x := (dvd_pow_self ϖ n.succ_ne_zero).trans h
  obtain ⟨⟨r₁, hr₁⟩, ⟨t₁, ht₁⟩⟩ := dvd_r_and_dvd_t_of_dvd_a₃_a₄_a₆ hϖ.prime (hp 1 h₃) (hp 1 h₄)
    (hp 2 h₆) (hp 1 h₃') (hp 1 h₄') (hp 2 h₆')
  rw [variableChange_a₂, (C.u⁻¹.isUnit.pow 2).dvd_mul_left] at h₂'
  rw [variableChange_a₆, (C.u⁻¹.isUnit.pow 6).dvd_mul_left] at h₆'
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  obtain ⟨x₃, hx₃⟩ := h₃
  obtain ⟨x₄, hx₄⟩ := h₄
  obtain ⟨x₆, hx₆⟩ := h₆
  obtain ⟨e₂, he₂⟩ := h₂'
  obtain ⟨e₆, he₆⟩ := h₆'
  rw [hx₁, hx₂, hr₁] at he₂
  rw [hx₁, hx₂, hx₃, hx₄, hx₆, hr₁, ht₁] at he₆
  refine ⟨⟨r₁, hr₁⟩, hϖ.prime.dvd_of_dvd_pow (n := 2) ⟨x₂ - C.s * x₁ + 3 * r₁ - e₂, ?_⟩,
    hϖ.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := 1)
      ⟨x₆ + r₁ * x₄ + r₁ ^ 2 * x₂ + r₁ ^ 3 - t₁ * x₃ - r₁ * t₁ * x₁ - e₆, ?_⟩⟩
  · linear_combination -he₂
  · rw [ht₁]
    linear_combination -he₆

/-- **The residue cubic of Step 6 under a change of variables.** If `W` and `C • W` are in the
normal form of Step 6, with residue cubics `T³ + A₂ T² + A₄ T + A₆` and `T³ + B₂ T² + B₄ T + B₆`,
and `C` has `r = ϖ r₁`, `ϖ ∣ s` and `ϖ² ∣ t`, then the second is `v⁶ P (v⁻² T + ρ)`, where `P` is
the first, `v` is the residue of `u⁻¹` and `ρ` the residue of `r₁`. -/
private theorem residue_stepSix_smul (hϖ : Irreducible ϖ) {C : VariableChange R}
    {x₁ x₃ A₂ A₄ A₆ B₂ B₄ B₆ r₁ : R} (hx₁ : W.a₁ = ϖ * x₁) (hx₃ : W.a₃ = ϖ ^ 2 * x₃)
    (hA₂ : W.a₂ = ϖ * A₂) (hA₄ : W.a₄ = ϖ ^ 2 * A₄) (hA₆ : W.a₆ = ϖ ^ 3 * A₆)
    (hB₂ : (C • W).a₂ = ϖ * B₂) (hB₄ : (C • W).a₄ = ϖ ^ 2 * B₄)
    (hB₆ : (C • W).a₆ = ϖ ^ 3 * B₆) (hr : C.r = ϖ * r₁) (hs : ϖ ∣ C.s) (ht : ϖ ^ 2 ∣ C.t) :
    residue R B₂ = residue R ↑C.u⁻¹ ^ 2 * (residue R A₂ + 3 * residue R r₁) ∧
    residue R B₄ = residue R ↑C.u⁻¹ ^ 4 *
      (residue R A₄ + 2 * residue R r₁ * residue R A₂ + 3 * residue R r₁ ^ 2) ∧
    residue R B₆ = residue R ↑C.u⁻¹ ^ 6 * (residue R A₆ + residue R r₁ * residue R A₄ +
      residue R r₁ ^ 2 * residue R A₂ + residue R r₁ ^ 3) := by
  obtain ⟨s₁, hs₁⟩ := hs
  obtain ⟨t₁, ht₁⟩ := ht
  have hϖ0 := hϖ.ne_zero
  have hres : residue R ϖ = 0 := (residue_eq_zero_iff_dvd hϖ ϖ).2 dvd_rfl
  rw [variableChange_a₂, hA₂, hx₁, hr, hs₁] at hB₂
  rw [variableChange_a₄, hA₂, hA₄, hx₁, hx₃, hr, hs₁, ht₁] at hB₄
  rw [variableChange_a₆, hA₂, hA₄, hA₆, hx₁, hx₃, hr, ht₁] at hB₆
  have e₂ : B₂ = ↑C.u⁻¹ ^ 2 * (A₂ + 3 * r₁ - ϖ * (s₁ * x₁ + s₁ ^ 2)) :=
    mul_left_cancel₀ hϖ0 (by linear_combination -hB₂)
  have e₄ : B₄ = ↑C.u⁻¹ ^ 4 * (A₄ + 2 * r₁ * A₂ + 3 * r₁ ^ 2 -
      ϖ * (s₁ * x₃ + (t₁ + r₁ * s₁) * x₁ + 2 * s₁ * t₁)) :=
    mul_left_cancel₀ (pow_ne_zero 2 hϖ0) (by linear_combination -hB₄)
  have e₆ : B₆ = ↑C.u⁻¹ ^ 6 * (A₆ + r₁ * A₄ + r₁ ^ 2 * A₂ + r₁ ^ 3 -
      ϖ * (t₁ * x₃ + t₁ ^ 2 + r₁ * t₁ * x₁)) :=
    mul_left_cancel₀ (pow_ne_zero 3 hϖ0) (by linear_combination -hB₆)
  refine ⟨?_, ?_, ?_⟩
  · rw [e₂]
    simp [hres, map_ofNat]
  · rw [e₄]
    simp [hres, map_ofNat]
  · rw [e₆]
    simp [hres]

/-- The normal form of Step 8, in which the residue cubic is `T³`, passes the tests of `I₀*` and
of the `Iₙ*` branch. -/
private theorem tateTest_five_six_of_stepEight (hϖ : Irreducible ϖ) (h₂ : ϖ ^ 2 ∣ W.a₂)
    (h₄ : ϖ ^ 3 ∣ W.a₄) (h₆ : ϖ ^ 4 ∣ W.a₆) : tateTest ϖ W 5 ∧ tateTest ϖ W 6 := by
  obtain ⟨y₂, hy₂⟩ := h₂
  obtain ⟨y₄, hy₄⟩ := h₄
  obtain ⟨y₆, hy₆⟩ := h₆
  have hres : residue R ϖ = 0 := (residue_eq_zero_iff_dvd hϖ ϖ).2 dvd_rfl
  have hA₂ : W.a₂ = ϖ * (ϖ * y₂) := by rw [hy₂]; ring
  have hA₄ : W.a₄ = ϖ ^ 2 * (ϖ * y₄) := by rw [hy₄]; ring
  have hA₆ : W.a₆ = ϖ ^ 3 * (ϖ * y₆) := by rw [hy₆]; ring
  refine ⟨(pow_seven_dvd_discr_iff hϖ hA₂ hA₄ hA₆).2 ?_, (pow_three_dvd_sq_sub_iff hϖ hA₂ hA₄).2 ?_⟩
  · simp [Cubic.discr, hres]
  · simp [hres]

/-- An equation on which Tate's algorithm stops at a symbol `Iₙ*` with `n ≥ 1` reaches the test of
the `Iₙ*` branch and fails it. -/
private theorem tateContext_six_of_doubleRoot (hϖ : Irreducible ϖ) (h₁ : ϖ ∣ W.a₁)
    (h₂ : ϖ ∣ W.a₂) (h₂' : ¬ ϖ ^ 2 ∣ W.a₂) (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : ϖ ^ 3 ∣ W.a₄)
    (h₆ : ϖ ^ 4 ∣ W.a₆) : TateContext ϖ 6 W ∧ ¬ tateTest ϖ W 6 := by
  have h₄' : ϖ ^ 2 ∣ W.a₄ := (pow_dvd_pow ϖ (by norm_num)).trans h₄
  have h₆' : ϖ ^ 3 ∣ W.a₆ := (pow_dvd_pow ϖ (by norm_num)).trans h₆
  have hp (n : ℕ) {x : R} (h : ϖ ^ (n + 1) ∣ x) : ϖ ∣ x := (dvd_pow_self ϖ n.succ_ne_zero).trans h
  have ht := tateTest_of_stepSix h₁ h₂ h₃ h₄' h₆'
  obtain ⟨A₂, hA₂⟩ := h₂
  obtain ⟨y₄, hy₄⟩ := h₄
  obtain ⟨y₆, hy₆⟩ := h₆
  have hres : residue R ϖ = 0 := (residue_eq_zero_iff_dvd hϖ ϖ).2 dvd_rfl
  have hA₄ : W.a₄ = ϖ ^ 2 * (ϖ * y₄) := by rw [hy₄]; ring
  have hA₆ : W.a₆ = ϖ ^ 3 * (ϖ * y₆) := by rw [hy₆]; ring
  refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨hp 1 h₃, hp 1 h₄', hp 2 h₆'⟩,
    fun _ ↦ ⟨h₁, ⟨A₂, hA₂⟩, h₃, h₄', h₆'⟩, by omega, by omega⟩, ?_⟩
  · rcases lt_or_ge k 5 with hk5 | hk5
    · exact ht k hk5
    · obtain rfl : k = 5 := by omega
      exact (pow_seven_dvd_discr_iff hϖ hA₂ hA₄ hA₆).2 (by simp [Cubic.discr, hres])
  · -- The residue cubic is `T³ + A₂ T²` with `A₂ ≠ 0` in the residue field.
    simp only [tateTest]
    rw [pow_three_dvd_sq_sub_iff hϖ hA₂ hA₄]
    have : residue R A₂ ≠ 0 := by
      rw [ne_eq, residue_eq_zero_iff_dvd hϖ]
      rintro ⟨B, rfl⟩
      exact h₂' ⟨B, by rw [hA₂]; ring⟩
    simpa [hres] using this

/-- **The test at which Tate's algorithm stops.** On an equation on which the algorithm stops with
symbol `s`, it reaches the test `chainIndex s` and fails it. -/
private theorem IsTateTerminal.tateContext (hϖ : Irreducible ϖ) {s : ReductionSymbol}
    (h : W.IsTateTerminal ϖ s) :
    TateContext ϖ (chainIndex s) W ∧ ¬ tateTest ϖ W (chainIndex s) := by
  have hp (n : ℕ) {x : R} (h : ϖ ^ (n + 1) ∣ x) : ϖ ∣ x := (dvd_pow_self ϖ n.succ_ne_zero).trans h
  have hle {m n : ℕ} (hmn : m ≤ n) {x : R} (h : ϖ ^ n ∣ x) : ϖ ^ m ∣ x :=
    (pow_dvd_pow ϖ hmn).trans h
  have hΔ (hs : ∀ n, s ≠ .I n) : ϖ ∣ W.Δ := hp _ (h.pow_componentCount_add_one_dvd_Δ hϖ.prime hs)
  match s, h with
  | .I 0, h =>
    exact ⟨⟨by simp [chainIndex], by simp [chainIndex], by simp [chainIndex], by simp [chainIndex],
      by simp [chainIndex]⟩, isTateTerminal_I_zero.1 h⟩
  | .I (n + 1), h =>
    obtain ⟨h₃, h₄, h₆, hb₂, hΔ', -⟩ := isTateTerminal_I_add_one.1 h
    refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨h₃, h₄, h₆⟩, by simp [chainIndex], by simp [chainIndex],
      by simp [chainIndex]⟩, hb₂⟩
    obtain rfl : k = 0 := by simpa [chainIndex] using hk
    exact hp n hΔ'
  | .II, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, h₆'⟩ := isTateTerminal_II.1 h
    refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨h₃, h₄, h₆⟩, by simp [chainIndex], by simp [chainIndex],
      by simp [chainIndex]⟩, h₆'⟩
    simp only [chainIndex] at hk
    interval_cases k
    exacts [hΔ (by simp), hb₂]
  | .III, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, hb₈⟩ := isTateTerminal_III.1 h
    refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨h₃, h₄, hp 1 h₆⟩, by simp [chainIndex],
      by simp [chainIndex], by simp [chainIndex]⟩, hb₈⟩
    simp only [chainIndex] at hk
    interval_cases k
    exacts [hΔ (by simp), hb₂, h₆]
  | .IV, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, hb₈, hb₆⟩ := isTateTerminal_IV.1 h
    refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨h₃, h₄, hp 1 h₆⟩, by simp [chainIndex],
      by simp [chainIndex], by simp [chainIndex]⟩, hb₆⟩
    simp only [chainIndex] at hk
    interval_cases k
    exacts [hΔ (by simp), hb₂, h₆, hb₈]
  | .IStar 0, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, hd⟩ := isTateTerminal_IStar_zero.1 h
    exact ⟨⟨tateTest_of_stepSix h₁ h₂ h₃ h₄ h₆, fun _ ↦ ⟨hp 1 h₃, hp 1 h₄, hp 2 h₆⟩,
      fun _ ↦ ⟨h₁, h₂, h₃, h₄, h₆⟩, by simp [chainIndex], by simp [chainIndex]⟩, hd⟩
  | .IStar (n + 1), h =>
    rcases isTateTerminal_IStar_add_one.1 h with ⟨k, -, hk, -⟩ | ⟨k, -, hk, -⟩
    · obtain ⟨h₁, h₂, h₂', h₃, h₄, h₆⟩ := isTateOddStage_iff.1 hk
      exact tateContext_six_of_doubleRoot hϖ h₁ h₂ h₂' (hle (by omega) h₃) (hle (by omega) h₄)
        (hle (by omega) h₆)
    · obtain ⟨h₁, h₂, h₂', h₃, h₄, h₆⟩ := isTateEvenStage_iff.1 hk
      exact tateContext_six_of_doubleRoot hϖ h₁ h₂ h₂' (hle (by omega) h₃) (hle (by omega) h₄)
        (hle (by omega) h₆)
  | .IVStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, hb₆⟩ := isTateTerminal_IVStar.1 h
    have ht := tateTest_of_stepSix h₁ (hp 1 h₂) h₃ (hle (by omega) h₄) (hle (by omega) h₆)
    have ht' := tateTest_five_six_of_stepEight hϖ h₂ h₄ h₆
    refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨hp 1 h₃, hp 2 h₄, hp 3 h₆⟩,
      fun _ ↦ ⟨h₁, hp 1 h₂, h₃, hle (by omega) h₄, hle (by omega) h₆⟩, fun _ ↦ ⟨h₂, h₄, h₆⟩,
      by simp [chainIndex]⟩, hb₆⟩
    simp only [chainIndex] at hk
    rcases lt_or_ge k 5 with hk5 | hk5
    · exact ht k hk5
    · interval_cases k
      exacts [ht'.1, ht'.2]
  | .IIIStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, h₄'⟩ := isTateTerminal_IIIStar.1 h
    have ht := tateTest_of_stepSix h₁ (hp 1 h₂) (hle (by omega) h₃) (hle (by omega) h₄)
      (hle (by omega) h₆)
    have ht' := tateTest_five_six_of_stepEight hϖ h₂ h₄ (hle (by omega) h₆)
    refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨hp 2 h₃, hp 2 h₄, hp 4 h₆⟩,
      fun _ ↦ ⟨h₁, hp 1 h₂, hle (by omega) h₃, hle (by omega) h₄, hle (by omega) h₆⟩,
      fun _ ↦ ⟨h₂, h₄, hle (by omega) h₆⟩, fun _ ↦ ⟨h₃, h₆⟩⟩, h₄'⟩
    simp only [chainIndex] at hk
    rcases lt_or_ge k 5 with hk5 | hk5
    · exact ht k hk5
    · interval_cases k
      exacts [ht'.1, ht'.2, tateTest_seven_of_stepNine h₃ h₆]
  | .IIStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IIStar.1 h
    have ht := tateTest_of_stepSix h₁ (hp 1 h₂) (hle (by omega) h₃) (hle (by omega) h₄)
      (hle (by omega) h₆)
    have ht' := tateTest_five_six_of_stepEight hϖ h₂ (hle (by omega) h₄) (hle (by omega) h₆)
    refine ⟨⟨fun k hk ↦ ?_, fun _ ↦ ⟨hp 2 h₃, hp 3 h₄, hp 4 h₆⟩,
      fun _ ↦ ⟨h₁, hp 1 h₂, hle (by omega) h₃, hle (by omega) h₄, hle (by omega) h₆⟩,
      fun _ ↦ ⟨h₂, hle (by omega) h₄, hle (by omega) h₆⟩, fun _ ↦ ⟨h₃, h₆⟩⟩, by
        simp [chainIndex, tateTest]⟩
    simp only [chainIndex] at hk
    rcases lt_or_ge k 5 with hk5 | hk5
    · exact ht k hk5
    · interval_cases k
      exacts [ht'.1, ht'.2, tateTest_seven_of_stepNine h₃ h₆, h₄]

/-- **Each test of Tate's algorithm is invariant under changes of variables over `R`** between
equations on which the algorithm reaches it. -/
private theorem tateTest_smul (hϖ : Irreducible ϖ) (C : VariableChange R) {i : ℕ}
    (h : TateContext ϖ i W) (h' : TateContext ϖ i (C • W)) (ht : tateTest ϖ W i) :
    tateTest ϖ (C • W) i := by
  have hv (n : ℕ) : IsUnit ((↑C.u⁻¹ : R) ^ n) := C.u⁻¹.isUnit.pow n
  -- Divisibility by `a` is unchanged by adding a multiple of `a` and multiplying by a unit.
  have dvd_iff_of_eq_mul_add {a x y v : R} (hv : IsUnit v) (z : R)
      (h : y = v * (x + a * z)) : a ∣ y ↔ a ∣ x := by
    rw [h, hv.dvd_mul_left, dvd_add_left (dvd_mul_right a z)]
  -- From the test of Step 2 on, both equations reduce to curves singular at the origin.
  have hrt (hi : 1 ≤ i) : ϖ ∣ C.r ∧ ϖ ∣ C.t := by
    obtain ⟨h₃, h₄, h₆⟩ := h.2.1 hi
    obtain ⟨h₃', h₄', h₆'⟩ := h'.2.1 hi
    exact dvd_r_and_dvd_t_of_dvd_a₃_a₄_a₆ hϖ.prime h₃ h₄ h₆ h₃' h₄' h₆'
  -- From the test of `I₀*` on, both equations are in the normal form of Step 6.
  have hstep (hi : 5 ≤ i) : ∃ r₁ x₁ x₃ A₂ A₄ A₆ B₂ B₄ B₆ : R, C.r = ϖ * r₁ ∧ ϖ ∣ C.s ∧
      ϖ ^ 2 ∣ C.t ∧ W.a₁ = ϖ * x₁ ∧ W.a₃ = ϖ ^ 2 * x₃ ∧ W.a₂ = ϖ * A₂ ∧ W.a₄ = ϖ ^ 2 * A₄ ∧
      W.a₆ = ϖ ^ 3 * A₆ ∧ (C • W).a₂ = ϖ * B₂ ∧ (C • W).a₄ = ϖ ^ 2 * B₄ ∧
      (C • W).a₆ = ϖ ^ 3 * B₆ := by
    obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := h.2.2.1 hi
    obtain ⟨-, h₂', h₃', h₄', h₆'⟩ := h'.2.2.1 hi
    obtain ⟨⟨r₁, hr₁⟩, hs, ht⟩ := dvd_r_s_t_of_stepSix hϖ h₁ h₂ h₃ h₄ h₆ h₂' h₃' h₄' h₆'
    obtain ⟨x₁, hx₁⟩ := h₁
    obtain ⟨x₃, hx₃⟩ := h₃
    obtain ⟨A₂, hA₂⟩ := h₂
    obtain ⟨A₄, hA₄⟩ := h₄
    obtain ⟨A₆, hA₆⟩ := h₆
    obtain ⟨B₂, hB₂⟩ := h₂'
    obtain ⟨B₄, hB₄⟩ := h₄'
    obtain ⟨B₆, hB₆⟩ := h₆'
    exact ⟨r₁, x₁, x₃, A₂, A₄, A₆, B₂, B₄, B₆, hr₁, hs, ht, hx₁, hx₃, hA₂, hA₄, hA₆, hB₂, hB₄, hB₆⟩
  have hst (hi : 5 ≤ i) : ϖ ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ 2 ∣ C.t := by
    obtain ⟨r₁, -, -, -, -, -, -, -, -, hr₁, hs, ht, -⟩ := hstep hi
    exact ⟨⟨r₁, hr₁⟩, hs, ht⟩
  -- From the test of `IV*` on, both residue cubics are `T³`, so `ρ = 0` and `ϖ² ∣ r`.
  have hr (hi : 7 ≤ i) : ϖ ^ 2 ∣ C.r := by
    obtain ⟨r₁, x₁, x₃, A₂, A₄, A₆, B₂, B₄, B₆, hr, hs, ht', hx₁, hx₃, hA₂, hA₄, hA₆, hB₂, hB₄,
      hB₆⟩ := hstep (by omega)
    obtain ⟨-, -, e₆⟩ := residue_stepSix_smul hϖ hx₁ hx₃ hA₂ hA₄ hA₆ hB₂ hB₄ hB₆ hr hs ht'
    obtain ⟨⟨y₂, hy₂⟩, ⟨y₄, hy₄⟩, ⟨y₆, hy₆⟩⟩ := h.2.2.2.1 hi
    obtain ⟨-, -, ⟨y₆', hy₆'⟩⟩ := h'.2.2.2.1 hi
    have hϖ0 := hϖ.ne_zero
    have hres : residue R ϖ = 0 := (residue_eq_zero_iff_dvd hϖ ϖ).2 dvd_rfl
    have hA (n : ℕ) (A y : R) (hA : ϖ ^ (n + 1) * A = ϖ ^ (n + 2) * y) : residue R A = 0 := by
      rw [mul_left_cancel₀ (pow_ne_zero (n + 1) hϖ0) (hA.trans (by ring) :
        _ = ϖ ^ (n + 1) * (ϖ * y))]
      simp [hres]
    rw [hA 0 A₂ y₂ (by linear_combination hA₂.symm.trans hy₂),
      hA 1 A₄ y₄ (by linear_combination hA₄.symm.trans hy₄),
      hA 2 A₆ y₆ (by linear_combination hA₆.symm.trans hy₆),
      hA 2 B₆ y₆' (by linear_combination hB₆.symm.trans hy₆')] at e₆
    obtain ⟨r₂, rfl⟩ : ϖ ∣ r₁ := by
      rw [← residue_eq_zero_iff_dvd hϖ]
      simpa [(C.u⁻¹.isUnit.map (residue R)).ne_zero] using e₆.symm
    exact ⟨r₂, by rw [hr]; ring⟩
  match i, h, h', ht with
  | 0, _, _, ht =>
    simp only [tateTest] at ht ⊢
    rw [variableChange_Δ]
    exact dvd_mul_of_dvd_right ht _
  | 1, _, _, ht =>
    obtain ⟨⟨r₁, hr₁⟩, -⟩ := hrt le_rfl
    exact (dvd_iff_of_eq_mul_add (hv 2) (12 * r₁) (by rw [variableChange_b₂, hr₁]; ring)).2 ht
  | 2, h, _, ht =>
    obtain ⟨⟨r₁, hr₁⟩, ⟨t₁, ht₁⟩⟩ := hrt (by norm_num)
    obtain ⟨⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, -⟩ := h.2.1 (by norm_num)
    refine (dvd_iff_of_eq_mul_add (hv 6) (r₁ * x₄ + r₁ ^ 2 * W.a₂ + ϖ * r₁ ^ 3 - t₁ * x₃ -
      t₁ ^ 2 - r₁ * t₁ * W.a₁) ?_).2 ht
    rw [variableChange_a₆, hr₁, ht₁, hx₃, hx₄]
    ring
  | 3, h, _, ht =>
    obtain ⟨⟨r₁, hr₁⟩, -⟩ := hrt (by norm_num)
    obtain ⟨⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, -⟩ := h.2.1 (by norm_num)
    obtain ⟨β₂, hβ₂⟩ : ϖ ∣ W.b₂ := h.1 1 (by norm_num)
    obtain ⟨y₆, hy₆⟩ : ϖ ^ 2 ∣ W.a₆ := h.1 2 (by norm_num)
    refine (dvd_iff_of_eq_mul_add (hv 8) (3 * r₁ * (x₃ ^ 2 + 4 * y₆) +
      3 * r₁ ^ 2 * (W.a₁ * x₃ + 2 * x₄) + ϖ * r₁ ^ 3 * β₂ + 3 * ϖ * r₁ ^ 4) ?_).2 ht
    rw [variableChange_b₈, hr₁, hβ₂, b₆, b₄, hx₃, hx₄, hy₆]
    ring
  | 4, h, _, ht =>
    obtain ⟨⟨r₁, hr₁⟩, -⟩ := hrt (by norm_num)
    obtain ⟨⟨x₃, hx₃⟩, -, -⟩ := h.2.1 (by norm_num)
    obtain ⟨β₂, hβ₂⟩ : ϖ ∣ W.b₂ := h.1 1 (by norm_num)
    obtain ⟨y₆, hy₆⟩ : ϖ ^ 2 ∣ W.a₆ := h.1 2 (by norm_num)
    obtain ⟨β₈, hβ₈⟩ : ϖ ^ 3 ∣ W.b₈ := h.1 3 (by norm_num)
    have hb₆ : W.b₆ = ϖ ^ 2 * (x₃ ^ 2 + 4 * y₆) := by rw [b₆, hx₃, hy₆]; ring
    -- `4 b₈ = b₂ b₆ - b₄²` gives `ϖ² ∣ b₄`.
    obtain ⟨β₄, hβ₄⟩ : ϖ ^ 2 ∣ W.b₄ := hϖ.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := 1)
      ⟨β₂ * (x₃ ^ 2 + 4 * y₆) - 4 * β₈, by
        linear_combination W.b_relation + W.b₂ * hb₆ + ϖ ^ 2 * (x₃ ^ 2 + 4 * y₆) * hβ₂ -
          4 * hβ₈⟩
    refine (dvd_iff_of_eq_mul_add (hv 6) (2 * r₁ * β₄ + r₁ ^ 2 * β₂ + 4 * r₁ ^ 3) ?_).2 ht
    rw [variableChange_b₆, hr₁, hβ₂, hβ₄]
    ring
  | 5, _, _, ht =>
    obtain ⟨r₁, x₁, x₃, A₂, A₄, A₆, B₂, B₄, B₆, hr, hs, ht', hx₁, hx₃, hA₂, hA₄, hA₆, hB₂, hB₄,
      hB₆⟩ := hstep (by norm_num)
    obtain ⟨e₂, e₄, e₆⟩ := residue_stepSix_smul hϖ hx₁ hx₃ hA₂ hA₄ hA₆ hB₂ hB₄ hB₆ hr hs ht'
    have hd := (pow_seven_dvd_discr_iff hϖ hA₂ hA₄ hA₆).1 ht
    refine (pow_seven_dvd_discr_iff hϖ hB₂ hB₄ hB₆).2 ?_
    -- The discriminant of the residue cubic changes by the unit `v¹²`.
    simp only [Cubic.discr] at hd ⊢
    rw [e₂, e₄, e₆]
    linear_combination residue R ↑C.u⁻¹ ^ 12 * hd
  | 6, _, _, ht =>
    obtain ⟨r₁, x₁, x₃, A₂, A₄, A₆, B₂, B₄, B₆, hr, hs, ht', hx₁, hx₃, hA₂, hA₄, hA₆, hB₂, hB₄,
      hB₆⟩ := hstep (by norm_num)
    obtain ⟨e₂, e₄, -⟩ := residue_stepSix_smul hϖ hx₁ hx₃ hA₂ hA₄ hA₆ hB₂ hB₄ hB₆ hr hs ht'
    have hd := (pow_three_dvd_sq_sub_iff hϖ hA₂ hA₄).1 ht
    refine (pow_three_dvd_sq_sub_iff hϖ hB₂ hB₄).2 ?_
    rw [e₂, e₄]
    linear_combination residue R ↑C.u⁻¹ ^ 4 * hd
  | 7, h, _, ht =>
    obtain ⟨r₂, hr₂⟩ := hr (by norm_num)
    obtain ⟨⟨x₁, hx₁⟩, -, ⟨x₃, hx₃⟩, -, -⟩ := h.2.2.1 (by norm_num)
    obtain ⟨⟨y₂, hy₂⟩, ⟨y₄, hy₄⟩, -⟩ := h.2.2.2.1 le_rfl
    refine (dvd_iff_of_eq_mul_add (hv 6) (2 * r₂ * (x₁ * x₃ + 2 * y₄) +
      ϖ * r₂ ^ 2 * (x₁ ^ 2 + 4 * y₂) + 4 * ϖ * r₂ ^ 3) ?_).2 ht
    rw [variableChange_b₆, hr₂, b₄, b₂, hx₁, hx₃, hy₂, hy₄]
    ring
  | 8, h, h', ht =>
    obtain ⟨r₂, hr₂⟩ := hr (by norm_num)
    obtain ⟨-, ⟨s₁, hs₁⟩, ⟨t₁, ht₁⟩⟩ := hst (by norm_num)
    obtain ⟨⟨x₁, hx₁⟩, -, -, -, -⟩ := h.2.2.1 (by norm_num)
    obtain ⟨⟨y₂, hy₂⟩, ⟨y₄, hy₄⟩, -⟩ := h.2.2.2.1 (by norm_num)
    obtain ⟨⟨z₃, hz₃⟩, ⟨z₆, hz₆⟩⟩ := h.2.2.2.2 le_rfl
    obtain ⟨-, h₆'⟩ := h'.2.2.2.2 le_rfl
    -- On the normal form of Step 9 also `ϖ³ ∣ t`.
    rw [variableChange_a₆, (hv 6).dvd_mul_left] at h₆'
    obtain ⟨e₆, he₆⟩ := h₆'
    obtain ⟨t₃, ht₃⟩ : ϖ ^ 3 ∣ C.t := by
      refine hϖ.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := 2)
        ⟨z₆ + r₂ * y₄ + ϖ * r₂ ^ 2 * y₂ + ϖ * r₂ ^ 3 - t₁ * z₃ - r₂ * t₁ * x₁ - e₆, ?_⟩
      rw [hr₂, hx₁, hy₂, hy₄, hz₃, hz₆, ht₁] at he₆
      rw [ht₁]
      linear_combination -he₆
    refine (dvd_iff_of_eq_mul_add (hv 4) (-(s₁ * z₃) + 2 * r₂ * y₂ - (t₃ + r₂ * s₁) * x₁ +
      3 * r₂ ^ 2 - 2 * s₁ * t₃) ?_).2 ht
    rw [variableChange_a₄, hr₂, hs₁, ht₃, hx₁, hy₂, hz₃]
    ring
  | i + 9, _, _, ht => exact ht.elim

/-- Tate's algorithm stops on `W` and on `C • W` at the same test: if it stopped on one at an
earlier test, that equation would fail a test which the other passes. -/
private theorem IsTateTerminal.chainIndex_eq (hϖ : Irreducible ϖ) {C : VariableChange R}
    {s s' : ReductionSymbol} (h : W.IsTateTerminal ϖ s) (h' : (C • W).IsTateTerminal ϖ s') :
    chainIndex s = chainIndex s' := by
  obtain ⟨hc, hn⟩ := h.tateContext hϖ
  obtain ⟨hc', hn'⟩ := h'.tateContext hϖ
  rcases lt_trichotomy (chainIndex s) (chainIndex s') with hlt | heq | hlt
  · have hc₀ : TateContext ϖ (chainIndex s) (C⁻¹ • C • W) := by rwa [inv_smul_smul]
    have ht := tateTest_smul hϖ C⁻¹ (hc'.mono hlt.le) hc₀ (hc'.1 _ hlt)
    rw [inv_smul_smul] at ht
    exact absurd ht hn
  · exact heq
  · exact absurd (tateTest_smul hϖ C (hc.mono hlt.le) hc' (hc.1 _ hlt)) hn'

/-- **The output of Tate's algorithm does not depend on the changes of variables.** If the
algorithm stops on `W` with a symbol `s` other than `Iₙ*` with `n ≥ 1`, and on `C • W`, for a
change of variables `C` over `R`, with a symbol `s'`, then `s' = s`. -/
theorem IsTateTerminal.eq_of_smul (hϖ : Irreducible ϖ) {C : VariableChange R}
    {s s' : ReductionSymbol} (h : W.IsTateTerminal ϖ s) (h' : (C • W).IsTateTerminal ϖ s')
    (hs : ∀ n, s ≠ .IStar (n + 1)) : s' = s := by
  have hj := h.chainIndex_eq hϖ h'
  -- The test determines the symbol, except for the indices of `Iₙ` and `Iₙ*`.
  rcases s with (_ | n) | _ | _ | _ | (_ | n) | _ | _ | _ <;>
    rcases s' with (_ | m) | _ | _ | _ | (_ | m) | _ | _ | _ <;>
    simp [chainIndex] at hj <;> first | rfl | skip
  · -- At `Iₙ` the index is the valuation of `Δ`, which changes by a unit.
    have hu : addVal R ((↑C.u⁻¹ : R) ^ 12) = 0 := by simp
    have e := h'.addVal_Δ_eq hϖ
    rw [variableChange_Δ, addVal_mul, hu, zero_add, h.addVal_Δ_eq hϖ] at e
    have : m + 1 = n + 1 := by exact_mod_cast e.symm
    rw [show m = n by omega]
  · exact absurd rfl (hs _)

/-- **The `Iₙ*` branch of Tate's algorithm does not depend on the changes of variables.** If the
algorithm stops on `W` with a symbol `Iₙ*` with `n ≥ 1`, then it stops on every `C • W`, for `C`
over `R`, with a symbol `Iₘ*` with `m ≥ 1`. -/
theorem IsTateTerminal.exists_eq_IStar_of_smul (hϖ : Irreducible ϖ) {C : VariableChange R}
    {n : ℕ} {s' : ReductionSymbol} (h : W.IsTateTerminal ϖ (.IStar (n + 1)))
    (h' : (C • W).IsTateTerminal ϖ s') : ∃ m, s' = .IStar (m + 1) := by
  have hj := h.chainIndex_eq hϖ h'
  rcases s' with (_ | m) | _ | _ | _ | (_ | m) | _ | _ | _ <;> simp [chainIndex] at hj ⊢

section MinimalModel

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ' : R}
  {W₁ W₂ : WeierstrassCurve R} [IsMinimal R (W₁.baseChange K)] [IsMinimal R (W₂.baseChange K)]
  [(W₁.baseChange K).IsElliptic]

/-- Two equations over `R` that are minimal and related by a change of variables over `K` are
related by a change of variables over `R`. -/
private theorem exists_smul_eq_of_isMinimal_smul (D : VariableChange K)
    (hD : D • W₁.baseChange K = W₂.baseChange K) : ∃ C : VariableChange R, C • W₁ = W₂ := by
  obtain ⟨C, -, hC⟩ :=
    VariableChange.exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul R D hD
  rw [integralModel_eq_of_baseChange_eq rfl, integralModel_eq_of_baseChange_eq rfl] at hC
  exact ⟨C, hC⟩

/-- **The output of Tate's algorithm is an invariant of the curve.** If the algorithm stops on two
minimal equations of one elliptic curve over `K`, with any uniformisers, then it stops with the same
symbol, unless that symbol is `Iₙ*` with `n ≥ 1`. -/
theorem IsTateTerminal.eq_of_isMinimal_smul (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (D : VariableChange K) (hD : D • W₁.baseChange K = W₂.baseChange K) {s₁ s₂ : ReductionSymbol}
    (h₁ : W₁.IsTateTerminal ϖ s₁) (h₂ : W₂.IsTateTerminal ϖ' s₂)
    (hs : ∀ n, s₁ ≠ .IStar (n + 1)) : s₂ = s₁ := by
  obtain ⟨C, rfl⟩ := exists_smul_eq_of_isMinimal_smul D hD
  exact h₁.eq_of_smul hϖ
    ((isTateTerminal_iff_of_associated (associated_of_irreducible R hϖ hϖ')).2 h₂) hs

/-- If Tate's algorithm stops on a minimal equation of an elliptic curve over `K` with a symbol
`Iₙ*` with `n ≥ 1`, then it stops on every minimal equation, with any uniformiser, with a symbol
`Iₘ*` with `m ≥ 1`. -/
theorem IsTateTerminal.exists_eq_IStar_of_isMinimal_smul (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (D : VariableChange K) (hD : D • W₁.baseChange K = W₂.baseChange K)
    {n : ℕ} {s₂ : ReductionSymbol} (h₁ : W₁.IsTateTerminal ϖ (.IStar (n + 1)))
    (h₂ : W₂.IsTateTerminal ϖ' s₂) : ∃ m, s₂ = .IStar (m + 1) := by
  obtain ⟨C, rfl⟩ := exists_smul_eq_of_isMinimal_smul D hD
  exact h₁.exists_eq_IStar_of_smul hϖ
    ((isTateTerminal_iff_of_associated (associated_of_irreducible R hϖ hϖ')).2 h₂)

end MinimalModel

end DiscreteValuationRing

end WeierstrassCurve

end
