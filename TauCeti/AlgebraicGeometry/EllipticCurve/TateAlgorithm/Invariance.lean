/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
import TauCeti.Algebra.Ring.Divisibility
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Additive
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Discriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Multiplicity

/-!
# Tate's algorithm: the output does not depend on the choices, and certifies minimality

Tate's algorithm reads the reduction symbol of a Weierstrass equation over a discrete valuation
ring `R` with uniformiser `ϖ` by alternating changes of variables over `R` with divisibility tests
(`WeierstrassCurve.IsTateTerminal`, `WeierstrassCurve.exists_isTateTerminal`). The changes of
variables are not unique: at each step any one moving the singular point, or the multiple root of
the residue polynomial, to the origin will do. This file proves that the symbol does not depend on
these choices, nor on the uniformiser. If `W` and `C • W` are equations over `R`, related by a
change of variables `C` over `R`, on which the algorithm stops with symbols `s` and `s'`, then
`s = s'`. Since two minimal equations of one elliptic curve over the fraction field are related by
a change of variables over `R`, the symbol at which the algorithm stops on a minimal equation is an
invariant of the curve. No minimality is needed for the first statement.

The same invariance shows that the algorithm stops only on minimal equations. A change of
variables over `R` carries a non-minimal equation to one with `ϖⁱ ∣ aᵢ` for `i = 1, 2, 3, 4, 6`
(`WeierstrassCurve.exists_variableChange_pow_dvd_a₁_a₂_a₃_a₄_a₆_of_not_isMinimal`). That equation
passes every test of the algorithm, Step 10's `ϖ⁶ ∣ a₆` included, so the algorithm cannot have
stopped on the original equation. Together with termination this says that Tate's algorithm
decides minimality.

## Main results

* `WeierstrassCurve.dvd_r_and_dvd_t_of_dvd_a₃_a₄_a₆`: a change of variables between two
  equations whose reductions modulo a prime are singular at the origin fixes the origin modulo
  that prime.
* `WeierstrassCurve.IsTateTerminal.eq_of_smul`: if the algorithm stops on `W` with a symbol `s`,
  and on `C • W`, for `C` over `R`, with a symbol `s'`, then `s' = s`.
* `WeierstrassCurve.isTateTerminal_iff_of_associated`: the stopping conditions do not depend on
  the uniformiser.
* `WeierstrassCurve.IsTateTerminal.eq_of_isMinimal_smul`: the same statement for two minimal
  equations of one elliptic curve over the fraction field, with any uniformisers.
* `WeierstrassCurve.IsTateTerminal.isMinimal_baseChange`: an equation on which the algorithm stops
  is minimal over the fraction field.
* `WeierstrassCurve.isMinimal_baseChange_iff_exists_isTateTerminal`: with perfect residue field, an
  equation with nonzero discriminant is minimal exactly when the algorithm, run on it, stops.

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
  form of Step 9 also `ϖ³ ∣ t`, which makes `a₄` modulo `ϖ⁴` invariant, the test of `III*`, and
  `a₆` modulo `ϖ⁶` invariant, the test of `II*`.

If the algorithm stopped on `W` at an earlier test than on `C • W`, then `W` would fail a test
that `C • W` passes, which invariance rules out. So it stops on both at the same test, and the
symbol is determined by the test, except for the index of `Iₙ`, which is the valuation of `Δ`, and
the index of `Iₙ*`, which is the stage at which the subprocedure of Step 7 stops. The same
argument applies to that subprocedure: each stage implies the previous one and passes its test,
and between two equations at the same stage a change of variables is close enough to the identity
(`ϖ^(k+2) ∣ r`, `ϖ ∣ s` and `ϖ^(k+2) ∣ t` at the odd stage `k`, and `ϖ^(k+3) ∣ t` at the even
stage `k`) that the test of the stage, `ϖ^(2k+5) ∣ b₆` or `ϖ^(2k+7) ∣ a₄² - 4 a₂ a₆`, is
invariant. The bounds are proved stage by stage from the equations for `a₄` and `a₆`.

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
  | 9 => ϖ ^ 6 ∣ W.a₆
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

variable {W : WeierstrassCurve R}

/-! ### The index of `Iₙ*`

The subprocedure of Step 7 runs through the stages of `IsTateOddStage` and `IsTateEvenStage` and
stops at the first one whose test fails. Counting the stages from `0`, as the index of `Iₙ*` minus
one does, stage `2k` is the odd stage `k`, with test `ϖ^(2k+5) ∣ b₆`, and stage `2k + 1` is the even
stage `k`, with test `ϖ^(2k+7) ∣ a₄² - 4 a₂ a₆`. Each stage implies the previous one and passes its
test. Between two equations at the same stage, a change of variables satisfies
`ϖ^(k+2) ∣ r`, `ϖ ∣ s` and `ϖ^(k+2) ∣ t` at the odd stage `k`, and moreover `ϖ^(k+3) ∣ t` at the
even stage `k`; these bounds make the test of the stage invariant. -/

/-- The property `P k` when `n = 2k`, and `Q k` when `n = 2k + 1`. -/
private def ByParity (P Q : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ k, (n = 2 * k → P k) ∧ (n = 2 * k + 1 → Q k)

private theorem byParity_two_mul {P Q : ℕ → Prop} {k : ℕ} : ByParity P Q (2 * k) ↔ P k := by
  refine ⟨fun h ↦ (h k).1 rfl, fun h j ↦ ⟨fun hj ↦ ?_, fun hj ↦ by omega⟩⟩
  obtain rfl : k = j := by omega
  exact h

private theorem byParity_two_mul_add_one {P Q : ℕ → Prop} {k : ℕ} :
    ByParity P Q (2 * k + 1) ↔ Q k := by
  refine ⟨fun h ↦ (h k).2 rfl, fun h j ↦ ⟨fun hj ↦ by omega, fun hj ↦ ?_⟩⟩
  obtain rfl : k = j := by omega
  exact h

/-- The equation is at stage `n` of the `Iₙ*` subprocedure, counting from `0`. -/
private def StarStage (ϖ : R) (n : ℕ) (W : WeierstrassCurve R) : Prop :=
  ByParity (IsTateOddStage ϖ · W) (IsTateEvenStage ϖ · W) n

/-- The equation passes the test of stage `n` of the `Iₙ*` subprocedure, counting from `0`. -/
private def StarTest (ϖ : R) (n : ℕ) (W : WeierstrassCurve R) : Prop :=
  ByParity (fun k ↦ ϖ ^ (2 * k + 5) ∣ W.b₆) (fun k ↦ ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆) n

private theorem starStage_two_mul {k : ℕ} : StarStage ϖ (2 * k) W ↔ IsTateOddStage ϖ k W :=
  byParity_two_mul

private theorem starStage_two_mul_add_one {k : ℕ} :
    StarStage ϖ (2 * k + 1) W ↔ IsTateEvenStage ϖ k W :=
  byParity_two_mul_add_one

private theorem starTest_two_mul {k : ℕ} : StarTest ϖ (2 * k) W ↔ ϖ ^ (2 * k + 5) ∣ W.b₆ :=
  byParity_two_mul

private theorem starTest_two_mul_add_one {k : ℕ} :
    StarTest ϖ (2 * k + 1) W ↔ ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆ :=
  byParity_two_mul_add_one

/-- The even stage `k` implies the odd stage `k` and passes its test `ϖ^(2k+5) ∣ b₆`. -/
private theorem IsTateEvenStage.isTateOddStage_and_pow_dvd_b₆ {k : ℕ}
    (h : IsTateEvenStage ϖ k W) : IsTateOddStage ϖ k W ∧ ϖ ^ (2 * k + 5) ∣ W.b₆ := by
  obtain ⟨h₁, h₂, h₂', ⟨x₃, hx₃⟩, h₄, ⟨x₆, hx₆⟩⟩ := isTateEvenStage_iff.1 h
  exact ⟨isTateOddStage_iff.2
    ⟨h₁, h₂, h₂', ⟨ϖ * x₃, by rw [hx₃]; ring⟩, h₄, ⟨ϖ * x₆, by rw [hx₆]; ring⟩⟩,
    ⟨ϖ * x₃ ^ 2 + 4 * x₆, by rw [b₆, hx₃, hx₆]; ring⟩⟩

/-- The odd stage `k + 1` implies the even stage `k` and passes its test
`ϖ^(2k+7) ∣ a₄² - 4 a₂ a₆`. -/
private theorem IsTateOddStage.isTateEvenStage_and_pow_dvd_discrim {k : ℕ}
    (h : IsTateOddStage ϖ (k + 1) W) :
    IsTateEvenStage ϖ k W ∧ ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆ := by
  obtain ⟨h₁, ⟨x₂, hx₂⟩, h₂', h₃, ⟨x₄, hx₄⟩, ⟨x₆, hx₆⟩⟩ := isTateOddStage_iff.1 h
  exact ⟨isTateEvenStage_iff.2
    ⟨h₁, ⟨x₂, hx₂⟩, h₂', h₃, ⟨ϖ * x₄, by rw [hx₄]; ring⟩, ⟨ϖ * x₆, by rw [hx₆]; ring⟩⟩,
    ⟨ϖ * x₄ ^ 2 - 4 * x₂ * x₆, by rw [discrim, hx₂, hx₄, hx₆]; ring⟩⟩

/-- Stage `n + 1` implies stage `n` and passes its test. -/
private theorem StarStage.succ {n : ℕ} (h : StarStage ϖ (n + 1) W) :
    StarStage ϖ n W ∧ StarTest ϖ n W := by
  obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
  · obtain ⟨h, ht⟩ := (starStage_two_mul_add_one.1 h).isTateOddStage_and_pow_dvd_b₆
    exact ⟨starStage_two_mul.2 h, starTest_two_mul.2 ht⟩
  · obtain ⟨h, ht⟩ := (starStage_two_mul (k := k + 1)).1 h |>.isTateEvenStage_and_pow_dvd_discrim
    exact ⟨starStage_two_mul_add_one.2 h, starTest_two_mul_add_one.2 ht⟩

/-- Stage `m` implies every earlier stage. -/
private theorem StarStage.mono {m n : ℕ} (h : StarStage ϖ m W) (hnm : n ≤ m) :
    StarStage ϖ n W := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih h.succ.1

/-- At the odd stage `k`, a change of variables with `ϖ^(k+2) ∣ r` preserves the test
`ϖ^(2k+5) ∣ b₆`. -/
private theorem pow_dvd_b₆_smul_iff {k : ℕ} {C : VariableChange R} (h : IsTateOddStage ϖ k W)
    (hr : ϖ ^ (k + 2) ∣ C.r) : ϖ ^ (2 * k + 5) ∣ (C • W).b₆ ↔ ϖ ^ (2 * k + 5) ∣ W.b₆ := by
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, -, ⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, -⟩ := isTateOddStage_iff.1 h
  obtain ⟨r₁, hr₁⟩ := hr
  refine (C.u⁻¹.isUnit.pow 6).dvd_iff_of_eq_mul_add (2 * r₁ * (x₁ * x₃ + 2 * x₄) +
    r₁ ^ 2 * (ϖ * x₁ ^ 2 + 4 * x₂) + 4 * ϖ ^ (k + 1) * r₁ ^ 3) ?_
  rw [variableChange_b₆, b₄, b₂, hr₁, hx₁, hx₂, hx₃, hx₄]
  ring

/-- At the even stage `k`, a change of variables with `ϖ^(k+2) ∣ r`, `ϖ ∣ s` and `ϖ^(k+3) ∣ t`
preserves the test `ϖ^(2k+7) ∣ a₄² - 4 a₂ a₆`. -/
private theorem pow_dvd_discrim_smul_iff {k : ℕ} {C : VariableChange R}
    (h : IsTateEvenStage ϖ k W) (hr : ϖ ^ (k + 2) ∣ C.r) (hs : ϖ ∣ C.s)
    (ht : ϖ ^ (k + 3) ∣ C.t) :
    ϖ ^ (2 * k + 7) ∣ discrim (C • W).a₂ (C • W).a₄ (C • W).a₆ ↔
      ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆ := by
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, -, ⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, ⟨x₆, hx₆⟩⟩ := isTateEvenStage_iff.1 h
  obtain ⟨ρ, hρ⟩ := hr
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht
  -- Up to units, `C • W` has `a₂ = ϖ (x₂ + ϖ e₂)`, `a₄ = ϖ^(k+3) (x₄ + 2 ρ x₂ + ϖ e₄)` and
  -- `a₆ = ϖ^(2k+5) (x₆ + ρ x₄ + ρ² x₂ + ϖ e₆)`, where `e₂`, `e₄` and `e₆` are the factors below.
  obtain ⟨e₂, he₂⟩ : ∃ e, e = -(σ * x₁) + 3 * ϖ ^ k * ρ - σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨e₄, he₄⟩ : ∃ e, e = -(σ * x₃) - (τ + ρ * σ) * x₁ + 3 * ϖ ^ k * ρ ^ 2 - 2 * σ * τ :=
    ⟨_, rfl⟩
  obtain ⟨e₆, he₆⟩ : ∃ e, e = ϖ ^ k * ρ ^ 3 - τ * x₃ - τ ^ 2 - ρ * τ * x₁ := ⟨_, rfl⟩
  refine (C.u⁻¹.isUnit.pow 8).dvd_iff_of_eq_mul_add (2 * (x₄ + 2 * ρ * x₂) * e₄ + ϖ * e₄ ^ 2 -
    4 * x₂ * e₆ - 4 * e₂ * (x₆ + ρ * x₄ + ρ ^ 2 * x₂) - 4 * ϖ * e₂ * e₆) ?_
  rw [discrim, discrim, variableChange_a₂, variableChange_a₄, variableChange_a₆, hx₁, hx₂, hx₃, hx₄,
    hx₆, hρ, hσ, hτ, he₂, he₄, he₆]
  ring

/-- If Tate's algorithm stops on `W` with `Iₙ*`, `n ≥ 1`, the subprocedure of Step 7 reaches its
stage `n - 1` on `W` and fails the test of that stage. -/
private theorem IsTateTerminal.starStage {n : ℕ} (h : W.IsTateTerminal ϖ (.IStar (n + 1))) :
    StarStage ϖ n W ∧ ¬ StarTest ϖ n W := by
  rcases isTateTerminal_IStar_add_one.1 h with ⟨k, rfl, hk, ht⟩ | ⟨k, rfl, hk, ht⟩
  · exact ⟨starStage_two_mul.2 hk, starTest_two_mul.not.2 ht⟩
  · exact ⟨starStage_two_mul_add_one.2 hk, starTest_two_mul_add_one.not.2 ht⟩

end CommRing

section DiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  {W : WeierstrassCurve R}

/-- The test separating the double-root branch (Step 7) from the triple-root branch (Step 8) is the
residue-cubic test `b² = 3c`: if `a₂ = ϖ A₂` and `a₄ = ϖ² A₄`, then `ϖ³ ∣ a₂² - 3 a₄` exactly when
`A₂² - 3 A₄` vanishes in the residue field. -/
private theorem pow_three_dvd_sq_sub_iff (hϖ : Irreducible ϖ) {A₂ A₄ : R} (hA₂ : W.a₂ = ϖ * A₂)
    (hA₄ : W.a₄ = ϖ ^ 2 * A₄) :
    ϖ ^ 3 ∣ W.a₂ ^ 2 - 3 * W.a₄ ↔ residue R A₂ ^ 2 - 3 * residue R A₄ = 0 := by
  rw [hA₂, hA₄, show (ϖ * A₂) ^ 2 - 3 * (ϖ ^ 2 * A₄) = ϖ ^ 2 * (A₂ ^ 2 - 3 * A₄) by ring,
    pow_succ, mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ.ne_zero), ← hϖ.residue_eq_zero_iff_dvd]
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
    hϖ.prime.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := 1)
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
  have hres : residue R ϖ = 0 := (hϖ.residue_eq_zero_iff_dvd ϖ).2 dvd_rfl
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
  have hres : residue R ϖ = 0 := (hϖ.residue_eq_zero_iff_dvd ϖ).2 dvd_rfl
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
  have hres : residue R ϖ = 0 := (hϖ.residue_eq_zero_iff_dvd ϖ).2 dvd_rfl
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
      rw [ne_eq, hϖ.residue_eq_zero_iff_dvd]
      rintro ⟨B, rfl⟩
      exact h₂' ⟨B, by rw [hA₂]; ring⟩
    simpa [hres] using this

/-- An equation with `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`, `ϖ⁴ ∣ a₄` and `ϖ⁵ ∣ a₆`, the normal form of
Step 10, reaches the test of `II*`. -/
private theorem tateContext_nine_of_pow_dvd (hϖ : Irreducible ϖ) (h₁ : ϖ ∣ W.a₁)
    (h₂ : ϖ ^ 2 ∣ W.a₂) (h₃ : ϖ ^ 3 ∣ W.a₃) (h₄ : ϖ ^ 4 ∣ W.a₄) (h₆ : ϖ ^ 5 ∣ W.a₆) :
    TateContext ϖ 9 W := by
  have hp (n : ℕ) {x : R} (h : ϖ ^ (n + 1) ∣ x) : ϖ ∣ x := (dvd_pow_self ϖ n.succ_ne_zero).trans h
  have hle {m n : ℕ} (hmn : m ≤ n) {x : R} (h : ϖ ^ n ∣ x) : ϖ ^ m ∣ x :=
    (pow_dvd_pow ϖ hmn).trans h
  have ht := tateTest_of_stepSix h₁ (hp 1 h₂) (hle (by omega) h₃) (hle (by omega) h₄)
    (hle (by omega) h₆)
  have ht' := tateTest_five_six_of_stepEight hϖ h₂ (hle (by omega) h₄) (hle (by omega) h₆)
  refine ⟨fun k hk ↦ ?_, fun _ ↦ ⟨hp 2 h₃, hp 3 h₄, hp 4 h₆⟩,
    fun _ ↦ ⟨h₁, hp 1 h₂, hle (by omega) h₃, hle (by omega) h₄, hle (by omega) h₆⟩,
    fun _ ↦ ⟨h₂, hle (by omega) h₄, hle (by omega) h₆⟩, fun _ ↦ ⟨h₃, h₆⟩⟩
  rcases lt_or_ge k 5 with hk5 | hk5
  · exact ht k hk5
  · interval_cases k
    exacts [ht'.1, ht'.2, tateTest_seven_of_stepNine h₃ h₆, h₄]

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
    obtain ⟨h₁, h₂, h₃, h₄, h₆, h₆'⟩ := isTateTerminal_IIStar.1 h
    exact ⟨tateContext_nine_of_pow_dvd hϖ h₁ h₂ h₃ h₄ h₆, h₆'⟩

/-- **Each test of Tate's algorithm is invariant under changes of variables over `R`** between
equations on which the algorithm reaches it. -/
private theorem tateTest_smul (hϖ : Irreducible ϖ) (C : VariableChange R) {i : ℕ}
    (h : TateContext ϖ i W) (h' : TateContext ϖ i (C • W)) (ht : tateTest ϖ W i) :
    tateTest ϖ (C • W) i := by
  have hv (n : ℕ) : IsUnit ((↑C.u⁻¹ : R) ^ n) := C.u⁻¹.isUnit.pow n
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
    have hres : residue R ϖ = 0 := (hϖ.residue_eq_zero_iff_dvd ϖ).2 dvd_rfl
    have hA (n : ℕ) (A y : R) (hA : ϖ ^ (n + 1) * A = ϖ ^ (n + 2) * y) : residue R A = 0 := by
      rw [mul_left_cancel₀ (pow_ne_zero (n + 1) hϖ0) (hA.trans (by ring) :
        _ = ϖ ^ (n + 1) * (ϖ * y))]
      simp [hres]
    rw [hA 0 A₂ y₂ (by linear_combination hA₂.symm.trans hy₂),
      hA 1 A₄ y₄ (by linear_combination hA₄.symm.trans hy₄),
      hA 2 A₆ y₆ (by linear_combination hA₆.symm.trans hy₆),
      hA 2 B₆ y₆' (by linear_combination hB₆.symm.trans hy₆')] at e₆
    obtain ⟨r₂, rfl⟩ : ϖ ∣ r₁ := by
      rw [← hϖ.residue_eq_zero_iff_dvd]
      simpa [(C.u⁻¹.isUnit.map (residue R)).ne_zero] using e₆.symm
    exact ⟨r₂, by rw [hr]; ring⟩
  -- From the test of `III*` on, both equations are in the normal form of Step 9, so `ϖ³ ∣ t`.
  have ht₃ (hi : 8 ≤ i) : ϖ ^ 3 ∣ C.t := by
    obtain ⟨r₂, hr₂⟩ := hr (by omega)
    obtain ⟨-, -, ⟨t₁, ht₁⟩⟩ := hst (by omega)
    obtain ⟨⟨x₁, hx₁⟩, -, -, -, -⟩ := h.2.2.1 (by omega)
    obtain ⟨⟨y₂, hy₂⟩, ⟨y₄, hy₄⟩, -⟩ := h.2.2.2.1 (by omega)
    obtain ⟨⟨z₃, hz₃⟩, ⟨z₆, hz₆⟩⟩ := h.2.2.2.2 hi
    obtain ⟨-, h₆'⟩ := h'.2.2.2.2 hi
    rw [variableChange_a₆, (hv 6).dvd_mul_left] at h₆'
    obtain ⟨e₆, he₆⟩ := h₆'
    refine hϖ.prime.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := 2)
      ⟨z₆ + r₂ * y₄ + ϖ * r₂ ^ 2 * y₂ + ϖ * r₂ ^ 3 - t₁ * z₃ - r₂ * t₁ * x₁ - e₆, ?_⟩
    rw [hr₂, hx₁, hy₂, hy₄, hz₃, hz₆, ht₁] at he₆
    rw [ht₁]
    linear_combination -he₆
  match i, h, h', ht with
  | 0, _, _, ht =>
    simp only [tateTest] at ht ⊢
    rw [variableChange_Δ]
    exact dvd_mul_of_dvd_right ht _
  | 1, _, _, ht =>
    obtain ⟨⟨r₁, hr₁⟩, -⟩ := hrt le_rfl
    exact ((hv 2).dvd_iff_of_eq_mul_add (12 * r₁) (by rw [variableChange_b₂, hr₁]; ring)).2 ht
  | 2, h, _, ht =>
    obtain ⟨⟨r₁, hr₁⟩, ⟨t₁, ht₁⟩⟩ := hrt (by norm_num)
    obtain ⟨⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, -⟩ := h.2.1 (by norm_num)
    refine ((hv 6).dvd_iff_of_eq_mul_add (r₁ * x₄ + r₁ ^ 2 * W.a₂ + ϖ * r₁ ^ 3 - t₁ * x₃ -
      t₁ ^ 2 - r₁ * t₁ * W.a₁) ?_).2 ht
    rw [variableChange_a₆, hr₁, ht₁, hx₃, hx₄]
    ring
  | 3, h, _, ht =>
    obtain ⟨⟨r₁, hr₁⟩, -⟩ := hrt (by norm_num)
    obtain ⟨⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, -⟩ := h.2.1 (by norm_num)
    obtain ⟨β₂, hβ₂⟩ : ϖ ∣ W.b₂ := h.1 1 (by norm_num)
    obtain ⟨y₆, hy₆⟩ : ϖ ^ 2 ∣ W.a₆ := h.1 2 (by norm_num)
    refine ((hv 8).dvd_iff_of_eq_mul_add (3 * r₁ * (x₃ ^ 2 + 4 * y₆) +
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
    obtain ⟨β₄, hβ₄⟩ : ϖ ^ 2 ∣ W.b₄ :=
      hϖ.prime.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := 1)
        ⟨β₂ * (x₃ ^ 2 + 4 * y₆) - 4 * β₈, by
          linear_combination W.b_relation + W.b₂ * hb₆ + ϖ ^ 2 * (x₃ ^ 2 + 4 * y₆) * hβ₂ -
            4 * hβ₈⟩
    refine ((hv 6).dvd_iff_of_eq_mul_add (2 * r₁ * β₄ + r₁ ^ 2 * β₂ + 4 * r₁ ^ 3) ?_).2 ht
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
    refine ((hv 6).dvd_iff_of_eq_mul_add (2 * r₂ * (x₁ * x₃ + 2 * y₄) +
      ϖ * r₂ ^ 2 * (x₁ ^ 2 + 4 * y₂) + 4 * ϖ * r₂ ^ 3) ?_).2 ht
    rw [variableChange_b₆, hr₂, b₄, b₂, hx₁, hx₃, hy₂, hy₄]
    ring
  | 8, h, _, ht =>
    obtain ⟨r₂, hr₂⟩ := hr (by norm_num)
    obtain ⟨-, ⟨s₁, hs₁⟩, -⟩ := hst (by norm_num)
    obtain ⟨t₃, ht₃⟩ := ht₃ le_rfl
    obtain ⟨⟨x₁, hx₁⟩, -, -, -, -⟩ := h.2.2.1 (by norm_num)
    obtain ⟨⟨y₂, hy₂⟩, -, -⟩ := h.2.2.2.1 (by norm_num)
    obtain ⟨⟨z₃, hz₃⟩, -⟩ := h.2.2.2.2 le_rfl
    refine ((hv 4).dvd_iff_of_eq_mul_add (-(s₁ * z₃) + 2 * r₂ * y₂ - (t₃ + r₂ * s₁) * x₁ +
      3 * r₂ ^ 2 - 2 * s₁ * t₃) ?_).2 ht
    rw [variableChange_a₄, hr₂, hs₁, ht₃, hx₁, hy₂, hz₃]
    ring
  | 9, h, _, ht =>
    obtain ⟨r₂, hr₂⟩ := hr (by norm_num)
    obtain ⟨t₃, ht₃⟩ := ht₃ (by norm_num)
    obtain ⟨⟨x₁, hx₁⟩, -, -, -, -⟩ := h.2.2.1 (by norm_num)
    obtain ⟨⟨y₂, hy₂⟩, -, -⟩ := h.2.2.2.1 (by norm_num)
    obtain ⟨⟨z₃, hz₃⟩, -⟩ := h.2.2.2.2 (by norm_num)
    obtain ⟨y₄, hy₄⟩ : ϖ ^ 4 ∣ W.a₄ := h.1 8 (by norm_num)
    refine ((hv 6).dvd_iff_of_eq_mul_add (r₂ * y₄ + r₂ ^ 2 * y₂ + r₂ ^ 3 - t₃ * z₃ - t₃ ^ 2 -
      r₂ * t₃ * x₁) ?_).2 ht
    rw [variableChange_a₆, hr₂, ht₃, hx₁, hy₂, hy₄, hz₃]
    ring
  | i + 10, _, _, ht => exact ht.elim

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

/-- Between two equations at the odd stage `0`, a change of variables has `ϖ² ∣ r`, `ϖ ∣ s` and
`ϖ² ∣ t`. Both residue cubics are `T² (T + c)`, so the shift `r / ϖ` of `T` reduces to `0`. -/
private theorem dvd_r_s_t_of_isTateOddStage_zero (hϖ : Irreducible ϖ) {C : VariableChange R}
    (h : IsTateOddStage ϖ 0 W) (h' : IsTateOddStage ϖ 0 (C • W)) :
    ϖ ^ 2 ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ 2 ∣ C.t := by
  obtain ⟨h₁, h₂, -, h₃, h₄, h₆⟩ := isTateOddStage_iff.1 h
  obtain ⟨-, h₂', -, h₃', h₄', h₆'⟩ := isTateOddStage_iff.1 h'
  have hle {m n : ℕ} (hmn : m ≤ n) {x : R} (h : ϖ ^ n ∣ x) : ϖ ^ m ∣ x :=
    (pow_dvd_pow ϖ hmn).trans h
  obtain ⟨⟨r₁, hr₁⟩, ⟨s₁, hs₁⟩, ⟨t₁, ht₁⟩⟩ := dvd_r_s_t_of_stepSix hϖ h₁ h₂ h₃
    (hle (by omega) h₄) (hle (by omega) h₆) h₂' h₃' (hle (by omega) h₄') (hle (by omega) h₆')
  rw [variableChange_a₄, (C.u⁻¹.isUnit.pow 4).dvd_mul_left] at h₄'
  rw [variableChange_a₆, (C.u⁻¹.isUnit.pow 6).dvd_mul_left] at h₆'
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  obtain ⟨x₃, hx₃⟩ := h₃
  obtain ⟨x₄, hx₄⟩ := h₄
  obtain ⟨x₆, hx₆⟩ := h₆
  obtain ⟨e₄, he₄⟩ := h₄'
  obtain ⟨e₆, he₆⟩ := h₆'
  rw [hx₁, hx₂, hx₃, hx₄, hr₁, hs₁, ht₁] at he₄
  rw [hx₁, hx₂, hx₃, hx₄, hx₆, hr₁, ht₁] at he₆
  have hϖ0 := hϖ.ne_zero
  -- The coefficients of `T` and `1` in the residue cubic of `C • W`, up to units.
  have k₄ : ϖ ∣ r₁ * (2 * x₂ + 3 * r₁) :=
    ⟨e₄ - x₄ + s₁ * x₃ + (t₁ + r₁ * s₁) * x₁ + 2 * s₁ * t₁,
      mul_left_cancel₀ (pow_ne_zero 2 hϖ0) (by linear_combination he₄)⟩
  have k₆ : ϖ ∣ r₁ ^ 2 * (x₂ + r₁) :=
    ⟨e₆ - x₆ - r₁ * x₄ + t₁ * x₃ + t₁ ^ 2 + r₁ * t₁ * x₁,
      mul_left_cancel₀ (pow_ne_zero 3 hϖ0) (by linear_combination he₆)⟩
  obtain ⟨r₂, rfl⟩ : ϖ ∣ r₁ := by
    by_contra hr
    have a := (hϖ.prime.dvd_or_dvd k₄).resolve_left hr
    have b := (hϖ.prime.dvd_or_dvd k₆).resolve_left fun h ↦ hr (hϖ.prime.dvd_of_dvd_pow h)
    exact hr (by convert dvd_sub a (dvd_mul_of_dvd_right b 2) using 1; ring)
  exact ⟨⟨r₂, by rw [hr₁]; ring⟩, ⟨s₁, hs₁⟩, ⟨t₁, ht₁⟩⟩

/-- Between two equations at the even stage `k`, a change of variables with `ϖ^(k+2) ∣ r` and
`ϖ^(k+2) ∣ t` has `ϖ^(k+3) ∣ t`: the equations for `a₆` give `ϖ^(2k+5) ∣ t²`. -/
private theorem pow_dvd_t_of_isTateEvenStage (hϖ : Irreducible ϖ) {k : ℕ}
    {C : VariableChange R} (h : IsTateEvenStage ϖ k W) (h' : IsTateEvenStage ϖ k (C • W))
    (hr : ϖ ^ (k + 2) ∣ C.r) (ht : ϖ ^ (k + 2) ∣ C.t) : ϖ ^ (k + 3) ∣ C.t := by
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, -, ⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, ⟨x₆, hx₆⟩⟩ := isTateEvenStage_iff.1 h
  obtain ⟨-, -, -, -, -, h₆'⟩ := isTateEvenStage_iff.1 h'
  obtain ⟨r₁, hr₁⟩ := hr
  obtain ⟨t₁, ht₁⟩ := ht
  rw [variableChange_a₆, (C.u⁻¹.isUnit.pow 6).dvd_mul_left] at h₆'
  obtain ⟨e₆, he₆⟩ := h₆'
  rw [hx₁, hx₂, hx₃, hx₄, hx₆, hr₁, ht₁] at he₆
  refine hϖ.prime.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := k + 2)
    ⟨x₆ + r₁ * x₄ + r₁ ^ 2 * x₂ + ϖ ^ (k + 1) * r₁ ^ 3 - t₁ * x₃ - r₁ * t₁ * x₁ - e₆, ?_⟩
  rw [ht₁]
  linear_combination -he₆

/-- Between two equations at the odd stage `k + 1`, a change of variables with `ϖ^(k+2) ∣ r` and
`ϖ^(k+3) ∣ t` has `ϖ^(k+3) ∣ r`: the equations for `a₆` give `ϖ^(2k+6) ∣ r² a₂`, and `ϖ ∥ a₂`. -/
private theorem pow_dvd_r_of_isTateOddStage_succ (hϖ : Irreducible ϖ) {k : ℕ}
    {C : VariableChange R} (h : IsTateOddStage ϖ (k + 1) W)
    (h' : IsTateOddStage ϖ (k + 1) (C • W)) (hr : ϖ ^ (k + 2) ∣ C.r)
    (ht : ϖ ^ (k + 3) ∣ C.t) : ϖ ^ (k + 3) ∣ C.r := by
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, h₂', ⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩, ⟨x₆, hx₆⟩⟩ := isTateOddStage_iff.1 h
  obtain ⟨-, -, -, -, -, h₆'⟩ := isTateOddStage_iff.1 h'
  obtain ⟨r₁, hr₁⟩ := hr
  obtain ⟨t₁, ht₁⟩ := ht
  rw [variableChange_a₆, (C.u⁻¹.isUnit.pow 6).dvd_mul_left] at h₆'
  obtain ⟨e₆, he₆⟩ := h₆'
  rw [hx₁, hx₂, hx₃, hx₄, hx₆, hr₁, ht₁] at he₆
  have hx₂' : ¬ ϖ ∣ x₂ := fun ⟨y, hy⟩ ↦ h₂' ⟨y, by rw [hx₂, hy]; ring⟩
  refine hϖ.prime.pow_succ_dvd_of_pow_mul_add_one_dvd_pow (n := 2) (k := k + 2)
    (hϖ.prime.pow_dvd_of_dvd_mul_right _ hx₂'
      ⟨e₆ - x₆ - r₁ * x₄ - ϖ ^ k * r₁ ^ 3 + t₁ * x₃ + t₁ ^ 2 + r₁ * t₁ * x₁, ?_⟩)
  apply mul_left_cancel₀ hϖ.ne_zero
  rw [hr₁]
  linear_combination he₆

/-- **The bounds on a change of variables between two equations at the same stage.** At the odd
stage `k` it has `ϖ^(k+2) ∣ r`, `ϖ ∣ s` and `ϖ^(k+2) ∣ t`; at the even stage `k` moreover
`ϖ^(k+3) ∣ t`. -/
private theorem dvd_r_s_t_of_isTateStage (hϖ : Irreducible ϖ) {C : VariableChange R} (k : ℕ) :
    (IsTateOddStage ϖ k W → IsTateOddStage ϖ k (C • W) →
      ϖ ^ (k + 2) ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ (k + 2) ∣ C.t) ∧
    (IsTateEvenStage ϖ k W → IsTateEvenStage ϖ k (C • W) →
      ϖ ^ (k + 2) ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ (k + 3) ∣ C.t) := by
  -- The even stage `k` lies inside the odd stage `k`.
  have heven (k : ℕ) (hodd : IsTateOddStage ϖ k W → IsTateOddStage ϖ k (C • W) →
      ϖ ^ (k + 2) ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ (k + 2) ∣ C.t) (h : IsTateEvenStage ϖ k W)
      (h' : IsTateEvenStage ϖ k (C • W)) :
      ϖ ^ (k + 2) ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ (k + 3) ∣ C.t := by
    obtain ⟨hr, hs, ht⟩ :=
      hodd h.isTateOddStage_and_pow_dvd_b₆.1 h'.isTateOddStage_and_pow_dvd_b₆.1
    exact ⟨hr, hs, pow_dvd_t_of_isTateEvenStage hϖ h h' hr ht⟩
  induction k with
  | zero =>
    have hodd := dvd_r_s_t_of_isTateOddStage_zero (W := W) (C := C) hϖ
    exact ⟨hodd, heven 0 hodd⟩
  | succ k ih =>
    -- The odd stage `k + 1` lies inside the even stage `k`.
    have hodd (h : IsTateOddStage ϖ (k + 1) W) (h' : IsTateOddStage ϖ (k + 1) (C • W)) :
        ϖ ^ (k + 1 + 2) ∣ C.r ∧ ϖ ∣ C.s ∧ ϖ ^ (k + 1 + 2) ∣ C.t := by
      obtain ⟨hr, hs, ht⟩ := ih.2 h.isTateEvenStage_and_pow_dvd_discrim.1
        h'.isTateEvenStage_and_pow_dvd_discrim.1
      exact ⟨pow_dvd_r_of_isTateOddStage_succ hϖ h h' hr ht, hs, ht⟩
    exact ⟨hodd, heven (k + 1) hodd⟩

/-- Between two equations at stage `n` of the `Iₙ*` subprocedure, a change of variables preserves
the test of that stage. -/
private theorem starTest_smul_iff (hϖ : Irreducible ϖ) {C : VariableChange R} {n : ℕ}
    (h : StarStage ϖ n W) (h' : StarStage ϖ n (C • W)) :
    StarTest ϖ n (C • W) ↔ StarTest ϖ n W := by
  obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
  · rw [starStage_two_mul] at h h'
    rw [starTest_two_mul, starTest_two_mul]
    exact pow_dvd_b₆_smul_iff h ((dvd_r_s_t_of_isTateStage hϖ k).1 h h').1
  · rw [starStage_two_mul_add_one] at h h'
    rw [starTest_two_mul_add_one, starTest_two_mul_add_one]
    obtain ⟨hr, hs, ht⟩ := (dvd_r_s_t_of_isTateStage hϖ k).2 h h'
    exact pow_dvd_discrim_smul_iff h hr hs ht

/-- If Tate's algorithm stops on `W` with `Iₙ*` and on `C • W` with `Iₘ*`, `n, m ≥ 1`, then
`m ≤ n`: otherwise `C • W` would reach stage `n` of the subprocedure of Step 7 and pass its test,
which `W` fails. -/
private theorem IsTateTerminal.le_of_IStar_of_smul (hϖ : Irreducible ϖ) {C : VariableChange R}
    {n m : ℕ} (h : W.IsTateTerminal ϖ (.IStar (n + 1)))
    (h' : (C • W).IsTateTerminal ϖ (.IStar (m + 1))) : m ≤ n := by
  by_contra! hnm
  obtain ⟨hs, ht⟩ := h.starStage
  obtain ⟨hs', ht'⟩ := (h'.starStage.1.mono (Nat.succ_le_of_lt hnm)).succ
  exact ht ((starTest_smul_iff hϖ hs hs').1 ht')

/-- **The output of Tate's algorithm does not depend on the changes of variables.** If the
algorithm stops on `W` with a symbol `s`, and on `C • W`, for a change of variables `C` over `R`,
with a symbol `s'`, then `s' = s`. -/
theorem IsTateTerminal.eq_of_smul (hϖ : Irreducible ϖ) {C : VariableChange R}
    {s s' : ReductionSymbol} (h : W.IsTateTerminal ϖ s) (h' : (C • W).IsTateTerminal ϖ s') :
    s' = s := by
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
    obtain rfl : m = n := by omega
    rfl
  · -- At `Iₙ*` the index is the stage at which the subprocedure of Step 7 stops.
    have h₀ : (C⁻¹ • C • W).IsTateTerminal ϖ (.IStar (n + 1)) := by rwa [inv_smul_smul]
    rw [le_antisymm (h.le_of_IStar_of_smul hϖ h') (h'.le_of_IStar_of_smul hϖ h₀)]

/-- An equation with `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`, `ϖ⁴ ∣ a₄` and `ϖ⁶ ∣ a₆`, on which Tate's
algorithm would go on to Step 11, passes every test. -/
private theorem tateContext_ten_of_pow_dvd (hϖ : Irreducible ϖ) (h₁ : ϖ ∣ W.a₁)
    (h₂ : ϖ ^ 2 ∣ W.a₂) (h₃ : ϖ ^ 3 ∣ W.a₃) (h₄ : ϖ ^ 4 ∣ W.a₄) (h₆ : ϖ ^ 6 ∣ W.a₆) :
    TateContext ϖ 10 W := by
  have hc := tateContext_nine_of_pow_dvd hϖ h₁ h₂ h₃ h₄ ((pow_dvd_pow ϖ (by omega)).trans h₆)
  refine ⟨fun k hk ↦ ?_, fun _ ↦ hc.2.1 (by omega), fun _ ↦ hc.2.2.1 (by omega),
    fun _ ↦ hc.2.2.2.1 (by omega), fun _ ↦ hc.2.2.2.2 (by omega)⟩
  rcases lt_or_ge k 9 with hk9 | hk9
  · exact hc.1 k hk9
  · obtain rfl : k = 9 := by omega
    exact h₆

/-- If Tate's algorithm stops on `W`, no change of variables over `R` carries `W` to an equation
on which it would go on to Step 11. -/
private theorem IsTateTerminal.not_pow_dvd_smul (hϖ : Irreducible ϖ) {s : ReductionSymbol}
    (h : W.IsTateTerminal ϖ s) (C : VariableChange R) :
    ¬ (ϖ ∣ (C • W).a₁ ∧ ϖ ^ 2 ∣ (C • W).a₂ ∧ ϖ ^ 3 ∣ (C • W).a₃ ∧ ϖ ^ 4 ∣ (C • W).a₄ ∧
      ϖ ^ 6 ∣ (C • W).a₆) := by
  rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
  obtain ⟨hc, hn⟩ := h.tateContext hϖ
  have hc' := tateContext_ten_of_pow_dvd hϖ h₁ h₂ h₃ h₄ h₆
  have hlt : chainIndex s < 10 := by
    rcases s with (_ | _) | _ | _ | _ | (_ | _) | _ | _ | _ <;> simp [chainIndex]
  have hc₀ : TateContext ϖ (chainIndex s) (C⁻¹ • C • W) := by rwa [inv_smul_smul]
  have ht := tateTest_smul hϖ C⁻¹ (hc'.mono hlt.le) hc₀ (hc'.1 _ hlt)
  rw [inv_smul_smul] at ht
  exact hn ht

section Minimality

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Tate's algorithm only stops on minimal equations.** If the algorithm stops on an equation
`W` over `R`, with any symbol, then the base change of `W` to the fraction field is minimal over
`R`. -/
theorem IsTateTerminal.isMinimal_baseChange (hϖ : Irreducible ϖ) {s : ReductionSymbol}
    (h : W.IsTateTerminal ϖ s) : IsMinimal R (W.baseChange K) := by
  by_contra hmin
  obtain ⟨r, s', t, hC⟩ := exists_variableChange_pow_dvd_a₁_a₂_a₃_a₄_a₆_of_not_isMinimal hϖ W hmin
  exact h.not_pow_dvd_smul hϖ _ hC

/-- **Tate's algorithm decides minimality.** Over a discrete valuation ring with perfect residue
field, an equation over `R` with nonzero discriminant is minimal over the fraction field exactly
when some change of variables over `R` carries it to an equation on which the algorithm stops. -/
theorem isMinimal_baseChange_iff_exists_isTateTerminal [PerfectField (ResidueField R)]
    (hϖ : Irreducible ϖ) (hΔ : W.Δ ≠ 0) :
    IsMinimal R (W.baseChange K) ↔
      ∃ (C : VariableChange R) (s : ReductionSymbol), (C • W).IsTateTerminal ϖ s := by
  refine ⟨fun _ ↦ exists_isTateTerminal (K := K) hϖ W hΔ, fun ⟨C, s, h⟩ ↦ ?_⟩
  have := h.isMinimal_baseChange (K := K) hϖ
  rw [← inv_smul_smul C W, ← baseChange_smul_baseChange]
  infer_instance

end Minimality

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
symbol. -/
theorem IsTateTerminal.eq_of_isMinimal_smul (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (D : VariableChange K) (hD : D • W₁.baseChange K = W₂.baseChange K) {s₁ s₂ : ReductionSymbol}
    (h₁ : W₁.IsTateTerminal ϖ s₁) (h₂ : W₂.IsTateTerminal ϖ' s₂) : s₂ = s₁ := by
  obtain ⟨C, rfl⟩ := exists_smul_eq_of_isMinimal_smul D hD
  exact h₁.eq_of_smul hϖ
    ((isTateTerminal_iff_of_associated (associated_of_irreducible R hϖ hϖ')).2 h₂)

end MinimalModel

end DiscreteValuationRing

end WeierstrassCurve

end
