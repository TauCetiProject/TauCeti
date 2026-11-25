/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Isolating

/-!
# The finite model of a quadratic correction under a small forcing

A gluing construction reduces a nonlinear elliptic equation to a finite-dimensional one. Over a
manifold `M` of finite parameters `p`, the infinite-dimensional part of the equation is the
complementary equation

`e p + D p x + N p x = 0`

of `TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic`: `D p` has a right inverse `Q p`
of norm at most `C`, the remainder `N p` is quadratic with constant `L` on the ball of radius `δ`,
and the residual satisfies `‖e p‖ ≤ ε`, `2 C² L ε < 1 / 4` and `2 C ε < δ / 4`. Its unique small
solution `x₀ p` in the range of `Q p` is inserted into a section `φ₀ p : X → F` with values in a
finite-dimensional space of the dimension of `M`, and the solutions of the full equation are the
zeros of the reduced section `p ↦ φ₀ p (x₀ p)`. They are counted by its local degree on an
isolating open set `U ⊆ M`, which needs a boundary margin `b ≤ ‖φ₀ p (x₀ p)‖` on the frontier
of `U` (`TauCeti.HomologicalOrientation.exists_pos_forall_localDegree_restrict_eq`).

A small forcing then perturbs everything at once (Taubes adds a curvature perturbation `ρ` of
size `t = ‖ρ‖`): it adds `g p` with `‖g p‖ ≤ B_c t` to the complementary equation, whose solution
becomes `x p`, it changes the section directly by at most `B_φ t`, and a second parameter (the
coefficients of the point sections) moves the section by at most `H`. This file shows that the
count survives, under an explicit tolerance on `t` that depends on the constants `C, L, δ, b` of
the unforced problem and on a constant `B` dominating the forcing budgets `B_c` and
`B_φ + 2 C K B_c`.

**The tolerance.** `TauCeti.IsForcingTolerance C L B δ b τ` records the three budgets

`16 C² L (1 + B) τ ≤ 1`,  `8 C (1 + B) τ ≤ δ`,  `4 (1 + B) τ ≤ b`,

for a constant `B` dominating the forcing of the complementary equation and of the section. For
`0 ≤ t < τ` the forced residual `ε + B τ` keeps the contraction constant below `3 / 8`
(`TauCeti.IsForcingTolerance.two_mul_sq_mul_mul_add_mul_lt`), the radius `2 C (ε + B τ)` of the
forced correction inside the uniqueness ball `min (δ / 2) (2 C L)⁻¹`
(`TauCeti.IsForcingTolerance.two_mul_mul_add_mul_lt_min`), and the forcing of the section below a
quarter of the margin, `B t < b / 4` (`TauCeti.IsForcingTolerance.mul_lt_div_four`). The
minimum of the three bounds is a tolerance (`TauCeti.isForcingTolerance_min`), and every smaller
nonnegative number is again one (`TauCeti.IsForcingTolerance.mono`). The factor `1 + B`
is what controls the forcing when `B` is large; the existence of the forced correction itself is
`TauCeti.exists_continuousOn_forall_add_add_add_eq_zero`.

**The forcing budget.** The forced correction moves by at most `2 C ‖g p‖`, so if the unforced
section `ψ p` with the new coefficients is `K`-Lipschitz on the ball of radius `δ` and
`B_φ + 2 C K B_c ≤ B`, the forced section differs from the reference section by less than
`B t + H < b / 2` (`TauCeti.norm_apply_sub_apply_lt_of_isForcingTolerance`), so it keeps the
margin `b / 2` (`TauCeti.div_two_lt_norm_apply_of_isForcingTolerance`). Inside the
uniqueness ball, the solutions of the forced full equation are exactly the zeros of the forced
reduced section, at the forced correction
(`TauCeti.add_add_add_eq_zero_and_apply_eq_zero_iff_of_isForcingTolerance`).

**The count.** Since these estimates hold on the frontier of an isolating `U`, the local degree on
`U` of the forced reduced section is that of the reference section
(`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_isForcingTolerance`); for this, the
hypotheses are only needed on the frontier of `U`. When this count is nonzero and the continuous
map agrees with the forced reduced section on all of `U`, the forced reduced section has a zero
in `U` (`TauCeti.HomologicalOrientation.exists_mem_apply_eq_zero_of_isForcingTolerance`).

## Main declarations

* `TauCeti.IsForcingTolerance`: the three budgets of a forcing tolerance.
* `TauCeti.isForcingTolerance_min`: the explicit tolerance.
* `TauCeti.norm_apply_sub_apply_lt_of_isForcingTolerance`: the forced section stays within half
  the margin of the reference section.
* `TauCeti.add_add_add_eq_zero_and_apply_eq_zero_iff_of_isForcingTolerance`: solutions of the
  forced equation near the origin are zeros of the forced reduced section.
* `TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_isForcingTolerance`: the count of
  the forced finite model is the unforced count.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
* K. Deimling, *Nonlinear Functional Analysis*, Springer, 1985, Chapter 1, Theorem 3.1 (the
  degree on bounded open sets under small perturbations).
-/

public section

open Metric Module Set TopologicalSpace
open scoped NNReal

namespace TauCeti

/-! ### The forcing tolerance -/

/-- A **forcing tolerance** `τ` for a quadratic correction with right-inverse bound `C`, quadratic
constant `L` and radius `δ`, a forcing constant `B` and a boundary margin `b`: a nonnegative `τ`
with `16 C² L (1 + B) τ ≤ 1`, `8 C (1 + B) τ ≤ δ` and `4 (1 + B) τ ≤ b`. Forcings of size `t < τ`
then keep the forced correction in the contraction and uniqueness regions of the unforced
problem and keep the forcing term `B t` below `b / 4`, so that under the budgets of
`TauCeti.norm_apply_sub_apply_lt_of_isForcingTolerance` the reduced section moves by less than
`b / 2`. -/
structure IsForcingTolerance (C L B : ℝ≥0) (δ b τ : ℝ) : Prop where
  /-- The tolerance is nonnegative. -/
  nonneg : 0 ≤ τ
  /-- The contraction budget `16 C² L (1 + B) τ ≤ 1`. -/
  sixteen_mul_sq_mul_mul_one_add_mul_le_one : 16 * (C : ℝ) ^ 2 * L * (1 + B) * τ ≤ 1
  /-- The radius budget `8 C (1 + B) τ ≤ δ`. -/
  eight_mul_mul_one_add_mul_le : 8 * (C : ℝ) * (1 + B) * τ ≤ δ
  /-- The boundary budget `4 (1 + B) τ ≤ b`. -/
  four_mul_one_add_mul_le : 4 * (1 + (B : ℝ)) * τ ≤ b

variable {C L B : ℝ≥0} {δ b τ ε : ℝ}

/-- **The explicit forcing tolerance.** For `δ, b ≥ 0`, the minimum of `(16 C² L (1 + B))⁻¹`,
`δ / (8 C (1 + B))` and `b / (4 (1 + B))` is a forcing tolerance; by
`TauCeti.IsForcingTolerance.mono`, so is every smaller nonnegative number. -/
theorem isForcingTolerance_min (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    IsForcingTolerance C L B δ b
      (min (min (16 * (C : ℝ) ^ 2 * L * (1 + B))⁻¹ (δ / (8 * C * (1 + B))))
        (b / (4 * (1 + B)))) := by
  set k : ℝ := 16 * (C : ℝ) ^ 2 * L * (1 + B)
  set m : ℝ := 8 * (C : ℝ) * (1 + B)
  set w : ℝ := 4 * (1 + (B : ℝ))
  have hk : 0 ≤ k := by positivity
  have hm : 0 ≤ m := by positivity
  have hw : 0 < w := by positivity
  set τ := min (min k⁻¹ (δ / m)) (b / w)
  have hτk : τ ≤ k⁻¹ := (min_le_left _ _).trans (min_le_left _ _)
  have hτm : τ ≤ δ / m := (min_le_left _ _).trans (min_le_right _ _)
  have hτw : τ ≤ b / w := min_le_right _ _
  refine ⟨le_min (le_min (inv_nonneg.2 hk) (div_nonneg hδ hm)) (div_nonneg hb hw.le), ?_, ?_, ?_⟩
  · refine (mul_le_mul_of_nonneg_left hτk hk).trans ?_
    rcases hk.eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
      exact zero_le_one
    · rw [mul_inv_cancel₀ hpos.ne']
  · refine (mul_le_mul_of_nonneg_left hτm hm).trans ?_
    rcases hm.eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
      exact hδ
    · exact (mul_div_cancel₀ δ hpos.ne').le
  · exact (mul_le_mul_of_nonneg_left hτw hw.le).trans (mul_div_cancel₀ b hw.ne').le

namespace IsForcingTolerance

/-- A nonnegative number below a forcing tolerance is a forcing tolerance. -/
theorem mono (h : IsForcingTolerance C L B δ b τ) {τ' : ℝ} (h₀ : 0 ≤ τ') (hτ' : τ' ≤ τ) :
    IsForcingTolerance C L B δ b τ' where
  nonneg := h₀
  sixteen_mul_sq_mul_mul_one_add_mul_le_one := (mul_le_mul_of_nonneg_left hτ' (by positivity)).trans
    h.sixteen_mul_sq_mul_mul_one_add_mul_le_one
  eight_mul_mul_one_add_mul_le := (mul_le_mul_of_nonneg_left hτ' (by positivity)).trans
    h.eight_mul_mul_one_add_mul_le
  four_mul_one_add_mul_le := (mul_le_mul_of_nonneg_left hτ' (by positivity)).trans
    h.four_mul_one_add_mul_le

/-- **The forced contraction constant.** If the unforced residual satisfies `2 C² L ε < 1 / 4`,
the forced residual `ε + B τ` satisfies `2 C² L (ε + B τ) < 3 / 8`: the budget
`16 C² L (1 + B) τ ≤ 1` gives `2 C² L B τ ≤ 1 / 8`. -/
theorem two_mul_sq_mul_mul_add_mul_lt (h : IsForcingTolerance C L B δ b τ)
    (hε : 2 * (C : ℝ) ^ 2 * L * ε < 1 / 4) : 2 * (C : ℝ) ^ 2 * L * (ε + B * τ) < 3 / 8 := by
  have h₁ := h.sixteen_mul_sq_mul_mul_one_add_mul_le_one
  have : (0 : ℝ) ≤ (C : ℝ) ^ 2 * L * τ := mul_nonneg (by positivity) h.nonneg
  nlinarith

/-- **The forced radius.** If the unforced residual satisfies `2 C ε < δ / 4`, the radius of the
forced correction satisfies `2 C (ε + B τ) < δ / 2`. -/
theorem two_mul_mul_add_mul_lt_div_two (h : IsForcingTolerance C L B δ b τ)
    (hεδ : 2 * (C : ℝ) * ε < δ / 4) : 2 * (C : ℝ) * (ε + B * τ) < δ / 2 := by
  have h₁ := h.eight_mul_mul_one_add_mul_le
  have : (0 : ℝ) ≤ C * τ := mul_nonneg C.coe_nonneg h.nonneg
  nlinarith

/-- **The forced correction lies in the uniqueness ball.** If `C, L > 0` and the unforced residual
satisfies `2 C² L ε < 1 / 4` and `2 C ε < δ / 4`, the radius of the forced correction satisfies
`2 C (ε + B τ) < min (δ / 2) (2 C L)⁻¹`. -/
theorem two_mul_mul_add_mul_lt_min (h : IsForcingTolerance C L B δ b τ) (hC : 0 < C) (hL : 0 < L)
    (hε : 2 * (C : ℝ) ^ 2 * L * ε < 1 / 4) (hεδ : 2 * (C : ℝ) * ε < δ / 4) :
    2 * (C : ℝ) * (ε + B * τ) < min (δ / 2) (2 * C * L)⁻¹ := by
  have hBτ : (B : ℝ) * τ ≤ (1 + B) * τ := by nlinarith [h.nonneg]
  have hCL : (0 : ℝ) ≤ 16 * (C : ℝ) ^ 2 * L := by positivity
  have hC8 : (0 : ℝ) ≤ 8 * (C : ℝ) := by positivity
  refine two_mul_mul_add_lt_min (by exact_mod_cast hC) (by exact_mod_cast hL) hε hεδ ?_ ?_
  · calc 16 * (C : ℝ) ^ 2 * L * (B * τ) ≤ 16 * (C : ℝ) ^ 2 * L * ((1 + B) * τ) :=
          mul_le_mul_of_nonneg_left hBτ hCL
      _ ≤ 1 := by rw [← mul_assoc]; exact h.sixteen_mul_sq_mul_mul_one_add_mul_le_one
  · calc 8 * (C : ℝ) * (B * τ) ≤ 8 * (C : ℝ) * ((1 + B) * τ) := mul_le_mul_of_nonneg_left hBτ hC8
      _ ≤ δ := by rw [← mul_assoc]; exact h.eight_mul_mul_one_add_mul_le

/-- **The forcing of the section stays below a quarter of the margin.** For `0 ≤ t < τ`,
`B t < b / 4`. -/
theorem mul_lt_div_four (h : IsForcingTolerance C L B δ b τ) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht : t < τ) : (B : ℝ) * t < b / 4 := by
  have h₁ := h.four_mul_one_add_mul_le
  have : (B : ℝ) * t ≤ B * τ := mul_le_mul_of_nonneg_left ht.le B.coe_nonneg
  nlinarith

end IsForcingTolerance

/-! ### The forced correction and the reduced section at one parameter -/

section Pointwise

variable {X Y G : Type*} [NormedAddCommGroup X] [SeminormedAddCommGroup Y] [FunLike G Y X]
  [AddMonoidHomClass G Y X] {Q : G} {D N : X → Y} {e g : Y} {Bc : ℝ≥0} {t : ℝ} {x : X}
  (hDQ : ∀ y, D (Q y) = y) (hQ : ∀ y, ‖Q y‖ ≤ C * ‖y‖)
  (hN : ∀ x ∈ closedBall (0 : X) δ, ∀ y ∈ closedBall (0 : X) δ,
    ‖N x - N y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
  (he : ‖e‖ ≤ ε) (hε : 2 * (C : ℝ) ^ 2 * L * ε < 1 / 4) (hεδ : 2 * (C : ℝ) * ε < δ / 4)
  (hτ : IsForcingTolerance C L B δ b τ) (ht₀ : 0 ≤ t) (ht : t < τ) (hg : ‖g‖ ≤ Bc * t)
  (hBc : Bc ≤ B) (hxQ : x ∈ range Q) (hx : ‖x‖ ≤ 2 * C * ‖e + g‖)
  (hxe : e + g + D x + N x = 0)
include he ht₀ ht hg hBc hx

/-- The forced correction has norm at most `2 C (ε + B τ)`. -/
private theorem norm_le_two_mul_mul_add_mul : ‖x‖ ≤ 2 * C * (ε + B * τ) := by
  have hgB : ‖g‖ ≤ B * τ := hg.trans (mul_le_mul (by exact_mod_cast hBc) ht.le ht₀ B.coe_nonneg)
  exact hx.trans (mul_le_mul_of_nonneg_left ((norm_add_le e g).trans (add_le_add he hgB))
    (by positivity))

include hDQ hQ hN hε hεδ hτ hxQ hxe

/-- **The forcing budget of the reduced section.** Let `x` be the forced correction, of norm at
most `2 C ‖e + g‖` in the range of `Q`, and `x₀` the unforced one, of norm at most `2 C ‖e‖`, for a
forcing `‖g‖ ≤ B_c t` with `0 ≤ t < τ` below a forcing tolerance `τ`. Compare the forced section
`φ` with a reference section `φ₀` through the unforced section `ψ` with the same coefficients:
suppose `‖φ x - ψ x‖ ≤ B_φ t`, that `ψ` is `K`-Lipschitz on the ball of radius `δ`, that
`‖ψ x₀ - φ₀ x₀‖ ≤ H < b / 4`, and that `B_c ≤ B` and `B_φ + 2 C K B_c ≤ B`. Then the reduced
sections are within half the margin: `‖φ x - φ₀ x₀‖ < b / 2`. -/
theorem norm_apply_sub_apply_lt_of_isForcingTolerance {x₀ : X} (hx₀Q : x₀ ∈ range Q)
    (hx₀ : ‖x₀‖ ≤ 2 * C * ‖e‖) (hx₀e : e + D x₀ + N x₀ = 0) {F : Type*}
    [SeminormedAddCommGroup F] {φ ψ φ₀ : X → F} {Bφ K : ℝ≥0} {H : ℝ} (hφ : ‖φ x - ψ x‖ ≤ Bφ * t)
    (hψ : LipschitzOnWith K ψ (closedBall 0 δ)) (hH : ‖ψ x₀ - φ₀ x₀‖ ≤ H) (hHb : H < b / 4)
    (hB : Bφ + 2 * C * K * Bc ≤ B) : ‖φ x - φ₀ x₀‖ < b / 2 := by
  -- Both corrections lie in the ball of radius `r = 2 C (ε + B τ)`, inside `δ / 2`, on which
  -- the contraction constant `C L r` is below `3 / 8`.
  set r : ℝ := 2 * C * (ε + B * τ)
  have hrδ : r < δ / 2 := hτ.two_mul_mul_add_mul_lt_div_two hεδ
  have hCLr : C * L * r ≤ 1 / 2 := by
    have := hτ.two_mul_sq_mul_mul_add_mul_lt hε
    have : (C : ℝ) * L * r = 2 * (C : ℝ) ^ 2 * L * (ε + B * τ) := by ring
    linarith
  have hxr : ‖x‖ ≤ r := norm_le_two_mul_mul_add_mul he ht₀ ht hg hBc hx
  have hx₀r : ‖x₀‖ ≤ r :=
    hx₀.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg B.coe_nonneg hτ.nonneg))
        (by positivity)))
  -- The forced correction moves by at most `2 C ‖g‖ ≤ 2 C B_c t`.
  have hxx₀ : ‖x - x₀‖ ≤ 2 * C * (Bc * t) := by
    have h := norm_sub_le_two_mul_mul_norm_sub hDQ hQ hN (e := e + g) (e' := e)
      (by linarith [norm_nonneg x])
      hCLr hxr hx₀r hxQ hxe hx₀Q hx₀e
    rw [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left hg (by positivity))
  have hψx : ‖ψ x - ψ x₀‖ ≤ K * ‖x - x₀‖ := by
    have hmem (z : X) (hz : ‖z‖ ≤ r) : z ∈ closedBall (0 : X) δ :=
      mem_closedBall_zero_iff.2 (by linarith [norm_nonneg z])
    simpa only [dist_eq_norm] using hψ.dist_le_mul x (hmem x hxr) x₀ (hmem x₀ hx₀r)
  have hBt := hτ.mul_lt_div_four ht₀ ht
  have hKt : (K : ℝ) * ‖x - x₀‖ ≤ K * (2 * C * (Bc * t)) :=
    mul_le_mul_of_nonneg_left hxx₀ K.coe_nonneg
  have hBt' : ((Bφ : ℝ) + 2 * C * K * Bc) * t ≤ B * t :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hB) ht₀
  calc ‖φ x - φ₀ x₀‖ ≤ ‖φ x - ψ x‖ + ‖ψ x - φ₀ x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖φ x - ψ x‖ + (‖ψ x - ψ x₀‖ + ‖ψ x₀ - φ₀ x₀‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Bφ * t + (K * (2 * C * (Bc * t)) + H) := by
        gcongr
        exact hψx.trans hKt
    _ < b / 2 := by linarith

/-- **Boundary separation under a forcing.** Under the hypotheses of
`TauCeti.norm_apply_sub_apply_lt_of_isForcingTolerance`, if the reference reduced section has
margin `b ≤ ‖φ₀ x₀‖`, the forced reduced section keeps the margin `b / 2 < ‖φ x‖`. -/
theorem div_two_lt_norm_apply_of_isForcingTolerance {x₀ : X} (hx₀Q : x₀ ∈ range Q)
    (hx₀ : ‖x₀‖ ≤ 2 * C * ‖e‖) (hx₀e : e + D x₀ + N x₀ = 0) {F : Type*}
    [SeminormedAddCommGroup F] {φ ψ φ₀ : X → F} {Bφ K : ℝ≥0} {H : ℝ} (hφ : ‖φ x - ψ x‖ ≤ Bφ * t)
    (hψ : LipschitzOnWith K ψ (closedBall 0 δ)) (hH : ‖ψ x₀ - φ₀ x₀‖ ≤ H) (hHb : H < b / 4)
    (hB : Bφ + 2 * C * K * Bc ≤ B) (hb : b ≤ ‖φ₀ x₀‖) : b / 2 < ‖φ x‖ := by
  have h := norm_apply_sub_apply_lt_of_isForcingTolerance hDQ hQ hN he hε hεδ hτ ht₀ ht hg hBc
    hxQ hx hxe hx₀Q hx₀ hx₀e hφ hψ hH hHb hB
  have := norm_sub_norm_le (φ₀ x₀) (φ x)
  rw [norm_sub_rev] at h
  linarith

/-- **Lyapunov–Schmidt reduction under a forcing.** Let `x` be the forced correction, of norm at
most `2 C ‖e + g‖` in the range of `Q`, for a forcing `‖g‖ ≤ B_c t` with `0 ≤ t < τ` below a
forcing tolerance `τ`. A point `y` in the range of `Q` of norm less than `min (δ / 2) (2 C L)⁻¹`
solves the forced equation `e + g + D y + N y = 0` together with the finite equation `φ y = 0`
exactly when it is the forced correction and the reduced section `φ x` vanishes. -/
theorem add_add_add_eq_zero_and_apply_eq_zero_iff_of_isForcingTolerance {F : Type*} [Zero F]
    {φ : X → F} {y : X} (hyQ : y ∈ range Q) (hy : ‖y‖ < min (δ / 2) (2 * C * L)⁻¹) :
    e + g + D y + N y = 0 ∧ φ y = 0 ↔ y = x ∧ φ x = 0 := by
  constructor
  · rintro ⟨hye, hφy⟩
    -- The uniqueness ball is nonempty, so `C, L > 0`, and the forced correction lies in it.
    have hCL : 0 < 2 * (C : ℝ) * L := inv_pos.1 ((norm_nonneg y).trans_lt (lt_min_iff.1 hy).2)
    have hC : 0 < C := by
      by_contra h0
      rw [not_lt, nonpos_iff_eq_zero] at h0
      simp [h0] at hCL
    have hL : 0 < L := by
      by_contra h0
      rw [not_lt, nonpos_iff_eq_zero] at h0
      simp [h0] at hCL
    have hxγ := (norm_le_two_mul_mul_add_mul he ht₀ ht hg hBc hx).trans_lt
      (hτ.two_mul_mul_add_mul_lt_min hC hL hε hεδ)
    have hyx := eq_of_add_add_eq_zero_of_lt_min hDQ hQ hN hy hxγ hyQ hye hxQ hxe
    exact ⟨hyx, hyx ▸ hφy⟩
  · rintro ⟨rfl, hφx⟩
    exact ⟨hxe, hφx⟩

end Pointwise

/-! ### The count of the forced finite model -/

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n)
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (o' : HomologicalOrientation F F n) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
  {X : Type*} [NormedAddCommGroup X] {Y G : M → Type*} [∀ p, SeminormedAddCommGroup (Y p)]
  [∀ p, FunLike (G p) (Y p) X] [∀ p, AddMonoidHomClass (G p) (Y p) X] {Q : ∀ p, G p}
  {D N : ∀ p, X → Y p} {e g : ∀ p, Y p} {x x₀ : M → X} {φ ψ φ₀ : M → X → F}
  {Bc Bφ K : ℝ≥0} {H t : ℝ} {U : Opens M} {f f₀ : C(M, F)}
  (hDQ : ∀ p ∈ frontier (U : Set M), ∀ y, D p (Q p y) = y)
  (hQ : ∀ p ∈ frontier (U : Set M), ∀ y, ‖Q p y‖ ≤ C * ‖y‖)
  (hN : ∀ p ∈ frontier (U : Set M), ∀ x ∈ closedBall (0 : X) δ, ∀ y ∈ closedBall (0 : X) δ,
    ‖N p x - N p y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
  (he : ∀ p ∈ frontier (U : Set M), ‖e p‖ ≤ ε) (hε : 2 * (C : ℝ) ^ 2 * L * ε < 1 / 4)
  (hεδ : 2 * (C : ℝ) * ε < δ / 4) (hτ : IsForcingTolerance C L B δ b τ) (ht₀ : 0 ≤ t)
  (ht : t < τ) (hg : ∀ p ∈ frontier (U : Set M), ‖g p‖ ≤ Bc * t) (hBc : Bc ≤ B)
  (hxQ : ∀ p ∈ frontier (U : Set M), x p ∈ range (Q p))
  (hx : ∀ p ∈ frontier (U : Set M), ‖x p‖ ≤ 2 * C * ‖e p + g p‖)
  (hxe : ∀ p ∈ frontier (U : Set M), e p + g p + D p (x p) + N p (x p) = 0)
  (hx₀Q : ∀ p ∈ frontier (U : Set M), x₀ p ∈ range (Q p))
  (hx₀ : ∀ p ∈ frontier (U : Set M), ‖x₀ p‖ ≤ 2 * C * ‖e p‖)
  (hx₀e : ∀ p ∈ frontier (U : Set M), e p + D p (x₀ p) + N p (x₀ p) = 0)
  (hφ : ∀ p ∈ frontier (U : Set M), ‖φ p (x p) - ψ p (x p)‖ ≤ Bφ * t)
  (hψ : ∀ p ∈ frontier (U : Set M), LipschitzOnWith K (ψ p) (closedBall 0 δ))
  (hH : ∀ p ∈ frontier (U : Set M), ‖ψ p (x₀ p) - φ₀ p (x₀ p)‖ ≤ H) (hHb : H < b / 4)
  (hB : Bφ + 2 * C * K * Bc ≤ B)
  (hf : ∀ p ∈ frontier (U : Set M), f p = φ p (x p))
  (hf₀ : ∀ p ∈ frontier (U : Set M), f₀ p = φ₀ p (x₀ p))
include hDQ hQ hN he hε hεδ hτ ht₀ ht hg hBc hxQ hx hxe hx₀Q hx₀ hx₀e hφ hψ hH hHb hB hf hf₀

omit [T2Space M] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- On the frontier of `U`, the forced reduced section is within half the margin of the reference
section. -/
private theorem norm_sub_lt_of_isForcingTolerance :
    ∀ p ∈ frontier (U : Set M), ‖f p - f₀ p‖ < b / 2 := fun p hp ↦ by
  rw [hf p hp, hf₀ p hp]
  exact norm_apply_sub_apply_lt_of_isForcingTolerance (hDQ p hp) (hQ p hp) (hN p hp) (he p hp)
    hε hεδ hτ ht₀ ht (hg p hp) hBc (hxQ p hp) (hx p hp) (hxe p hp) (hx₀Q p hp) (hx₀ p hp)
    (hx₀e p hp) (hφ p hp) (hψ p hp) (hH p hp) hHb hB

include hF in
/-- **The count of the forced finite model.** Let `U` have compact closure, and let `f` and `f₀`
be continuous maps equal on the frontier of `U` to the forced reduced section `p ↦ φ p (x p)` and
the reference reduced section `p ↦ φ₀ p (x₀ p)`, where `x` and `x₀` are the forced and unforced
corrections. Suppose `f₀` has margin `b ≤ ‖f₀ p‖` on the frontier of `U`. For a forcing of size
`0 ≤ t < τ` below a forcing tolerance `τ`, within the budgets `B_c ≤ B`, `B_φ + 2 C K B_c ≤ B` and
`H < b / 4` of `TauCeti.norm_apply_sub_apply_lt_of_isForcingTolerance`, `f` has the same local
degree on `U` at `0` as `f₀`. -/
theorem localDegree_restrict_eq_of_isForcingTolerance (hU : IsCompact (closure (U : Set M)))
    (hb : ∀ p ∈ frontier (U : Set M), b ≤ ‖f₀ p‖) :
    (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) 0 =
      (o.comap U.isOpenEmbedding').localDegree o' hE (f₀.restrict U) 0 := by
  refine (o.localDegree_restrict_eq_of_norm_sub_lt o' hE hF hU fun p hp ↦ ?_).symm
  have h := norm_sub_lt_of_isForcingTolerance hDQ hQ hN he hε hεδ hτ ht₀ ht hg hBc hxQ hx hxe
    hx₀Q hx₀ hx₀e hφ hψ hH hHb hB hf hf₀ p hp
  rw [sub_zero, sub_zero]
  linarith [hb p hp, norm_nonneg (f p), norm_nonneg (f p - f₀ p)]

include hF in
/-- **A nonzero count has a forced solution.** Under the hypotheses of
`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_isForcingTolerance`, if `f` also agrees
with the forced reduced section `p ↦ φ p (x p)` on `U` and `f₀` has nonzero local degree on `U` at
`0`, then the forced reduced section vanishes at some point of `U`. -/
theorem exists_mem_apply_eq_zero_of_isForcingTolerance (hU : IsCompact (closure (U : Set M)))
    (hb : ∀ p ∈ frontier (U : Set M), b ≤ ‖f₀ p‖) (hfU : ∀ p ∈ (U : Set M), f p = φ p (x p))
    (hdeg : (o.comap U.isOpenEmbedding').localDegree o' hE (f₀.restrict U) 0 ≠ 0) :
    ∃ p ∈ U, φ p (x p) = 0 := by
  rw [← o.localDegree_restrict_eq_of_isForcingTolerance o' hE hF hDQ hQ hN he hε hεδ hτ ht₀ ht
    hg hBc hxQ hx hxe hx₀Q hx₀ hx₀e hφ hψ hH hHb hB hf hf₀ hU hb] at hdeg
  obtain ⟨p, hp, hfp⟩ := o.exists_mem_apply_eq_of_localDegree_restrict_ne_zero o' hE hF hdeg
  exact ⟨p, hp, hfU p hp ▸ hfp⟩

end HomologicalOrientation

end TauCeti
