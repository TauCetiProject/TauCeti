/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Homogenize
public import TauCeti.Analysis.Normed.Field.LinearForms
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.Theorem

import TauCeti.Data.Int.MaxAbs
import TauCeti.RingTheory.Polynomial.BinaryForm
import TauCeti.RingTheory.Algebraic.Basic

/-!
# Roth's theorem for binary forms

Let `F ∈ ℤ[X₀, X₁]` be a binary form of degree `d` with no squared linear factor over `ℂ`. Roth's
theorem gives the **Thue–Roth inequality**: for every `κ > 2` there is `c > 0` with

`|F(x, y)| ≥ c max(|x|, |y|) ^ (d - κ)` whenever `x, y ∈ ℤ` and `F(x, y) ≠ 0`.

Over `ℂ`, `F = a ∏ᵢ Lᵢ` is a product of `d` pairwise non-proportional linear forms, each `X₁` or
`X₀ - α X₁` with `α` algebraic (`MvPolynomial.IsHomogeneous.exists_linear_factors`). At an integer
point `(x, y)` with `M = max(|x|, |y|)`:

* by Cramer's rule, two non-proportional forms cannot both be much smaller than `M`
  (`TauCeti.norm_det_mul_max_norm_le`), so all forms but the smallest one are at least `c M`
  (`TauCeti.exists_pos_mul_max_norm_le_norm_of_pairwise`);
* by Roth's theorem for `α`, the smallest one is still at least `c M ^ (1 - κ)`
  (`IsAlgebraic.exists_pos_mul_max_abs_rpow_le_norm_sub_mul`).

Multiplying gives `|F(x, y)| ≥ c M ^ (d - 1) M ^ (1 - κ)`
(`TauCeti.exists_pos_mul_max_abs_rpow_le_prod_norm`). Like Roth's theorem, the inequality is
ineffective. For `d ≥ 3` it is the analytic input to Thue's theorem on the equations
`F(x, y) = m` with `m ≠ 0`: choosing `2 < κ < d` bounds `max(|x|, |y|)` on the solutions of
`0 < |F(x, y)| ≤ B`. An arbitrary binary form `F` such that `F(X, 1)` has at least three distinct
complex zeros has such a divisor `G ∣ F` of degree at least `3`
(`MvPolynomial.IsHomogeneous.exists_dvd_isHomogeneous_not_sq_dvd`), and `G(x, y)` divides
`F(x, y)`, so Thue's theorem holds for `F` as well.

## Main results

* `IsAlgebraic.exists_pos_mul_max_abs_rpow_le_norm_sub_mul`: Roth's theorem for the linear form
  `x - α y`: `‖x - α y‖ ≥ c max(|x|, |y|) ^ (1 - κ)` for integers with `x ≠ α y`.
* `TauCeti.exists_pos_mul_max_abs_rpow_le_prod_norm`: a product of pairwise non-proportional
  linear forms satisfying such bounds is at least `c max(|x|, |y|) ^ (#T - κ)`.
* `MvPolynomial.IsHomogeneous.exists_pos_mul_max_abs_rpow_le_abs_eval`: the Thue–Roth inequality
  for binary forms without squared linear factors.
* `MvPolynomial.IsHomogeneous.finite_setOf_eval_ne_zero_and_abs_le`,
  `MvPolynomial.IsHomogeneous.finite_setOf_eval_eq`: the Thue inequality `0 < |F(x, y)| ≤ B`
  and Thue's equation `F(x, y) = m` with `m ≠ 0` have finitely many integer solutions, for such
  forms of degree `d ≥ 3`.
* `MvPolynomial.IsHomogeneous.finite_setOf_eval_ne_zero_and_abs_le_of_three_le_card_roots`,
  `MvPolynomial.IsHomogeneous.finite_setOf_eval_eq_of_three_le_card_roots`: the same for binary
  forms `F` such that `F(X, 1)` has at least three distinct complex zeros (Thue's theorem).
* `TauCeti.finite_setOf_mul_pow_add_mul_pow_eq`: the binomial Thue equation `a x ^ n + c y ^ n = m`
  with `n ≥ 3` and `a, c, m ≠ 0` has finitely many integer solutions.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Theorem 6.3 and
  Corollary 6.4.
* A. Thue, *Über Annäherungswerte algebraischer Zahlen*, J. Reine Angew. Math. 135 (1909),
  284–305.
-/

public section

open Filter Finset Height Polynomial Real Topology

namespace TauCeti

/-- **Roth's theorem for a linear form.** If `α ∈ ℂ` is algebraic and `κ > 2`, then there is
`c > 0` with `‖x - α y‖ ≥ c max(|x|, |y|) ^ (1 - κ)` for all integers `x`, `y` with `x ≠ α y`. -/
theorem _root_.IsAlgebraic.exists_pos_mul_max_abs_rpow_le_norm_sub_mul {α : ℂ}
    (hα : IsAlgebraic ℚ α) {κ : ℝ} (hκ : 2 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℤ, (x : ℂ) - α * y ≠ 0 →
      c * max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ ‖(x : ℂ) - α * y‖ := by
  obtain ⟨c₀, hc₀, h⟩ := hα.exists_pos_mul_mulHeight₁_rpow_neg_le_norm_sub hκ
  set A := ‖α‖ + 1
  have hA : 1 ≤ A := by linarith [norm_nonneg α]
  refine ⟨min (1 / 2) (c₀ / (2 * A)), by positivity, fun x y hxy ↦ ?_⟩
  set M := max |(x : ℝ)| |(y : ℝ)|
  have hy₀ := abs_nonneg (y : ℝ)
  have hM : 1 ≤ M := Int.one_le_max_abs_cast <| by
    by_contra! h0
    exact hxy (by simp [h0.1, h0.2])
  have hM₀ : 0 < M := by linarith
  rcases le_or_gt (2 * A * |(y : ℝ)|) |(x : ℝ)| with hbig | hsmall
  · -- If `|x| ≥ 2 A |y|`, then `‖x - α y‖ ≥ |x| / 2 = M / 2`.
    have hMx : M = |(x : ℝ)| := max_eq_left (by nlinarith)
    have h1 : M / 2 ≤ ‖(x : ℂ) - α * y‖ := by
      have := norm_sub_norm_le (x : ℂ) (α * y)
      rw [Complex.norm_intCast, norm_mul, Complex.norm_intCast] at this
      rw [hMx]
      nlinarith [norm_nonneg α]
    have h2 : M ^ (1 - κ) ≤ M := by
      calc M ^ (1 - κ) ≤ M ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hM (by linarith)
        _ = M := rpow_one M
    calc min (1 / 2) (c₀ / (2 * A)) * M ^ (1 - κ) ≤ 1 / 2 * M := by
          gcongr
          · exact min_le_left _ _
      _ ≤ ‖(x : ℂ) - α * y‖ := by linarith
  · -- Otherwise `y ≠ 0` and `M ≤ 2 A |y|`; apply Roth's theorem to `ξ = x / y`.
    have hy : y ≠ 0 := by
      rintro rfl
      simp only [Int.cast_zero, abs_zero, mul_zero] at hsmall
      linarith [abs_nonneg (x : ℝ)]
    have hyR : (y : ℂ) ≠ 0 := Int.cast_ne_zero.2 hy
    have hMy : M ≤ 2 * A * |(y : ℝ)| := max_le hsmall.le (by nlinarith)
    set ξ : ℚ := (x : ℚ) / y
    have hξ : (ξ : ℂ) = x / y := by simp [ξ]
    have hsub : (x : ℂ) - α * y = y * ((ξ : ℂ) - α) := by
      rw [hξ]
      field_simp
    have hξα : (ξ : ℂ) ≠ α := fun h ↦ hxy (by rw [hsub, h, sub_self, mul_zero])
    have hH : mulHeight₁ ξ ≤ M := Rat.mulHeight₁_intCast_div_le x hy
    have hHκ : M ^ (-κ) ≤ mulHeight₁ ξ ^ (-κ) :=
      rpow_le_rpow_of_nonpos (mulHeight₁_pos ξ) hH (by linarith)
    have hMκ : M ^ (1 - κ) = M * M ^ (-κ) := by
      rw [sub_eq_add_neg, rpow_add hM₀, rpow_one]
    rw [hsub, norm_mul, Complex.norm_intCast, hMκ]
    calc min (1 / 2) (c₀ / (2 * A)) * (M * M ^ (-κ))
        ≤ c₀ / (2 * A) * (2 * A * |(y : ℝ)| * M ^ (-κ)) := by
          gcongr
          exact min_le_right _ _
      _ = |(y : ℝ)| * (c₀ * M ^ (-κ)) := by field_simp
      _ ≤ |(y : ℝ)| * ‖(ξ : ℂ) - α‖ := by
          gcongr
          exact (mul_le_mul_of_nonneg_left hHκ hc₀.le).trans (h ξ hξα)

/-- Let `ℓ.1 x + ℓ.2 y`, `ℓ ∈ T`, be pairwise non-proportional complex linear forms, each bounded
below by `c max(|x|, |y|) ^ (1 - κ)` at the integer points where it does not vanish, for some
`κ ≥ 0`. Then there is `c > 0` with `∏_{ℓ ∈ T} ‖ℓ.1 x + ℓ.2 y‖ ≥ c max(|x|, |y|) ^ (#T - κ)` at
every integer point where no form vanishes. -/
theorem exists_pos_mul_max_abs_rpow_le_prod_norm {T : Finset (ℂ × ℂ)}
    (hT : (T : Set (ℂ × ℂ)).Pairwise fun ℓ ℓ' ↦ ℓ.1 * ℓ'.2 - ℓ.2 * ℓ'.1 ≠ 0) {κ : ℝ}
    (hκ : 0 ≤ κ) (hL : ∀ ℓ ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ x y : ℤ, ℓ.1 * x + ℓ.2 * y ≠ 0 →
      c * max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ ‖ℓ.1 * x + ℓ.2 * y‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℤ, (∀ ℓ ∈ T, ℓ.1 * x + ℓ.2 * y ≠ 0) →
      c * max |(x : ℝ)| |(y : ℝ)| ^ ((#T : ℝ) - κ) ≤ ∏ ℓ ∈ T, ‖ℓ.1 * x + ℓ.2 * y‖ := by
  obtain ⟨c₁, hc₁, h₁⟩ := exists_pos_mul_max_norm_le_norm_of_pairwise hT
  -- A common constant `c ≤ min c₁ 1` for the lower bounds of all the forms.
  have h : ∀ ℓ ∈ T, ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ x y : ℤ, ℓ.1 * x + ℓ.2 * y ≠ 0 →
      c * max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ ‖ℓ.1 * x + ℓ.2 * y‖ := fun ℓ hℓ ↦ by
    obtain ⟨c, hc, hcL⟩ := hL ℓ hℓ
    filter_upwards [Ioc_mem_nhdsGT hc] with c' hc' x y hxy
    exact (mul_le_mul_of_nonneg_right hc'.2 (by positivity)).trans (hcL x y hxy)
  obtain ⟨c, ⟨hcL, hc'⟩, hc⟩ := (((eventually_all_finset _).2 h).and
    (Ioc_mem_nhdsGT (lt_min hc₁ one_pos))).and self_mem_nhdsWithin |>.exists
  have hcc₁ : c ≤ c₁ := hc'.2.trans (min_le_left _ _)
  refine ⟨c ^ #T, pow_pos hc _, fun x y hxy ↦ ?_⟩
  set M := max |(x : ℝ)| |(y : ℝ)|
  rcases T.eq_empty_or_nonempty with rfl | hne
  · -- The empty product: `M ^ (-κ) ≤ 1`.
    simp only [card_empty, pow_zero, one_mul, CharP.cast_eq_zero, zero_sub, prod_empty]
    by_cases hxy0 : x = 0 ∧ y = 0
    · simp only [M, hxy0.1, hxy0.2, Int.cast_zero, abs_zero, max_self]
      exact zero_rpow_le_one _
    · exact rpow_le_one_of_one_le_of_nonpos (Int.one_le_max_abs_cast (not_and_or.1 hxy0))
        (by linarith)
  -- Split off a form `ℓ₀` of least norm; all the others are at least `c₁ M ≥ c M`.
  obtain ⟨ℓ₀, hℓ₀, hmin⟩ := T.exists_min_image (fun ℓ ↦ ‖ℓ.1 * x + ℓ.2 * y‖) hne
  have hM : 1 ≤ M := Int.one_le_max_abs_cast <| by
    by_contra! h0
    exact hxy ℓ₀ hℓ₀ (by simp [h0.1, h0.2])
  have hM₀ : 0 < M := by linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Finset.card_ne_zero.2 hne)
  have hrest : (c * M) ^ m ≤ ∏ ℓ ∈ T.erase ℓ₀, ‖ℓ.1 * x + ℓ.2 * y‖ := by
    have hcard : #(T.erase ℓ₀) = m := by rw [card_erase_of_mem hℓ₀, hm, Nat.add_sub_cancel]
    rw [← hcard, ← prod_const]
    refine prod_le_prod₀ (fun _ _ ↦ by positivity) fun ℓ hℓ ↦ ?_
    have h₁ℓ := h₁ x y ℓ₀ hℓ₀ hmin ℓ (mem_of_mem_erase hℓ) (ne_of_mem_erase hℓ)
    rw [Complex.norm_intCast, Complex.norm_intCast] at h₁ℓ
    exact (mul_le_mul_of_nonneg_right hcc₁ hM₀.le).trans h₁ℓ
  rw [← mul_prod_erase T _ hℓ₀]
  calc c ^ #T * M ^ ((#T : ℝ) - κ) = c * M ^ (1 - κ) * (c * M) ^ m := by
        rw [hm, mul_pow, ← rpow_natCast M m, pow_succ']
        push_cast
        rw [show (m : ℝ) + 1 - κ = (1 - κ) + m by ring, rpow_add hM₀]
        ring
    _ ≤ _ := mul_le_mul (hcL ℓ₀ hℓ₀ x y (hxy ℓ₀ hℓ₀)) hrest (by positivity) (norm_nonneg _)

/-- **The Thue–Roth inequality for binary forms** (Evertse, Theorem 6.3). Let `F ∈ ℤ[X₀, X₁]` be
a binary form of degree `d` with no squared linear factor over `ℂ`, and let `κ > 2`. Then there
is `c > 0` with `|F(x, y)| ≥ c max(|x|, |y|) ^ (d - κ)` for all integers `x`, `y` with
`F(x, y) ≠ 0`. The proof is ineffective: it gives no value of `c`. -/
theorem _root_.MvPolynomial.IsHomogeneous.exists_pos_mul_max_abs_rpow_le_abs_eval
    {F : MvPolynomial (Fin 2) ℤ} {d : ℕ} (hF : F.IsHomogeneous d)
    (hsq : ∀ a b : ℂ, (a, b) ≠ (0, 0) →
      ¬(MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) ^ 2 ∣
        F.map (Int.castRingHom ℂ))
    {κ : ℝ} (hκ : 2 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℤ, MvPolynomial.eval ![x, y] F ≠ 0 →
      c * max |(x : ℝ)| |(y : ℝ)| ^ ((d : ℝ) - κ) ≤ |(MvPolynomial.eval ![x, y] F : ℝ)| := by
  rcases eq_or_ne F 0 with rfl | hF₀
  · exact ⟨1, one_pos, fun x y h ↦ absurd (map_zero _) h⟩
  -- Over `ℂ`, `F` splits into pairwise non-proportional linear factors.
  have hG₀ : F.map (Int.castRingHom ℂ) ≠ 0 := fun h ↦
    hF₀ (MvPolynomial.map_injective _ (RingHom.injective_int _) (by rw [h, map_zero]))
  obtain ⟨a, ha, T, hTd, hT, hTL, hFT⟩ :=
    (hF.map _).exists_linear_factors hG₀ IsAlgClosed.card_roots_eq_natDegree hsq
  have heval : ∀ x y : ℂ, MvPolynomial.eval ![x, y] (F.map (Int.castRingHom ℂ)) =
      a * ∏ ℓ ∈ T, (ℓ.1 * x + ℓ.2 * y) := fun x y ↦ by
    rw [hFT]
    simp
  -- The roots of `F(X, 1)` are algebraic.
  have halg : ∀ α ∈ (MvPolynomial.aeval ![Polynomial.X, 1] (F.map (Int.castRingHom ℂ)) :
      ℂ[X]).roots, IsAlgebraic ℚ α := fun α hα ↦ by
    rw [MvPolynomial.aeval_X_one_map, ← algebraMap_int_eq] at hα
    exact (isAlgebraic_of_mem_aroots hα).extendScalars (R := ℤ) Int.cast_injective
  -- Each linear factor satisfies Roth's inequality: `X₁` trivially, `X₀ - α X₁` by Roth's theorem.
  have hL : ∀ ℓ ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ x y : ℤ, ℓ.1 * x + ℓ.2 * y ≠ 0 →
      c * max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ ‖ℓ.1 * x + ℓ.2 * y‖ := by
    intro ℓ hℓ
    rcases hTL ℓ hℓ with rfl | ⟨α, hα, rfl⟩
    · refine ⟨1, one_pos, fun x y hxy ↦ ?_⟩
      simp only [zero_mul, one_mul, zero_add, Complex.norm_intCast] at hxy ⊢
      have hy : y ≠ 0 := by exact_mod_cast hxy
      calc max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ 1 :=
            rpow_le_one_of_one_le_of_nonpos (Int.one_le_max_abs_cast (Or.inr hy)) (by linarith)
        _ ≤ |(y : ℝ)| := by exact_mod_cast Int.one_le_abs hy
    · obtain ⟨c, hc, h⟩ := (halg α hα).exists_pos_mul_max_abs_rpow_le_norm_sub_mul hκ
      refine ⟨c, hc, fun x y hxy ↦ ?_⟩
      have e : (1 : ℂ) * x + -α * y = x - α * y := by ring
      rw [e] at hxy ⊢
      exact h x y hxy
  obtain ⟨c, hc, h⟩ := exists_pos_mul_max_abs_rpow_le_prod_norm hT (by linarith) hL
  refine ⟨‖a‖ * c, mul_pos (norm_pos_iff.2 ha) hc, fun x y hxy ↦ ?_⟩
  have hcast : ((MvPolynomial.eval ![x, y] F : ℤ) : ℂ) = a * ∏ ℓ ∈ T, (ℓ.1 * x + ℓ.2 * y) := by
    have hv : ![(x : ℂ), (y : ℂ)] = Int.castRingHom ℂ ∘ ![x, y] := by
      ext i
      fin_cases i <;> simp
    rw [← heval, hv, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp, eq_intCast]
  have hne : ∀ ℓ ∈ T, ℓ.1 * (x : ℂ) + ℓ.2 * y ≠ 0 := fun ℓ hℓ h0 ↦
    hxy (Int.cast_eq_zero.1 (hcast.trans (by rw [prod_eq_zero hℓ h0, mul_zero])))
  have habs : |(MvPolynomial.eval ![x, y] F : ℝ)| = ‖a‖ * ∏ ℓ ∈ T, ‖ℓ.1 * x + ℓ.2 * y‖ := by
    rw [← Complex.norm_intCast, hcast, norm_mul, norm_prod]
  rw [habs, mul_assoc, ← hTd]
  exact mul_le_mul_of_nonneg_left (h x y hne) (norm_nonneg a)

end TauCeti

namespace MvPolynomial.IsHomogeneous

/-- **The Thue inequality for square-free binary forms** (Evertse, Corollary 6.4, square-free
case). Let `F ∈ ℤ[X₀, X₁]` be a binary form of degree `d ≥ 3` with no squared linear factor over
`ℂ`. Then for every bound `B`, the inequality `0 < |F(x, y)| ≤ B` has only finitely many integer
solutions. Like Roth's theorem, the proof is ineffective. -/
theorem finite_setOf_eval_ne_zero_and_abs_le
    {F : MvPolynomial (Fin 2) ℤ} {d : ℕ} (hF : F.IsHomogeneous d)
    (hsq : ∀ a b : ℂ, (a, b) ≠ (0, 0) →
      ¬(MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) ^ 2 ∣
        F.map (Int.castRingHom ℂ))
    (hd : 3 ≤ d) (B : ℤ) :
    {p : ℤ × ℤ | MvPolynomial.eval ![p.1, p.2] F ≠ 0 ∧
      |MvPolynomial.eval ![p.1, p.2] F| ≤ B}.Finite := by
  -- The Thue–Roth inequality with `κ = 5/2 < d` bounds `max (|x|, |y|)` on the solutions.
  obtain ⟨c, hc, h⟩ := hF.exists_pos_mul_max_abs_rpow_le_abs_eval hsq (κ := 5 / 2) (by norm_num)
  have he : 0 < (d : ℝ) - 5 / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- Every solution satisfies `max(|x|, |y|) ≤ N := (B / c) ^ (1 / (d - 5/2))`.
  set N : ℝ := ((B : ℝ) / c) ^ ((d : ℝ) - 5 / 2)⁻¹
  have hbound : ∀ p ∈ {p : ℤ × ℤ | MvPolynomial.eval ![p.1, p.2] F ≠ 0 ∧
      |MvPolynomial.eval ![p.1, p.2] F| ≤ B}, max |(p.1 : ℝ)| |(p.2 : ℝ)| ≤ N := by
    rintro ⟨x, y⟩ ⟨hp, hpB⟩
    have hM : 0 ≤ max |(x : ℝ)| |(y : ℝ)| := le_max_of_le_left (abs_nonneg _)
    have hpB' : |(MvPolynomial.eval ![x, y] F : ℝ)| ≤ B := by exact_mod_cast hpB
    have hpow : max |(x : ℝ)| |(y : ℝ)| ^ ((d : ℝ) - 5 / 2) ≤ B / c := by
      rw [le_div_iff₀ hc, mul_comm]
      exact (h x y hp).trans hpB'
    calc max |(x : ℝ)| |(y : ℝ)|
        = (max |(x : ℝ)| |(y : ℝ)| ^ ((d : ℝ) - 5 / 2)) ^ ((d : ℝ) - 5 / 2)⁻¹ :=
          (rpow_rpow_inv hM he.ne').symm
      _ ≤ N := rpow_le_rpow (rpow_nonneg hM _) hpow (inv_nonneg.2 he.le)
  -- Hence the solutions lie in the square `[-K, K]²` with `K = ⌈N⌉`.
  refine ((Set.finite_Icc (-⌈N⌉) ⌈N⌉).prod (Set.finite_Icc (-⌈N⌉) ⌈N⌉)).subset ?_
  intro p hp
  have hN := hbound p hp
  have h1 : |(p.1 : ℝ)| ≤ ⌈N⌉ := (le_max_left _ _).trans (hN.trans (Int.le_ceil N))
  have h2 : |(p.2 : ℝ)| ≤ ⌈N⌉ := (le_max_right _ _).trans (hN.trans (Int.le_ceil N))
  exact ⟨abs_le.1 (by exact_mod_cast h1), abs_le.1 (by exact_mod_cast h2)⟩

/-- **Thue's theorem for square-free binary forms** (Evertse, Corollary 6.4, square-free case).
Let `F ∈ ℤ[X₀, X₁]` be a binary form of degree `d ≥ 3` with no squared linear factor over `ℂ`,
and let `m ≠ 0`. Then the Thue equation `F(x, y) = m` has only finitely many integer solutions.
Like Roth's theorem, the proof is ineffective. -/
theorem finite_setOf_eval_eq
    {F : MvPolynomial (Fin 2) ℤ} {d : ℕ} (hF : F.IsHomogeneous d)
    (hsq : ∀ a b : ℂ, (a, b) ≠ (0, 0) →
      ¬(MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) ^ 2 ∣
        F.map (Int.castRingHom ℂ))
    (hd : 3 ≤ d) {m : ℤ} (hm : m ≠ 0) :
    {p : ℤ × ℤ | MvPolynomial.eval ![p.1, p.2] F = m}.Finite :=
  (hF.finite_setOf_eval_ne_zero_and_abs_le hsq hd |m|).subset fun _ hp ↦
    ⟨hp ▸ hm, hp ▸ le_rfl⟩

/-- **The Thue inequality** (Evertse, Corollary 6.4). Let `F ∈ ℤ[X₀, X₁]` be a binary form such
that `F(X, 1)` has at least three distinct complex zeros. Then for every bound `B`, the
inequality `0 < |F(x, y)| ≤ B` has only finitely many integer solutions. Like Roth's theorem,
the proof is ineffective. -/
theorem finite_setOf_eval_ne_zero_and_abs_le_of_three_le_card_roots
    {F : MvPolynomial (Fin 2) ℤ} {d : ℕ} (hF : F.IsHomogeneous d)
    (hroots : 3 ≤ ((MvPolynomial.aeval ![Polynomial.X, 1] F : ℤ[X]).map
      (Int.castRingHom ℂ)).roots.toFinset.card) (B : ℤ) :
    {p : ℤ × ℤ | MvPolynomial.eval ![p.1, p.2] F ≠ 0 ∧
      |MvPolynomial.eval ![p.1, p.2] F| ≤ B}.Finite := by
  obtain ⟨G, hGF, hG, hsq⟩ := hF.exists_dvd_isHomogeneous_not_sq_dvd ℂ
  refine (hG.finite_setOf_eval_ne_zero_and_abs_le hsq hroots B).subset ?_
  rintro p ⟨hp, hpB⟩
  have hdvd := map_dvd (MvPolynomial.eval ![p.1, p.2]) hGF
  -- `G(x, y)` is a divisor of the nonzero integer `F(x, y)`.
  exact ⟨fun h ↦ hp (zero_dvd_iff.1 (h ▸ hdvd)),
    (Int.le_of_dvd (abs_pos.2 hp) ((abs_dvd_abs _ _).2 hdvd)).trans hpB⟩

/-- **Thue's theorem** (Thue 1909; Evertse, Corollary 6.4). Let `F ∈ ℤ[X₀, X₁]` be a binary form
such that `F(X, 1)` has at least three distinct complex zeros, and let `m ≠ 0`. Then the Thue
equation `F(x, y) = m` has only finitely many integer solutions. Like Roth's theorem, the proof
is ineffective. -/
theorem finite_setOf_eval_eq_of_three_le_card_roots
    {F : MvPolynomial (Fin 2) ℤ} {d : ℕ} (hF : F.IsHomogeneous d)
    (hroots : 3 ≤ ((MvPolynomial.aeval ![Polynomial.X, 1] F : ℤ[X]).map
      (Int.castRingHom ℂ)).roots.toFinset.card) {m : ℤ} (hm : m ≠ 0) :
    {p : ℤ × ℤ | MvPolynomial.eval ![p.1, p.2] F = m}.Finite :=
  (hF.finite_setOf_eval_ne_zero_and_abs_le_of_three_le_card_roots hroots |m|).subset fun _ hp ↦
    ⟨hp ▸ hm, hp ▸ le_rfl⟩

end MvPolynomial.IsHomogeneous

namespace TauCeti

/-- **Binomial Thue equations.** For `n ≥ 3` and nonzero integers `a`, `c` and `m`, the equation
`a x ^ n + c y ^ n = m` has only finitely many integer solutions: `a X ^ n + c` has `n` distinct
complex zeros. Like Thue's theorem, the proof is ineffective. -/
theorem finite_setOf_mul_pow_add_mul_pow_eq {n : ℕ} (hn : 3 ≤ n) {a c m : ℤ} (ha : a ≠ 0)
    (hc : c ≠ 0) (hm : m ≠ 0) :
    {p : ℤ × ℤ | a * p.1 ^ n + c * p.2 ^ n = m}.Finite := by
  set F : MvPolynomial (Fin 2) ℤ :=
    MvPolynomial.C a * MvPolynomial.X 0 ^ n + MvPolynomial.C c * MvPolynomial.X 1 ^ n
  have hF : F.IsHomogeneous n :=
    ((MvPolynomial.isHomogeneous_X_pow 0 n).C_mul a).add
      ((MvPolynomial.isHomogeneous_X_pow 1 n).C_mul c)
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hF1 : (MvPolynomial.aeval ![X, 1] F : ℤ[X]).map (Int.castRingHom ℂ) =
      C (a : ℂ) * (X ^ n - C (-(c : ℂ) / a)) := by
    rw [mul_sub, ← C_mul, mul_div_cancel₀ _ ha', C_neg, sub_neg_eq_add]
    simp [F]
  have hsep : (X ^ n - C (-(c : ℂ) / a)).Separable :=
    separable_X_pow_sub_C _ (by exact_mod_cast (by omega : n ≠ 0))
      (div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hc)) ha')
  have hroots : 3 ≤ ((MvPolynomial.aeval ![X, 1] F : ℤ[X]).map
      (Int.castRingHom ℂ)).roots.toFinset.card := by
    rw [hF1, roots_C_mul _ ha', Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, natDegree_X_pow_sub_C]
    exact hn
  simpa [F] using hF.finite_setOf_eval_eq_of_three_le_card_roots hroots hm

end TauCeti
