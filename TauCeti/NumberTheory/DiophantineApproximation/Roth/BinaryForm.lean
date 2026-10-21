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
`F(x, y) = m` with `m ≠ 0`: choosing `2 < κ < d` bounds `max(|x|, |y|)` on their solutions.

## Main results

* `IsAlgebraic.exists_pos_mul_max_abs_rpow_le_norm_sub_mul`: Roth's theorem for the linear form
  `x - α y`: `‖x - α y‖ ≥ c max(|x|, |y|) ^ (1 - κ)` for integers with `x ≠ α y`.
* `TauCeti.exists_pos_mul_max_abs_rpow_le_prod_norm`: a product of pairwise non-proportional
  linear forms satisfying such bounds is at least `c max(|x|, |y|) ^ (#T - κ)`.
* `MvPolynomial.IsHomogeneous.exists_pos_mul_max_abs_rpow_le_abs_eval`: the Thue–Roth inequality
  for binary forms without squared linear factors.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Theorem 6.3.
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
