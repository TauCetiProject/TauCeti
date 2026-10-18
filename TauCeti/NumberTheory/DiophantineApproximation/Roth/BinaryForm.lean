/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Homogenize
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.Theorem

/-!
# Roth's theorem for binary forms

Let `F ∈ ℤ[X₀, X₁]` be a binary form of degree `d` with no squared linear factor over `ℂ`. Roth's
theorem gives the **Thue–Roth inequality**: for every `κ > 2` there is `c > 0` with

`|F(x, y)| ≥ c max(|x|, |y|) ^ (d - κ)` whenever `x, y ∈ ℤ` and `F(x, y) ≠ 0`.

Over `ℂ`, `F = a ∏ᵢ Lᵢ` is a product of `d` pairwise non-proportional linear forms, each `X₁` or
`X₀ - α X₁` with `α` algebraic (`Polynomial.homogenize_eq_C_mul_X_pow_mul_prod`). At an integer
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

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜]

/-- **Cramer's rule bound** for two linear forms `L = a x + b y` and `L' = a' x + b' y` in two
variables: the determinant `D = a b' - b a'` satisfies
`‖D‖ max(‖x‖, ‖y‖) ≤ (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) (‖L‖ + ‖L'‖)`. -/
theorem norm_det_mul_max_norm_le (a b a' b' x y : 𝕜) :
    ‖a * b' - b * a'‖ * max ‖x‖ ‖y‖ ≤
      (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) * (‖a * x + b * y‖ + ‖a' * x + b' * y‖) := by
  set L := a * x + b * y
  set L' := a' * x + b' * y
  have hx : (a * b' - b * a') * x = b' * L - b * L' := by ring
  have hy : (a * b' - b * a') * y = a * L' - a' * L := by ring
  have hL := norm_nonneg L
  have hL' := norm_nonneg L'
  rw [mul_max_of_nonneg _ _ (norm_nonneg _), ← norm_mul, ← norm_mul, hx, hy]
  refine max_le ((norm_sub_le _ _).trans ?_) ((norm_sub_le _ _).trans ?_) <;>
    simp only [norm_mul] <;> nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg a',
      norm_nonneg b']

/-- Among pairwise non-proportional linear forms `ℓ.1 x + ℓ.2 y`, `ℓ ∈ T`, in two variables, all
but one are large at every point: there is `c > 0` such that if `ℓ₀ ∈ T` minimizes
`‖ℓ.1 x + ℓ.2 y‖`, then every other `ℓ ∈ T` has `‖ℓ.1 x + ℓ.2 y‖ ≥ c max(‖x‖, ‖y‖)`. -/
theorem exists_pos_mul_max_norm_le_norm_of_pairwise {T : Finset (𝕜 × 𝕜)}
    (hT : (T : Set (𝕜 × 𝕜)).Pairwise fun ℓ ℓ' ↦ ℓ.1 * ℓ'.2 - ℓ.2 * ℓ'.1 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : 𝕜, ∀ ℓ₀ ∈ T,
      (∀ ℓ ∈ T, ‖ℓ₀.1 * x + ℓ₀.2 * y‖ ≤ ‖ℓ.1 * x + ℓ.2 * y‖) →
        ∀ ℓ ∈ T, ℓ ≠ ℓ₀ → c * max ‖x‖ ‖y‖ ≤ ‖ℓ.1 * x + ℓ.2 * y‖ := by
  -- For each pair `ℓ ≠ ℓ₀`, every `c ≤ ‖D‖ / (2 N)` works, by `norm_det_mul_max_norm_le`.
  have h : ∀ p ∈ T ×ˢ T, ∀ᶠ c in 𝓝[>] (0 : ℝ), p.1 ≠ p.2 → ∀ x y : 𝕜,
      ‖p.2.1 * x + p.2.2 * y‖ ≤ ‖p.1.1 * x + p.1.2 * y‖ →
        c * max ‖x‖ ‖y‖ ≤ ‖p.1.1 * x + p.1.2 * y‖ := by
    rintro ⟨ℓ, ℓ₀⟩ hp
    rw [Finset.mem_product] at hp
    by_cases hne : ℓ = ℓ₀
    · exact Eventually.of_forall fun _ h ↦ absurd hne h
    set D := ℓ.1 * ℓ₀.2 - ℓ.2 * ℓ₀.1
    set N := ‖ℓ.1‖ + ‖ℓ.2‖ + ‖ℓ₀.1‖ + ‖ℓ₀.2‖
    have hD : 0 < ‖D‖ := norm_pos_iff.2 (hT hp.1 hp.2 hne)
    have hN : 0 < N := by
      have hND := norm_det_mul_max_norm_le ℓ.1 ℓ.2 ℓ₀.1 ℓ₀.2 1 0
      simp only [norm_one, norm_zero, max_eq_left zero_le_one, mul_one, mul_zero,
        add_zero] at hND
      nlinarith [norm_nonneg ℓ.1, norm_nonneg ℓ₀.1]
    filter_upwards [Ioc_mem_nhdsGT (div_pos hD (mul_pos two_pos hN))] with c hc _ x y hle
    have key := norm_det_mul_max_norm_le ℓ.1 ℓ.2 ℓ₀.1 ℓ₀.2 x y
    have hM : 0 ≤ max ‖x‖ ‖y‖ := (norm_nonneg x).trans (le_max_left _ _)
    have hc' : c * (2 * N) ≤ ‖D‖ := (le_div_iff₀ (by positivity)).1 hc.2
    nlinarith
  obtain ⟨c, hc, hc₀⟩ := ((eventually_all_finset _).2 h).and self_mem_nhdsWithin |>.exists
  exact ⟨c, hc₀, fun x y ℓ₀ hℓ₀ hmin ℓ hℓ hne ↦
    hc ⟨ℓ, ℓ₀⟩ (Finset.mem_product.2 ⟨hℓ, hℓ₀⟩) hne x y (hmin ℓ hℓ)⟩

end NormedField

/-- A point `(x, y)` of `ℤ²` other than the origin has `max(|x|, |y|) ≥ 1`. -/
private theorem one_le_max_abs_intCast {x y : ℤ} (h : x ≠ 0 ∨ y ≠ 0) :
    1 ≤ max |(x : ℝ)| |(y : ℝ)| := by
  rcases h with hx | hy
  · exact le_max_of_le_left (by exact_mod_cast Int.one_le_abs hx)
  · exact le_max_of_le_right (by exact_mod_cast Int.one_le_abs hy)

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
  have hM : 1 ≤ M := one_le_max_abs_intCast <| by
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
    · exact rpow_le_one_of_one_le_of_nonpos (one_le_max_abs_intCast (not_and_or.1 hxy0))
        (by linarith)
  -- Split off a form `ℓ₀` of least norm; all the others are at least `c₁ M ≥ c M`.
  obtain ⟨ℓ₀, hℓ₀, hmin⟩ := T.exists_min_image (fun ℓ ↦ ‖ℓ.1 * x + ℓ.2 * y‖) hne
  have hM : 1 ≤ M := one_le_max_abs_intCast <| by
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

/-- A binary form `F ∈ ℤ[X₀, X₁]` of degree `d` with no squared linear factor over `ℂ` factors
over `ℂ` as `a ∏_{ℓ ∈ T} (ℓ.1 X₀ + ℓ.2 X₁)` with `a ≠ 0` and `d` pairwise non-proportional linear
forms, each either `X₁` or `X₀ - α X₁` with `α` algebraic. -/
private theorem exists_linear_factors {F : MvPolynomial (Fin 2) ℤ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF₀ : F ≠ 0)
    (hsq : ∀ a b : ℂ, (a, b) ≠ (0, 0) →
      ¬(MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) ^ 2 ∣
        F.map (Int.castRingHom ℂ)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ T : Finset (ℂ × ℂ), #T = d ∧
      (T : Set (ℂ × ℂ)).Pairwise (fun ℓ ℓ' ↦ ℓ.1 * ℓ'.2 - ℓ.2 * ℓ'.1 ≠ 0) ∧
      (∀ ℓ ∈ T, ℓ = (0, 1) ∨ ∃ α : ℂ, IsAlgebraic ℚ α ∧ ℓ = (1, -α)) ∧
      ∀ x y : ℂ, MvPolynomial.eval ![x, y] (F.map (Int.castRingHom ℂ)) =
        a * ∏ ℓ ∈ T, (ℓ.1 * x + ℓ.2 * y) := by
  classical
  -- `F = g.homogenize d` for the dehomogenization `g = F(X, 1)`, which splits over `ℂ`.
  set f : ℤ[X] := MvPolynomial.aeval ![Polynomial.X, 1] F
  set g : ℂ[X] := f.map (Int.castRingHom ℂ)
  have hgd : g.natDegree ≤ d := natDegree_map_le.trans hF.natDegree_aeval_X_one_le
  have hG : F.map (Int.castRingHom ℂ) = g.homogenize d := by
    rw [homogenize_map, homogenize_eq_of_isHomogeneous hF rfl]
  have hg₀ : g ≠ 0 := by
    intro hg
    rw [hg, homogenize_zero] at hG
    exact hF₀ (MvPolynomial.map_injective _ (RingHom.injective_int _) (by rw [hG, map_zero]))
  have hf₀ : f ≠ 0 := fun hf ↦ hg₀ (by simp [g, hf])
  have hfac := g.homogenize_eq_C_mul_X_pow_mul_prod hgd IsAlgClosed.card_roots_eq_natDegree
  rw [← hG] at hfac
  have hdk : g.natDegree + (d - g.natDegree) = d := Nat.add_sub_cancel' hgd
  generalize d - g.natDegree = k at hfac hdk
  -- No squared linear factor: `X₁ ^ 2 ∤ F` gives `k ≤ 1`, and `(X₀ - α X₁) ^ 2 ∤ F` gives
  -- simple roots.
  have hk : k ≤ 1 := by
    by_contra! hk
    obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    refine hsq 0 1 (by simp) ⟨MvPolynomial.C g.leadingCoeff * MvPolynomial.X 1 ^ j *
      (g.roots.map fun a ↦ MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod, ?_⟩
    rw [hfac, hj]
    simp only [map_zero, zero_mul, map_one, one_mul, zero_add]
    ring
  have hnodup : g.roots.Nodup := by
    rw [Multiset.nodup_iff_ne_cons_cons]
    rintro α t ht
    refine hsq 1 (-α) (by simp) ⟨MvPolynomial.C g.leadingCoeff * MvPolynomial.X 1 ^ k *
      (t.map fun a ↦ MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod, ?_⟩
    rw [hfac, ht, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    simp only [map_one, one_mul, map_neg, neg_mul, ← sub_eq_add_neg]
    ring
  have halg : ∀ α ∈ g.roots, IsAlgebraic ℚ α := fun α hα ↦ by
    refine (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).1 ⟨f, hf₀, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq]
    exact (Polynomial.mem_roots hg₀).1 hα
  -- The linear forms `X₀ - α X₁` for the roots `α`, and `k` copies of `X₁`.
  set s : Multiset (ℂ × ℂ) := g.roots.map (fun α ↦ ((1 : ℂ), -α)) + Multiset.replicate k (0, 1)
  have hmem : ∀ ℓ ∈ s, (∃ α ∈ g.roots, ℓ = (1, -α)) ∨ ℓ = (0, 1) := fun ℓ hℓ ↦ by
    rcases Multiset.mem_add.1 hℓ with h | h
    · obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 h
      exact Or.inl ⟨α, hα, rfl⟩
    · exact Or.inr (Multiset.eq_of_mem_replicate h)
  have hs : s.Nodup := by
    refine Multiset.nodup_add.2 ⟨hnodup.map fun α β h ↦ neg_injective (Prod.ext_iff.1 h).2,
      ?_, Multiset.disjoint_left.2 fun h1 h2 ↦ ?_⟩
    · interval_cases k <;> simp
    · obtain ⟨α, -, rfl⟩ := Multiset.mem_map.1 h1
      exact one_ne_zero (Prod.ext_iff.1 (Multiset.eq_of_mem_replicate h2)).1
  set T : Finset (ℂ × ℂ) := ⟨s, hs⟩
  refine ⟨g.leadingCoeff, leadingCoeff_ne_zero.2 hg₀, T, ?_, ?_, ?_, fun x y ↦ ?_⟩
  · simp [T, s, IsAlgClosed.card_roots_eq_natDegree, hdk]
  · intro ℓ hℓ ℓ' hℓ' hne
    rcases hmem ℓ hℓ with ⟨α, -, rfl⟩ | rfl <;> rcases hmem ℓ' hℓ' with ⟨β, -, rfl⟩ | rfl
    · intro h
      obtain rfl : α = β := by linear_combination h
      exact hne rfl
    all_goals simp_all
  · intro ℓ hℓ
    rcases hmem ℓ hℓ with ⟨α, hα, rfl⟩ | rfl
    · exact Or.inr ⟨α, halg α hα, rfl⟩
    · exact Or.inl rfl
  · rw [hfac, Finset.prod_eq_multiset_prod]
    simp only [T, s, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X,
      map_multiset_prod, Multiset.map_map, Multiset.map_add, Multiset.prod_add,
      Multiset.map_replicate, Multiset.prod_replicate, Function.comp_def, map_sub]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul,
      one_mul, zero_add, neg_mul, ← sub_eq_add_neg]
    ring

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
  obtain ⟨a, ha, T, hTd, hT, hTL, heval⟩ := exists_linear_factors hF hF₀ hsq
  -- Each linear factor satisfies Roth's inequality: `X₁` trivially, `X₀ - α X₁` by Roth's theorem.
  have hL : ∀ ℓ ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ x y : ℤ, ℓ.1 * x + ℓ.2 * y ≠ 0 →
      c * max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ ‖ℓ.1 * x + ℓ.2 * y‖ := by
    intro ℓ hℓ
    rcases hTL ℓ hℓ with rfl | ⟨α, hα, rfl⟩
    · refine ⟨1, one_pos, fun x y hxy ↦ ?_⟩
      simp only [zero_mul, one_mul, zero_add, Complex.norm_intCast] at hxy ⊢
      have hy : y ≠ 0 := by exact_mod_cast hxy
      calc max |(x : ℝ)| |(y : ℝ)| ^ (1 - κ) ≤ 1 :=
            rpow_le_one_of_one_le_of_nonpos (one_le_max_abs_intCast (Or.inr hy)) (by linarith)
        _ ≤ |(y : ℝ)| := by exact_mod_cast Int.one_le_abs hy
    · obtain ⟨c, hc, h⟩ := hα.exists_pos_mul_max_abs_rpow_le_norm_sub_mul hκ
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
