/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
public import TauCeti.Geometry.Manifold.Instances.CircleFamily.Pullback

/-!
# Uniform derivative estimates for the normalized lift of a family of circles

Let `p : E → ℝ_{>0}` be a positive period function on a real normed space `E`, and let
`TauCeti.CircleFamily.Pullback p` be the family of the circles `AddCircle (p b)` over `E`. Its real
representatives are related to the normalized coordinates of `E × AddCircle 1` by the real
normalization (`TauCeti.CircleFamily.Pullback.realNormalization`)

`T (b, t) = (b, t / p b)`, with inverse `T⁻¹ (b, θ) = (b, θ * p b)`.

This file bounds every iterated derivative of `T` and of `T⁻¹` of positive order on a parameter
sector, in terms of the actual `C^k` bounds of the period function. Write `‖D^i p b‖` for the norm
of the `i`-th iterated derivative of `b ↦ (p b : ℝ)`.

* If `|t| ≤ R`, `ε ≤ p b` with `0 < ε ≤ 1`, and `‖D^i p b‖ ≤ C` for `1 ≤ i ≤ k` with `1 ≤ C`,
  then `‖D^k T (b, t)‖ ≤ (k!)^2 C^k (R + 1) / ε^(k+1)`
  (`TauCeti.CircleFamily.Pullback.norm_iteratedFDeriv_realNormalization_le`).
* If `|θ| ≤ Θ` and `‖D^i p b‖ ≤ C` for `i ≤ k` (so that `p b ≤ C`) with `1 ≤ C`, then
  `‖D^k T⁻¹ (b, θ)‖ ≤ (Θ + k) C`
  (`TauCeti.CircleFamily.Pullback.norm_iteratedFDeriv_realNormalization_symm_le`).

The lower bound `ε` on the period is essential: a positive period alone bounds neither `t / p` nor
its derivatives, and the derivative bounds of `p` are retained as hypotheses, since a positive
lower bound on `p` does not control its derivatives. The bounds are uniform over the whole window
`|t| ≤ R`; when `p b ≤ R`, this window contains a real lift of every point of the circle of period
`p b`. The zeroth derivative is excluded because `T` contains the identity of the unbounded base.

For a single variable period, the derivatives of `t / p` in `p` are computed exactly in
`TauCeti.iteratedDeriv_const_div`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (angle variables of a family of tori whose periods
  vary with the action variables).
-/

public section

open scoped Nat Manifold ContDiff

namespace TauCeti.CircleFamily.Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : E → PositivePeriod)
  {n : ℕ∞ω}

/-- A `C^n` positive period function is `C^n` as a real-valued function. -/
private theorem contDiff_coe_period (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) n p) :
    ContDiff ℝ n (fun x ↦ (p x : ℝ)) :=
  contMDiff_iff_contDiff.mp (contMDiff_subtype_val.comp hp)

/-- The bound `(k!)^2 C^k / ε^(k+1)` of `TauCeti.norm_iteratedFDeriv_inv_comp_le` is at least one
when `0 < ε ≤ 1` and `1 ≤ C`. -/
private theorem one_le_factorial_sq_mul_pow_div_pow (k : ℕ) {ε C : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hC : 1 ≤ C) : 1 ≤ (k ! : ℝ) ^ 2 * C ^ k / ε ^ (k + 1) := by
  rw [one_le_div (by positivity)]
  calc ε ^ (k + 1) ≤ 1 := pow_le_one₀ hε.le hε₁
    _ ≤ (k ! : ℝ) ^ 2 * C ^ k :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by exact_mod_cast k.factorial_pos))
        (one_le_pow₀ hC)

/-- For `0 < ε ≤ 1` and `1 ≤ C`, `k + 1` times the bound `(k!)^2 C^k / ε^(k+1)` of
`TauCeti.norm_iteratedFDeriv_inv_comp_le` is at most the bound of order `k + 1`. -/
private theorem succ_mul_factorial_sq_mul_pow_div_pow_le (k : ℕ) {ε C : ℝ} (hε : 0 < ε)
    (hε₁ : ε ≤ 1) (hC : 1 ≤ C) :
    ((k + 1 : ℕ) : ℝ) * ((k ! : ℝ) ^ 2 * C ^ k / ε ^ (k + 1)) ≤
      ((k + 1) ! : ℝ) ^ 2 * C ^ (k + 1) / ε ^ (k + 1 + 1) := by
  have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 k
  calc ((k + 1 : ℕ) : ℝ) * ((k ! : ℝ) ^ 2 * C ^ k / ε ^ (k + 1))
      ≤ ((k + 1 : ℕ) : ℝ) * ((k ! : ℝ) ^ 2 * C ^ (k + 1) / ε ^ (k + 1 + 1)) := by
        gcongr _ * (_ * ?_ / ?_)
        · exact pow_le_pow_right₀ hC k.le_succ
        · exact pow_le_pow_of_le_one hε.le hε₁ (k + 1).le_succ
    _ ≤ ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) * ((k ! : ℝ) ^ 2 * C ^ (k + 1) / ε ^ (k + 1 + 1))) := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hk
    _ = ((k + 1) ! : ℝ) ^ 2 * C ^ (k + 1) / ε ^ (k + 1 + 1) := by
        rw [Nat.factorial_succ]
        push_cast
        ring

/-- **Uniform derivative bounds for the real normalization.** Let `p` be a `C^n` positive period
function and `1 ≤ k ≤ n`. At a point `(b, t)` with `|t| ≤ R`, `ε ≤ p b` for some `0 < ε ≤ 1`, and
`‖D^i p b‖ ≤ C` for `1 ≤ i ≤ k` with `1 ≤ C`, the `k`-th iterated derivative of
`(b, t) ↦ (b, t / p b)` has norm at most `(k!)^2 C^k (R + 1) / ε^(k+1)`. -/
theorem norm_iteratedFDeriv_realNormalization_le (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) n p) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) {z : E × ℝ} {R ε C : ℝ} (hz : |z.2| ≤ R) (hε : 0 < ε)
    (hε₁ : ε ≤ 1) (hpz : ε ≤ p z.1) (hC : 1 ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (fun x ↦ (p x : ℝ)) z.1‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (realNormalization p 𝓘(ℝ, E) hp) z‖ ≤
      (k ! : ℝ) ^ 2 * C ^ k * (R + 1) / ε ^ (k + 1) := by
  have hq : ContDiff ℝ k (fun x ↦ (p x : ℝ)) := (contDiff_coe_period p hp).of_le hkn
  have hpos : ∀ x, 0 < (p x : ℝ) := fun x ↦ (p x).property
  have hinv : ContDiff ℝ k (fun x ↦ (p x : ℝ)⁻¹) := hq.inv fun x ↦ (hpos x).ne'
  have hR : 0 ≤ R := (abs_nonneg _).trans hz
  have hcoe : ⇑(realNormalization p 𝓘(ℝ, E) hp) =
      fun w : E × ℝ ↦ (w.1, w.2 * (p w.1 : ℝ)⁻¹) := by
    funext w
    rw [realNormalization_apply, div_eq_mul_inv]
  rw [hcoe]
  refine (norm_iteratedFDeriv_fst_prodMk_snd_mul_comp_fst_le hinv hk z).trans ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  -- The bound `X` on the last derivative of `p⁻¹`, which dominates the previous one.
  set X : ℝ := ((m + 1) ! : ℝ) ^ 2 * C ^ (m + 1) / ε ^ (m + 1 + 1) with hX
  have hX₁ : 1 ≤ X := one_le_factorial_sq_mul_pow_div_pow (m + 1) hε hε₁ hC
  have hlast : ‖iteratedFDeriv ℝ (m + 1) (fun x ↦ (p x : ℝ)⁻¹) z.1‖ ≤ X :=
    norm_iteratedFDeriv_inv_comp_le hq hε hε₁ hpz hC hD
  have hprev : ((m + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ m (fun x ↦ (p x : ℝ)⁻¹) z.1‖ ≤ X := by
    have h := norm_iteratedFDeriv_inv_comp_le (hq.of_le (by exact_mod_cast Nat.le_succ m))
      hε hε₁ hpz hC fun i hi₁ hi ↦ hD i hi₁ (hi.trans (Nat.le_succ m))
    calc ((m + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ m (fun x ↦ (p x : ℝ)⁻¹) z.1‖
        ≤ ((m + 1 : ℕ) : ℝ) * ((m ! : ℝ) ^ 2 * C ^ m / ε ^ (m + 1)) := by gcongr
      _ ≤ X := succ_mul_factorial_sq_mul_pow_div_pow_le m hε hε₁ hC
  refine max_le ?_ ?_
  · calc (1 : ℝ) ≤ X := hX₁
      _ ≤ X * (R + 1) := le_mul_of_one_le_right (by positivity) (by linarith)
      _ = _ := by rw [hX]; ring
  · rw [Nat.add_sub_cancel, Real.norm_eq_abs]
    calc |z.2| * ‖iteratedFDeriv ℝ (m + 1) (fun x ↦ (p x : ℝ)⁻¹) z.1‖ +
          ((m + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ m (fun x ↦ (p x : ℝ)⁻¹) z.1‖
        ≤ R * X + X := by gcongr
      _ = _ := by rw [hX]; ring

/-- **Uniform derivative bounds for the inverse real normalization.** Let `p` be a `C^n` positive
period function and `1 ≤ k ≤ n`. At a point `(b, θ)` with `|θ| ≤ Θ` and `‖D^i p b‖ ≤ C` for all
`i ≤ k` with `1 ≤ C`, the `k`-th iterated derivative of `(b, θ) ↦ (b, θ * p b)` has norm at most
`(Θ + k) C`. The case `i = 0` of the hypothesis is the upper bound `p b ≤ C` on the period. -/
theorem norm_iteratedFDeriv_realNormalization_symm_le (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) n p)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {z : E × ℝ} {Θ C : ℝ} (hz : |z.2| ≤ Θ) (hC : 1 ≤ C)
    (hD : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (fun x ↦ (p x : ℝ)) z.1‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (realNormalization p 𝓘(ℝ, E) hp).symm z‖ ≤ (Θ + k) * C := by
  have hq : ContDiff ℝ k (fun x ↦ (p x : ℝ)) := (contDiff_coe_period p hp).of_le hkn
  have hΘ : 0 ≤ Θ := (abs_nonneg _).trans hz
  have hcoe : ⇑(realNormalization p 𝓘(ℝ, E) hp).symm =
      fun w : E × ℝ ↦ (w.1, w.2 * (p w.1 : ℝ)) := by
    funext w
    rw [realNormalization_symm_apply]
  rw [hcoe]
  refine (norm_iteratedFDeriv_fst_prodMk_snd_mul_comp_fst_le hq hk z).trans ?_
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine max_le ?_ ?_
  · nlinarith
  · rw [Real.norm_eq_abs]
    calc |z.2| * ‖iteratedFDeriv ℝ k (fun x ↦ (p x : ℝ)) z.1‖ +
          (k : ℝ) * ‖iteratedFDeriv ℝ (k - 1) (fun x ↦ (p x : ℝ)) z.1‖
        ≤ Θ * C + k * C := by
          gcongr
          · exact hD k le_rfl
          · exact hD (k - 1) (Nat.sub_le k 1)
      _ = (Θ + k) * C := by ring

end TauCeti.CircleFamily.Pullback
