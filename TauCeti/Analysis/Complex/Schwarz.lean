/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import TauCeti.Analysis.Analytic.ExtractZeros

/-!
# Schwarz's lemma with prescribed zeros

Let `f` be analytic on a neighbourhood of the closed disc `closedBall c T`, bounded by `M` on the
circle `sphere c T`, and vanishing to order at least `k x` at each point `x` of a finite set `s`
inside the open disc. Dividing out the zeros, `f = (∏ x ∈ s, (· - x) ^ k x) • g` with `g`
analytic, and the maximum modulus principle applied to `g` gives
`‖f z‖ ≤ M * ∏ x ∈ s, (‖z - x‖ / (T - ‖x - c‖)) ^ k x` on the closed disc.

When the zeros and the point `z` lie in the smaller disc `closedBall c R` with `3 * R ≤ T`, every
factor is at most `3 * R / T`, so `‖f z‖ ≤ M * (3 * R / T) ^ ∑ x ∈ s, k x`. This is the
analytic estimate of transcendence proofs: an auxiliary function with many zeros in a small disc
is very small there.

## Main results

* `TauCeti.norm_le_mul_prod_div_pow`: the bound by the product over the zeros.
* `TauCeti.norm_le_mul_three_mul_div_pow`: the bound `M * (3 * R / T) ^ ∑ x ∈ s, k x`.

## References

* J.-H. Evertse, *Diophantine approximation*, lecture notes (2019), ch. 4, §4.4, Lemma 4.26.
* M. Waldschmidt, *Diophantine approximation on linear algebraic groups*, Springer (2000), §2.2,
  Lemma 2.4.
-/

public section

open Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} {T M : ℝ}
  {s : Finset ℂ} {k : ℂ → ℕ}

/-- **Schwarz's lemma with prescribed zeros.** If `f` is analytic on a neighbourhood of
`closedBall c T`, bounded by `M` on `sphere c T`, and vanishes to order at least `k x` at each
point `x` of a finite set `s ⊆ ball c T`, then on `closedBall c T`
`‖f z‖ ≤ M * ∏ x ∈ s, (‖z - x‖ / (T - ‖x - c‖)) ^ k x`. -/
theorem norm_le_mul_prod_div_pow (hf : AnalyticOnNhd ℂ f (closedBall c T))
    (hk : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt f x) (hs : (s : Set ℂ) ⊆ ball c T)
    (hM : ∀ w ∈ sphere c T, ‖f w‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall c T) :
    ‖f z‖ ≤ M * ∏ x ∈ s, (‖z - x‖ / (T - ‖x - c‖)) ^ k x := by
  have hsT (x : ℂ) (hx : x ∈ s) : ‖x - c‖ < T := by
    simpa [dist_eq_norm] using hs hx
  rcases le_or_gt T 0 with hT | hT
  · -- A degenerate disc has no interior zeros, and `z` lies on the circle.
    have hs₀ : s = ∅ := Finset.eq_empty_of_forall_notMem fun x hx ↦
      (hsT x hx).not_ge (hT.trans (norm_nonneg _))
    subst hs₀
    have hzc : dist z c = T := le_antisymm (mem_closedBall.mp hz) (hT.trans dist_nonneg)
    simpa using hM z (mem_sphere.mpr hzc)
  obtain ⟨g, hg, hfg⟩ := hf.exists_eq_prod_pow_smul s k hk
  set Q : ℝ := ∏ x ∈ s, (T - ‖x - c‖) ^ k x
  have hQ : 0 < Q := Finset.prod_pos fun x hx ↦ pow_pos (sub_pos.mpr (hsT x hx)) _
  have hnorm (w : ℂ) : ‖f w‖ = (∏ x ∈ s, ‖w - x‖ ^ k x) * ‖g w‖ := by
    rw [hfg, norm_smul, norm_prod]
    simp [norm_pow]
  -- On the circle, each factor `‖w - x‖` is at least `T - ‖x - c‖`, so `‖g w‖ ≤ M / Q`.
  have hgM (w : ℂ) (hw : w ∈ frontier (ball c T)) : ‖g w‖ ≤ M / Q := by
    rw [frontier_ball c hT.ne', mem_sphere, dist_eq_norm] at hw
    have hPQ : Q ≤ ∏ x ∈ s, ‖w - x‖ ^ k x :=
      Finset.prod_le_prod₀ (fun x hx ↦ pow_nonneg (sub_pos.mpr (hsT x hx)).le _)
        fun x _ ↦ pow_le_pow_left₀ (sub_pos.mpr (hsT x ‹_›)).le
          (by linarith [norm_sub_le_norm_sub_add_norm_sub w x c]) _
    rw [le_div_iff₀ hQ, mul_comm]
    calc Q * ‖g w‖ ≤ (∏ x ∈ s, ‖w - x‖ ^ k x) * ‖g w‖ :=
          mul_le_mul_of_nonneg_right hPQ (norm_nonneg _)
      _ = ‖f w‖ := (hnorm w).symm
      _ ≤ M := hM w (by rw [mem_sphere, dist_eq_norm, hw])
  have hgz : ‖g z‖ ≤ M / Q :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hg.differentiableOn.diffContOnCl_ball subset_rfl) hgM
      (by rwa [closure_ball c hT.ne'])
  calc ‖f z‖ = (∏ x ∈ s, ‖z - x‖ ^ k x) * ‖g z‖ := hnorm z
    _ ≤ (∏ x ∈ s, ‖z - x‖ ^ k x) * (M / Q) :=
        mul_le_mul_of_nonneg_left hgz (Finset.prod_nonneg fun _ _ ↦ by positivity)
    _ = M * ∏ x ∈ s, (‖z - x‖ / (T - ‖x - c‖)) ^ k x := by
        simp only [Q, div_pow, Finset.prod_div_distrib]
        ring

/-- **Schwarz's lemma with prescribed zeros**, in the form `M * (3 * R / T) ^ ∑ x ∈ s, k x`. If
`f` is analytic on a neighbourhood of `closedBall c T`, bounded by `M` on `sphere c T`, and
vanishes to order at least `k x` at each point `x` of a finite set `s ⊆ closedBall c R`, where
`3 * R ≤ T`, then `‖f z‖ ≤ M * (3 * R / T) ^ ∑ x ∈ s, k x` on `closedBall c R`. -/
theorem norm_le_mul_three_mul_div_pow {R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c T))
    (hk : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt f x) (hs : (s : Set ℂ) ⊆ closedBall c R)
    (hRT : 3 * R ≤ T) (hM : ∀ w ∈ sphere c T, ‖f w‖ ≤ M) {z : ℂ}
    (hz : z ∈ closedBall c R) : ‖f z‖ ≤ M * (3 * R / T) ^ ∑ x ∈ s, k x := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_closedBall.mp hz)
  have hzc : ‖z - c‖ ≤ R := by simpa [dist_eq_norm] using hz
  have hsR (x : ℂ) (hx : x ∈ s) : ‖x - c‖ ≤ R := by
    simpa [dist_eq_norm] using hs hx
  rcases (show 0 ≤ T by linarith).eq_or_lt with hT | hT
  · -- A degenerate disc: `R = 0`, so `z = c` and every zero is `c`, while `3 * R / T = 0`.
    subst hT
    have hzc₀ : z = c := by simpa [show R = 0 by linarith] using hz
    subst hzc₀
    rw [div_zero]
    rcases Nat.eq_zero_or_pos (∑ x ∈ s, k x) with h0 | hpos
    · simpa [h0] using hM z (by simp)
    -- Some zero has positive multiplicity; it lies at `z`, so `f z = 0`.
    obtain ⟨x, hx, hkx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    have hxz : x = z := by simpa [show R = 0 by linarith] using hs hx
    subst hxz
    have hfx : f x = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero
      (lt_of_lt_of_le (mod_cast Nat.pos_of_ne_zero hkx) (hk x hx)).ne'
    simp [hfx, zero_pow hpos.ne']
  have hM₀ : 0 ≤ M :=
    (norm_nonneg _).trans (hM (c + T) (by simp [abs_of_pos hT]))
  have hRT' : R < T := by linarith
  refine (norm_le_mul_prod_div_pow hf hk
    (hs.trans (closedBall_subset_ball hRT')) hM
    (closedBall_subset_closedBall hRT'.le hz)).trans ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
    (fun x hx ↦ pow_nonneg (div_nonneg (norm_nonneg _) (by linarith [hsR x hx])) _)
    fun x hx ↦ pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by linarith [hsR x hx])) ?_ _) hM₀
  -- `‖z - x‖ ≤ ‖z - c‖ + ‖x - c‖ ≤ 2 * R`, and `T - ‖x - c‖ ≥ T - R ≥ 2 * T / 3`.
  have hd := hsR x hx
  have hzx : ‖z - x‖ ≤ R + ‖x - c‖ := by
    linarith [norm_sub_le_norm_sub_add_norm_sub z c x, norm_sub_rev c x]
  rw [div_le_div_iff₀ (by linarith) hT]
  nlinarith [norm_nonneg (x - c)]

end TauCeti
