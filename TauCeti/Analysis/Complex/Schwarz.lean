/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import TauCeti.Analysis.Analytic.ExtractZeros
public import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz

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

At a zero `a ∈ s` itself the same quotient controls the derivative of order `k a`: since
`f = (z - a) ^ k a • h` with `h = (∏ x ∈ s \ {a}, (· - x) ^ k x) • g`, Leibniz's rule gives
`f⁽ᵏ⁽ᵃ⁾⁾(a) = (k a)! • h a`. This bounds the first nonvanishing derivative of an auxiliary function
at one of its zeros, as in Gelfond's proof of the Gelfond–Schneider theorem.

## Main results

* `TauCeti.norm_le_mul_prod_div_pow`: the bound by the product over the zeros.
* `TauCeti.norm_le_mul_three_mul_div_pow`: the bound `M * (3 * R / T) ^ ∑ x ∈ s, k x`.
* `TauCeti.norm_iteratedDeriv_le_mul_prod_div_pow`: the bound for the derivative of order `k a`
  at a zero `a ∈ s`.

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

/-- The norm of `f = (∏ x ∈ s, (· - x) ^ k x) • g` is the product of the distances to the zeros
times the norm of the quotient. -/
private theorem norm_eq_prod_mul_of_eq_prod_pow_smul {g : ℂ → E}
    (hfg : ∀ z, f z = (∏ x ∈ s, (z - x) ^ k x) • g z) (w : ℂ) :
    ‖f w‖ = (∏ x ∈ s, ‖w - x‖ ^ k x) * ‖g w‖ := by
  rw [hfg, norm_smul, norm_prod]
  simp [norm_pow]

/-- The maximum modulus step of Schwarz's lemma: if `f = (∏ x ∈ s, (· - x) ^ k x) • g` with `g`
analytic on a neighbourhood of `closedBall c T`, `f` is bounded by `M` on `sphere c T` and every
`x ∈ s` satisfies `‖x - c‖ < T`, then `‖g z‖ ≤ M / ∏ x ∈ s, (T - ‖x - c‖) ^ k x` on the disc. -/
private theorem norm_le_div_prod_of_eq_prod_pow_smul (hT : 0 < T) {g : ℂ → E}
    (hg : AnalyticOnNhd ℂ g (closedBall c T)) (hfg : ∀ z, f z = (∏ x ∈ s, (z - x) ^ k x) • g z)
    (hsT : ∀ x ∈ s, ‖x - c‖ < T) (hM : ∀ w ∈ sphere c T, ‖f w‖ ≤ M) {z : ℂ}
    (hz : z ∈ closedBall c T) : ‖g z‖ ≤ M / ∏ x ∈ s, (T - ‖x - c‖) ^ k x := by
  set Q : ℝ := ∏ x ∈ s, (T - ‖x - c‖) ^ k x
  have hQ : 0 < Q := Finset.prod_pos fun x hx ↦ pow_pos (sub_pos.mpr (hsT x hx)) _
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
      _ = ‖f w‖ := (norm_eq_prod_mul_of_eq_prod_pow_smul hfg w).symm
      _ ≤ M := hM w (by rw [mem_sphere, dist_eq_norm, hw])
  exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hg.differentiableOn.diffContOnCl_ball subset_rfl) hgM (by rwa [closure_ball c hT.ne'])

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
  have hgz : ‖g z‖ ≤ M / Q := norm_le_div_prod_of_eq_prod_pow_smul hT hg hfg hsT hM hz
  calc ‖f z‖ = (∏ x ∈ s, ‖z - x‖ ^ k x) * ‖g z‖ := norm_eq_prod_mul_of_eq_prod_pow_smul hfg z
    _ ≤ (∏ x ∈ s, ‖z - x‖ ^ k x) * (M / Q) :=
        mul_le_mul_of_nonneg_left hgz (Finset.prod_nonneg fun _ _ ↦ by positivity)
    _ = M * ∏ x ∈ s, (‖z - x‖ / (T - ‖x - c‖)) ^ k x := by
        simp only [Q, div_pow, Finset.prod_div_distrib]
        ring

/-- **Schwarz's lemma for the first nonvanishing derivative.** If `f` is analytic on a
neighbourhood of `closedBall c T`, bounded by `M` on `sphere c T`, and vanishes to order at least
`k x` at each point `x` of a finite set `s ⊆ ball c T`, then at every `a ∈ s`
`‖f⁽ᵏ⁽ᵃ⁾⁾(a)‖ ≤ k(a)! M / (T - ‖a - c‖) ^ k(a) * ∏ x ∈ s \ {a}, (‖a - x‖ / (T - ‖x - c‖)) ^ k x`. -/
theorem norm_iteratedDeriv_le_mul_prod_div_pow (hf : AnalyticOnNhd ℂ f (closedBall c T))
    (hk : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt f x) (hs : (s : Set ℂ) ⊆ ball c T)
    (hM : ∀ w ∈ sphere c T, ‖f w‖ ≤ M) {a : ℂ} (ha : a ∈ s) :
    ‖iteratedDeriv (k a) f a‖ ≤ (k a).factorial * M / (T - ‖a - c‖) ^ k a *
      ∏ x ∈ s.erase a, (‖a - x‖ / (T - ‖x - c‖)) ^ k x := by
  have hsT (x : ℂ) (hx : x ∈ s) : ‖x - c‖ < T := by
    simpa [dist_eq_norm] using hs hx
  have hT : 0 < T := (norm_nonneg _).trans_lt (hsT a ha)
  obtain ⟨g, hg, hfg⟩ := hf.exists_eq_prod_pow_smul s k hk
  have hac : a ∈ closedBall c T := ball_subset_closedBall (hs ha)
  have hgz : ‖g a‖ ≤ M / ∏ x ∈ s, (T - ‖x - c‖) ^ k x :=
    norm_le_div_prod_of_eq_prod_pow_smul hT hg hfg hsT hM hac
  -- Splitting off the factor `(z - a) ^ k a`, the derivative of order `k a` at `a` is
  -- `(k a)!` times the value of the remaining product times `g` at `a`.
  have hfa : f = fun z ↦ (z - a) ^ k a • ((∏ x ∈ s.erase a, (z - x) ^ k x) • g z) := by
    funext z
    rw [hfg, ← Finset.mul_prod_erase s _ ha, mul_smul]
  have hder : iteratedDeriv (k a) f a =
      (k a).factorial • ((∏ x ∈ s.erase a, (a - x) ^ k x) • g a) := by
    have hh : AnalyticOnNhd ℂ (fun z ↦ (∏ x ∈ s.erase a, (z - x) ^ k x) • g z) (ball c T) :=
      fun z hz ↦ ((s.erase a).analyticAt_fun_prod fun x _ ↦ by fun_prop).smul
        (hg z (ball_subset_closedBall hz))
    rw [hfa]
    exact iteratedDeriv_pow_sub_smul_self ((hh.analyticOn.contDiffOn
      isOpen_ball.uniqueDiffOn).contDiffAt (isOpen_ball.mem_nhds (hs ha)))
  have hQ : ∏ x ∈ s, (T - ‖x - c‖) ^ k x =
      (T - ‖a - c‖) ^ k a * ∏ x ∈ s.erase a, (T - ‖x - c‖) ^ k x :=
    (Finset.mul_prod_erase s _ ha).symm
  have hQ₀ : 0 < ∏ x ∈ s.erase a, (T - ‖x - c‖) ^ k x :=
    Finset.prod_pos fun x hx ↦ pow_pos (sub_pos.mpr (hsT x (Finset.mem_of_mem_erase hx))) _
  have hTa : 0 < (T - ‖a - c‖) ^ k a := pow_pos (sub_pos.mpr (hsT a ha)) _
  calc ‖iteratedDeriv (k a) f a‖
      = (k a).factorial * ((∏ x ∈ s.erase a, ‖a - x‖ ^ k x) * ‖g a‖) := by
        rw [hder, ← Nat.cast_smul_eq_nsmul ℂ, norm_smul, norm_smul, norm_prod]
        simp [norm_pow]
    _ ≤ (k a).factorial * ((∏ x ∈ s.erase a, ‖a - x‖ ^ k x) *
          (M / ((T - ‖a - c‖) ^ k a * ∏ x ∈ s.erase a, (T - ‖x - c‖) ^ k x))) := by
        rw [← hQ]
        gcongr
    _ = (k a).factorial * M / (T - ‖a - c‖) ^ k a *
          ∏ x ∈ s.erase a, (‖a - x‖ / (T - ‖x - c‖)) ^ k x := by
        simp only [div_pow, Finset.prod_div_distrib]
        field_simp

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
