/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
public import TauCeti.Analysis.InnerProductSpace.Laplacian.IteratedFDeriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.IteratedFDeriv.LeibnizRemainder
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Exponential decay of all derivatives of solutions of `Δu = G(u)`

Let `G : ℝ → ℝ` be smooth with `G'(0) > 0`, and let `u` be a smooth solution of the semilinear
equation `Δu = G(u)` outside a ball in a finite-dimensional real inner product space, with `u → 0`
at infinity. The linearization of the equation at the vacuum `u = 0` is the massive operator
`Δ - G'(0)`, and this file shows that every derivative of `u` of positive order decays at every
rate `c` with `c² < G'(0)`:

`‖Dⁿ⁺¹u z‖ ≤ K exp (-c ‖z‖)` far out
(`TauCeti.exists_norm_iteratedFDeriv_succ_le_mul_exp_of_laplacian_eq`).

Such equations govern the profiles of massive fields, for instance the logarithmic modulus
`log |α|²` of a plane vortex, which solves `Δ ℓ = (exp ℓ - 1) / 4`. The decay of all derivatives
is what places such a profile, after subtracting its asymptotic model, in every Sobolev space.

## The argument

The decay of each derivative is proved by comparison with the barrier `exp (-c ‖z‖)` on the
exterior of a ball, applied to translation differences `d = w - w (· + h)` rather than to the
derivative itself, whose limit at infinity is not known in advance. If `d` solves `Δ d = V d` up
to an error `‖h‖ G exp (-c ‖z‖)`, with `V ≥ c'²` and `c < c'`, the comparison principle with a
source (`TauCeti.le_mul_exp_add_of_mul_le_laplacian_add`) bounds `|d|` by a multiple of
`‖h‖ exp (-c ‖z‖)`, and dividing by `‖h‖` bounds the gradient of `w`.

* For `w = u` the differences solve `Δ d = V d` exactly, with `V` a difference quotient of `G`,
  which exceeds `c'²` where `u` is small.
* For `w = Dⁿu (·) m`, `n ≥ 1`, the Laplacian commutes with the derivatives
  (`TauCeti.laplacian_iteratedFDeriv_apply`), so `Δ w = G'(u) w + f`, where
  `f = Dⁿ(G ∘ u) m - G'(u) Dⁿu m`. By the Leibniz rule, `Dⁿ⁺¹(G ∘ u) - G'(u) Dⁿ⁺¹u` only involves
  derivatives of `u` of order at most `n`, so by induction the gradient of `f` decays, and so does
  the error in the equation for `d`.

The solution is first cut off near the ball, so that the Leibniz and chain rule bounds of Mathlib
for globally smooth functions apply.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, Chapter 3 (comparison with barriers).
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti

open Filter Metric Set Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Decay of a translation difference.** Let `w` be `C²` outside the ball of radius `R > 0`,
tend to zero at infinity, and have gradient at most `L` on the annulus `R + 1 ≤ ‖z‖ ≤ R + 3`. If
`‖h‖ ≤ 1` and `d = w - w (· + h)` satisfies `Δ d = V d` up to an error `‖h‖ G exp (-c ‖z‖)`, for a
potential `V ≥ c'²` with `0 < c < c'`, then `|d y| ≤ ‖h‖ K exp (-c ‖y‖)` for `‖y‖ ≥ R + 2`, with
`K = L exp (c (R + 2)) + G / (c'² - c²)`. -/
private theorem abs_sub_comp_add_le_mul_exp {w V : E → ℝ} {R c c' L G : ℝ} {h : E} (hR : 0 < R)
    (hc : 0 < c) (hcc' : c < c') (hL : 0 ≤ L) (hG : 0 ≤ G) (hh : ‖h‖ ≤ 1)
    (hw : ∀ z, R < ‖z‖ → ContDiffAt ℝ 2 w z) (hlim : Tendsto w (cocompact E) (𝓝 0))
    (hwL : ∀ z, R + 1 ≤ ‖z‖ → ‖z‖ ≤ R + 3 → ‖fderiv ℝ w z‖ ≤ L)
    (hV : ∀ z, R + 1 < ‖z‖ → c' ^ 2 ≤ V z)
    (heq : ∀ z, R + 1 < ‖z‖ →
      |Δ w z - Δ w (z + h) - V z * (w z - w (z + h))| ≤ ‖h‖ * G * Real.exp (-(c * ‖z‖)))
    {y : E} (hy : R + 2 ≤ ‖y‖) :
    |w y - w (y + h)| ≤
      ‖h‖ * (L * Real.exp (c * (R + 2)) + G / (c' ^ 2 - c ^ 2)) * Real.exp (-(c * ‖y‖)) := by
  set K := L * Real.exp (c * (R + 2)) + G / (c' ^ 2 - c ^ 2)
  have hgap : 0 < c' ^ 2 - c ^ 2 := by nlinarith
  have hR₁ : 0 < R + 2 := by linarith
  have hnorm : ∀ y : E, ‖y‖ - 1 ≤ ‖y + h‖ := fun y ↦ by
    have := norm_sub_le (y + h) h
    rw [add_sub_cancel_right] at this
    linarith
  set d : E → ℝ := fun y ↦ w y - w (y + h)
  have hsh : ∀ y : E, R + 1 < ‖y‖ → ContDiffAt ℝ 2 (fun y ↦ w (y + h)) y := fun y hy ↦
    (hw (y + h) (by linarith [hnorm y])).comp y (contDiffAt_id.add contDiffAt_const)
  have hdcd : ∀ y : E, R + 1 < ‖y‖ → ContDiffAt ℝ 2 d y := fun y hy ↦
    (hw y (by linarith)).sub (hsh y hy)
  have hdΔ : ∀ y : E, R + 1 < ‖y‖ → Δ d y = Δ w y - Δ w (y + h) := fun y hy ↦ by
    have hd : d = w - fun y ↦ w (y + h) := rfl
    rw [hd, (hw y (by linarith)).laplacian_sub (hsh y hy), laplacian_comp_add_right]
  have hdcont : ContinuousOn d {y | R + 2 ≤ ‖y‖} := fun y hy ↦
    (hdcd y (by have hy' : R + 2 ≤ ‖y‖ := hy; linarith)).continuousAt.continuousWithinAt
  have hdlim : Tendsto d (cocompact E) (𝓝 0) := by
    have := hlim.sub (hlim.comp (Homeomorph.addRight h).isClosedEmbedding.tendsto_cocompact)
    rwa [sub_zero] at this
  -- On the sphere `‖y‖ = R + 2` the mean value inequality bounds `|d|` by `L ‖h‖`.
  have hbdry : ∀ y : E, ‖y‖ = R + 2 → |d y| ≤ L * ‖h‖ := fun y hy ↦ by
    have hball : ∀ p ∈ closedBall y 1, R + 1 ≤ ‖p‖ ∧ ‖p‖ ≤ R + 3 := fun p hp ↦ by
      have h₁ := norm_le_of_mem_closedBall hp
      have h₂ := norm_le_of_mem_closedBall (mem_closedBall_comm.mp hp)
      constructor <;> linarith
    have hmv := (convex_closedBall y 1).norm_image_sub_le_of_norm_fderiv_le (f := w) (C := L)
      (fun p hp ↦ (hw p (by linarith [(hball p hp).1])).differentiableAt (by norm_num))
      (fun p hp ↦ hwL p (hball p hp).1 (hball p hp).2) (mem_closedBall_self zero_le_one)
      (by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
    rw [add_sub_cancel_left, Real.norm_eq_abs, abs_sub_comm] at hmv
    exact hmv
  -- Compare `d` and `-d` with the barrier.
  have hexp : ∀ y : E, R + 2 ≤ ‖y‖ →
      L * ‖h‖ * Real.exp (-(c' * (‖y‖ - (R + 2)))) + ‖h‖ * G / (c' ^ 2 - c ^ 2) *
        Real.exp (-(c * ‖y‖)) ≤ ‖h‖ * K * Real.exp (-(c * ‖y‖)) := fun y hy ↦ by
    have h₁ : Real.exp (-(c' * (‖y‖ - (R + 2)))) ≤
        Real.exp (c * (R + 2)) * Real.exp (-(c * ‖y‖)) := by
      rw [← exp_neg_mul_sub]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have h₂ : 0 ≤ L * ‖h‖ := by positivity
    calc L * ‖h‖ * Real.exp (-(c' * (‖y‖ - (R + 2)))) + ‖h‖ * G / (c' ^ 2 - c ^ 2) *
          Real.exp (-(c * ‖y‖))
        ≤ L * ‖h‖ * (Real.exp (c * (R + 2)) * Real.exp (-(c * ‖y‖))) +
          ‖h‖ * G / (c' ^ 2 - c ^ 2) * Real.exp (-(c * ‖y‖)) := by gcongr
      _ = ‖h‖ * K * Real.exp (-(c * ‖y‖)) := by ring
  have hup := le_mul_exp_add_of_mul_le_laplacian_add (u := d) (V := V) hR₁ hc hcc'
    (by positivity) (by positivity : 0 ≤ ‖h‖ * G) hdcont (fun y hy ↦ hdcd y (by linarith))
    (fun y hy ↦ hV y (by linarith)) (fun y hy ↦ by
      have := heq y (by linarith)
      rw [abs_le] at this
      rw [hdΔ y (by linarith)]
      linarith) (fun y hy ↦ (le_abs_self _).trans (hbdry y hy)) hdlim hy
  have hlow := le_mul_exp_add_of_mul_le_laplacian_add (u := -d) (V := V) hR₁ hc hcc'
    (by positivity) (by positivity : 0 ≤ ‖h‖ * G) hdcont.neg
    (fun y hy ↦ (hdcd y (by linarith)).neg) (fun y hy ↦ hV y (by linarith))
    (fun y hy ↦ by
      have := heq y (by linarith)
      rw [abs_le] at this
      rw [laplacian_neg, Pi.neg_apply, Pi.neg_apply, hdΔ y (by linarith)]
      linarith) (fun y hy ↦ (neg_le_abs _).trans (hbdry y hy))
    (by have := hdlim.neg; rwa [neg_zero] at this) hy
  rw [Pi.neg_apply] at hlow
  rw [abs_le]
  constructor <;> linarith [hexp y hy]

/-- **Gradient decay from the difference equations.** If for every `h` with `‖h‖ ≤ 1` the
translation difference `w - w (· + h)` satisfies the hypotheses of
`abs_sub_comp_add_le_mul_exp`, then `‖Dw z‖ ≤ K exp (-c ‖z‖)` for `‖z‖ ≥ R + 2`, with
`K = L exp (c (R + 2)) + G / (c'² - c²)`. -/
private theorem norm_fderiv_le_of_abs_laplacian_sub_sub_le {w : E → ℝ} {R c c' L G : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hcc' : c < c') (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hw : ∀ z, R < ‖z‖ → ContDiffAt ℝ 2 w z) (hlim : Tendsto w (cocompact E) (𝓝 0))
    (hwL : ∀ z, R + 1 ≤ ‖z‖ → ‖z‖ ≤ R + 3 → ‖fderiv ℝ w z‖ ≤ L)
    (heq : ∀ h : E, ‖h‖ ≤ 1 → ∃ V : E → ℝ, ∀ z, R + 1 < ‖z‖ → c' ^ 2 ≤ V z ∧
      |Δ w z - Δ w (z + h) - V z * (w z - w (z + h))| ≤ ‖h‖ * G * Real.exp (-(c * ‖z‖)))
    {z : E} (hz : R + 2 ≤ ‖z‖) :
    ‖fderiv ℝ w z‖ ≤
      (L * Real.exp (c * (R + 2)) + G / (c' ^ 2 - c ^ 2)) * Real.exp (-(c * ‖z‖)) := by
  have hgap : 0 < c' ^ 2 - c ^ 2 := by nlinarith
  refine norm_fderiv_le_of_lip' ℝ (by positivity) ?_
  filter_upwards [closedBall_mem_nhds z one_pos] with y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  obtain ⟨V, hV⟩ := heq (y - z) hy
  have h := abs_sub_comp_add_le_mul_exp hR hc hcc' hL hG hy hw hlim hwL (fun x hx ↦ (hV x hx).1)
    (fun x hx ↦ (hV x hx).2) hz
  rw [add_sub_cancel, abs_sub_comm] at h
  rw [Real.norm_eq_abs]
  exact h.trans_eq (by ring)

/-- **Gradient decay for `Δu = G(u)`.** Let `u` be `C²` with `Δu = G(u)` outside a ball and
`u → 0` at infinity, where `G` is `C¹` with `G' > c'²` on `(-δ, δ)`. Then `‖Du z‖ ≤ K exp (-c ‖z‖)`
far out, for every `0 < c < c'`. The differences `u - u (· + h)` solve `Δ d = V d` for a
difference quotient `V` of `G`, which is at least `c'²` where `u` is small. -/
private theorem exists_norm_fderiv_le_mul_exp_of_laplacian_eq {u : E → ℝ} {G : ℝ → ℝ}
    {R c c' δ : ℝ} (hG : ContDiff ℝ 1 G) (hc : 0 < c) (hcc' : c < c') (hδ : 0 < δ)
    (hδG : ∀ t, |t| < δ → c' ^ 2 < deriv G t) (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ z, R < ‖z‖ → Δ u z = G (u z)) (hlim : Tendsto u (cocompact E) (𝓝 0)) :
    ∃ K R', ∀ z, R' ≤ ‖z‖ → ‖fderiv ℝ u z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  -- The derivative of `G` exceeds `c'²` on `(-δ, δ)`, so do its difference quotients.
  have hmv : ∀ a b, |a| < δ → |b| < δ → a ≤ b → c' ^ 2 * (b - a) ≤ G b - G a := by
    intro a b ha hb hab
    refine (convex_Ioo (-δ) δ).mul_sub_le_image_sub_of_le_deriv hG.continuous.continuousOn
      (hG.differentiable one_ne_zero).differentiableOn (fun t ht ↦ (hδG t ?_).le) a
      (abs_lt.mp ha) b (abs_lt.mp hb) hab
    rw [interior_Ioo] at ht
    exact abs_lt.mpr ht
  have hslope : ∀ a b, |a| < δ → |b| < δ → a ≠ b → c' ^ 2 ≤ (G a - G b) / (a - b) := by
    intro a b ha hb hab
    rcases lt_or_gt_of_ne hab with h | h
    · rw [le_div_iff_of_neg (sub_neg.mpr h)]
      linarith [hmv a b ha hb h.le]
    · rw [le_div_iff₀ (sub_pos.mpr h)]
      linarith [hmv b a hb ha h.le]
  -- Far out, `u` is small and the equation holds.
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ hlim.eventually (Metric.ball_mem_nhds 0 hδ))
  set Rc := max (max R R₀) 0 + 1
  have hRc : 0 < Rc := by positivity
  have hsmall : ∀ z : E, Rc < ‖z‖ + 1 → |u z| < δ := fun z hz ↦ by
    have : u z ∈ ball (0 : ℝ) δ := hR₀ (show R₀ ≤ ‖z‖ by
      linarith [le_max_right R R₀, le_max_left (max R R₀) 0])
    rwa [mem_ball_zero_iff, Real.norm_eq_abs] at this
  obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall (0 : E) (Rc + 3)).exists_bound_of_continuousOn
    (hu.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨_, Rc + 2, fun z hz ↦ norm_fderiv_le_of_abs_laplacian_sub_sub_le (w := u) (G := 0) hRc
    hc hcc' (le_max_right L₀ 0) le_rfl (fun z _ ↦ hu.contDiffAt) hlim
    (fun z _ hz ↦ (hL₀ z (mem_closedBall_zero_iff.mpr hz)).trans (le_max_left _ _))
    (fun h hh ↦ ⟨fun z ↦ if u z = u (z + h) then c' ^ 2 else (G (u z) - G (u (z + h))) /
      (u z - u (z + h)), fun z hz ↦ ?_⟩) hz⟩
  have hnorm : ‖z‖ - 1 ≤ ‖z + h‖ := by
    have := norm_sub_le (z + h) h
    rw [add_sub_cancel_right] at this
    linarith
  have hRR : R ≤ Rc - 1 := by linarith [le_max_left R R₀, le_max_left (max R R₀) 0]
  have hz₁ := hsmall z (by linarith)
  have hz₂ := hsmall (z + h) (by linarith)
  rw [hΔ z (by linarith), hΔ (z + h) (by linarith)]
  dsimp only
  split_ifs with heq
  · refine ⟨le_rfl, ?_⟩
    rw [heq]
    simp
  · refine ⟨hslope _ _ hz₁ hz₂ heq, ?_⟩
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr heq)]
    simp

/-- **The inductive step.** Let `u` be smooth with `Δu = G(u)` outside a ball and `u → 0`, where
`G` is smooth with `G' > c'²` near `0`. If the derivatives of `u` of orders `1` to `n ≥ 1` are
bounded by `K exp (-c ‖z‖)` far out, with `0 < c < c'`, then so is the derivative of order
`n + 1`, with another constant. Each `n`-th directional derivative `w = Dⁿu (·) m` solves
`Δ w = G'(u) w + f`, where `f` only involves derivatives of `u` of orders at most `n` and of
`G' ∘ u`, so it has a decaying gradient. -/
private theorem exists_norm_iteratedFDeriv_succ_le_mul_exp {u : E → ℝ} {G : ℝ → ℝ}
    {R c c' δ K R₁ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hG : ContDiff ℝ ∞ G) (hc : 0 < c) (hcc' : c < c')
    (hδ : 0 < δ) (hδG : ∀ t, |t| < δ → c' ^ 2 < deriv G t) (hu : ContDiff ℝ ∞ u)
    (hΔ : ∀ z, R < ‖z‖ → Δ u z = G (u z)) (hlim : Tendsto u (cocompact E) (𝓝 0)) (hK : 0 ≤ K)
    (hder : ∀ z, R₁ ≤ ‖z‖ → ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j u z‖ ≤ K * Real.exp (-(c * ‖z‖))) :
    ∃ K' R', ∀ z, R' ≤ ‖z‖ → ‖iteratedFDeriv ℝ (n + 1) u z‖ ≤ K' * Real.exp (-(c * ‖z‖)) := by
  set V : E → ℝ := deriv G ∘ u
  have hG' : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.mp hG).2
  have hV : ContDiff ℝ ∞ V := hG'.comp hu
  have hGu : ContDiff ℝ ∞ (G ∘ u) := hG.comp hu
  have hgap : 0 < c' ^ 2 - c ^ 2 := by nlinarith
  have htop : ∀ k : ℕ, (k : WithTop ℕ∞) ≤ ∞ := fun k ↦ by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have hdiff : ∀ {f : E → ℝ}, ContDiff ℝ ∞ f → ∀ k y, DifferentiableAt ℝ (iteratedFDeriv ℝ k f) y :=
    fun hf k y ↦ (ContDiff.differentiable_iteratedFDeriv (m := k)
      (by exact_mod_cast ENat.natCast_lt_top k) hf) y
  -- A bound `C_G` for the derivatives of `G'` of order at most `n` on `[-1, 1]`.
  obtain ⟨CG, hCG⟩ : ∃ C, ∀ t : ℝ, |t| ≤ 1 → ∀ i ≤ n, ‖iteratedFDeriv ℝ i (deriv G) t‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (f := fun t ↦ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i (deriv G) t‖)
      (continuous_finsetSum _ fun i _ ↦
        (hG'.continuous_iteratedFDeriv (htop i)).norm).continuousOn
    refine ⟨C, fun t ht i hi ↦ ?_⟩
    have h := hC t (abs_le.mp ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at h
    exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (iteratedFDeriv ℝ j (deriv G) t))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans h
  have hCG₀ : 0 ≤ CG := (norm_nonneg _).trans (hCG 0 (by simp) 0 (Nat.zero_le _))
  set BV := (n.factorial : ℝ) * CG
  have hBV : 0 ≤ BV := by positivity
  -- Far out, `u` is small, its derivatives of order `1` to `n` are at most `1`, and the equation
  -- holds.
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸
      ((hlim.eventually (Metric.ball_mem_nhds 0 (lt_min hδ one_pos))).and
        ((((tendsto_exp_neg_mul_norm_cocompact hc).const_mul K).eventually
          (eventually_le_nhds (by simp : K * 0 < 1))).and
          (tendsto_norm_cocompact_atTop.eventually_ge_atTop (max R₁ (R + 1))))))
  have hfar : ∀ p : E, R₀ ≤ ‖p‖ → |u p| < min δ 1 ∧ K * Real.exp (-(c * ‖p‖)) ≤ 1 ∧
      R₁ ≤ ‖p‖ ∧ R + 1 ≤ ‖p‖ := fun p hp ↦ by
    obtain ⟨h₁, h₂, h₃⟩ := hR₀ hp
    rw [Real.dist_eq, sub_zero] at h₁
    exact ⟨h₁, h₂, (le_max_left _ _).trans h₃, (le_max_right _ _).trans h₃⟩
  have hder' : ∀ p : E, R₀ ≤ ‖p‖ → ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j u p‖ ≤ K * Real.exp (-(c * ‖p‖)) := fun p hp ↦
    hder p (hfar p hp).2.2.1
  -- The derivatives of `V = G' ∘ u` of order `1` to `n` are bounded by `BV` far out.
  have hVb : ∀ p : E, R₀ ≤ ‖p‖ → ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i V p‖ ≤ BV := by
    intro p hp i hi₁ hi
    obtain ⟨hup, hKp, -, -⟩ := hfar p hp
    refine (norm_iteratedFDeriv_comp_le hG' hu (htop i) p (C := CG) (D := 1)
      (fun k hk ↦ hCG (u p) (hup.trans_le (min_le_right _ _)).le k (hk.trans hi))
      fun k hk₁ hk₂ ↦ ?_).trans ?_
    · rw [one_pow]
      exact (hder' p hp k hk₁ (hk₂.trans hi)).trans hKp
    · rw [one_pow, mul_one]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hi) hCG₀
  have hkey : ∀ p : E, R₀ ≤ ‖p‖ →
      ‖iteratedFDeriv ℝ (n + 1) (G ∘ u) p - V p • iteratedFDeriv ℝ (n + 1) u p‖ ≤
        2 ^ n * BV * (K * Real.exp (-(c * ‖p‖))) := fun p hp ↦
    norm_iteratedFDeriv_succ_comp_sub_smul_le (hG.of_le (by exact_mod_cast htop (n + 1)))
      (hu.of_le (by exact_mod_cast htop (n + 1))) p hBV (by positivity) (hVb p hp) (hder' p hp)
  -- The constants of the final bound.
  set Rc := max R₀ 0 + 1
  have hRc : 0 < Rc := by positivity
  obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall (0 : E) (Rc + 3)).exists_bound_of_continuousOn
    (hu.continuous_iteratedFDeriv (htop (n + 1))).continuousOn
  set L := max L₀ 0
  set G₁ := 2 ^ n * BV * K + BV * K
  refine ⟨L * Real.exp (c * (Rc + 2)) + (G₁ + BV * K) * Real.exp c / (c' ^ 2 - c ^ 2), Rc + 2,
    fun z hz ↦ ?_⟩
  rw [← norm_fderiv_iteratedFDeriv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦
    ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  rw [show fderiv ℝ (iteratedFDeriv ℝ n u) z v m = iteratedFDeriv ℝ (n + 1) u z (Fin.cons v m) by
    rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]]
  -- The `n`-th derivative in the directions `m`, and the remainder of its equation.
  set P := ∏ i, ‖m i‖
  have hP : 0 ≤ P := by positivity
  set w : E → ℝ := fun y ↦ iteratedFDeriv ℝ n u y m
  have hw : ∀ y, DifferentiableAt ℝ w y := fun y ↦
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) ℝ m).differentiableAt.comp y
      (hdiff hu n y)
  have happly : ∀ {g : E → ℝ}, ContDiff ℝ ∞ g → ∀ y v,
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ n g y m) y v =
        iteratedFDeriv ℝ (n + 1) g y (Fin.cons v m) := fun hg y v ↦ by
    rw [(hdiff hg n y).iteratedFDeriv_succ_apply_left', Fin.tail_cons, Fin.cons_zero]
  have hwfd : ∀ y v, fderiv ℝ w y v = iteratedFDeriv ℝ (n + 1) u y (Fin.cons v m) := happly hu
  have hwfn : ∀ y, ‖fderiv ℝ w y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) u y‖ * P := fun y ↦
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ by
      rw [hwfd]
      exact ((iteratedFDeriv ℝ (n + 1) u y).norm_map_cons_le v m).trans_eq (by ring)
  have hwn : ∀ y, |w y| ≤ ‖iteratedFDeriv ℝ n u y‖ * P := fun y ↦ by
    rw [← Real.norm_eq_abs]
    exact ContinuousMultilinearMap.le_opNorm _ m
  set f : E → ℝ := (fun y ↦ iteratedFDeriv ℝ n (G ∘ u) y m) - V * w
  have hwΔ : ∀ y : E, R < ‖y‖ → Δ w y = f y + V y * w y := fun y hy ↦ by
    have hev : Δ u =ᶠ[𝓝 y] G ∘ u :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hy)
        fun z hz ↦ hΔ z hz
    rw [laplacian_iteratedFDeriv_apply isOpen_univ (hu.of_le (htop (n + 2))).contDiffOn m
      (mem_univ y),
      (hev.iteratedFDeriv ℝ n).eq_of_nhds]
    simp [f]
  -- The gradient of the remainder `f` decays.
  have hfd : ∀ p : E, R₀ ≤ ‖p‖ → DifferentiableAt ℝ f p ∧
      ‖fderiv ℝ f p‖ ≤ G₁ * Real.exp (-(c * ‖p‖)) * P := by
    intro p hp
    have hVd : DifferentiableAt ℝ V p := hV.differentiable (by simp) p
    refine ⟨((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) ℝ m).differentiableAt.comp p
      (hdiff hGu n p)).sub (hVd.mul (hw p)),
      (norm_fderiv_iteratedFDeriv_apply_sub_smul_le (hdiff hGu n p) (hdiff hu n p) hVd m).trans ?_⟩
    have hVfd : ‖fderiv ℝ V p‖ ≤ BV := by
      rw [← norm_iteratedFDeriv_one]
      exact hVb p hp 1 le_rfl (by omega)
    calc _ ≤ (2 ^ n * BV * (K * Real.exp (-(c * ‖p‖))) + BV * (K * Real.exp (-(c * ‖p‖)))) * P := by
          gcongr
          · exact hkey p hp
          · exact hder' p hp n (by omega) le_rfl
      _ = G₁ * Real.exp (-(c * ‖p‖)) * P := by ring
  -- Feed the difference equations into the core estimate.
  have hshift : ∀ y : E, Real.exp (-(c * (‖y‖ - 1))) = Real.exp c * Real.exp (-(c * ‖y‖)) :=
    fun y ↦ by rw [exp_neg_mul_sub, mul_one]
  have hcore := norm_fderiv_le_of_abs_laplacian_sub_sub_le (w := w) (L := L * P)
    (G := (G₁ + BV * K) * Real.exp c * P) hRc hc hcc' (by positivity) (by positivity)
    (fun y _ ↦ ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) ℝ m).contDiff.comp
      (hu.iteratedFDeriv_right (m := 2) (by exact_mod_cast htop (2 + n)))).contDiffAt)
    (squeeze_zero_norm' (Filter.eventually_of_mem
      (tendsto_norm_cocompact_atTop.eventually_ge_atTop R₀) fun y hy ↦
        (hwn y).trans (mul_le_mul_of_nonneg_right (hder' y hy n (by omega) le_rfl) hP))
      (by simpa using ((tendsto_exp_neg_mul_norm_cocompact hc).const_mul K).mul_const P))
    (fun y _ hy ↦ (hwfn y).trans (mul_le_mul_of_nonneg_right
      ((hL₀ y (mem_closedBall_zero_iff.mpr hy)).trans (le_max_left _ _)) hP))
    (fun h hh ↦ ⟨V, fun y hy ↦ ?_⟩) hz
  · calc ‖iteratedFDeriv ℝ (n + 1) u z (Fin.cons v m)‖ = ‖fderiv ℝ w z v‖ := by rw [hwfd]
      _ ≤ ‖fderiv ℝ w z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by
          refine (mul_le_mul_of_nonneg_right hcore (norm_nonneg v)).trans_eq ?_
          field_simp
  -- The difference equation for `w`, with the remainder controlled by the mean value inequality.
  have hball : ∀ p ∈ closedBall y 1, R₀ ≤ ‖p‖ ∧ ‖y‖ - 1 ≤ ‖p‖ := fun p hp ↦ by
    have := norm_le_of_mem_closedBall (mem_closedBall_comm.mp hp)
    constructor <;> linarith [le_max_left R₀ 0]
  have hyh : y + h ∈ closedBall y 1 := by
    rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hy₀ : R₀ ≤ ‖y‖ := by linarith [le_max_left R₀ 0]
  obtain ⟨hyu, -, -, hyR⟩ := hfar y hy₀
  obtain ⟨-, -, -, hyhR⟩ := hfar (y + h) (hball _ hyh).1
  refine ⟨(hδG (u y) (hyu.trans_le (min_le_left _ _))).le, ?_⟩
  have hfmv : |f y - f (y + h)| ≤ G₁ * Real.exp (-(c * (‖y‖ - 1))) * P * ‖h‖ := by
    have := (convex_closedBall y 1).norm_image_sub_le_of_norm_fderiv_le (f := f)
      (C := G₁ * Real.exp (-(c * (‖y‖ - 1))) * P) (fun p hp ↦ (hfd p (hball p hp).1).1)
      (fun p hp ↦ (hfd p (hball p hp).1).2.trans
        (by gcongr; nlinarith [(hball p hp).2]))
      (mem_closedBall_self zero_le_one) hyh
    rwa [add_sub_cancel_left, Real.norm_eq_abs, abs_sub_comm] at this
  have hVmv : |V y - V (y + h)| ≤ BV * ‖h‖ := by
    have := (convex_closedBall y 1).norm_image_sub_le_of_norm_fderiv_le (f := V)
      (fun p _ ↦ hV.differentiable (by simp) p) (fun p hp ↦ by
        rw [← norm_iteratedFDeriv_one]
        exact hVb p (hball p hp).1 1 le_rfl (by omega)) (mem_closedBall_self zero_le_one) hyh
    rwa [add_sub_cancel_left, Real.norm_eq_abs, abs_sub_comm] at this
  have hwh : |w (y + h)| ≤ K * Real.exp (-(c * (‖y‖ - 1))) * P := by
    refine (hwn _).trans (mul_le_mul_of_nonneg_right ((hder' _ (hball _ hyh).1 n (by omega)
      le_rfl).trans ?_) hP)
    gcongr
    nlinarith [(hball _ hyh).2]
  rw [hwΔ y (by linarith), hwΔ (y + h) (by linarith)]
  have hsplit : f y + V y * w y - (f (y + h) + V (y + h) * w (y + h)) - V y * (w y - w (y + h)) =
      (f y - f (y + h)) + (V y - V (y + h)) * w (y + h) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hprod : |V y - V (y + h)| * |w (y + h)| ≤ BV * ‖h‖ * (K * Real.exp (-(c * (‖y‖ - 1))) * P) :=
    mul_le_mul hVmv hwh (abs_nonneg _) (by positivity)
  rw [hshift] at hfmv hprod
  calc |f y - f (y + h)| + |V y - V (y + h)| * |w (y + h)|
      ≤ G₁ * (Real.exp c * Real.exp (-(c * ‖y‖))) * P * ‖h‖ +
          BV * ‖h‖ * (K * (Real.exp c * Real.exp (-(c * ‖y‖))) * P) := add_le_add hfmv hprod
    _ = ‖h‖ * ((G₁ + BV * K) * Real.exp c * P) * Real.exp (-(c * ‖y‖)) := by ring

/-- Decay of all derivatives for a smooth solution on the whole space; see
`TauCeti.exists_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq`. -/
private theorem exists_norm_iteratedFDeriv_succ_le_mul_exp_of_contDiff {u : E → ℝ}
    {G : ℝ → ℝ} {R c : ℝ} (hG : ContDiff ℝ ∞ G) (hc : 0 < c) (hcG : c ^ 2 < deriv G 0)
    (hu : ContDiff ℝ ∞ u) (hΔ : ∀ z, R < ‖z‖ → Δ u z = G (u z))
    (hlim : Tendsto u (cocompact E) (𝓝 0)) (n : ℕ) :
    ∃ K R', 0 ≤ K ∧ ∀ z, R' ≤ ‖z‖ → ∀ j ≤ n,
      ‖iteratedFDeriv ℝ (j + 1) u z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  -- An intermediate rate `c < c' < √(G'(0))`, and an interval `(-δ, δ)` on which `G' > c'²`.
  set μ := Real.sqrt (deriv G 0)
  have hcμ : c < μ := Real.lt_sqrt hc.le |>.mpr hcG
  set c' := (c + μ) / 2 with hc'
  have hcc' : c < c' := by rw [hc']; linarith
  have hc'G : c' ^ 2 < deriv G 0 := by
    calc c' ^ 2 < μ ^ 2 := pow_lt_pow_left₀ (by linarith) (by rw [hc']; linarith) two_ne_zero
      _ = deriv G 0 := Real.sq_sqrt ((sq_nonneg c).trans hcG.le)
  obtain ⟨δ, hδ, hδG⟩ : ∃ δ > 0, ∀ t, |t| < δ → c' ^ 2 < deriv G t := by
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp
      (((hG.continuous_deriv (by simp)).tendsto 0).eventually (lt_mem_nhds hc'G))
    exact ⟨δ, hδ, fun t ht ↦ h (by rwa [Real.dist_eq, sub_zero])⟩
  induction n with
  | zero =>
    obtain ⟨K, R', hK⟩ := exists_norm_fderiv_le_mul_exp_of_laplacian_eq (hG.of_le (by simp))
      hc hcc' hδ hδG (hu.of_le (by simp)) hΔ hlim
    refine ⟨max K 0, R', le_max_right _ _, fun z hz j hj ↦ ?_⟩
    obtain rfl : j = 0 := by omega
    rw [zero_add, norm_iteratedFDeriv_one]
    exact (hK z hz).trans (by gcongr; exact le_max_left _ _)
  | succ n ih =>
    obtain ⟨K, R₁, hK, hder⟩ := ih
    obtain ⟨K', R', hK'⟩ := exists_norm_iteratedFDeriv_succ_le_mul_exp (n := n + 1) (by omega) hG
      hc hcc' hδ hδG hu hΔ hlim hK fun z hz j hj₁ hj ↦ by
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        exact hder z hz i (by omega)
    refine ⟨max K K', max R₁ R', hK.trans (le_max_left _ _), fun z hz j hj ↦ ?_⟩
    rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · exact (hder z ((le_max_left _ _).trans hz) j (by omega)).trans
        (by gcongr; exact le_max_left _ _)
    · obtain rfl : j = n + 1 := by omega
      exact (hK' z ((le_max_right _ _).trans hz)).trans (by gcongr; exact le_max_right _ _)

/-- **Exponential decay of all derivatives of a solution of `Δu = G(u)`.** Let `G : ℝ → ℝ` be
smooth with `G'(0) > 0`, and let `u` be smooth outside a ball of radius `R` in a finite-dimensional
real inner product space, solve `Δu = G(u)` there and tend to zero at infinity. Then every
derivative of `u` of positive order decays exponentially at every rate `c` with
`c² < G'(0)`: there are `K` and `R'` with `‖Dⁿ⁺¹u z‖ ≤ K exp (-c ‖z‖)` for `‖z‖ ≥ R'`.

The rate is that of the linearized operator `-Δ + G'(0)` at the vacuum `u = 0`. No decay of `u`
itself is assumed. -/
theorem exists_norm_iteratedFDeriv_succ_le_mul_exp_of_laplacian_eq {u : E → ℝ} {G : ℝ → ℝ}
    {R c : ℝ} (hG : ContDiff ℝ ∞ G) (hcG : c ^ 2 < deriv G 0)
    (hu : ContDiffOn ℝ ∞ u {z | R < ‖z‖}) (hΔ : ∀ z, R < ‖z‖ → Δ u z = G (u z))
    (hlim : Tendsto u (cocompact E) (𝓝 0)) (n : ℕ) :
    ∃ K R', ∀ z, R' ≤ ‖z‖ → ‖iteratedFDeriv ℝ (n + 1) u z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  -- Replace `c` by a positive rate `c₁ ≥ c` with `c₁² < G'(0)`.
  have hG₀ : 0 < deriv G 0 := (sq_nonneg c).trans_lt hcG
  set c₁ := max c (Real.sqrt (deriv G 0) / 2)
  have hc₁ : 0 < c₁ := lt_max_of_lt_right (by positivity)
  have hc₁G : c₁ ^ 2 < deriv G 0 := by
    rcases le_total c (Real.sqrt (deriv G 0) / 2) with h | h
    · rw [show c₁ = Real.sqrt (deriv G 0) / 2 from max_eq_right h, div_pow, Real.sq_sqrt hG₀.le]
      linarith
    · rwa [show c₁ = c from max_eq_left h]
  -- Cut `u` off near the ball, keeping it unchanged outside the ball of radius `R₂ + 2`.
  set R₂ := max R 0
  let χ : ContDiffBump (0 : E) := ⟨R₂ + 1, R₂ + 2, by positivity, by linarith⟩
  set v : E → ℝ := fun z ↦ (1 - χ z) * u z
  have hfar : ∀ z : E, R₂ + 2 < ‖z‖ → v =ᶠ[𝓝 z] u := fun z hz ↦
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
      fun y hy ↦ by
        simp only [v, χ.zero_of_le_dist (by rw [dist_zero_right]; exact le_of_lt hy), sub_zero,
          one_mul]
  have hv : ContDiff ℝ ∞ v := by
    refine contDiff_iff_contDiffAt.mpr fun z ↦ ?_
    rcases lt_or_ge R ‖z‖ with hz | hz
    · exact (contDiffAt_const.sub χ.contDiffAt).mul
        (hu.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz))
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
        (show ‖z‖ < R₂ + 1 by linarith [le_max_left R 0]))] with y hy
      simp [v, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hvΔ : ∀ z, R₂ + 2 < ‖z‖ → Δ v z = G (v z) := fun z hz ↦ by
    rw [(laplacian_congr_nhds (hfar z hz)).eq_of_nhds, (hfar z hz).eq_of_nhds,
      hΔ z (by linarith [le_max_left R 0])]
  have hvlim : Tendsto v (cocompact E) (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (R₂ + 2)] with z hz
    exact ((hfar z hz).eq_of_nhds).symm
  obtain ⟨K, R', -, hK⟩ := exists_norm_iteratedFDeriv_succ_le_mul_exp_of_contDiff hG hc₁ hc₁G hv
    hvΔ hvlim n
  refine ⟨max K 0, max R' (R₂ + 3), fun z hz ↦ ?_⟩
  rw [← ((hfar z (by linarith [le_max_right R' (R₂ + 3)])).iteratedFDeriv ℝ (n + 1)).eq_of_nhds]
  refine (hK z ((le_max_left _ _).trans hz) n le_rfl).trans ?_
  gcongr
  · exact le_max_left _ _
  · exact le_max_left _ _

end TauCeti
