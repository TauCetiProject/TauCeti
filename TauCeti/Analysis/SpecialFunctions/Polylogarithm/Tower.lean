/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.UniversalCoverBranch
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The polylogarithm tower and its differential analytic continuation

The principal polylogarithms `Liₙ(z)` (`n ≥ 1`) cannot be analytically continued across `(1, ∞)`
one weight at a time in isolation: continuing `Liₙ` around `1` mixes in lower-weight powers of
`Log z`, since `z · d/dz Liₙ₊₁(z) = Liₙ(z)` and `d/dz Li₁(z) = (1 - z)⁻¹`. Following Oesterlé
(*Polylogarithmes*, Séminaire Bourbaki 762, §2), one bundles `Log z` and `Li₁(z), …, Li_N(z)` into
an `(N + 1)`-component vector germ `polylogTower N : ℂ → Fin (N + 1) → ℂ`.

* `TauCeti.Polylog.polylogTower`: the `(N + 1)`-tuple `(Log z, Li₁ z, …, Li_N z)`, together with
  projection, truncation, basepoint (`z = 1 / 2`), and cut-obstruction (`z = 3`) lemmas.
* `TauCeti.Polylog.IsPolylogTowerGerm`: a local holomorphic tuple `F : ℂ → Fin (N + 1) → ℂ` at `w`
  satisfying `exp (F z 0) = z`, `(1 - z) · (F · 1)'(z) = 1`, and `z · (F · (k + 1))'(z) = F z k`.
  Any such germ avoids `0` (and `1` when `N ≠ 0`), is uniquely determined near `w` by `F w`,
  persists along analytic continuation, and continues along every path in `ℂ \ {0, 1}`, inducing a
  branch on the universal cover whose local determinations satisfy the same differential system.

For the polynomial peripheral monodromy representation of `π₁(ℂ \ {0, 1}, 1/2)` and universal-cover
monodromy theorems, see `TauCeti.Analysis.SpecialFunctions.Polylogarithm.Monodromy`.

## References

* J. Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993), §2.
* D. Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*
  (2007), Part I, §1–§2.
-/

public section

namespace TauCeti.Polylog

open Filter Metric Set Topology unitInterval

/-! ### The principal polylogarithm tower -/

/-- The classical polylogarithm tower of height `N`: entry `0` is `Complex.log z` and entry
`i ≥ 1` is `polylog i z`. -/
noncomputable def polylogTower (N : ℕ) (z : ℂ) : Fin (N + 1) → ℂ :=
  fun i => if (i : ℕ) = 0 then Complex.log z else polylog (i : ℕ) z

/-- Coordinate formula for `polylogTower`. -/
theorem polylogTower_apply (N : ℕ) (z : ℂ) (i : Fin (N + 1)) :
    polylogTower N z i = if (i : ℕ) = 0 then Complex.log z else polylog (i : ℕ) z := by rfl

/-- Entry `0` of `polylogTower N z` is the principal logarithm `Complex.log z`. -/
@[simp]
theorem polylogTower_zero (N : ℕ) (z : ℂ) : polylogTower N z 0 = Complex.log z := by rfl

/-- Entry `i.succ` of `polylogTower N z` is `polylog (i + 1) z`. -/
@[simp]
theorem polylogTower_succ (N : ℕ) (z : ℂ) (i : Fin N) :
    polylogTower N z i.succ = polylog (i.succ : ℕ) z := by simp [polylogTower]

/-- At any nonzero index `i`, `polylogTower N z i` is `polylog i z`. -/
theorem polylogTower_apply_of_ne_zero {N : ℕ} (z : ℂ) {i : Fin (N + 1)} (hi : (i : ℕ) ≠ 0) :
    polylogTower N z i = polylog (i : ℕ) z := by simp [polylogTower, hi]

/-- At `z = 0`, every totalised coordinate of `polylogTower N 0` vanishes. -/
@[simp]
theorem polylogTower_zero_arg (N : ℕ) : polylogTower N 0 = 0 := by
  ext i; by_cases hi : (i : ℕ) = 0 <;> simp [polylogTower, hi]

/-- Truncating `polylogTower N` to the first `M + 1` coordinates (`M ≤ N`) gives `polylogTower M`.
-/
theorem polylogTower_castLE {M N : ℕ} (hMN : M ≤ N) (z : ℂ) (i : Fin (M + 1)) :
    polylogTower N z (Fin.castLE (Nat.add_le_add_right hMN 1) i) = polylogTower M z i := by
  simp [polylogTower]

/-- At the basepoint `1 / 2`, entry `0` of `polylogTower` is `-Real.log 2`. -/
theorem polylogTower_half_zero (N : ℕ) : polylogTower N (1 / 2) 0 = -(Real.log 2 : ℂ) := by
  have h : (1 / 2 : ℂ) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [polylogTower_zero, h, ← Complex.ofReal_log (by positivity), Real.log_inv, Complex.ofReal_neg]

/-- At the basepoint `1 / 2`, entry `1` of `polylogTower` (`1 ≤ N`) is `Real.log 2`. -/
theorem polylogTower_half_one {N : ℕ} (hN : 1 ≤ N) :
    polylogTower N (1 / 2) ⟨1, Nat.succ_lt_succ hN⟩ = (Real.log 2 : ℂ) := by
  have hidx : (⟨1, Nat.succ_lt_succ hN⟩ : Fin (N + 1)) = (⟨0, hN⟩ : Fin N).succ := rfl
  have hval : ((⟨0, hN⟩ : Fin N).succ : ℕ) = 1 := rfl
  have h : (1 - (1 / 2 : ℂ)) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hidx, polylogTower_succ, hval, Nat.cast_one, polylog_one, h,
    ← Complex.ofReal_log (by positivity), Real.log_inv, Complex.ofReal_neg, neg_neg]

/-- Height zero (`Log z` alone) is complex analytic at `z = 3`, since `3` lies off `(-∞, 0]`. -/
theorem analyticAt_polylogTower_zero_three : AnalyticAt ℂ (polylogTower 0) 3 :=
  AnalyticAt.pi fun i => by
    fin_cases i
    simpa [polylogTower] using
      analyticAt_id.clog (Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num)))

/-- For `1 ≤ N`, `polylogTower N` is not complex analytic at `z = 3`, because `Li₁(z) = -Log(1 - z)`
jumps across `(1, ∞)`. -/
theorem not_analyticAt_polylogTower_three {N : ℕ} (hN : 1 ≤ N) :
    ¬ AnalyticAt ℂ (polylogTower N) 3 := by
  intro h
  let idx : Fin (N + 1) := (⟨0, hN⟩ : Fin N).succ
  have h1 : AnalyticAt ℂ (fun z => polylogTower N z idx) 3 := analyticAt_pi_iff.1 h idx
  have hsub : AnalyticAt ℂ (fun w : ℂ => 1 - w) (-2) := analyticAt_const.sub analyticAt_id
  have h3 : (1 : ℂ) - (-2) = 3 := by norm_num
  have hlog : ContinuousAt Complex.log (-2) := by
    have han : AnalyticAt ℂ (fun w : ℂ => -(polylogTower N (1 - w) idx)) (-2) :=
      ((h3 ▸ h1).comp hsub).neg
    have hval : ((⟨0, hN⟩ : Fin N).succ : ℕ) = 1 := rfl
    have heq : (fun w : ℂ => -(polylogTower N (1 - w) idx)) = Complex.log := by
      ext w; dsimp only [idx]; rw [polylogTower_succ, hval, Nat.cast_one, polylog_one]; simp
    exact (heq ▸ han).continuousAt
  let φ : ℝ → ℂ := fun y => (-2 : ℂ) + (y : ℂ) * Complex.I
  have hφ : ContinuousAt φ 0 := by fun_prop
  have hφ0 : φ 0 = -2 := by simp [φ]
  have hcont_im : ContinuousAt (fun y : ℝ => (Complex.log (φ y)).im) 0 :=
    Complex.continuous_im.continuousAt.comp ((hφ0.symm ▸ hlog).comp hφ)
  have htend : Tendsto (fun y : ℝ => (Complex.log (φ y)).im) (𝓝[<] 0)
      (𝓝 ((Complex.log (-2)).im)) := by
    simpa [hφ0] using hcont_im.tendsto.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ y : ℝ in 𝓝[<] 0, (Complex.log (φ y)).im ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < 0)
    exact Complex.log_im (φ y) ▸ (Complex.arg_neg_iff.2 (by simp [φ, hy])).le
  have him_le : (Complex.log (-2)).im ≤ 0 := le_of_tendsto htend hle
  have hm2 : (-2 : ℂ) = ((-2 : ℝ) : ℂ) := by norm_num
  have him_pi : (Complex.log (-2)).im = Real.pi := by
    rw [hm2, Complex.log_im, Complex.arg_ofReal_of_neg (by norm_num)]
  linarith [Real.pi_pos]

/-! ### Differential/exponential polylogarithm tower germs -/

/-- `IsPolylogTowerGerm N F w` states that `F : ℂ → Fin (N + 1) → ℂ` is complex analytic at `w`,
`exp (F z 0) = z` near `w`, and its higher coordinates satisfy the cleared-denominator Euler system
`(1 - z) · (F · 1)'(z) = 1` and `z · (F · (k + 1))'(z) = F z k` near `w`. -/
structure IsPolylogTowerGerm (N : ℕ) (F : ℂ → Fin (N + 1) → ℂ) (w : ℂ) : Prop where
  /-- `F` is complex analytic at `w`. -/
  analyticAt : AnalyticAt ℂ F w
  /-- Entry `0` is a local holomorphic branch of `log` near `w`. -/
  eventually_exp_zero : ∀ᶠ z in 𝓝 w, Complex.exp (F z 0) = z
  /-- Entries `1, …, N` satisfy the iterated differential equations of `Li₁, …, Li_N`. -/
  eventually_deriv_succ : ∀ i : Fin N, ∀ᶠ z in 𝓝 w,
    (if (i : ℕ) = 0 then 1 - z else z) * deriv (fun u => F u i.succ) z =
      if (i : ℕ) = 0 then 1 else F z i.castSucc

namespace IsPolylogTowerGerm

variable {N : ℕ} {F G : ℂ → Fin (N + 1) → ℂ} {w : ℂ}

/-- Evaluating `eventually_exp_zero` at `w` gives `exp (F w 0) = w`. -/
theorem exp_zero (hF : IsPolylogTowerGerm N F w) : Complex.exp (F w 0) = w :=
  hF.eventually_exp_zero.self_of_nhds

/-- No polylogarithm tower germ exists at the puncture `0`. -/
theorem ne_zero (hF : IsPolylogTowerGerm N F w) : w ≠ 0 :=
  hF.exp_zero ▸ Complex.exp_ne_zero (F w 0)

/-- When `N ≠ 0`, no polylogarithm tower germ exists at the puncture `1`. -/
theorem ne_one (hF : IsPolylogTowerGerm N F w) (hN : N ≠ 0) : w ≠ 1 := fun hw => by
  have h := (hF.eventually_deriv_succ ⟨0, Nat.pos_of_ne_zero hN⟩).self_of_nhds
  simp [hw] at h

/-- `IsPolylogTowerGerm` depends only on the germ of `F` at `w`. -/
theorem congr (hF : IsPolylogTowerGerm N F w) (hFG : F =ᶠ[𝓝 w] G) :
    IsPolylogTowerGerm N G w where
  analyticAt := hF.analyticAt.congr hFG
  eventually_exp_zero := by
    filter_upwards [hF.eventually_exp_zero, hFG] with z hexp heq; simpa [heq] using hexp
  eventually_deriv_succ i := by
    have hi : (fun u => F u i.succ) =ᶠ[𝓝 w] fun u => G u i.succ := hFG.mono fun _ h => by simp [h]
    filter_upwards [hF.eventually_deriv_succ i, hi.deriv, hFG] with z hderiv hd heq
    simpa [hd, heq] using hderiv

/-- Differentiating `exp (F z 0) = z` gives `z * deriv (F · 0) z = 1` near `w`. -/
theorem eventually_deriv_zero (hF : IsPolylogTowerGerm N F w) :
    ∀ᶠ z in 𝓝 w, z * deriv (fun u => F u 0) z = 1 := by
  have han0 : AnalyticAt ℂ (fun u => F u 0) w := analyticAt_pi_iff.1 hF.analyticAt 0
  have hcexp : (fun z => Complex.exp (F z 0)) =ᶠ[𝓝 w] id := hF.eventually_exp_zero
  filter_upwards [han0.eventually_analyticAt, hF.eventually_exp_zero, hcexp.deriv] with z hz hexp hd
  rwa [(hz.differentiableAt.hasDerivAt.cexp).deriv, hexp, deriv_id] at hd

/-- Truncating an `N`-tower germ to height `M ≤ N` gives an `M`-tower germ. -/
theorem castLE {M : ℕ} (hMN : M ≤ N) (hF : IsPolylogTowerGerm N F w) :
    IsPolylogTowerGerm M (fun z i => F z (Fin.castLE (Nat.add_le_add_right hMN 1) i)) w where
  analyticAt := AnalyticAt.pi fun _ => analyticAt_pi_iff.1 hF.analyticAt _
  eventually_exp_zero := hF.eventually_exp_zero
  eventually_deriv_succ i := hF.eventually_deriv_succ (Fin.castLE hMN i)

/-- **Persistence of the tower differential system along analytic continuation.** -/
theorem of_isAnalyticContinuationAlong {X : Type*} [TopologicalSpace X] {s : Set X} {t₀ t₁ : X}
    (hs : IsPreconnected s) (ht₀ : t₀ ∈ s) (ht₁ : t₁ ∈ s)
    {c : X → ℂ} {f : X → ℂ → Fin (N + 1) → ℂ}
    (hf : IsAnalyticContinuationAlong f c s) (hf0 : f t₀ =ᶠ[𝓝 (c t₀)] F)
    (hF : IsPolylogTowerGerm N F (c t₀)) :
    IsPolylogTowerGerm N (f t₁) (c t₁) where
  analyticAt := hf.analyticAt t₁ ht₁
  eventually_exp_zero := by
    have hE : IsAnalyticContinuationAlong (fun t z => Complex.exp (f t z 0) - z) c s :=
      ((hf.eval_apply 0).comp_analyticAt fun _ _ => analyticAt_id.cexp).sub
        (.const hf.continuousOn fun _ _ => analyticAt_id)
    have hZ : IsAnalyticContinuationAlong (fun _ _ => (0 : ℂ)) c s :=
      .const hf.continuousOn fun _ _ => analyticAt_const
    have h0 : (fun z => Complex.exp (f t₀ z 0) - z) =ᶠ[𝓝 (c t₀)] fun _ => 0 := by
      filter_upwards [hf0, hF.eventually_exp_zero] with z hz hexp; simp [hz, hexp]
    exact (hE.eventuallyEq hZ hs ht₀ ht₁ h0).mono fun _ => sub_eq_zero.mp
  eventually_deriv_succ i := by
    have hfac : IsAnalyticContinuationAlong
        (fun _ z => if (i : ℕ) = 0 then 1 - z else z) c s :=
      .const hf.continuousOn fun _ _ => by
        if hi : (i : ℕ) = 0 then
          simp only [hi, ↓reduceIte]; exact analyticAt_const.sub analyticAt_id
        else
          simp only [hi, ↓reduceIte]; exact analyticAt_id
    have hrhs : IsAnalyticContinuationAlong
        (fun t z => if (i : ℕ) = 0 then 1 else f t z i.castSucc) c s := by
      by_cases hi : (i : ℕ) = 0
      · simpa [hi] using IsAnalyticContinuationAlong.const hf.continuousOn fun _ _ =>
          analyticAt_const
      · simpa [hi] using hf.eval_apply i.castSucc
    have hD := (hfac.mul (hf.eval_apply i.succ).deriv).sub hrhs
    have hZ : IsAnalyticContinuationAlong (fun _ _ => (0 : ℂ)) c s :=
      .const hf.continuousOn fun _ _ => analyticAt_const
    have hi0 : (fun u => f t₀ u i.succ) =ᶠ[𝓝 (c t₀)] fun u => F u i.succ :=
      hf0.mono fun _ h => by simp [h]
    have h0 : (fun z => (if (i : ℕ) = 0 then 1 - z else z) * deriv (fun u => f t₀ u i.succ) z -
        (if (i : ℕ) = 0 then 1 else f t₀ z i.castSucc)) =ᶠ[𝓝 (c t₀)] fun _ => 0 := by
      filter_upwards [hf0, hi0.deriv, hF.eventually_deriv_succ i] with z hz hd hode
      simp [hz, hd, hode]
    exact (hD.eventuallyEq hZ hs ht₀ ht₁ h0).mono fun _ => sub_eq_zero.mp

private theorem eq_of_exp_eq_of_norm_sub_lt_one {a b : ℂ}
    (hexp : Complex.exp a = Complex.exp b) (hnorm : ‖a - b‖ < 1) : a = b := by
  have hexp_sub : Complex.exp (a - b) = 1 := by
    rw [Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero b)]
  have him : |(a - b).im| < Real.pi := by linarith [Complex.abs_im_le_norm (a - b), Real.two_le_pi]
  have hlog := Complex.log_exp (x := a - b) (neg_lt_of_abs_lt him) (le_of_lt (lt_of_abs_lt him))
  rw [hexp_sub, Complex.log_one] at hlog
  exact sub_eq_zero.mp hlog.symm

/-- **Initial-value uniqueness for `IsPolylogTowerGerm`.** Two polylogarithm tower germs at `w`
have the same germ at `w` if and only if their values at `w` coincide. -/
theorem eventuallyEq_iff_eq (hF : IsPolylogTowerGerm N F w) (hG : IsPolylogTowerGerm N G w) :
    (F =ᶠ[𝓝 w] G) ↔ F w = G w := by
  refine ⟨EventuallyEq.eq_of_nhds, fun hFG => ?_⟩
  suffices hcoord : ∀ (k : ℕ) (hk : k < N + 1),
      (fun z => F z ⟨k, hk⟩) =ᶠ[𝓝 w] fun z => G z ⟨k, hk⟩ by
    have hall : ∀ᶠ z in 𝓝 w, ∀ i : Fin (N + 1), F z i = G z i :=
      eventually_all.mpr fun i => hcoord i.1 i.2
    exact hall.mono fun _ => funext
  intro k
  induction k with
  | zero =>
    intro _
    have hcont : ContinuousAt (fun z => F z 0 - G z 0) w :=
      (analyticAt_pi_iff.1 hF.analyticAt 0).continuousAt.sub
        (analyticAt_pi_iff.1 hG.analyticAt 0).continuousAt
    have hlt : ∀ᶠ z in 𝓝 w, ‖F z 0 - G z 0‖ < 1 := by
      simpa [congrFun hFG 0] using Metric.tendsto_nhds.mp hcont 1 zero_lt_one
    filter_upwards [hF.eventually_exp_zero, hG.eventually_exp_zero, hlt] with z hexpF hexpG hnorm
    exact eq_of_exp_eq_of_norm_sub_lt_one (hexpF.trans hexpG.symm) hnorm
  | succ k ih =>
    intro hk
    let j : Fin N := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    have hj_succ : j.succ = ⟨k + 1, hk⟩ := rfl
    have hprev := ih (Nat.lt_succ_of_lt j.2)
    have hfac_ne : ∀ᶠ z in 𝓝 w, (if (j : ℕ) = 0 then 1 - z else z) ≠ 0 := by
      by_cases hj0 : (j : ℕ) = 0
      · exact (eventually_ne_nhds (hF.ne_one (Nat.ne_of_gt (Nat.zero_lt_of_lt j.2)))).mono
          fun z hz => by simp [hj0, sub_ne_zero, hz.symm]
      · simpa [hj0] using eventually_ne_nhds hF.ne_zero
    have hderiv_eq : deriv (fun u => F u j.succ) =ᶠ[𝓝 w] deriv (fun u => G u j.succ) := by
      filter_upwards [hF.eventually_deriv_succ j, hG.eventually_deriv_succ j, hprev, hfac_ne]
        with z hdF hdG hp hne
      apply mul_left_cancel₀ hne
      rw [hdF, hdG]; by_cases hj0 : (j : ℕ) = 0 <;> simp [hj0, j, hp]
    have hanF := analyticAt_pi_iff.1 hF.analyticAt j.succ
    have hanG := analyticAt_pi_iff.1 hG.analyticAt j.succ
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
      (hanF.eventually_analyticAt.and (hanG.eventually_analyticAt.and hderiv_eq))
    have heqOn := isOpen_ball.eqOn_of_deriv_eq (convex_ball w δ).isPreconnected
      (fun z hz => (hball (mem_ball.mp hz)).1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hball (mem_ball.mp hz)).2.1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hball (mem_ball.mp hz)).2.2) (mem_ball_self hδ) (congrFun hFG j.succ)
    exact hj_succ ▸ eventually_of_mem (Metric.ball_mem_nhds w hδ) heqOn

private theorem exists_analyticOnNhd_ball_zero {w : ℂ} {r : ℝ}
    (h0 : 0 ∉ ball w r) (c₀ : ℂ) (hexp₀ : Complex.exp c₀ = w) :
    ∃ G : ℂ → Fin 1 → ℂ,
      AnalyticOnNhd ℂ G (ball w r) ∧ G w = (fun _ => c₀) ∧
      ∀ z ∈ ball w r, IsPolylogTowerGerm 0 G z := by
  have hw0 : w ≠ 0 := hexp₀ ▸ Complex.exp_ne_zero c₀
  have hrw : r ≤ ‖w‖ := by simpa [mem_ball, dist_zero_left] using h0
  have hslit : ∀ z ∈ ball w r, z / w ∈ Complex.slitPlane := fun z hz =>
    Complex.ball_one_subset_slitPlane <| by
      rw [mem_ball, dist_eq_norm, div_sub_one hw0, norm_div, div_lt_one (norm_pos_iff.mpr hw0)]
      exact (by simpa [mem_ball, dist_eq_norm] using hz : ‖z - w‖ < r).trans_le hrw
  let G : ℂ → Fin 1 → ℂ := fun z _ => c₀ + Complex.log (z / w)
  have hGan : AnalyticOnNhd ℂ G (ball w r) := fun z hz =>
    AnalyticAt.pi fun _ =>
      analyticAt_const.add ((analyticAt_id.div analyticAt_const hw0).clog (hslit z hz))
  have hexp : ∀ z ∈ ball w r, Complex.exp (G z 0) = z := fun z hz => by
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hz)
    rw [Complex.exp_add, hexp₀, Complex.exp_log (div_ne_zero hz0 hw0), mul_div_cancel₀ _ hw0]
  refine ⟨G, hGan, by ext i; fin_cases i; simp [G, div_self hw0],
    fun z hz => ⟨hGan z hz, eventually_of_mem (isOpen_ball.mem_nhds hz) hexp, fun i => i.elim0⟩⟩

private theorem exists_analyticOnNhd_ball_succ {M : ℕ} {w : ℂ} {r : ℝ}
    (h0 : 0 ∉ ball w r) (h1 : 1 ∉ ball w r)
    {G' : ℂ → Fin (M + 1) → ℂ} (hG'an : AnalyticOnNhd ℂ G' (ball w r))
    (hG'tower : ∀ z ∈ ball w r, IsPolylogTowerGerm M G' z) (c : ℂ) :
    ∃ G : ℂ → Fin (M + 2) → ℂ,
      AnalyticOnNhd ℂ G (ball w r) ∧ G w = Fin.lastCases c (G' w) ∧
      ∀ z ∈ ball w r, IsPolylogTowerGerm (M + 1) G z := by
  let rhs : ℂ → ℂ := if M = 0 then fun z => (1 - z)⁻¹ else fun z => G' z (Fin.last M) / z
  have hrhs_an : AnalyticOnNhd ℂ rhs (ball w r) := fun z hz => by
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hz)
    have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr fun h => h1 (h.symm ▸ hz)
    by_cases hM : M = 0
    · have hinv : AnalyticAt ℂ (fun u => (1 - u)⁻¹) z :=
        (analyticAt_const.sub analyticAt_id).inv hz1
      simpa [rhs, hM] using hinv
    · have hdiv : AnalyticAt ℂ (fun u => G' u (Fin.last M) / u) z :=
        (analyticAt_pi_iff.1 (hG'an z hz) (Fin.last M)).div analyticAt_id hz0
      simpa [rhs, hM] using hdiv
  obtain ⟨g, hgw, hgderiv⟩ := ((hrhs_an.differentiableOn).isExactOn_ball).with_val_at w c
  have hgan : AnalyticOnNhd ℂ g (ball w r) := DifferentiableOn.analyticOnNhd
    (fun z hz => (hgderiv z hz).differentiableAt.differentiableWithinAt) isOpen_ball
  let G : ℂ → Fin (M + 2) → ℂ := fun z => Fin.lastCases (g z) (G' z)
  have hGan : AnalyticOnNhd ℂ G (ball w r) := fun z hz => AnalyticAt.pi <|
    Fin.lastCases (by simpa [G, Fin.lastCases_last] using hgan z hz)
      fun i => by simpa [G, Fin.lastCases_castSucc] using analyticAt_pi_iff.1 (hG'an z hz) i
  have hG0 : ∀ u, G u 0 = G' u 0 := fun u =>
    (congrArg (G u) (Fin.ext rfl : (0 : Fin (M + 2)) = (0 : Fin (M + 1)).castSucc)).trans
      (Fin.lastCases_castSucc 0)
  refine ⟨G, hGan, by ext i; refine Fin.lastCases (by simp [G, hgw]) (fun _ => by simp [G]) i,
    fun z hz => ⟨hGan z hz, by simpa [hG0] using (hG'tower z hz).eventually_exp_zero, ?_⟩⟩
  refine Fin.lastCases ?_ fun i => ?_
  · have hGl : (fun v => G v (Fin.last M).succ) = g := funext fun v =>
      (congrArg (G v) (Fin.ext rfl : (Fin.last M).succ = Fin.last (M + 1))).trans Fin.lastCases_last
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
    have hu1 : 1 - u ≠ 0 := sub_ne_zero.mpr fun h => h1 (h.symm ▸ hu)
    rw [hGl, (hgderiv u hu).deriv]
    have hGc : G u (Fin.last M).castSucc = G' u (Fin.last M) := Fin.lastCases_castSucc _
    by_cases hM : M = 0
    · simp [Fin.val_last, hM, rhs, mul_inv_cancel₀ hu1]
    · simp [Fin.val_last, hM, rhs, hGc, mul_div_cancel₀ _ hu0]
  · have hGs : (fun u => G u i.castSucc.succ) = fun u => G' u i.succ := funext fun u =>
      (congrArg (G u) (Fin.ext rfl : i.castSucc.succ = i.succ.castSucc)).trans
        (Fin.lastCases_castSucc _)
    have hGc : ∀ u, G u i.castSucc.castSucc = G' u i.castSucc := fun _ => Fin.lastCases_castSucc _
    filter_upwards [(hG'tower z hz).eventually_deriv_succ i] with u hu
    simpa [hGs, hGc] using hu

/-- **Local disc extension of a tower germ.** On any open disc `ball w r` avoiding `0` (and `1`
when `N ≠ 0`), an `IsPolylogTowerGerm` extends to a single-valued analytic map on `ball w r`. -/
theorem exists_analyticOnNhd_ball (hF : IsPolylogTowerGerm N F w) {r : ℝ}
    (h0 : 0 ∉ ball w r) (h1 : N ≠ 0 → 1 ∉ ball w r) :
    ∃ G : ℂ → Fin (N + 1) → ℂ,
      AnalyticOnNhd ℂ G (ball w r) ∧ (G =ᶠ[𝓝 w] F) ∧
      ∀ z ∈ ball w r, IsPolylogTowerGerm N G z := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.mpr hr]
    exact ⟨F, fun _ h => h.elim, .rfl, fun _ h => h.elim⟩
  induction N with
  | zero =>
    obtain ⟨G, hGan, hGw, hGt⟩ := exists_analyticOnNhd_ball_zero h0 (F w 0) hF.exp_zero
    have hGw' : G w = F w := hGw.trans (by ext i; fin_cases i; rfl)
    exact ⟨G, hGan, ((hGt w (mem_ball_self hr)).eventuallyEq_iff_eq hF).mpr hGw', hGt⟩
  | succ M ih =>
    obtain ⟨G', hG'an, hG'eq, hG't⟩ :=
      ih (hF.castLE (Nat.le_succ M)) fun _ => h1 (Nat.succ_ne_zero M)
    obtain ⟨G, hGan, hGw, hGt⟩ := exists_analyticOnNhd_ball_succ h0 (h1 (Nat.succ_ne_zero M))
      hG'an hG't (F w (Fin.last (M + 1)))
    have hGw' : G w = F w := hGw.trans (by
      ext i
      refine Fin.lastCases Fin.lastCases_last (fun j => ?_) i
      have hidx : Fin.castLE (Nat.add_le_add_right (Nat.le_succ M) 1) j = j.castSucc := Fin.ext rfl
      exact (Fin.lastCases_castSucc j).trans (hidx ▸ congrFun hG'eq.eq_of_nhds j))
    exact ⟨G, hGan, ((hGt w (mem_ball_self hr)).eventuallyEq_iff_eq hF).mpr hGw', hGt⟩

/-- **Global continuation of a tower germ along any path in `ℂ \ {0, 1}`.** -/
theorem continuesAlong {c : I → ℂ} (hF : IsPolylogTowerGerm N F (c 0)) (hc : Continuous c)
    (hc0 : ∀ t, c t ≠ 0) (hc1 : N ≠ 0 → ∀ t, c t ≠ 1) :
    ContinuesAlong F c := by
  let S : Set I := {b | ∃ f : I → ℂ → Fin (N + 1) → ℂ,
    IsAnalyticContinuationAlong f c (Iic b) ∧ f 0 =ᶠ[𝓝 (c 0)] F}
  have h0S : (0 : I) ∈ S := ⟨fun _ => F, .const hc.continuousOn fun t ht =>
    (Subtype.ext (le_antisymm (Subtype.coe_le_coe.mpr (mem_Iic.mp ht)) t.2.1)) ▸ hF.analyticAt,
    .rfl⟩
  let b₀ : I := sSup S
  let r : ℝ := if N = 0 then ‖c b₀‖ else min ‖c b₀‖ ‖c b₀ - 1‖
  have hr : 0 < r := by by_cases hN : N = 0 <;> simp [r, hN, hc0 b₀, sub_ne_zero, hc1]
  have h0_b₀ : 0 ∉ ball (c b₀) r := by by_cases hN : N = 0 <;> simp [r, hN, dist_zero_left]
  have h1_b₀ : N ≠ 0 → 1 ∉ ball (c b₀) r := fun hN => by simp [r, hN, dist_eq_norm, norm_sub_rev]
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc.continuousAt (r / 3) (by positivity)
  have hcoe_sup : (b₀ : ℝ) = sSup ((↑) '' S : Set ℝ) := Set.Icc.coe_sSup zero_le_one ⟨0, h0S⟩
  obtain ⟨_, ⟨t₁, ⟨f₁, hf₁, hf₁0⟩, rfl⟩, ht₁_gt⟩ :=
    exists_lt_of_lt_csSup (Set.Nonempty.image _ ⟨0, h0S⟩) (hcoe_sup ▸ sub_lt_self (b₀ : ℝ) hδ)
  have ht₁_le : t₁ ≤ b₀ := le_csSup (OrderTop.bddAbove S) ⟨f₁, hf₁, hf₁0⟩
  have hdist_t₁ : dist (c t₁) (c b₀) < r / 3 := hδc <| by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [Subtype.coe_le_coe.mpr ht₁_le])]
    linarith
  have hsub_ball : ball (c t₁) (2 * r / 3) ⊆ ball (c b₀) r := ball_subset_ball' (by linarith)
  have hFt₁ : IsPolylogTowerGerm N (f₁ t₁) (c t₁) :=
    of_isAnalyticContinuationAlong isPreconnected_Iic (mem_Iic.mpr bot_le) (mem_Iic.mpr le_rfl)
      hf₁ hf₁0 hF
  obtain ⟨G, hGan, hGeq, -⟩ := hFt₁.exists_analyticOnNhd_ball
    (fun h => h0_b₀ (hsub_ball h)) (fun hN h => h1_b₀ hN (hsub_ball h))
  let t₂ : I := projIcc 0 1 zero_le_one ((b₀ : ℝ) + δ / 2)
  have hGan_Icc : ∀ t ∈ Icc t₁ t₂, AnalyticAt ℂ G (c t) := fun t ht => hGan _ <| mem_ball.mpr <| by
    have ht_dist : dist t b₀ < δ := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
      have ht2 : (t : ℝ) ≤ (b₀ : ℝ) + δ / 2 := (Subtype.coe_le_coe.mpr ht.2).trans
        (by rw [coe_projIcc]; exact max_le (by linarith [b₀.2.1]) (min_le_right _ _))
      exact ⟨by linarith [Subtype.coe_le_coe.mpr ht.1], by linarith⟩
    linarith [dist_triangle (c t) (c b₀) (c t₁), hδc ht_dist, dist_comm (c t₁) (c b₀)]
  have hf_ext := hf₁.extend_Iic hc.continuousOn hGan_Icc hGeq.symm
  have hf_ext0 : (if (0 : I) ≤ t₁ then f₁ 0 else G) =ᶠ[𝓝 (c 0)] F := by simpa [bot_le] using hf₁0
  have ht₂_one : t₂ = 1 := Subtype.ext <| by
    have hle := Subtype.coe_le_coe.mpr (le_csSup (OrderTop.bddAbove S) ⟨_, hf_ext, hf_ext0⟩)
    rw [coe_projIcc, max_eq_right (le_min zero_le_one (by linarith [b₀.2.1]))] at hle ⊢
    by_contra hne
    rw [min_eq_right (le_of_not_ge fun h => hne (min_eq_left h))] at hle
    linarith
  exact continuesAlong_iff_exists.mpr
    ⟨_, hf_ext.mono fun t _ => ht₂_one ▸ mem_Iic.mpr (Subtype.coe_le_coe.mp t.2.2), hf_ext0⟩

/-- **Continuation inside `ℂ \ {0, 1}`.** -/
theorem continuesInside (hF : IsPolylogTowerGerm N F w) :
    ContinuesInside F {z : ℂ | z ≠ 0 ∧ z ≠ 1} w :=
  ContinuesInside.of_forall fun _ hc hcU hc0 =>
    (hc0 ▸ hF).continuesAlong hc (fun t => (hcU t).1) (fun _ t => (hcU t).2)

/-- At height `0` (`Log z` alone), `1` is not a puncture: `F` continues inside `{z : ℂ | z ≠ 0}`. -/
theorem continuesInside_zero {F : ℂ → Fin 1 → ℂ} (hF : IsPolylogTowerGerm 0 F w) :
    ContinuesInside F {z : ℂ | z ≠ 0} w :=
  ContinuesInside.of_forall fun _ hc hcU hc0 =>
    (hc0 ▸ hF).continuesAlong hc hcU (fun h => absurd rfl h)

/-- **Local determinations of the universal-cover branch satisfy the tower ODE system.** -/
theorem isPolylogTowerGerm_universalCoverBranch_comp {U : Set ℂ} {z₀ : U}
    (hF : IsPolylogTowerGerm N F (z₀ : ℂ)) (H : ContinuesInside F U (z₀ : ℂ))
    {sec : ℂ → UniversalCover z₀} {u : ℂ} (hsec : ContinuousAt sec u)
    (hproj : (fun z => ((sec z).proj : ℂ)) =ᶠ[𝓝 u] id) :
    IsPolylogTowerGerm N (H.universalCoverBranch ∘ sec) u := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (sec u).path
  obtain ⟨f, hf, hf0, -⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
  have hgu : (γ 1 : ℂ) = u := (congrArg Subtype.val γ.target).trans hproj.self_of_nhds
  have hf1 : IsPolylogTowerGerm N (f 1) u := hgu ▸ of_isAnalyticContinuationAlong
    isPreconnected_univ (mem_univ 0) (mem_univ 1) hf (by simpa [γ.source] using hf0)
    (by simpa [γ.source] using hF)
  exact hf1.congr
    (H.eventuallyEq_universalCoverBranch_comp_of_continuousAt hsec hproj hγ hf hf0).symm

end IsPolylogTowerGerm

/-- **Existence of polylogarithm tower germs at every unpunctured point in every height `N`.** -/
theorem exists_isPolylogTowerGerm (N : ℕ) {w : ℂ} (hw0 : w ≠ 0) (hw1 : N ≠ 0 → w ≠ 1) :
    ∃ F : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N F w ∧ F w 0 = Complex.log w := by
  induction N with
  | zero =>
    have h0 : (0 : ℂ) ∉ ball w ‖w‖ := by simp [dist_zero_left]
    obtain ⟨G, -, hGw, hGt⟩ :=
      IsPolylogTowerGerm.exists_analyticOnNhd_ball_zero h0 (Complex.log w) (Complex.exp_log hw0)
    exact ⟨G, hGt w (mem_ball_self (norm_pos_iff.mpr hw0)), congrFun hGw 0⟩
  | succ M ih =>
    obtain ⟨F', hF', hF'0⟩ := ih fun _ => hw1 (Nat.succ_ne_zero M)
    let r : ℝ := min ‖w‖ ‖w - 1‖
    have hr : 0 < r := lt_min (norm_pos_iff.mpr hw0)
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hw1 (Nat.succ_ne_zero M))))
    have h0 : 0 ∉ ball w r := by simp [r, dist_zero_left]
    have h1 : 1 ∉ ball w r := by simp [r, dist_eq_norm, norm_sub_rev]
    obtain ⟨G', hG'an, hG'eq, hG't⟩ := hF'.exists_analyticOnNhd_ball h0 fun _ => h1
    obtain ⟨G, -, hGw, hGt⟩ :=
      IsPolylogTowerGerm.exists_analyticOnNhd_ball_succ h0 h1 hG'an hG't 0
    have h0_cast : Fin.lastCases (0 : ℂ) (G' w) (0 : Fin (M + 2)) = G' w 0 :=
      (congrArg (Fin.lastCases 0 (G' w))
        (Fin.ext rfl : (0 : Fin (M + 2)) = (0 : Fin (M + 1)).castSucc)).trans
        (Fin.lastCases_castSucc 0)
    exact ⟨G, hGt w (mem_ball_self hr),
      (congrFun hGw 0).trans (h0_cast.trans ((congrFun hG'eq.eq_of_nhds 0).trans hF'0))⟩

/-- `polylogTower 0` is an `IsPolylogTowerGerm 0` at every point of `Complex.slitPlane`. -/
theorem isPolylogTowerGerm_polylogTower_zero {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    IsPolylogTowerGerm 0 (polylogTower 0) w where
  analyticAt := AnalyticAt.pi fun i => by
    fin_cases i; simpa [polylogTower] using analyticAt_id.clog hw
  eventually_exp_zero := (eventually_ne_nhds (Complex.slitPlane_ne_zero hw)).mono fun _ hz => by
    simp [Complex.exp_log hz]
  eventually_deriv_succ i := i.elim0

/-- `polylogTower 1` is an `IsPolylogTowerGerm 1` at every `w` with `w ∈ Complex.slitPlane` and
`1 - w ∈ Complex.slitPlane` (in particular at `w = 1 / 2`). -/
theorem isPolylogTowerGerm_polylogTower_one {w : ℂ} (hw0 : w ∈ Complex.slitPlane)
    (hw1 : 1 - w ∈ Complex.slitPlane) :
    IsPolylogTowerGerm 1 (polylogTower 1) w where
  analyticAt := AnalyticAt.pi fun i => by
    fin_cases i
    · simpa [polylogTower] using analyticAt_id.clog hw0
    · have han : AnalyticAt ℂ (fun z => -Complex.log (1 - z)) w :=
        ((analyticAt_const.sub analyticAt_id).clog hw1).neg
      simpa [polylogTower] using han
  eventually_exp_zero := (eventually_ne_nhds (Complex.slitPlane_ne_zero hw0)).mono fun _ hz => by
    simp [Complex.exp_log hz]
  eventually_deriv_succ i := by
    fin_cases i
    have hopen : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
      Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
    filter_upwards [hopen.mem_nhds hw1] with z (hz : 1 - z ∈ Complex.slitPlane)
    have hhd : HasDerivAt (fun u : ℂ => polylogTower 1 u 1) (1 - z)⁻¹ z := by
      have h1 : HasDerivAt (fun u : ℂ => -Complex.log (1 - u)) (-((0 - 1 : ℂ) / (1 - z))) z :=
        (HasDerivAt.clog ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)) hz).neg
      convert h1 using 1
      · ext u; simp [polylogTower]
      · ring
    simp [hhd.deriv, mul_inv_cancel₀ (Complex.slitPlane_ne_zero hz)]

end TauCeti.Polylog
