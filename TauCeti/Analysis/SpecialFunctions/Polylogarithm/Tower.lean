/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FundamentalGroup
public import TauCeti.Analysis.Complex.Conformal.UniversalCoverBranch
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The polylogarithm tower, its differential continuation, and peripheral monodromy

The principal polylogarithms `Liₙ(z)` (`n ≥ 1`) cannot be analytically continued across `(1, ∞)`
one weight at a time in isolation: continuing `Liₙ` around `1` mixes in powers of `Log z` of lower
weight, because `z · d/dz Liₙ₊₁(z) = Liₙ(z)` and `d/dz Li₁(z) = (1 - z)⁻¹`. Following Oesterlé
(*Polylogarithmes*, Séminaire Bourbaki 762, §2), one bundles `Log z` and `Li₁(z), …, Li_N(z)` into
a single `(N + 1)`-component vector germ `polylogTower N : ℂ → Fin (N + 1) → ℂ`.

This file develops the differential-equation continuation and peripheral monodromy of that tower:

* `TauCeti.Polylog.polylogTower`: the `(N + 1)`-tuple `(Log z, Li₁ z, …, Li_N z)`, together with
  projection, truncation, basepoint (`z = 1 / 2`), and cut-obstruction (`z = 3`) lemmas.
* `TauCeti.Polylog.IsPolylogTowerGerm`: a local holomorphic tuple `F : ℂ → Fin (N + 1) → ℂ` at `w`
  satisfying `exp (F z 0) = z`, `(1 - z) · (F · 1)'(z) = 1`, and `z · (F · (k + 1))'(z) = F z k`.
  Any such germ avoids `0` (and `1` when `N ≠ 0`), is uniquely determined near `w` by its value
  `F w` (`IsPolylogTowerGerm.eventuallyEq_iff_eq`), persists along any analytic continuation
  (`IsPolylogTowerGerm.of_isAnalyticContinuationAlong`), and continues analytically along every path
  in `ℂ \ {0, 1}` (`IsPolylogTowerGerm.continuesAlong`, `IsPolylogTowerGerm.continuesInside`),
  inducing a single-valued branch on `TauCeti.UniversalCover ThricePuncturedSphere.basePt` whose
  local determinations again satisfy the tower differential system
  (`IsPolylogTowerGerm.isPolylogTowerGerm_universalCoverBranch_comp`).
* `TauCeti.Polylog.polylogMonodromy`: the unipotent polynomial representation of
  `FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt` on `Fin (N + 1) → ℂ`
  prescribed by the two peripheral generators `periph0⁻¹` and `periph1⁻¹`, with coordinate
  `MvPolynomial` witnesses (`exists_mvPolynomial_polylogMonodromy`), holomorphy, invariance of
  `IsPolylogTowerGerm` (`IsPolylogTowerGerm.comp_polylogMonodromy`), and the weight-two commutator
  `4π²` (`polylogMonodromy_commutator_two`).
* All-weight peripheral and full-`π₁` universal-cover monodromy
  (`universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball`,
  `IsPolylogTowerGerm.universalCoverBranch_periph1_inv_smul`,
  `IsPolylogTowerGerm.universalCoverBranch_smul_of_analyticOnNhd_ball`), instantiated
  unconditionally at heights `0` and `1` (`polylogOneBranch`, `exists_polylogBranch_monodromy_zero`,
  `exists_polylogBranch_monodromy_one`).

## References

* J. Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993), §2,
  pp. 51–53.
* D. Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*
  (2007), Part I, §1–§2.
-/

public section

namespace TauCeti.Polylog

open Filter Metric Set Topology unitInterval

/-! ### The principal polylogarithm tower -/

/-- The classical polylogarithm tower of height `N`: entry `0` is `Complex.log z` and entry
`i ≥ 1` is `polylog i z`. Continuing this vector-valued germ along a path in `ℂ \ {0, 1}` continues
`Log` and `Li₁, …, Li_N` coherently along the same path. -/
noncomputable def polylogTower (N : ℕ) (z : ℂ) : Fin (N + 1) → ℂ :=
  fun i => if (i : ℕ) = 0 then Complex.log z else polylog (i : ℕ) z

/-- Coordinate formula for `polylogTower`. -/
theorem polylogTower_apply (N : ℕ) (z : ℂ) (i : Fin (N + 1)) :
    polylogTower N z i = if (i : ℕ) = 0 then Complex.log z else polylog (i : ℕ) z := by
  rfl

/-- Entry `0` of `polylogTower N z` is the principal logarithm `Complex.log z`. -/
@[simp]
theorem polylogTower_zero (N : ℕ) (z : ℂ) : polylogTower N z 0 = Complex.log z := by
  rfl

/-- Entry `i.succ` of `polylogTower N z` is `polylog (i + 1) z`. -/
@[simp]
theorem polylogTower_succ (N : ℕ) (z : ℂ) (i : Fin N) :
    polylogTower N z i.succ = polylog (i.succ : ℕ) z := by
  simp [polylogTower]

/-- At any nonzero index `i`, `polylogTower N z i` is `polylog i z`. -/
theorem polylogTower_apply_of_ne_zero {N : ℕ} (z : ℂ) {i : Fin (N + 1)} (hi : (i : ℕ) ≠ 0) :
    polylogTower N z i = polylog (i : ℕ) z := by
  simp [polylogTower, hi]

/-- At `z = 0`, every totalised coordinate of `polylogTower N 0` vanishes. -/
@[simp]
theorem polylogTower_zero_arg (N : ℕ) : polylogTower N 0 = 0 := by
  ext i
  by_cases hi : (i : ℕ) = 0 <;> simp [polylogTower, hi]

/-- Truncating `polylogTower N` to the first `M + 1` coordinates (`M ≤ N`) yields
`polylogTower M`. -/
theorem polylogTower_castLE {M N : ℕ} (hMN : M ≤ N) (z : ℂ) (i : Fin (M + 1)) :
    polylogTower N z (Fin.castLE (Nat.add_le_add_right hMN 1) i) = polylogTower M z i := by
  simp [polylogTower]

/-- At the basepoint `1 / 2`, entry `0` of `polylogTower` is `-Real.log 2`. -/
theorem polylogTower_half_zero (N : ℕ) : polylogTower N (1 / 2) 0 = -(Real.log 2 : ℂ) := by
  rw [polylogTower_zero]
  have h : (1 / 2 : ℂ) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_log (by positivity), Real.log_inv, Complex.ofReal_neg]

/-- At the basepoint `1 / 2`, entry `1` of `polylogTower` (`1 ≤ N`) is `Real.log 2`. -/
theorem polylogTower_half_one {N : ℕ} (hN : 1 ≤ N) :
    polylogTower N (1 / 2) ⟨1, Nat.succ_lt_succ hN⟩ = (Real.log 2 : ℂ) := by
  have hidx : (⟨1, Nat.succ_lt_succ hN⟩ : Fin (N + 1)) = (⟨0, hN⟩ : Fin N).succ := rfl
  have hval : ((⟨0, hN⟩ : Fin N).succ : ℕ) = 1 := rfl
  rw [hidx, polylogTower_succ, hval, Nat.cast_one, polylog_one]
  have h : (1 - (1 / 2 : ℂ)) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_log (by positivity), Real.log_inv, Complex.ofReal_neg, neg_neg]

/-- Height zero (`Log z` alone) is complex analytic at `z = 3`, since `3` lies off `(-∞, 0]`. -/
theorem analyticAt_polylogTower_zero_three : AnalyticAt ℂ (polylogTower 0) 3 :=
  AnalyticAt.pi fun i => by
    fin_cases i
    simp only [polylogTower, ↓reduceIte]
    exact analyticAt_id.clog (Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num)))

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
      ext w
      dsimp only [idx]
      rw [polylogTower_succ, hval, Nat.cast_one, polylog_one]
      simp
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
    rw [Complex.log_im]
    exact (Complex.arg_neg_iff.2 (by simp [φ, hy])).le
  have him_le : (Complex.log (-2)).im ≤ 0 := le_of_tendsto htend hle
  have hm2 : (-2 : ℂ) = ((-2 : ℝ) : ℂ) := by norm_num
  have him_pi : (Complex.log (-2)).im = Real.pi := by
    rw [hm2, Complex.log_im, Complex.arg_ofReal_of_neg (by norm_num)]
  linarith [Real.pi_pos]

/-! ### Differential/exponential polylogarithm tower germs -/

/-- `IsPolylogTowerGerm N F w` states that `F : ℂ → Fin (N + 1) → ℂ` is complex analytic at `w`,
`exp (F z 0) = z` near `w`, and its higher coordinates satisfy the cleared-denominator Euler system
`(1 - z) · (F · 1)'(z) = 1` and `z · (F · (k + 1))'(z) = F z k` near `w`.

Writing the differential equations in cleared-denominator form makes them entire algebraic-analytic
relations in `(z, F z, deriv F z)`: they persist automatically along every analytic continuation
without needing puncture hypotheses on the path, while evaluating at `w` forces `w ≠ 0` (and
`w ≠ 1` whenever `N ≠ 0`). -/
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
theorem ne_one (hF : IsPolylogTowerGerm N F w) (hN : N ≠ 0) : w ≠ 1 := by
  intro hw
  have h := (hF.eventually_deriv_succ ⟨0, Nat.pos_of_ne_zero hN⟩).self_of_nhds
  simp [hw] at h

/-- `IsPolylogTowerGerm` depends only on the germ of `F` at `w`. -/
theorem congr (hF : IsPolylogTowerGerm N F w) (hFG : F =ᶠ[𝓝 w] G) :
    IsPolylogTowerGerm N G w where
  analyticAt := hF.analyticAt.congr hFG
  eventually_exp_zero := by
    filter_upwards [hF.eventually_exp_zero, hFG] with z hexp heq
    simpa [heq] using hexp
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
  have hchain : deriv (fun u => Complex.exp (F u 0)) z =
      Complex.exp (F z 0) * deriv (fun u => F u 0) z :=
    (hz.differentiableAt.hasDerivAt.cexp).deriv
  rw [hchain, hexp, deriv_id] at hd
  exact hd

/-- Truncating an `N`-tower germ to height `M ≤ N` gives an `M`-tower germ. -/
theorem castLE {M : ℕ} (hMN : M ≤ N) (hF : IsPolylogTowerGerm N F w) :
    IsPolylogTowerGerm M (fun z i => F z (Fin.castLE (Nat.add_le_add_right hMN 1) i)) w where
  analyticAt := AnalyticAt.pi fun _ => analyticAt_pi_iff.1 hF.analyticAt _
  eventually_exp_zero := hF.eventually_exp_zero
  eventually_deriv_succ i := hF.eventually_deriv_succ (Fin.castLE hMN i)

/-- **Persistence of the tower differential system along analytic continuation.** If `f` continues
an `IsPolylogTowerGerm` along `c` over a preconnected parameter set `s`, then every time in `s`
carries an `IsPolylogTowerGerm` — with no puncture assumptions on `c`. -/
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
      filter_upwards [hf0, hF.eventually_exp_zero] with z hz hexp
      simp [hz, hexp]
    filter_upwards [hE.eventuallyEq hZ hs ht₀ ht₁ h0] with z hz
    exact sub_eq_zero.mp hz
  eventually_deriv_succ i := by
    have hfac : IsAnalyticContinuationAlong
        (fun _ z => if (i : ℕ) = 0 then 1 - z else z) c s :=
      .const hf.continuousOn fun t _ => by
        if hi : (i : ℕ) = 0 then
          simp only [hi, ↓reduceIte]
          exact analyticAt_const.sub analyticAt_id
        else
          simp only [hi, ↓reduceIte]
          exact analyticAt_id
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
    filter_upwards [hD.eventuallyEq hZ hs ht₀ ht₁ h0] with z hz
    exact sub_eq_zero.mp hz

/-- Two complex numbers with equal exponentials at distance strictly less than `1` are equal. -/
private theorem eq_of_exp_eq_of_norm_sub_lt_one {a b : ℂ}
    (hexp : Complex.exp a = Complex.exp b) (hnorm : ‖a - b‖ < 1) : a = b := by
  have hexp_sub : Complex.exp (a - b) = 1 := by
    rw [Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero b)]
  have him : |(a - b).im| < Real.pi := by
    linarith [Complex.abs_im_le_norm (a - b), Real.two_le_pi]
  have hlog := Complex.log_exp (x := a - b) (neg_lt_of_abs_lt him) (le_of_lt (lt_of_abs_lt him))
  rw [hexp_sub, Complex.log_one] at hlog
  exact sub_eq_zero.mp hlog.symm

/-- Entry `0` of two tower germs at `w` with the same value at `w` agree on a neighborhood of
`w`. -/
private theorem eventuallyEq_zero_coord {M : ℕ} {G : ℂ → Fin (M + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F w) (hG : IsPolylogTowerGerm M G w) (h0 : F w 0 = G w 0) :
    (fun z => F z 0) =ᶠ[𝓝 w] fun z => G z 0 := by
  have hcont : ContinuousAt (fun z => F z 0 - G z 0) w :=
    (analyticAt_pi_iff.1 hF.analyticAt 0).continuousAt.sub
      (analyticAt_pi_iff.1 hG.analyticAt 0).continuousAt
  have hlt : ∀ᶠ z in 𝓝 w, ‖F z 0 - G z 0‖ < 1 := by
    simpa [h0] using Metric.tendsto_nhds.mp hcont 1 zero_lt_one
  filter_upwards [hF.eventually_exp_zero, hG.eventually_exp_zero, hlt] with z hexpF hexpG hnorm
  exact eq_of_exp_eq_of_norm_sub_lt_one (hexpF.trans hexpG.symm) hnorm

/-- **Initial-value uniqueness for `IsPolylogTowerGerm`.** Two polylogarithm tower germs at `w`
have the same germ at `w` if and only if their values at the single point `w` coincide. -/
theorem eventuallyEq_iff_eq (hF : IsPolylogTowerGerm N F w) (hG : IsPolylogTowerGerm N G w) :
    (F =ᶠ[𝓝 w] G) ↔ F w = G w := by
  refine ⟨EventuallyEq.eq_of_nhds, fun hFG => ?_⟩
  suffices hcoord : ∀ (k : ℕ) (hk : k < N + 1),
      (fun z => F z ⟨k, hk⟩) =ᶠ[𝓝 w] fun z => G z ⟨k, hk⟩ by
    rw [Filter.eventuallyEq_iff_exists_mem]
    have hall : ∀ᶠ z in 𝓝 w, ∀ i : Fin (N + 1), F z i = G z i :=
      eventually_all.mpr fun i => hcoord i.1 i.2
    exact ⟨_, hall, fun _ hz => funext hz⟩
  intro k
  induction k with
  | zero =>
    intro _
    exact hF.eventuallyEq_zero_coord hG (congrFun hFG 0)
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
      rw [hdF, hdG]
      by_cases hj0 : (j : ℕ) = 0 <;> simp [hj0, j, hp]
    have hanF := analyticAt_pi_iff.1 hF.analyticAt j.succ
    have hanG := analyticAt_pi_iff.1 hG.analyticAt j.succ
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
      (hanF.eventually_analyticAt.and (hanG.eventually_analyticAt.and hderiv_eq))
    have heqOn := isOpen_ball.eqOn_of_deriv_eq (convex_ball w δ).isPreconnected
      (fun z hz => (hball (mem_ball.mp hz)).1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hball (mem_ball.mp hz)).2.1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hball (mem_ball.mp hz)).2.2) (mem_ball_self hδ) (congrFun hFG j.succ)
    exact hj_succ ▸ eventually_of_mem (Metric.ball_mem_nhds w hδ) heqOn

/-- Base step (`N = 0`) of `exists_analyticOnNhd_ball`: rotate `Complex.log` by `w`. -/
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
  refine ⟨G, hGan, ?_, fun z hz => ⟨hGan z hz,
    eventually_of_mem (isOpen_ball.mem_nhds hz) hexp, fun i => i.elim0⟩⟩
  ext i
  fin_cases i
  simp [G, div_self hw0]

/-- Inductive step (`M → M + 1`) of `exists_analyticOnNhd_ball`: adjoin a disc primitive for the
next polylogarithm weight via Morera's theorem (`DifferentiableOn.isExactOn_ball`). -/
private theorem exists_analyticOnNhd_ball_succ {M : ℕ} {w : ℂ} {r : ℝ}
    (h0 : 0 ∉ ball w r) (h1 : 1 ∉ ball w r)
    {G' : ℂ → Fin (M + 1) → ℂ} (hG'an : AnalyticOnNhd ℂ G' (ball w r))
    (hG'tower : ∀ z ∈ ball w r, IsPolylogTowerGerm M G' z) (c : ℂ) :
    ∃ G : ℂ → Fin (M + 2) → ℂ,
      AnalyticOnNhd ℂ G (ball w r) ∧
      G w = Fin.lastCases c (G' w) ∧
      ∀ z ∈ ball w r, IsPolylogTowerGerm (M + 1) G z := by
  let rhs : ℂ → ℂ :=
    if M = 0 then fun z => (1 - z)⁻¹ else fun z => G' z (Fin.last M) / z
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
  have hdiff : DifferentiableOn ℂ g (ball w r) :=
    fun z hz => (hgderiv z hz).differentiableAt.differentiableWithinAt
  have hgan : AnalyticOnNhd ℂ g (ball w r) := hdiff.analyticOnNhd isOpen_ball
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
  · have hGl : (fun v => G v (Fin.last M).succ) = g := by
      ext v
      exact (congrArg (G v) (Fin.ext rfl : (Fin.last M).succ = Fin.last (M + 1))).trans
        Fin.lastCases_last
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
    have hu1 : 1 - u ≠ 0 := sub_ne_zero.mpr fun h => h1 (h.symm ▸ hu)
    rw [hGl, (hgderiv u hu).deriv]
    have hGc : G u (Fin.last M).castSucc = G' u (Fin.last M) := Fin.lastCases_castSucc _
    by_cases hM : M = 0
    · simp [Fin.val_last, hM, rhs, mul_inv_cancel₀ hu1]
    · simp [Fin.val_last, hM, rhs, hGc, mul_div_cancel₀ _ hu0]
  · have hGs : (fun u => G u i.castSucc.succ) = fun u => G' u i.succ := by
      ext u
      exact (congrArg (G u) (Fin.ext rfl : i.castSucc.succ = i.succ.castSucc)).trans
        (Fin.lastCases_castSucc _)
    have hGc : ∀ u, G u i.castSucc.castSucc = G' u i.castSucc := fun _ => Fin.lastCases_castSucc _
    filter_upwards [(hG'tower z hz).eventually_deriv_succ i] with u hu
    simpa [hGs, hGc] using hu

/-- **Local disc extension of a tower germ.** On any open disc `ball w r` avoiding `0` (and
avoiding `1` when `N ≠ 0`), an `IsPolylogTowerGerm` extends to a single-valued analytic map on
`ball w r` satisfying `IsPolylogTowerGerm` at every point of the disc. -/
theorem exists_analyticOnNhd_ball (hF : IsPolylogTowerGerm N F w) {r : ℝ}
    (h0 : 0 ∉ ball w r) (h1 : N ≠ 0 → 1 ∉ ball w r) :
    ∃ G : ℂ → Fin (N + 1) → ℂ,
      AnalyticOnNhd ℂ G (ball w r) ∧
      (G =ᶠ[𝓝 w] F) ∧
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

/-- **Global continuation of a tower germ along any path in `ℂ \ {0, 1}`.** If `F` is an
`IsPolylogTowerGerm N` at `c 0` and `c : I → ℂ` avoids `0` (and avoids `1` when `N ≠ 0`), then `F`
continues analytically along `c`. -/
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

/-- **Continuation inside `ℂ \ {0, 1}`.** Every `IsPolylogTowerGerm N F w` continues inside
`{z : ℂ | z ≠ 0 ∧ z ≠ 1}`, the underlying set of `TauCeti.ThricePuncturedSphere`. -/
theorem continuesInside (hF : IsPolylogTowerGerm N F w) :
    ContinuesInside F {z : ℂ | z ≠ 0 ∧ z ≠ 1} w :=
  ContinuesInside.of_forall fun _ hc hcU hc0 =>
    (hc0 ▸ hF).continuesAlong hc (fun t => (hcU t).1) (fun _ t => (hcU t).2)

/-- At height `0` (`Log z` alone), `1` is not a puncture: an `IsPolylogTowerGerm 0 F w` continues
inside `{z : ℂ | z ≠ 0}`. -/
theorem continuesInside_zero {F : ℂ → Fin 1 → ℂ} (hF : IsPolylogTowerGerm 0 F w) :
    ContinuesInside F {z : ℂ | z ≠ 0} w :=
  ContinuesInside.of_forall fun _ hc hcU hc0 =>
    (hc0 ▸ hF).continuesAlong hc hcU (fun h => absurd rfl h)

/-- **Local determinations of the universal-cover branch satisfy the tower ODE system.** Along any
continuous local section `sec` of `UniversalCover.proj` at `u`, `H.universalCoverBranch ∘ sec` is
again an `IsPolylogTowerGerm N` at `u`. -/
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

/-- **Existence of polylogarithm tower germs at every unpunctured point in every height `N`.** For
every `N : ℕ` and `w ≠ 0` (with `w ≠ 1` when `N ≠ 0`), there exists `F : ℂ → Fin (N + 1) → ℂ`
satisfying `IsPolylogTowerGerm N F w` with `F w 0 = Complex.log w`. -/
theorem exists_isPolylogTowerGerm (N : ℕ) {w : ℂ} (hw0 : w ≠ 0) (hw1 : N ≠ 0 → w ≠ 1) :
    ∃ F : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N F w ∧ F w 0 = Complex.log w := by
  let r : ℝ := if N = 0 then ‖w‖ else min ‖w‖ ‖w - 1‖
  have hr : 0 < r := by by_cases hN : N = 0 <;> simp [r, hN, hw0, sub_ne_zero, hw1]
  have h0 : 0 ∉ ball w r := by by_cases hN : N = 0 <;> simp [r, hN, dist_zero_left]
  have h1 : N ≠ 0 → 1 ∉ ball w r := fun hN => by simp [r, hN, dist_eq_norm, norm_sub_rev]
  cases N with
  | zero =>
    obtain ⟨G, -, hGw, hGt⟩ :=
      IsPolylogTowerGerm.exists_analyticOnNhd_ball_zero h0 (Complex.log w) (Complex.exp_log hw0)
    exact ⟨G, hGt w (mem_ball_self hr), congrFun hGw 0⟩
  | succ M =>
    have h1' : 1 ∉ ball w r := h1 (Nat.succ_ne_zero M)
    have hex : ∀ K : ℕ, ∃ G : ℂ → Fin (K + 1) → ℂ,
        AnalyticOnNhd ℂ G (ball w r) ∧ G w 0 = Complex.log w ∧
        ∀ z ∈ ball w r, IsPolylogTowerGerm K G z := fun K => by
      induction K with
      | zero =>
        obtain ⟨G, hGan, hGw, hGt⟩ := IsPolylogTowerGerm.exists_analyticOnNhd_ball_zero h0
          (Complex.log w) (Complex.exp_log hw0)
        exact ⟨G, hGan, congrFun hGw 0, hGt⟩
      | succ K ihK =>
        obtain ⟨G', hG'an, hG'0, hG't⟩ := ihK
        obtain ⟨G, hGan, hGw, hGt⟩ :=
          IsPolylogTowerGerm.exists_analyticOnNhd_ball_succ h0 h1' hG'an hG't 0
        have h0_cast : Fin.lastCases (0 : ℂ) (G' w) (0 : Fin (K + 2)) = G' w 0 :=
          (congrArg (Fin.lastCases 0 (G' w))
            (Fin.ext rfl : (0 : Fin (K + 2)) = (0 : Fin (K + 1)).castSucc)).trans
            (Fin.lastCases_castSucc 0)
        exact ⟨G, hGan, (congrFun hGw 0).trans (h0_cast.trans hG'0), hGt⟩
    obtain ⟨G, -, hG0, hGt⟩ := hex (M + 1)
    exact ⟨G, hGt w (mem_ball_self hr), hG0⟩

/-- `polylogTower 0` is an `IsPolylogTowerGerm 0` at every point of `Complex.slitPlane`. -/
theorem isPolylogTowerGerm_polylogTower_zero {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    IsPolylogTowerGerm 0 (polylogTower 0) w where
  analyticAt := AnalyticAt.pi fun i => by
    fin_cases i
    simpa [polylogTower] using analyticAt_id.clog hw
  eventually_exp_zero := by
    filter_upwards [eventually_ne_nhds (Complex.slitPlane_ne_zero hw)] with z hz
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
  eventually_exp_zero := by
    filter_upwards [eventually_ne_nhds (Complex.slitPlane_ne_zero hw0)] with z hz
    simp [Complex.exp_log hz]
  eventually_deriv_succ i := by
    fin_cases i
    have hopen : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
      Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
    filter_upwards [hopen.mem_nhds hw1] with z (hz : 1 - z ∈ Complex.slitPlane)
    have hz_ne : 1 - z ≠ 0 := Complex.slitPlane_ne_zero hz
    have hhd : HasDerivAt (fun u : ℂ => polylogTower 1 u 1) (1 - z)⁻¹ z := by
      have h1 : HasDerivAt (fun u : ℂ => -Complex.log (1 - u)) (-((0 - 1 : ℂ) / (1 - z))) z :=
        (HasDerivAt.clog ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)) hz).neg
      convert h1 using 1
      · ext u
        simp [polylogTower]
      · ring
    simp [hhd.deriv, mul_inv_cancel₀ hz_ne]

/-! ### The polynomial monodromy representation of `π₁(ℂ \ {0, 1}, 1/2)` -/

/-- Additive shift of coordinate `0` (`Log`) on `Fin (N + 1) → ℂ`. -/
private def shiftLog (N : ℕ) (c : ℂ) (v : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun i => v i + if (i : ℕ) = 0 then c else 0

/-- Unipotent shift of coordinates `1, …, N` by `c * v 0 ^ (i - 1) / (i - 1)!` on
`Fin (N + 1) → ℂ`. -/
private noncomputable def shiftPolylog (N : ℕ) (c : ℂ) (v : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun i => v i + if (i : ℕ) = 0 then 0 else
    c * v 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)

/-- `shiftLog N c` as a permutation of `Fin (N + 1) → ℂ` with inverse `shiftLog N (-c)`. -/
private def shiftLogEquiv (N : ℕ) (c : ℂ) : Equiv.Perm (Fin (N + 1) → ℂ) where
  toFun := shiftLog N c
  invFun := shiftLog N (-c)
  left_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftLog, hi]
  right_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftLog, hi]

/-- `shiftPolylog N c` as a permutation of `Fin (N + 1) → ℂ` with inverse `shiftPolylog N (-c)`
(using that coordinate `0` is fixed). -/
private noncomputable def shiftPolylogEquiv (N : ℕ) (c : ℂ) : Equiv.Perm (Fin (N + 1) → ℂ) where
  toFun := shiftPolylog N c
  invFun := shiftPolylog N (-c)
  left_inv v := by
    ext i
    if hi : (i : ℕ) = 0 then simp [shiftPolylog, hi] else simp [shiftPolylog, hi]; ring
  right_inv v := by
    ext i
    if hi : (i : ℕ) = 0 then simp [shiftPolylog, hi] else simp [shiftPolylog, hi]; ring

/-- **The peripheral monodromy representation of the polylogarithm tower.** On the free generators
`periph0` and `periph1` of `FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt`,
`periph0⁻¹` (prefixing the counterclockwise loop `γ0` around `0`) adds `2πi` to entry `0` and fixes
entries `1, …, N`, while `periph1⁻¹` (prefixing the counterclockwise loop `γ1` around `1`) fixes
entry `0` and subtracts `2πi · w₀^(i-1) / (i-1)!` from entry `i ≥ 1`. -/
noncomputable def polylogMonodromy (N : ℕ) :
    FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt →*
      Equiv.Perm (Fin (N + 1) → ℂ) :=
  (FreeGroup.lift ![shiftLogEquiv N (-(2 * Real.pi * Complex.I)),
      shiftPolylogEquiv N (2 * Real.pi * Complex.I)]).comp
    ThricePuncturedSphere.fundamentalGroupMulEquivFreeGroup.toMonoidHom

/-- Action of `periph0⁻¹` (counterclockwise loop `γ0` around `0`) under `polylogMonodromy N`. -/
theorem polylogMonodromy_periph0_inv (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ w i =
      w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  simp [polylogMonodromy, shiftLogEquiv, shiftLog, Equiv.Perm.inv_def]

/-- Simp normal form (`map_inv` + `Equiv.Perm.coe_inv`) of `polylogMonodromy_periph0_inv`. -/
@[simp]
theorem polylogMonodromy_periph0_symm (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (polylogMonodromy N ThricePuncturedSphere.periph0).symm w i =
      w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  rw [← Equiv.Perm.inv_def, ← map_inv, polylogMonodromy_periph0_inv]

/-- Action of `periph0` under `polylogMonodromy N`. -/
@[simp]
theorem polylogMonodromy_periph0 (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph0 w i =
      w i - if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hi : (i : ℕ) = 0 <;> simp [polylogMonodromy, shiftLogEquiv, shiftLog, hi, sub_eq_add_neg]

/-- Action of `periph1⁻¹` (counterclockwise loop `γ1` around `1`) under `polylogMonodromy N`. -/
theorem polylogMonodromy_periph1_inv (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph1⁻¹ w i =
      w i - if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  if hi : (i : ℕ) = 0 then
    simp [polylogMonodromy, shiftPolylogEquiv, shiftPolylog, Equiv.Perm.inv_def, hi]
  else
    simp [polylogMonodromy, shiftPolylogEquiv, shiftPolylog, Equiv.Perm.inv_def, hi]
    ring

/-- Simp normal form (`map_inv` + `Equiv.Perm.coe_inv`) of `polylogMonodromy_periph1_inv`. -/
@[simp]
theorem polylogMonodromy_periph1_symm (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (polylogMonodromy N ThricePuncturedSphere.periph1).symm w i =
      w i - if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  rw [← Equiv.Perm.inv_def, ← map_inv, polylogMonodromy_periph1_inv]

/-- Action of `periph1` under `polylogMonodromy N`. -/
@[simp]
theorem polylogMonodromy_periph1 (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph1 w i =
      w i + if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  simp [polylogMonodromy, shiftPolylogEquiv, shiftPolylog]

private theorem exists_mvPolynomial_shiftLog (N : ℕ) (c : ℂ) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, shiftLog N c w i = MvPolynomial.eval w P :=
  ⟨MvPolynomial.X i + MvPolynomial.C (if (i : ℕ) = 0 then c else 0), fun _ => by simp [shiftLog]⟩

private theorem exists_mvPolynomial_shiftPolylog (N : ℕ) (c : ℂ) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, shiftPolylog N c w i = MvPolynomial.eval w P :=
  ⟨MvPolynomial.X i + if (i : ℕ) = 0 then 0 else
      MvPolynomial.C (c / (((i : ℕ) - 1).factorial : ℂ)) * MvPolynomial.X 0 ^ ((i : ℕ) - 1),
    fun _ => by by_cases hi : (i : ℕ) = 0 <;> simp [shiftPolylog, hi, div_mul_eq_mul_div]⟩

/-- **Polynomiality of `polylogMonodromy`.** Every element of `π₁(ℂ \ {0, 1}, 1/2)` acts on
`Fin (N + 1) → ℂ` by polynomial maps (`MvPolynomial (Fin (N + 1)) ℂ` in each coordinate), with
polynomial inverse supplied by `g⁻¹`. -/
theorem exists_mvPolynomial_polylogMonodromy (N : ℕ)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ,
      ∀ w, polylogMonodromy N g w i = MvPolynomial.eval w P := by
  let HasPoly (Φ : (Fin (N + 1) → ℂ) → Fin (N + 1) → ℂ) : Prop :=
    ∀ j, ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, Φ w j = MvPolynomial.eval w P
  have hcomp : ∀ {Φ Ψ}, HasPoly Φ → HasPoly Ψ → HasPoly (Φ ∘ Ψ) := fun {Φ Ψ} hΦ hΨ j => by
    choose Q hQ using hΨ
    obtain ⟨P, hP⟩ := hΦ j
    refine ⟨MvPolynomial.bind₁ Q P, fun w => ?_⟩
    have hQw : (fun k => MvPolynomial.eval w (Q k)) = Ψ w := funext fun k => (hQ k w).symm
    simp only [MvPolynomial.eval] at hQw hP ⊢
    rw [Function.comp_apply, hP, MvPolynomial.eval₂Hom_bind₁, hQw]
  suffices hboth : HasPoly (polylogMonodromy N g) ∧ HasPoly (polylogMonodromy N g⁻¹) from hboth.1 i
  have hmem : g ∈ Subgroup.closure {ThricePuncturedSphere.periph0, ThricePuncturedSphere.periph1} :=
    ThricePuncturedSphere.closure_periph0_periph1 ▸ Subgroup.mem_top g
  refine Subgroup.closure_induction (fun x hx => ?_)
    ⟨fun j => ⟨MvPolynomial.X j, by simp⟩, fun j => ⟨MvPolynomial.X j, by simp⟩⟩
    (fun x y _ _ ihx ihy =>
      ⟨by simpa [MonoidHom.map_mul, Equiv.Perm.coe_mul] using hcomp ihx.1 ihy.1,
        by simpa [mul_inv_rev, MonoidHom.map_mul, Equiv.Perm.coe_mul] using hcomp ihy.2 ihx.2⟩)
    (fun _ _ ih => ⟨ih.2, by simpa using ih.1⟩) hmem
  rcases hx with rfl | rfl
  · exact ⟨by simpa [polylogMonodromy, shiftLogEquiv, HasPoly] using
        exists_mvPolynomial_shiftLog N (-(2 * Real.pi * Complex.I)),
      by simpa [polylogMonodromy, shiftLogEquiv, Equiv.Perm.inv_def, HasPoly] using
        exists_mvPolynomial_shiftLog N (2 * Real.pi * Complex.I)⟩
  · exact ⟨by simpa [polylogMonodromy, shiftPolylogEquiv, HasPoly] using
        exists_mvPolynomial_shiftPolylog N (2 * Real.pi * Complex.I),
      by simpa [polylogMonodromy, shiftPolylogEquiv, Equiv.Perm.inv_def, HasPoly] using
        exists_mvPolynomial_shiftPolylog N (-(2 * Real.pi * Complex.I))⟩

/-- Every monodromy operator `polylogMonodromy N g` is complex analytic on `Set.univ`. -/
theorem analyticOnNhd_polylogMonodromy (N : ℕ)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt) :
    AnalyticOnNhd ℂ (polylogMonodromy N g) univ := fun w _ =>
  AnalyticAt.pi fun i => by
    obtain ⟨P, hP⟩ := exists_mvPolynomial_polylogMonodromy N g i
    simpa [← funext hP] using AnalyticOnNhd.eval_mvPolynomial P w (mem_univ w)

/-- `polylogMonodromy` commutes with truncating the tower from height `N` to height `M ≤ N`. -/
theorem polylogMonodromy_castLE {M N : ℕ} (hMN : M ≤ N)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt)
    (w : Fin (N + 1) → ℂ) (i : Fin (M + 1)) :
    polylogMonodromy N g w (Fin.castLE (Nat.add_le_add_right hMN 1) i) =
      polylogMonodromy M g (fun j => w (Fin.castLE (Nat.add_le_add_right hMN 1) j)) i := by
  let π : (Fin (N + 1) → ℂ) → Fin (M + 1) → ℂ :=
    fun v j => v (Fin.castLE (Nat.add_le_add_right hMN 1) j)
  suffices hboth : (π ∘ polylogMonodromy N g = polylogMonodromy M g ∘ π) ∧
      (π ∘ polylogMonodromy N g⁻¹ = polylogMonodromy M g⁻¹ ∘ π) from
    congrFun (congrFun hboth.1 w) i
  have hmem : g ∈ Subgroup.closure {ThricePuncturedSphere.periph0, ThricePuncturedSphere.periph1} :=
    ThricePuncturedSphere.closure_periph0_periph1 ▸ Subgroup.mem_top g
  refine Subgroup.closure_induction (fun x hx => ?_) ⟨by ext; simp [π], by ext; simp [π]⟩
    (fun x y _ _ ihx ihy => ⟨?_, ?_⟩) (fun _ _ ih => ⟨ih.2, by simpa using ih.1⟩) hmem
  · rcases hx with rfl | rfl <;> constructor <;> ext v j <;> simp [π]
  · simp only [MonoidHom.map_mul, Equiv.Perm.coe_mul]
    rw [← Function.comp_assoc, ihx.1, Function.comp_assoc, ihy.1, ← Function.comp_assoc]
  · simp only [mul_inv_rev, MonoidHom.map_mul, Equiv.Perm.coe_mul]
    rw [← Function.comp_assoc, ihy.2, Function.comp_assoc, ihx.2, ← Function.comp_assoc]

/-- **Noncommutativity of the peripheral monodromy at weight two.** Applying `periph0⁻¹` then
`periph1⁻¹` differs from `periph1⁻¹` then `periph0⁻¹` in coordinate `2` (`Li₂`) by `4π²`. -/
theorem polylogMonodromy_commutator_two {N : ℕ} (hN : 2 ≤ N) (w : Fin (N + 1) → ℂ) :
    polylogMonodromy N ThricePuncturedSphere.periph1⁻¹
        (polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ w) ⟨2, Nat.succ_lt_succ hN⟩ -
      polylogMonodromy N ThricePuncturedSphere.periph0⁻¹
        (polylogMonodromy N ThricePuncturedSphere.periph1⁻¹ w) ⟨2, Nat.succ_lt_succ hN⟩ =
      4 * (Real.pi : ℂ) ^ 2 := by
  simp only [polylogMonodromy_periph1_inv, polylogMonodromy_periph0_inv, Fin.val_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero]
  norm_num
  ring_nf
  simp [Complex.I_sq]

namespace IsPolylogTowerGerm

/-- Shifting coordinate `0` by an integer multiple of `2πi` preserves `IsPolylogTowerGerm`. -/
private theorem comp_shiftLog {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w) (k : ℤ) :
    IsPolylogTowerGerm N (shiftLog N ((k : ℂ) * (2 * Real.pi * Complex.I)) ∘ F) w where
  analyticAt := AnalyticAt.pi fun i =>
    (analyticAt_pi_iff.1 hF.analyticAt i).add analyticAt_const
  eventually_exp_zero := by
    filter_upwards [hF.eventually_exp_zero] with z hexp
    simp [shiftLog, Complex.exp_add, hexp, Complex.exp_int_mul_two_pi_mul_I]
  eventually_deriv_succ i := by
    filter_upwards [hF.eventually_deriv_succ i] with z hode
    have hsucc : (fun u => (shiftLog N ((k : ℂ) * (2 * Real.pi * Complex.I)) ∘ F) u i.succ) =
        fun u => F u i.succ := by ext u; simp [shiftLog]
    rw [hsucc]
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, ↓reduceIte] at hode ⊢
      exact hode
    · simp only [hi, ↓reduceIte, Function.comp_apply, shiftLog, Fin.val_castSucc,
        add_zero] at hode ⊢
      exact hode

/-- Shifting positive coordinates by `c * (F z 0)^(i - 1) / (i - 1)!` preserves
`IsPolylogTowerGerm` for every `c : ℂ`. -/
private theorem comp_shiftPolylog {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w) (c : ℂ) :
    IsPolylogTowerGerm N (shiftPolylog N c ∘ F) w where
  analyticAt := AnalyticAt.pi fun i => by
    obtain ⟨P, hP⟩ := exists_mvPolynomial_shiftPolylog N c i
    have hPan : AnalyticAt ℂ (fun v => MvPolynomial.eval v P) (F w) :=
      AnalyticOnNhd.eval_mvPolynomial P (F w) (mem_univ _)
    exact (hPan.comp hF.analyticAt).congr (Eventually.of_forall fun z => (hP (F z)).symm)
  eventually_exp_zero := by
    filter_upwards [hF.eventually_exp_zero] with z hexp
    simpa [shiftPolylog] using hexp
  eventually_deriv_succ i := by
    have han0 := analyticAt_pi_iff.1 hF.analyticAt 0
    have hans := analyticAt_pi_iff.1 hF.analyticAt i.succ
    filter_upwards [hF.eventually_deriv_succ i, hF.eventually_deriv_zero,
      han0.eventually_analyticAt, hans.eventually_analyticAt] with z hode hd0 hz0 hzs
    rcases i with ⟨_ | m, hm⟩
    · simp only [Fin.succ_mk, Fin.castSucc_mk] at hode ⊢
      have hfn : (fun u => (shiftPolylog N c ∘ F) u ⟨1, Nat.succ_lt_succ hm⟩) =
          fun u => F u ⟨1, Nat.succ_lt_succ hm⟩ + c := by ext u; simp [shiftPolylog]
      rw [hfn, deriv_add_const]
      exact hode
    · simp only [Fin.succ_mk, Fin.castSucc_mk, Nat.succ_ne_zero, ↓reduceIte] at hzs hode ⊢
      have hfn : (fun u => (shiftPolylog N c ∘ F) u ⟨m + 2, Nat.succ_lt_succ hm⟩) =
          fun u => F u ⟨m + 2, Nat.succ_lt_succ hm⟩ +
            c / ((m + 1).factorial : ℂ) * (F u 0) ^ (m + 1) := by
        ext u; simp [shiftPolylog, div_mul_eq_mul_div]
      have hhd_term : HasDerivAt (fun u => c / ((m + 1).factorial : ℂ) * (F u 0) ^ (m + 1))
          (c / ((m + 1).factorial : ℂ) *
            (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z)) z :=
        (hz0.differentiableAt.hasDerivAt.pow (m + 1)).const_mul _
      have hd_sum : deriv (fun u => (shiftPolylog N c ∘ F) u ⟨m + 2, Nat.succ_lt_succ hm⟩) z =
          deriv (fun u => F u ⟨m + 2, Nat.succ_lt_succ hm⟩) z +
            c / ((m + 1).factorial : ℂ) *
              (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z) := by
        rw [hfn]
        exact (hzs.differentiableAt.hasDerivAt.add hhd_term).deriv
      have hfac_ne : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      rw [hd_sum, mul_add, hode]
      simp only [Function.comp_apply, shiftPolylog, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]
      congr 1
      calc z * (c / ((m + 1).factorial : ℂ) *
              (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z))
          = (c * ((m + 1 : ℕ) : ℂ) * (F z 0) ^ m / (((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ))) *
              (z * deriv (fun u => F u 0) z) := by
            rw [Nat.factorial_succ, Nat.cast_mul]; ring
        _ = c * (F z 0) ^ m / (m.factorial : ℂ) := by
            rw [hd0, mul_one]; field_simp [hfac_ne]

/-- **Monodromy invariance of the polylogarithm tower differential system.** Post-composing any
`IsPolylogTowerGerm N F w` with `polylogMonodromy N g` yields another `IsPolylogTowerGerm N` at
`w`, for every `g ∈ π₁(ℂ \ {0, 1}, 1/2)`. -/
theorem comp_polylogMonodromy {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt) :
    IsPolylogTowerGerm N (polylogMonodromy N g ∘ F) w := by
  suffices hboth : (∀ G : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N G w →
        IsPolylogTowerGerm N (polylogMonodromy N g ∘ G) w) ∧
      (∀ G : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N G w →
        IsPolylogTowerGerm N (polylogMonodromy N g⁻¹ ∘ G) w) from hboth.1 F hF
  have hmem : g ∈ Subgroup.closure {ThricePuncturedSphere.periph0, ThricePuncturedSphere.periph1} :=
    ThricePuncturedSphere.closure_periph0_periph1 ▸ Subgroup.mem_top g
  refine Subgroup.closure_induction (fun x hx => ?_)
    ⟨fun _ hG => by simpa using hG, fun _ hG => by simpa using hG⟩
    (fun x y _ _ ihx ihy => ⟨fun G hG => by
        rw [MonoidHom.map_mul, Equiv.Perm.coe_mul, Function.comp_assoc]
        exact ihx.1 _ (ihy.1 G hG),
      fun G hG => by
        rw [mul_inv_rev, MonoidHom.map_mul, Equiv.Perm.coe_mul, Function.comp_assoc]
        exact ihy.2 _ (ihx.2 G hG)⟩)
    (fun _ _ ih => ⟨ih.2, by simpa using ih.1⟩) hmem
  rcases hx with rfl | rfl
  · refine ⟨fun G hG => ?_, fun G hG => ?_⟩
    · simpa [polylogMonodromy, shiftLogEquiv] using hG.comp_shiftLog (-1)
    · simpa [polylogMonodromy, shiftLogEquiv, Equiv.Perm.inv_def] using hG.comp_shiftLog 1
  · refine ⟨fun G hG => ?_, fun G hG => ?_⟩
    · simpa [polylogMonodromy, shiftPolylogEquiv] using
        hG.comp_shiftPolylog (2 * Real.pi * Complex.I)
    · simpa [polylogMonodromy, shiftPolylogEquiv, Equiv.Perm.inv_def] using
        hG.comp_shiftPolylog (-(2 * Real.pi * Complex.I))

end IsPolylogTowerGerm

/-! ### Explicit winding continuations around `0` and `1` and universal-cover monodromy -/

/-- Explicit continuation family carrying `Complex.log` around `γ0(t) = (1/2)·exp(2πit)`: rotating
`z` by `exp(-2πit)` keeps `γ0(t)` fixed at `1/2 ∈ slitPlane`. -/
private noncomputable def logCont0 (t : I) (z : ℂ) : ℂ :=
  Complex.log (z * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ)))) +
    2 * Real.pi * Complex.I * (t : ℂ)

private theorem γ0_mul_exp_neg (t : I) :
    (ThricePuncturedSphere.γ0 t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) =
      1 / 2 := by
  rw [ThricePuncturedSphere.coe_γ0_eq_exp, mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, mul_one]

private theorem logCont0_zero : logCont0 0 = Complex.log := by
  ext z
  simp [logCont0]

private theorem logCont0_one (z : ℂ) : logCont0 1 z = Complex.log z + 2 * Real.pi * Complex.I := by
  have h1 : (((1 : I) : ℝ) : ℂ) = 1 := by simp
  rw [logCont0, h1, mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

private theorem exp_logCont0 (t : I) {z : ℂ} (hz : z ≠ 0) : Complex.exp (logCont0 t z) = z := by
  have hrot : z * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) ≠ 0 :=
    mul_ne_zero hz (Complex.exp_ne_zero _)
  rw [logCont0, Complex.exp_add, Complex.exp_log hrot, mul_assoc, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero, mul_one]

/-- `logCont0` is an analytic continuation of `Complex.log` along `ThricePuncturedSphere.γ0`. -/
private theorem isAnalyticContinuationAlong_logCont0 :
    IsAnalyticContinuationAlong logCont0 (fun t => (ThricePuncturedSphere.γ0 t : ℂ)) univ where
  continuousOn := (continuous_subtype_val.comp ThricePuncturedSphere.γ0.continuous).continuousOn
  analyticAt t _ := by
    have hhalf : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    have hval : (ThricePuncturedSphere.γ0 t : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) ∈ Complex.slitPlane :=
      (γ0_mul_exp_neg t).symm ▸ hhalf
    exact ((analyticAt_id.mul analyticAt_const).clog hval).add analyticAt_const
  locallyEq t _ := by
    have hhalf : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    let rot : I × ℂ → ℂ := fun p =>
      p.2 * Complex.exp (-(2 * Real.pi * Complex.I * ((p.1 : ℝ) : ℂ)))
    have hrot_cont : Continuous rot := by fun_prop
    have hrot_val : rot (t, (ThricePuncturedSphere.γ0 t : ℂ)) ∈ Complex.slitPlane := by
      dsimp only [rot]
      exact (γ0_mul_exp_neg t).symm ▸ hhalf
    have hcont1 : ContinuousAt (fun p : I × ℂ => logCont0 p.1 p.2)
        (t, (ThricePuncturedSphere.γ0 t : ℂ)) :=
      (hrot_cont.continuousAt.clog hrot_val).add (by fun_prop)
    have hcont2 : ContinuousAt (fun p : I × ℂ => logCont0 t p.2)
        (t, (ThricePuncturedSphere.γ0 t : ℂ)) :=
      ((continuous_snd.mul continuous_const).continuousAt.clog hrot_val).add continuousAt_const
    have hlt : ∀ᶠ p : I × ℂ in 𝓝 (t, (ThricePuncturedSphere.γ0 t : ℂ)),
        ‖logCont0 p.1 p.2 - logCont0 t p.2‖ < 1 := by
      simpa using Metric.tendsto_nhds.mp (hcont1.sub hcont2) 1 zero_lt_one
    have hmem : {p : I × ℂ | ‖logCont0 p.1 p.2 - logCont0 t p.2‖ < 1 ∧ p.2 ≠ 0} ∈
        𝓝 t ×ˢ 𝓝 (ThricePuncturedSphere.γ0 t : ℂ) := by
      rw [← nhds_prod_eq]
      exact hlt.and (continuous_snd.continuousAt.eventually
        (eventually_ne_nhds (ThricePuncturedSphere.ne_zero _)))
    obtain ⟨V, hV, W', hW', hVW'⟩ := Filter.mem_prod_iff.mp hmem
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW'
    have hγcont : Continuous (fun u : I => (ThricePuncturedSphere.γ0 u : ℂ)) :=
      continuous_subtype_val.comp ThricePuncturedSphere.γ0.continuous
    filter_upwards [nhdsWithin_le_nhds (Filter.inter_mem hV
      (hγcont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hε))))]
      with u ⟨huV, huW⟩
    filter_upwards [isOpen_ball.mem_nhds huW] with z hzW
    obtain ⟨hnorm, hz0⟩ := hVW' (mk_mem_prod huV (hεW hzW))
    exact IsPolylogTowerGerm.eq_of_exp_eq_of_norm_sub_lt_one
      ((exp_logCont0 u hz0).trans (exp_logCont0 t hz0).symm) hnorm

/-- Explicit continuation family carrying `polylog 1` around `γ1(t) = 1 - (1/2)·exp(2πit)`,
obtained from `logCont0` via the involution `z ↦ 1 - z`. -/
private noncomputable def li1Cont1 (t : I) (z : ℂ) : ℂ :=
  -logCont0 t (1 - z)

private theorem one_sub_γ1 (t : I) :
    1 - (ThricePuncturedSphere.γ1 t : ℂ) = (ThricePuncturedSphere.γ0 t : ℂ) := by
  rw [ThricePuncturedSphere.coe_γ1_eq_exp, ThricePuncturedSphere.coe_γ0_eq_exp]
  ring

private theorem li1Cont1_zero : li1Cont1 0 = polylog 1 := by
  ext z
  simp [li1Cont1, logCont0_zero]

private theorem li1Cont1_one (z : ℂ) : li1Cont1 1 z = polylog 1 z - 2 * Real.pi * Complex.I := by
  simp [li1Cont1, logCont0_one]
  ring

private theorem isAnalyticContinuationAlong_li1Cont1 :
    IsAnalyticContinuationAlong li1Cont1 (fun t => (ThricePuncturedSphere.γ1 t : ℂ)) univ where
  continuousOn := (continuous_subtype_val.comp ThricePuncturedSphere.γ1.continuous).continuousOn
  analyticAt t _ := by
    have han := isAnalyticContinuationAlong_logCont0.analyticAt t (mem_univ t)
    have hsub : AnalyticAt ℂ (fun z : ℂ => 1 - z) (ThricePuncturedSphere.γ1 t : ℂ) :=
      analyticAt_const.sub analyticAt_id
    exact (((one_sub_γ1 t).symm ▸ han).comp hsub).neg
  locallyEq t _ := by
    filter_upwards [isAnalyticContinuationAlong_logCont0.locallyEq t (mem_univ t)] with u hu
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) (ThricePuncturedSphere.γ1 u : ℂ) :=
      continuousAt_const.sub continuousAt_id
    have hu' : logCont0 u =ᶠ[𝓝 (1 - (ThricePuncturedSphere.γ1 u : ℂ))] logCont0 t :=
      (one_sub_γ1 u).symm ▸ hu
    filter_upwards [hcont.eventually hu'] with z hz
    simp [li1Cont1, hz]

/-- Logarithmic singular model around `z = 1`: `0` in entry `0`, and
`w * (Log z)^(i - 1) / (i - 1)!` in entry `i ≥ 1` for a value `w` of `Li₁`. -/
private noncomputable def logSing1 (N : ℕ) (w z : ℂ) : Fin (N + 1) → ℂ :=
  fun i => if (i : ℕ) = 0 then 0 else
    w * (Complex.log z) ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)

private theorem analyticAt_logSing1 (N : ℕ) {w : ℂ → ℂ} {z : ℂ} (hw : AnalyticAt ℂ w z)
    (hz : z ∈ Complex.slitPlane) : AnalyticAt ℂ (fun u => logSing1 N (w u) u) z :=
  AnalyticAt.pi fun i => by
    by_cases hi : (i : ℕ) = 0
    · simp [logSing1, hi, analyticAt_const]
    · simp only [logSing1, hi, ↓reduceIte]
      exact (hw.mul ((analyticAt_id.clog hz).pow _)).div analyticAt_const
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

private theorem analyticAt_add_logSing1 {N : ℕ} {A : ℂ → Fin (N + 1) → ℂ}
    (hAan : AnalyticOnNhd ℂ A (ball 1 (3 / 4))) :
    AnalyticAt ℂ (fun z => A z + logSing1 N (polylog 1 z) z) (1 / 2) := by
  have h1 : 1 - (1 / 2 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  have h0 : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  have hli1 : AnalyticAt ℂ (polylog 1) (1 / 2) := by
    rw [funext polylog_one]
    exact ((analyticAt_const.sub analyticAt_id).clog h1).neg
  exact (hAan _ (by rw [mem_ball, dist_eq_norm]; norm_num)).add (analyticAt_logSing1 N hli1 h0)

/-- Euler-derivative identity canceling `(1 - z)⁻¹ * (Log z)^(K + 1) / (K + 1)!` against
`dslope _ 1` near `1 / 2`. -/
private theorem eventually_deriv_last_logSing1 {K : ℕ} {g a : ℂ → ℂ}
    (haderiv : ∀ z ∈ ball (1 : ℂ) (3 / 4), HasDerivAt a
      (g z / z + dslope (fun u => (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) 1 z) z) :
    ∀ᶠ z in 𝓝 (1 / 2 : ℂ),
      z * deriv (fun u => a u +
        polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) z =
      g z + polylog 1 z * (Complex.log z) ^ K / (K.factorial : ℂ) := by
  let B : ℂ → ℂ := fun u => (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)
  have hB1 : B 1 = 0 := by simp [B]
  have hball : ball (1 : ℂ) (3 / 4) ∈ 𝓝 (1 / 2 : ℂ) :=
    isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; norm_num)
  have hslit0 : Complex.slitPlane ∈ 𝓝 (1 / 2 : ℂ) :=
    Complex.isOpen_slitPlane.mem_nhds (Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num)))
  have hslit1 : {z : ℂ | 1 - z ∈ Complex.slitPlane} ∈ 𝓝 (1 / 2 : ℂ) :=
    (Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).mem_nhds
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num)))
  filter_upwards [hball, hslit0, hslit1] with z hzb hz0 hz1
  have hz_ne : z ≠ 0 := Complex.slitPlane_ne_zero hz0
  have h1z_ne : 1 - z ≠ 0 := Complex.slitPlane_ne_zero hz1
  have hd_li1 : HasDerivAt (polylog 1) ((1 - z)⁻¹) z := by
    convert (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).clog hz1).neg using 1
    · ext u; exact polylog_one u
    · dsimp; rw [zero_sub, neg_div, neg_neg, one_div]
  have hd_B : HasDerivAt B ((Complex.log z) ^ K / (K.factorial : ℂ) / z) z := by
    convert ((Complex.hasDerivAt_log hz0).pow (K + 1)).div_const ((K + 1).factorial : ℂ) using 1
    have hne : ((K + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero K)
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, div_div]
    field_simp [hne, hz_ne]
  have hB_eq : B z = -(1 - z) * dslope B 1 z := by
    have hsub := sub_smul_dslope B 1 z
    rw [hB1, sub_zero, smul_eq_mul] at hsub
    rw [← hsub]; ring
  have hfun : (fun u => a u + polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) =
      fun u => a u + polylog 1 u * B u := by ext u; dsimp [B]; ring
  have hd_tot : HasDerivAt (fun u => a u + polylog 1 u * B u)
      ((g z / z + dslope B 1 z) + ((1 - z)⁻¹ * B z +
        polylog 1 z * ((Complex.log z) ^ K / (K.factorial : ℂ) / z))) z :=
    (haderiv z hzb).add (hd_li1.mul hd_B)
  rw [hfun, hd_tot.deriv, hB_eq, neg_mul, mul_neg, inv_mul_cancel_left₀ h1z_ne]
  field_simp [hz_ne]
  ring

/-- Inductive step (`K + 1 → K + 2`) of the logarithmic singular decomposition on
`ball 1 (3 / 4)`. -/
private theorem exists_analyticOnNhd_ball_one_succ {K : ℕ}
    {A' : ℂ → Fin (K + 2) → ℂ} (hA'an : AnalyticOnNhd ℂ A' (ball 1 (3 / 4)))
    (hG' : IsPolylogTowerGerm (K + 1) (fun z => A' z + logSing1 (K + 1) (polylog 1 z) z) (1 / 2))
    (c : ℂ) :
    ∃ A : ℂ → Fin (K + 3) → ℂ,
      AnalyticOnNhd ℂ A (ball 1 (3 / 4)) ∧
      (A (1 / 2) + logSing1 (K + 2) (polylog 1 (1 / 2)) (1 / 2)) =
        Fin.lastCases c (A' (1 / 2) + logSing1 (K + 1) (polylog 1 (1 / 2)) (1 / 2)) ∧
      IsPolylogTowerGerm (K + 2) (fun z => A z + logSing1 (K + 2) (polylog 1 z) z) (1 / 2) := by
  have hslit : ∀ z ∈ ball (1 : ℂ) (3 / 4), z ∈ Complex.slitPlane := fun _ hz =>
    Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz)
  let B : ℂ → ℂ := fun z => (Complex.log z) ^ (K + 1) / ((K + 1).factorial : ℂ)
  have hBan : AnalyticOnNhd ℂ B (ball 1 (3 / 4)) := fun z hz =>
    ((analyticAt_id.clog (hslit z hz)).pow (K + 1)).div analyticAt_const
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hdslope : AnalyticOnNhd ℂ (dslope B 1) (ball 1 (3 / 4)) :=
    ((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))).mpr
      hBan.differentiableOn).analyticOnNhd isOpen_ball
  have hrhs : AnalyticOnNhd ℂ (fun z => A' z (Fin.last (K + 1)) / z + dslope B 1 z)
      (ball 1 (3 / 4)) := fun z hz =>
    ((analyticAt_pi_iff.1 (hA'an z hz) _).div analyticAt_id
      (Complex.slitPlane_ne_zero (hslit z hz))).add (hdslope z hz)
  obtain ⟨a, ha_val, haderiv⟩ := (hrhs.differentiableOn.isExactOn_ball).with_val_at (1 / 2)
    (c - polylog 1 (1 / 2) * B (1 / 2))
  have ha_an : AnalyticOnNhd ℂ a (ball 1 (3 / 4)) := DifferentiableOn.analyticOnNhd
    (fun z hz => (haderiv z hz).differentiableAt.differentiableWithinAt) isOpen_ball
  let A : ℂ → Fin (K + 3) → ℂ := fun z => Fin.lastCases (a z) (A' z)
  have hAan : AnalyticOnNhd ℂ A (ball 1 (3 / 4)) := fun z hz => AnalyticAt.pi <|
    Fin.lastCases (by simpa [A, Fin.lastCases_last] using ha_an z hz)
      fun j => by simpa [A, Fin.lastCases_castSucc] using analyticAt_pi_iff.1 (hA'an z hz) j
  have hGcast : ∀ u (j : Fin (K + 2)), (A u + logSing1 (K + 2) (polylog 1 u) u) j.castSucc =
      (A' u + logSing1 (K + 1) (polylog 1 u) u) j :=
    fun u j => by simp [A, logSing1, Fin.lastCases_castSucc]
  have h0cast : (0 : Fin (K + 3)) = (0 : Fin (K + 2)).castSucc := rfl
  refine ⟨A, hAan, ?_, analyticAt_add_logSing1 hAan,
    hG'.eventually_exp_zero.mono fun z hz => by rwa [h0cast, hGcast z 0],
    Fin.lastCases ?_ fun j => ?_⟩
  · ext i; refine Fin.lastCases ?_ (fun j => by rw [hGcast (1 / 2) j, Fin.lastCases_castSucc]) i
    have hk : K + 2 - 1 = K + 1 := rfl
    simp only [A, Pi.add_apply, logSing1, Fin.val_last, Nat.succ_ne_zero, ↓reduceIte, hk,
      Fin.lastCases_last, ha_val, B]; ring
  · have hidx : (Fin.last (K + 1)).succ = Fin.last (K + 2) := Fin.ext rfl
    have hlast : (fun u => (A u + logSing1 (K + 2) (polylog 1 u) u) (Fin.last (K + 1)).succ) =
        fun u => a u + polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ) := by
      ext u; rw [hidx, Pi.add_apply]; dsimp only [A, logSing1]; rw [Fin.lastCases_last]; simp
    filter_upwards [eventually_deriv_last_logSing1 haderiv] with z hz
    rw [hlast, hGcast z (Fin.last (K + 1))]; simpa [Fin.val_last, logSing1] using hz
  · have hidx : (Fin.castSucc j).succ = Fin.castSucc j.succ := Fin.ext rfl
    have hs : (fun u => (A u + logSing1 (K + 2) (polylog 1 u) u) (Fin.castSucc j).succ) =
        fun u => (A' u + logSing1 (K + 1) (polylog 1 u) u) j.succ :=
      funext fun u => (congrArg _ hidx).trans (hGcast u j.succ)
    filter_upwards [hG'.eventually_deriv_succ j] with z hz
    rw [hs, hGcast z j.castSucc]; simpa using hz

/-- Every initial value `v : Fin (N + 1) → ℂ` with `v 0 = Complex.log (1 / 2)` is realized by a
polylogarithm tower germ at `1 / 2` of the form `A + logSing1 N (polylog 1 ·)` with `A` analytic
across `z = 1` on `ball 1 (3 / 4)`. -/
private theorem exists_analyticOnNhd_ball_one_add_logSing1 :
    ∀ (N : ℕ) (v : Fin (N + 1) → ℂ), v 0 = Complex.log (1 / 2) →
      ∃ A : ℂ → Fin (N + 1) → ℂ,
        AnalyticOnNhd ℂ A (ball 1 (3 / 4)) ∧
        (A (1 / 2) + logSing1 N (polylog 1 (1 / 2)) (1 / 2)) = v ∧
        IsPolylogTowerGerm N (fun z => A z + logSing1 N (polylog 1 z) z) (1 / 2)
  | 0, v, hv0 => by
    have hhalf : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    refine ⟨polylogTower 0, fun z hz => AnalyticAt.pi fun i => ?_,
      by ext i; fin_cases i; simp [logSing1, hv0],
      (isPolylogTowerGerm_polylogTower_zero hhalf).congr
        (Eventually.of_forall fun z => by ext i; fin_cases i; simp [logSing1])⟩
    fin_cases i; simp only [polylogTower, ↓reduceIte]
    exact analyticAt_id.clog (Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz))
  | 1, v, hv0 => by
    have h0 : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    have h1 : 1 - (1 / 2 : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    let c₁ : ℂ := v 1 - polylog 1 (1 / 2)
    let A : ℂ → Fin 2 → ℂ := fun z => Fin.cases (Complex.log z) (fun _ => c₁)
    refine ⟨A, fun z hz => AnalyticAt.pi <|
      Fin.cases (analyticAt_id.clog
        (Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz)))
        (fun _ => analyticAt_const), ?_, ?_⟩
    · ext i; refine Fin.cases (by simp [A, logSing1, hv0]) (fun j => ?_) i
      dsimp only [A, Pi.add_apply]; rw [Fin.cases_succ]; fin_cases j; simp [c₁, logSing1]
    · refine ((isPolylogTowerGerm_polylogTower_one h0 h1).comp_shiftPolylog c₁).congr
        (Eventually.of_forall fun z => ?_)
      ext i; refine Fin.cases (by simp [A, shiftPolylog, logSing1, polylogTower]) (fun j => ?_) i
      dsimp only [A, Pi.add_apply, Function.comp_apply]; rw [Fin.cases_succ]
      fin_cases j; simp [shiftPolylog, logSing1, polylogTower]; ring
  | K + 2, v, hv0 => by
    obtain ⟨A', hA'an, hA'val, hG'⟩ :=
      exists_analyticOnNhd_ball_one_add_logSing1 (K + 1) (fun j => v j.castSucc) hv0
    obtain ⟨A, hAan, hAval, hG⟩ :=
      exists_analyticOnNhd_ball_one_succ hA'an hG' (v (Fin.last (K + 2)))
    refine ⟨A, hAan, hAval.trans ?_, hG⟩
    ext i
    exact Fin.lastCases Fin.lastCases_last
      (fun j => (Fin.lastCases_castSucc j).trans (congrFun hA'val j)) i

/-- **`γ0`-monodromy for any tower germ analytic on the open unit disc in positive weights.** If
`F` continues inside `ℂ \ {0, 1}` from `1 / 2`, agrees with `Complex.log` in coordinate `0` near
`1 / 2`, and its positive coordinates extend analytically to `ball 0 1` (which contains `γ0`), then
acting by `periph0⁻¹` applies `polylogMonodromy N periph0⁻¹` to `H.universalCoverBranch`. -/
theorem universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball {N : ℕ}
    {F : ℂ → Fin (N + 1) → ℂ}
    (H : ContinuesInside F {z : ℂ | z ≠ 0 ∧ z ≠ 1} (ThricePuncturedSphere.basePt : ℂ))
    (hF0 : (fun z => F z 0) =ᶠ[𝓝 (1 / 2 : ℂ)] Complex.log)
    {G : ℂ → Fin N → ℂ} (hGan : AnalyticOnNhd ℂ G (ball 0 1))
    (hFG : ∀ i : Fin N, (fun z => F z i.succ) =ᶠ[𝓝 (1 / 2 : ℂ)] fun z => G z i)
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    H.universalCoverBranch (ThricePuncturedSphere.periph0⁻¹ • p) =
      polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ (H.universalCoverBranch p) := by
  let f : I → ℂ → Fin (N + 1) → ℂ := fun t z =>
    Fin.cases (logCont0 t z) (fun i => G z i)
  have hγ0_ball : ∀ t : I, (ThricePuncturedSphere.γ0 t : ℂ) ∈ ball 0 1 := fun t => by
    rw [mem_ball, dist_zero_right, ThricePuncturedSphere.norm_coe_γ0]
    norm_num
  have hf : IsAnalyticContinuationAlong f (fun t => (ThricePuncturedSphere.γ0 t : ℂ)) univ := by
    refine ⟨(continuous_subtype_val.comp ThricePuncturedSphere.γ0.continuous).continuousOn,
      fun t _ => AnalyticAt.pi <| Fin.cases
        (isAnalyticContinuationAlong_logCont0.analyticAt t (mem_univ t))
        (fun i => analyticAt_pi_iff.1 (hGan _ (hγ0_ball t)) i),
      fun t _ => ?_⟩
    filter_upwards [isAnalyticContinuationAlong_logCont0.locallyEq t (mem_univ t)] with u hu
    filter_upwards [hu] with z hz
    ext i
    exact Fin.cases hz (fun _ => rfl) i
  have hf0 : f 0 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)] F := by
    rw [ThricePuncturedSphere.coe_basePt]
    have hall : ∀ᶠ z in 𝓝 (1 / 2 : ℂ), ∀ i : Fin (N + 1), f 0 z i = F z i :=
      eventually_all.mpr <| Fin.cases
        (hF0.symm.mono fun z hz => by simp [f, logCont0_zero, hz])
        (fun i => (hFG i).symm.mono fun z hz => by simp [f, hz])
    exact hall.mono fun _ hz => funext hz
  have hf1 : f 1 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)]
      polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ ∘ F := by
    rw [ThricePuncturedSphere.coe_basePt]
    have hall : ∀ᶠ z in 𝓝 (1 / 2 : ℂ), ∀ i : Fin (N + 1),
        f 1 z i = polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ (F z) i :=
      eventually_all.mpr <| Fin.cases
        (hF0.mono fun z hz => by simp [f, logCont0_one, hz])
        (fun i => (hFG i).mono fun z hz => by simp [f, ← hz])
    exact hall.mono fun _ hz => funext hz
  have hloop := H.universalCoverBranch_inv_smul_of_loop hf hf0
    (analyticOnNhd_polylogMonodromy N ThricePuncturedSphere.periph0⁻¹) hf1 p
  have hp0 : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ThricePuncturedSphere.γ0) =
      ThricePuncturedSphere.periph0 := ThricePuncturedSphere.periph0_def.symm
  rwa [hp0] at hloop

namespace IsPolylogTowerGerm

/-- **`γ1`-monodromy in arbitrary height `N` from the tower differential system alone.** For every
`N : ℕ` and every `IsPolylogTowerGerm N F (1 / 2)` whose `0`-th coordinate takes the principal value
`Complex.log (1 / 2)` at `1 / 2`, acting by `periph1⁻¹` applies `polylogMonodromy N periph1⁻¹` to
the universal-cover branch. -/
theorem universalCoverBranch_periph1_inv_smul {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (ThricePuncturedSphere.basePt : ℂ))
    (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    hF.continuesInside.universalCoverBranch (ThricePuncturedSphere.periph1⁻¹ • p) =
      polylogMonodromy N ThricePuncturedSphere.periph1⁻¹
        (hF.continuesInside.universalCoverBranch p) := by
  have hF_half : IsPolylogTowerGerm N F (1 / 2) := ThricePuncturedSphere.coe_basePt ▸ hF
  obtain ⟨A, hAan, hAval, hG⟩ := exists_analyticOnNhd_ball_one_add_logSing1 N (F (1 / 2)) hF0
  have hGF : (fun z => A z + logSing1 N (polylog 1 z) z) =ᶠ[𝓝 (1 / 2 : ℂ)] F :=
    (hG.eventuallyEq_iff_eq hF_half).mpr hAval
  have hF0_eq : (fun z => F z 0) =ᶠ[𝓝 (1 / 2 : ℂ)] Complex.log := by
    have hhalf : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    exact hF_half.eventuallyEq_zero_coord (isPolylogTowerGerm_polylogTower_zero hhalf) hF0
  let f : I → ℂ → Fin (N + 1) → ℂ := fun t z => A z + logSing1 N (li1Cont1 t z) z
  have hγ1_ball : ∀ t : I, (ThricePuncturedSphere.γ1 t : ℂ) ∈ ball (1 : ℂ) (3 / 4) := fun t => by
    rw [mem_ball, dist_eq_norm, ThricePuncturedSphere.norm_coe_γ1_sub_one]; norm_num
  have hγ1_slit : ∀ t : I, (ThricePuncturedSphere.γ1 t : ℂ) ∈ Complex.slitPlane := fun t =>
    Complex.mem_slitPlane_iff.mpr
      (Or.inl (ThricePuncturedSphere.mem_rightOpen.1 (ThricePuncturedSphere.γ1_mem_rightOpen t)))
  have hf : IsAnalyticContinuationAlong f (fun t => (ThricePuncturedSphere.γ1 t : ℂ)) univ := by
    refine ⟨(continuous_subtype_val.comp ThricePuncturedSphere.γ1.continuous).continuousOn,
      fun t _ => (hAan _ (hγ1_ball t)).add
        (analyticAt_logSing1 N (isAnalyticContinuationAlong_li1Cont1.analyticAt t (mem_univ t))
          (hγ1_slit t)),
      fun t _ => ?_⟩
    filter_upwards [isAnalyticContinuationAlong_li1Cont1.locallyEq t (mem_univ t)] with u hu
    filter_upwards [hu] with z hz
    ext i
    simp [f, logSing1, hz]
  have hf0 : f 0 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)] F := by
    rw [ThricePuncturedSphere.coe_basePt]
    simpa [f, li1Cont1_zero] using hGF
  have hf1 : f 1 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)]
      polylogMonodromy N ThricePuncturedSphere.periph1⁻¹ ∘ F := by
    rw [ThricePuncturedSphere.coe_basePt]
    filter_upwards [hGF, hF0_eq] with z hz hz0
    ext i
    by_cases hi : (i : ℕ) = 0
    · simp [f, logSing1, hi, ← hz]
    · rw [Function.comp_apply, polylogMonodromy_periph1_inv, hz0, ← hz]
      simp only [f, Pi.add_apply, logSing1, hi, ↓reduceIte, li1Cont1_one]
      ring
  have hloop := hF.continuesInside.universalCoverBranch_inv_smul_of_loop hf hf0
    (analyticOnNhd_polylogMonodromy N ThricePuncturedSphere.periph1⁻¹) hf1 p
  have hp1 : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ThricePuncturedSphere.γ1) =
      ThricePuncturedSphere.periph1 := ThricePuncturedSphere.periph1_def.symm
  rwa [hp1] at hloop

/-- **Full `π₁(ℂ \ {0, 1}, 1/2)`-equivariance in arbitrary height `N`.** Any polylogarithm tower
germ `F` at `basePt = 1 / 2` with `F (1 / 2) 0 = Complex.log (1 / 2)` whose positive coordinates
extend analytically across `0` on `ball 0 1` has universal-cover branch equivariant under the entire
fundamental group via `polylogMonodromy N`. -/
theorem universalCoverBranch_smul_of_analyticOnNhd_ball {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (ThricePuncturedSphere.basePt : ℂ))
    (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    {G : ℂ → Fin N → ℂ} (hGan : AnalyticOnNhd ℂ G (ball 0 1))
    (hFG : ∀ i : Fin N, (fun z => F z i.succ) =ᶠ[𝓝 (1 / 2 : ℂ)] fun z => G z i)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt)
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    hF.continuesInside.universalCoverBranch (g • p) =
      polylogMonodromy N g (hF.continuesInside.universalCoverBranch p) := by
  have hF_half : IsPolylogTowerGerm N F (1 / 2) := ThricePuncturedSphere.coe_basePt ▸ hF
  have hhalf : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  have hF0_eq : (fun z => F z 0) =ᶠ[𝓝 (1 / 2 : ℂ)] Complex.log :=
    hF_half.eventuallyEq_zero_coord (isPolylogTowerGerm_polylogTower_zero hhalf) hF0
  refine hF.continuesInside.universalCoverBranch_smul_of_closure
    ThricePuncturedSphere.closure_periph0_periph1 (fun x hx q => ?_) g p
  rcases hx with rfl | rfl
  · exact universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball
      hF.continuesInside hF0_eq hGan hFG q
  · exact hF.universalCoverBranch_periph1_inv_smul hF0 q

end IsPolylogTowerGerm

/-- `polylogTower 0` continues inside `{z : ℂ | z ≠ 0 ∧ z ≠ 1}` from `basePt = 1 / 2`. -/
theorem continuesInside_polylogTower_zero :
    ContinuesInside (polylogTower 0) {z : ℂ | z ≠ 0 ∧ z ≠ 1}
      (ThricePuncturedSphere.basePt : ℂ) := by
  have hhalf : (ThricePuncturedSphere.basePt : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num [ThricePuncturedSphere.coe_basePt]))
  exact (isPolylogTowerGerm_polylogTower_zero hhalf).continuesInside

/-- `polylogTower 1` continues inside `{z : ℂ | z ≠ 0 ∧ z ≠ 1}` from `basePt = 1 / 2`. -/
theorem continuesInside_polylogTower_one :
    ContinuesInside (polylogTower 1) {z : ℂ | z ≠ 0 ∧ z ≠ 1}
      (ThricePuncturedSphere.basePt : ℂ) := by
  have hhalf0 : (ThricePuncturedSphere.basePt : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num [ThricePuncturedSphere.coe_basePt]))
  have hhalf1 : 1 - (ThricePuncturedSphere.basePt : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num [ThricePuncturedSphere.coe_basePt]))
  exact (isPolylogTowerGerm_polylogTower_one hhalf0 hhalf1).continuesInside

/-- The universal-cover branch of `polylogTower 1 = (Log, Li₁)` over the thrice-punctured sphere
based at `1 / 2`. -/
noncomputable def polylogOneBranch :
    UniversalCover ThricePuncturedSphere.basePt → Fin 2 → ℂ :=
  continuesInside_polylogTower_one.universalCoverBranch

/-- Equivariance of `polylogOneBranch` under the full fundamental group `π₁(ℂ \ {0, 1}, 1/2)`. -/
theorem polylogOneBranch_smul
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt)
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    polylogOneBranch (g • p) = polylogMonodromy 1 g (polylogOneBranch p) := by
  have hhalf0 : (ThricePuncturedSphere.basePt : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num [ThricePuncturedSphere.coe_basePt]))
  have hhalf1 : 1 - (ThricePuncturedSphere.basePt : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num [ThricePuncturedSphere.coe_basePt]))
  have h1 := isPolylogTowerGerm_polylogTower_one hhalf0 hhalf1
  refine h1.universalCoverBranch_smul_of_analyticOnNhd_ball
    rfl (G := fun z _ => polylog 1 z) (fun z hz => AnalyticAt.pi fun _ => ?_)
    (fun i => by fin_cases i; exact .rfl) g p
  have h1z : 1 - z ∈ Complex.slitPlane :=
    sub_eq_add_neg (1 : ℂ) z ▸ Complex.mem_slitPlane_of_norm_lt_one (by simpa using hz)
  rw [funext polylog_one]
  exact ((analyticAt_const.sub analyticAt_id).clog h1z).neg

/-- **Coherent universal-cover branch and polynomial monodromy at height `0` (`Log`).** -/
theorem exists_polylogBranch_monodromy_zero :
    ∃ (B : UniversalCover ThricePuncturedSphere.basePt → Fin 1 → ℂ)
      (ρ : FundamentalGroup ThricePuncturedSphere
        ThricePuncturedSphere.basePt →* Equiv.Perm (Fin 1 → ℂ)),
      (∀ (z : ThricePuncturedSphere) (γ : Path ThricePuncturedSphere.basePt z),
        ∃ f : I → ℂ → Fin 1 → ℂ,
          IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
          (f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogTower 0) ∧
          B ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ)) ∧
      (∀ g i, ∃ P : MvPolynomial (Fin 1) ℂ, ∀ w, ρ g w i = MvPolynomial.eval w P) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph0⁻¹ w i =
        w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph1⁻¹ w i =
        w i - if (i : ℕ) = 0 then 0 else
          2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)) ∧
      (∀ g p, B (g • p) = ρ g (B p)) := by
  refine ⟨fun p i => polylogOneBranch p (Fin.castLE (by decide) i), polylogMonodromy 0,
    fun z γ => ?_, exists_mvPolynomial_polylogMonodromy 0,
    polylogMonodromy_periph0_inv 0, polylogMonodromy_periph1_inv 0, fun g p => ?_⟩
  · obtain ⟨f, hf, hf0, hval⟩ :=
      continuesInside_polylogTower_one.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    let π : (Fin 2 → ℂ) → (Fin 1 → ℂ) := fun v i => v (Fin.castLE (by decide) i)
    refine ⟨fun t z => π (f t z), hf.comp_analyticAt fun _ _ =>
      AnalyticAt.pi fun i => analyticAt_pi_iff.1 analyticAt_id _, ?_, ?_⟩
    · rw [ThricePuncturedSphere.coe_basePt] at hf0
      refine (hf0.fun_comp π).trans (Eventually.of_forall fun u => ?_)
      ext i
      exact polylogTower_castLE (Nat.zero_le 1) u i
    · simp [polylogOneBranch, π, hval]
  · ext i
    fin_cases i
    simpa using (congrFun (polylogOneBranch_smul g p) 0).trans
      (polylogMonodromy_castLE (Nat.zero_le 1) g (polylogOneBranch p) 0)

/-- **Coherent universal-cover branch and polynomial monodromy at height `1` (`(Log, Li₁)`).** -/
theorem exists_polylogBranch_monodromy_one :
    ∃ (B : UniversalCover ThricePuncturedSphere.basePt → Fin 2 → ℂ)
      (ρ : FundamentalGroup ThricePuncturedSphere
        ThricePuncturedSphere.basePt →* Equiv.Perm (Fin 2 → ℂ)),
      (∀ (z : ThricePuncturedSphere) (γ : Path ThricePuncturedSphere.basePt z),
        ∃ f : I → ℂ → Fin 2 → ℂ,
          IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
          (f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogTower 1) ∧
          B ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ)) ∧
      (∀ g i, ∃ P : MvPolynomial (Fin 2) ℂ, ∀ w, ρ g w i = MvPolynomial.eval w P) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph0⁻¹ w i =
        w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph1⁻¹ w i =
        w i - if (i : ℕ) = 0 then 0 else
          2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)) ∧
      (∀ g p, B (g • p) = ρ g (B p)) :=
  ⟨polylogOneBranch, polylogMonodromy 1,
    fun _ γ => by
      obtain ⟨f, hf, hf0, hval⟩ :=
        continuesInside_polylogTower_one.exists_isAnalyticContinuationAlong_universalCoverBranch γ
      rw [ThricePuncturedSphere.coe_basePt] at hf0
      exact ⟨f, hf, hf0, hval⟩,
    exists_mvPolynomial_polylogMonodromy 1, polylogMonodromy_periph0_inv 1,
    polylogMonodromy_periph1_inv 1, polylogOneBranch_smul⟩

/-- At `basepointLift`, `polylogOneBranch` evaluates to `(-Real.log 2, Real.log 2)`. -/
theorem polylogOneBranch_basepointLift :
    polylogOneBranch (UniversalCover.basepointLift ThricePuncturedSphere.basePt) =
      ![-(Real.log 2 : ℂ), (Real.log 2 : ℂ)] := by
  rw [polylogOneBranch, ContinuesInside.universalCoverBranch_basepointLift,
    ThricePuncturedSphere.coe_basePt]
  ext i
  fin_cases i
  · exact polylogTower_half_zero 1
  · exact polylogTower_half_one le_rfl

/-- After one counterclockwise loop `γ0` around `0` from `1 / 2`, `Log` becomes
`-Real.log 2 + 2πi` while `Li₁` stays `Real.log 2`. -/
theorem polylogOneBranch_periph0_inv_smul_basepointLift :
    polylogOneBranch (ThricePuncturedSphere.periph0⁻¹ •
        (UniversalCover.basepointLift ThricePuncturedSphere.basePt :
          UniversalCover ThricePuncturedSphere.basePt)) =
      ![-(Real.log 2 : ℂ) + 2 * Real.pi * Complex.I, (Real.log 2 : ℂ)] := by
  rw [polylogOneBranch_smul, polylogOneBranch_basepointLift]
  ext i
  fin_cases i <;> simp

/-- After one counterclockwise loop `γ1` around `1` from `1 / 2`, `Log` stays `-Real.log 2` while
`Li₁` becomes `Real.log 2 - 2πi`. -/
theorem polylogOneBranch_periph1_inv_smul_basepointLift :
    polylogOneBranch (ThricePuncturedSphere.periph1⁻¹ •
        (UniversalCover.basepointLift ThricePuncturedSphere.basePt :
          UniversalCover ThricePuncturedSphere.basePt)) =
      ![-(Real.log 2 : ℂ), (Real.log 2 : ℂ) - 2 * Real.pi * Complex.I] := by
  rw [polylogOneBranch_smul, polylogOneBranch_basepointLift]
  ext i
  fin_cases i <;> simp

end TauCeti.Polylog
