/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.UniversalCoverBranch
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# The polylogarithm tower and its differential analytic continuation

Following Oesterlé (*Polylogarithmes*, Séminaire Bourbaki 762, §2), continuing `Liₙ(z)` around `1`
mixes in lower-weight powers of `Log z`, so one bundles `Log z` and `Li₁(z), …, Li_N(z)` into
`polylogTower N : ℂ → Fin (N + 1) → ℂ`.

* `TauCeti.Polylog.polylogTower`: `(Log z, Li₁ z, …, Li_N z)`, with projection, truncation,
  basepoint (`1 / 2`), holomorphy, and real-cut (`x > 1`) non-analyticity lemmas.
* `TauCeti.Polylog.IsPolylogTowerGerm`: a local holomorphic tuple `F : ℂ → Fin (N + 1) → ℂ` at `w`
  satisfying `exp (F z 0) = z`, `(1 - z) · (F · 1)'(z) = 1` for `1 ≤ N`, and
  `z · (F · (k + 1))'(z) = F z k` for `1 ≤ k < N`; uniquely determined by `F w`, preserved under
  analytic continuation, and continuing inside `ℂ \ {0, 1}` to a universal-cover branch.

## References

* J. Oesterlé, *Polylogarithmes*, Astérisque 216 (1993), §2; D. Zagier, *The dilogarithm function*.
-/

public section

namespace TauCeti.Polylog

open Filter Metric Set Topology unitInterval

/-- Polylogarithm tower of height `N`: entry `0` is `Complex.log z` and `i ≥ 1` is `polylog i z`. -/
noncomputable def polylogTower (N : ℕ) (z : ℂ) : Fin (N + 1) → ℂ :=
  fun i => if (i : ℕ) = 0 then Complex.log z else polylog (i : ℕ) z

/-- Coordinate formula for `polylogTower`. -/
theorem polylogTower_apply (N : ℕ) (z : ℂ) (i : Fin (N + 1)) :
    polylogTower N z i = if (i : ℕ) = 0 then Complex.log z else polylog (i : ℕ) z := by rfl

/-- Entry `0` of `polylogTower N z` is `Complex.log z`. -/
@[simp] theorem polylogTower_zero (N : ℕ) (z : ℂ) : polylogTower N z 0 = Complex.log z := by rfl

/-- Entry `i.succ` of `polylogTower N z` is `polylog (i + 1) z`. -/
@[simp] theorem polylogTower_succ (N : ℕ) (z : ℂ) (i : Fin N) :
    polylogTower N z i.succ = polylog (i.succ : ℕ) z := by simp [polylogTower]

/-- Entry `1` of `polylogTower N z` (`[NeZero N]`) is `polylog 1 z`. -/
@[simp] theorem polylogTower_one {N : ℕ} [NeZero N] (z : ℂ) :
    polylogTower N z 1 = polylog 1 z := by
  simp [polylogTower_apply, Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.pos_of_ne_zero (NeZero.ne N)))]

/-- At any nonzero index `i`, `polylogTower N z i` is `polylog i z`. -/
theorem polylogTower_apply_of_ne_zero {N : ℕ} (z : ℂ) {i : Fin (N + 1)} (hi : (i : ℕ) ≠ 0) :
    polylogTower N z i = polylog (i : ℕ) z := by simp [polylogTower, hi]

/-- At `z = 0`, every totalised coordinate of `polylogTower N 0` vanishes. -/
@[simp] theorem polylogTower_zero_right (N : ℕ) : polylogTower N 0 = 0 := by
  ext i; by_cases hi : (i : ℕ) = 0 <;> simp [polylogTower, hi]

/-- Restricting `polylogTower (N + 1)` along `Fin.castSucc` gives `polylogTower N`. -/
@[simp] theorem polylogTower_castSucc (N : ℕ) (z : ℂ) (i : Fin (N + 1)) :
    polylogTower (N + 1) z i.castSucc = polylogTower N z i := by simp [polylogTower]

/-- Truncating `polylogTower N` to the first `M + 1` coordinates gives `polylogTower M`. -/
@[simp] theorem polylogTower_castLE {M N : ℕ} (h : M + 1 ≤ N + 1) (z : ℂ) (i : Fin (M + 1)) :
    polylogTower N z (Fin.castLE h i) = polylogTower M z i := by simp [polylogTower]

/-- At the basepoint `1 / 2`, entry `0` of `polylogTower` is `-Real.log 2`. -/
theorem polylogTower_half_zero (N : ℕ) : polylogTower N (1 / 2) 0 = -(Real.log 2 : ℂ) := by
  have h : (1 / 2 : ℂ) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [polylogTower_zero, h, ← Complex.ofReal_log (by positivity), Real.log_inv, Complex.ofReal_neg]

/-- At the basepoint `1 / 2`, entry `1` of `polylogTower` (`1 ≤ N`) is `Real.log 2`. -/
theorem polylogTower_half_one {N : ℕ} (hN : 1 ≤ N) :
    polylogTower N (1 / 2) ⟨1, Nat.succ_lt_succ hN⟩ = (Real.log 2 : ℂ) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hidx : (⟨1, Nat.succ_lt_succ hN⟩ : Fin (N + 1)) = 1 :=
    Fin.ext (Nat.mod_eq_of_lt (Nat.succ_lt_succ hN)).symm
  have h : (1 - (1 / 2 : ℂ)) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hidx, polylogTower_one, polylog_one, h,
    ← Complex.ofReal_log (by positivity), Real.log_inv, Complex.ofReal_neg, neg_neg]

/-- For `1 ≤ N`, `polylogTower N` is not complex analytic at any real point `x > 1`. -/
theorem not_analyticAt_polylogTower_of_one_lt {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 1 < x) :
    ¬ AnalyticAt ℂ (polylogTower N) x := fun h => by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩; have h1 := analyticAt_pi_iff.1 h 1
  simp only [polylogTower_one] at h1
  exact (Complex.mem_slitPlane_iff.mp (continuousAt_polylog_one_iff.mp h1.continuousAt)).elim
    (fun hlt => by simp at hlt; linarith) (fun him => by simp at him)

/-- `IsPolylogTowerGerm N F w` states that `F : ℂ → Fin (N + 1) → ℂ` is complex analytic at `w`,
`exp (F z 0) = z` near `w`, and its higher coordinates satisfy `(1 - z) · (F · 1)'(z) = 1` for
`1 ≤ N` and `z · (F · (k + 1))'(z) = F z k` for `1 ≤ k < N` near `w`. -/
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

/-- No polylogarithm tower germ exists at `0`. -/
theorem ne_zero (hF : IsPolylogTowerGerm N F w) : w ≠ 0 :=
  hF.exp_zero ▸ Complex.exp_ne_zero (F w 0)

/-- When `N ≠ 0`, no polylogarithm tower germ exists at `1`. -/
theorem ne_one (hF : IsPolylogTowerGerm N F w) (hN : N ≠ 0) : w ≠ 1 := fun hw => by
  have h := (hF.eventually_deriv_succ ⟨0, Nat.pos_of_ne_zero hN⟩).self_of_nhds; simp [hw] at h

/-- `IsPolylogTowerGerm` depends only on the germ of `F` at `w`. -/
theorem congr (hF : IsPolylogTowerGerm N F w) (hFG : F =ᶠ[𝓝 w] G) : IsPolylogTowerGerm N G w where
  analyticAt := hF.analyticAt.congr hFG
  eventually_exp_zero := hF.eventually_exp_zero.mp (hFG.mono fun _ heq hexp => heq ▸ hexp)
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

/-- Pointwise derivative of coordinate `0` of an `IsPolylogTowerGerm` at `w`. -/
theorem hasDerivAt_zero (hF : IsPolylogTowerGerm N F w) : HasDerivAt (fun u => F u 0) w⁻¹ w := by
  have hd := (analyticAt_pi_iff.1 hF.analyticAt 0).differentiableAt.hasDerivAt
  rwa [mul_left_cancel₀ hF.ne_zero (hF.eventually_deriv_zero.self_of_nhds.trans
    (mul_inv_cancel₀ hF.ne_zero).symm)] at hd

/-- Pointwise `deriv` formula for coordinate `0` at `w`. -/
theorem deriv_zero (hF : IsPolylogTowerGerm N F w) : deriv (fun u => F u 0) w = w⁻¹ :=
  hF.hasDerivAt_zero.deriv

/-- Pointwise derivative of coordinate `1` (`[NeZero N]`) at `w`. -/
theorem hasDerivAt_one [NeZero N] (hF : IsPolylogTowerGerm N F w) :
    HasDerivAt (fun u => F u 1) (1 - w)⁻¹ w := by
  have hd := (analyticAt_pi_iff.1 hF.analyticAt 1).differentiableAt.hasDerivAt
  have hw1 : 1 - w ≠ 0 := sub_ne_zero.mpr (hF.ne_one (NeZero.ne N)).symm
  have h0 := (hF.eventually_deriv_succ 0).self_of_nhds
  simp only [Fin.val_zero, ↓reduceIte, Fin.succ_zero_eq_one'] at h0
  rwa [mul_left_cancel₀ hw1 (h0.trans (mul_inv_cancel₀ hw1).symm)] at hd

/-- Pointwise `deriv` formula for coordinate `1` (`[NeZero N]`) at `w`. -/
theorem deriv_one [NeZero N] (hF : IsPolylogTowerGerm N F w) :
    deriv (fun u => F u 1) w = (1 - w)⁻¹ := hF.hasDerivAt_one.deriv

/-- Pointwise derivative of coordinate `i.succ` (`(i : ℕ) ≠ 0`) at `w`. -/
theorem hasDerivAt_succ (hF : IsPolylogTowerGerm N F w) {i : Fin N} (hi : (i : ℕ) ≠ 0) :
    HasDerivAt (fun u => F u i.succ) (F w i.castSucc / w) w := by
  have hd := (analyticAt_pi_iff.1 hF.analyticAt i.succ).differentiableAt.hasDerivAt
  have h0 := (hF.eventually_deriv_succ i).self_of_nhds; simp only [hi, ↓reduceIte] at h0
  rwa [mul_left_cancel₀ hF.ne_zero (h0.trans (mul_div_cancel₀ _ hF.ne_zero).symm)] at hd

/-- Pointwise `deriv` formula for coordinate `i.succ` (`(i : ℕ) ≠ 0`) at `w`. -/
theorem deriv_succ (hF : IsPolylogTowerGerm N F w) {i : Fin N} (hi : (i : ℕ) ≠ 0) :
    deriv (fun u => F u i.succ) w = F w i.castSucc / w := (hF.hasDerivAt_succ hi).deriv

/-- Truncating an `N`-tower germ to height `M` (`M + 1 ≤ N + 1`) gives an `M`-tower germ. -/
theorem castLE {M : ℕ} (h : M + 1 ≤ N + 1) (hF : IsPolylogTowerGerm N F w) :
    IsPolylogTowerGerm M (fun z i => F z (Fin.castLE h i)) w where
  analyticAt := AnalyticAt.pi fun _ => analyticAt_pi_iff.1 hF.analyticAt _
  eventually_exp_zero := hF.eventually_exp_zero
  eventually_deriv_succ i := hF.eventually_deriv_succ (Fin.castLE (Nat.le_of_succ_le_succ h) i)

/-- **Persistence of the tower differential system along analytic continuation.** If `f` is an
analytic continuation along `c` over a preconnected set `s` starting at an `IsPolylogTowerGerm` at
`c t₀`, then `f t₁` is an `IsPolylogTowerGerm` at `c t₁`. -/
theorem of_isAnalyticContinuationAlong {X : Type*} [TopologicalSpace X] {s : Set X} {t₀ t₁ : X}
    (hs : IsPreconnected s) (ht₀ : t₀ ∈ s) (ht₁ : t₁ ∈ s) {c : X → ℂ}
    {f : X → ℂ → Fin (N + 1) → ℂ} (hf : IsAnalyticContinuationAlong f c s)
    (hf0 : f t₀ =ᶠ[𝓝 (c t₀)] F) (hF : IsPolylogTowerGerm N F (c t₀)) :
    IsPolylogTowerGerm N (f t₁) (c t₁) where
  analyticAt := hf.analyticAt t₁ ht₁
  eventually_exp_zero := by
    have hE : IsAnalyticContinuationAlong (fun t z => Complex.exp (f t z 0) - z) c s :=
      ((hf.eval 0).analyticAt_comp fun _ _ => analyticAt_id.cexp).sub
        (.const hf.continuousOn fun _ _ => analyticAt_id)
    have h0 : (fun z => Complex.exp (f t₀ z 0) - z) =ᶠ[𝓝 (c t₀)] fun _ => 0 := by
      filter_upwards [hf0, hF.eventually_exp_zero] with z hz hexp; simp [hz, hexp]
    exact (hE.eventuallyEq (.const hf.continuousOn fun _ _ => analyticAt_const) hs ht₀ ht₁ h0).mono
      fun _ => sub_eq_zero.mp
  eventually_deriv_succ i := by
    have hfac : IsAnalyticContinuationAlong (fun _ z => if (i : ℕ) = 0 then 1 - z else z) c s :=
      .const hf.continuousOn fun _ _ => by
      if hi : (i : ℕ) = 0 then simp only [hi, ↓reduceIte]; exact analyticAt_const.sub analyticAt_id
      else simp only [hi, ↓reduceIte]; exact analyticAt_id
    have hrhs : IsAnalyticContinuationAlong
        (fun t z => if (i : ℕ) = 0 then 1 else f t z i.castSucc) c s := by
      if hi : (i : ℕ) = 0 then
        simpa [hi] using IsAnalyticContinuationAlong.const hf.continuousOn fun _ _ =>
          analyticAt_const
      else simpa [hi] using hf.eval i.castSucc
    have hi0 : (fun u => f t₀ u i.succ) =ᶠ[𝓝 (c t₀)] fun u => F u i.succ :=
      hf0.mono fun _ h => by simp [h]
    have h0 : (fun z => (if (i : ℕ) = 0 then 1 - z else z) * deriv (fun u => f t₀ u i.succ) z -
        (if (i : ℕ) = 0 then 1 else f t₀ z i.castSucc)) =ᶠ[𝓝 (c t₀)] fun _ => 0 := by
      filter_upwards [hf0, hi0.deriv, hF.eventually_deriv_succ i] with z hz hd hode
      simp [hz, hd, hode]
    exact (((hfac.mul (hf.eval i.succ).deriv).sub hrhs).eventuallyEq
      (.const hf.continuousOn fun _ _ => analyticAt_const) hs ht₀ ht₁ h0).mono
      fun _ => sub_eq_zero.mp

/-- **Initial-value uniqueness for `IsPolylogTowerGerm`.** Two `N`-tower germs at `w` agree on
a neighborhood of `w` if and only if they have the same value at `w`. -/
theorem eventuallyEq_iff_eq (hF : IsPolylogTowerGerm N F w) (hG : IsPolylogTowerGerm N G w) :
    (F =ᶠ[𝓝 w] G) ↔ F w = G w := by
  refine ⟨EventuallyEq.eq_of_nhds, fun hFG => ?_⟩
  suffices hcoord : ∀ (k : ℕ) (hk : k < N + 1),
      (fun z => F z ⟨k, hk⟩) =ᶠ[𝓝 w] fun z => G z ⟨k, hk⟩ from
    (eventually_all.mpr fun i : Fin (N + 1) => hcoord i.val i.isLt).mono fun _ => funext
  intro k; induction k with
  | zero =>
    intro _
    have hcont : ContinuousAt (fun z => F z 0 - G z 0) w :=
      (analyticAt_pi_iff.1 hF.analyticAt 0).continuousAt.sub
        (analyticAt_pi_iff.1 hG.analyticAt 0).continuousAt
    have hlt : ∀ᶠ z in 𝓝 w, ‖F z 0 - G z 0‖ < 2 * Real.pi := by
      simpa [congrFun hFG 0] using
        Metric.tendsto_nhds.mp hcont (2 * Real.pi) (mul_pos two_pos Real.pi_pos)
    filter_upwards [hF.eventually_exp_zero, hG.eventually_exp_zero, hlt] with z hexpF hexpG hnorm
    exact Complex.eq_of_exp_eq_of_norm_sub_lt (hexpF.trans hexpG.symm) hnorm
  | succ k ih =>
    intro hk
    let j : Fin N := ⟨k, Nat.lt_of_succ_lt_succ hk⟩; have hj_succ : j.succ = ⟨k + 1, hk⟩ := rfl
    have hfac_ne : ∀ᶠ z in 𝓝 w, (if (j : ℕ) = 0 then 1 - z else z) ≠ 0 := by
      by_cases hj0 : (j : ℕ) = 0
      · exact (eventually_ne_nhds (hF.ne_one (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)))).mono
          fun z hz => by simp [hj0, sub_ne_zero, hz.symm]
      · simpa [hj0] using eventually_ne_nhds hF.ne_zero
    have hderiv_eq : deriv (fun u => F u j.succ) =ᶠ[𝓝 w] deriv (fun u => G u j.succ) := by
      filter_upwards [hF.eventually_deriv_succ j, hG.eventually_deriv_succ j,
        ih (Nat.lt_succ_of_lt j.isLt), hfac_ne] with z hdF hdG hp hne
      apply mul_left_cancel₀ hne; rw [hdF, hdG]; by_cases hj0 : (j : ℕ) = 0 <;> simp [hj0, j, hp]
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
      ((analyticAt_pi_iff.1 hF.analyticAt j.succ).eventually_analyticAt.and
        ((analyticAt_pi_iff.1 hG.analyticAt j.succ).eventually_analyticAt.and hderiv_eq))
    have heqOn := isOpen_ball.eqOn_of_deriv_eq (convex_ball w δ).isPreconnected
      (fun z hz => (hball (mem_ball.mp hz)).1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hball (mem_ball.mp hz)).2.1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hball (mem_ball.mp hz)).2.2) (mem_ball_self hδ) (congrFun hFG j.succ)
    exact hj_succ ▸ eventually_of_mem (Metric.ball_mem_nhds w hδ) heqOn

/-- Appending a coordinate `g` satisfying the `(M + 1)`-th tower differential equation at `w` to
an `M`-tower germ `G'` yields an `(M + 1)`-tower germ `fun z => Fin.lastCases (g z) (G' z)`. -/
theorem lastCases {M : ℕ} {G' : ℂ → Fin (M + 1) → ℂ} {g : ℂ → ℂ} {w : ℂ}
    (hG' : IsPolylogTowerGerm M G' w) (hg : AnalyticAt ℂ g w)
    (hode : ∀ᶠ z in 𝓝 w,
      (if M = 0 then 1 - z else z) * deriv g z = if M = 0 then 1 else G' z (Fin.last M)) :
    IsPolylogTowerGerm (M + 1) (fun z => Fin.lastCases (g z) (G' z)) w where
  analyticAt := AnalyticAt.pi <| Fin.lastCases (by simpa [Fin.lastCases_last] using hg)
    fun i => by simpa [Fin.lastCases_castSucc] using analyticAt_pi_iff.1 hG'.analyticAt i
  eventually_exp_zero := by
    have h0 : ∀ u, Fin.lastCases (g u) (G' u) 0 = G' u 0 := fun u =>
      (congrArg (Fin.lastCases (g u) (G' u))
        (Fin.ext rfl : (0 : Fin (M + 2)) = (0 : Fin (M + 1)).castSucc)).trans
        (Fin.lastCases_castSucc 0)
    simpa [h0] using hG'.eventually_exp_zero
  eventually_deriv_succ := Fin.lastCases
    (by
      have hGl : (fun v => Fin.lastCases (g v) (G' v) (Fin.last M).succ) = g :=
        funext fun v => (congrArg (Fin.lastCases (g v) (G' v))
          (Fin.ext rfl : (Fin.last M).succ = Fin.last (M + 1))).trans Fin.lastCases_last
      have hGc : ∀ u, Fin.lastCases (g u) (G' u) (Fin.last M).castSucc = G' u (Fin.last M) :=
        fun _ => Fin.lastCases_castSucc _
      filter_upwards [hode] with u hu
      simpa [Fin.val_last, hGl, hGc] using hu)
    (fun i => by
      have hGs : (fun u => Fin.lastCases (g u) (G' u) i.castSucc.succ) =
          fun u => G' u i.succ := funext fun u =>
        (congrArg (Fin.lastCases (g u) (G' u))
          (Fin.ext rfl : i.castSucc.succ = i.succ.castSucc)).trans (Fin.lastCases_castSucc _)
      have hGc : ∀ u, Fin.lastCases (g u) (G' u) i.castSucc.castSucc = G' u i.castSucc :=
        fun _ => Fin.lastCases_castSucc _
      exact (hG'.eventually_deriv_succ i).mono fun u hu => by simpa [hGs, hGc] using hu)

end IsPolylogTowerGerm

private theorem exists_pos_radius_avoiding {N : ℕ} {w : ℂ} (hw0 : w ≠ 0)
    (hw1 : N ≠ 0 → w ≠ 1) : ∃ r > 0, 0 ∉ ball w r ∧ (N ≠ 0 → 1 ∉ ball w r) := by
  let r : ℝ := if N = 0 then ‖w‖ else min ‖w‖ ‖w - 1‖
  exact ⟨r, by by_cases hN : N = 0 <;> simp [r, hN, hw0, sub_ne_zero, hw1],
    by by_cases hN : N = 0 <;> simp [r, hN, dist_zero_left],
    fun hN => by simp [r, hN, dist_eq_norm, norm_sub_rev]⟩

private theorem exists_analyticOnNhd_ball_zero {w : ℂ} {r : ℝ} (h0 : 0 ∉ ball w r) (c₀ : ℂ)
    (hexp₀ : Complex.exp c₀ = w) : ∃ G : ℂ → Fin 1 → ℂ, AnalyticOnNhd ℂ G (ball w r) ∧
      G w = (fun _ => c₀) ∧ ∀ z ∈ ball w r, IsPolylogTowerGerm 0 G z := by
  obtain ⟨L, hLan, hLw, hLexp⟩ := analyticOnNhd_id.exists_eqOn_exp_comp_ball
    (fun z hz h => h0 (h ▸ hz)) hexp₀
  let G : ℂ → Fin 1 → ℂ := fun z _ => L z
  have hGan : AnalyticOnNhd ℂ G (ball w r) := fun z hz => AnalyticAt.pi fun _ => hLan z hz
  refine ⟨G, hGan, by ext i; simp [G, hLw], fun z hz =>
    ⟨hGan z hz, eventually_of_mem (isOpen_ball.mem_nhds hz) fun _ hu => hLexp hu, fun i => i.elim0⟩⟩

private theorem exists_analyticOnNhd_ball_succ {M : ℕ} {w : ℂ} {r : ℝ} (h0 : 0 ∉ ball w r)
    (h1 : 1 ∉ ball w r) {G' : ℂ → Fin (M + 1) → ℂ} (hG'an : AnalyticOnNhd ℂ G' (ball w r))
    (hG'tower : ∀ z ∈ ball w r, IsPolylogTowerGerm M G' z) (c : ℂ) :
    ∃ G : ℂ → Fin (M + 2) → ℂ, AnalyticOnNhd ℂ G (ball w r) ∧ G w = Fin.lastCases c (G' w) ∧
      ∀ z ∈ ball w r, IsPolylogTowerGerm (M + 1) G z := by
  let rhs : ℂ → ℂ := if M = 0 then fun z => (1 - z)⁻¹ else fun z => G' z (Fin.last M) / z
  have hrhs_an : AnalyticOnNhd ℂ rhs (ball w r) := fun z hz => by
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hz)
    have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr fun h => h1 (h.symm ▸ hz)
    by_cases hM : M = 0
    · have hinv : AnalyticAt ℂ (fun u => (1 - u)⁻¹) z :=
        (analyticAt_const.sub analyticAt_id).inv hz1; simpa [rhs, hM] using hinv
    · have hdiv : AnalyticAt ℂ (fun u => G' u (Fin.last M) / u) z :=
        (analyticAt_pi_iff.1 (hG'an z hz) (Fin.last M)).div analyticAt_id hz0
      simpa [rhs, hM] using hdiv
  obtain ⟨g, hgw, hgderiv⟩ := ((hrhs_an.differentiableOn).isExactOn_ball).with_val_at w c
  have hgan : AnalyticOnNhd ℂ g (ball w r) := DifferentiableOn.analyticOnNhd
    (fun z hz => (hgderiv z hz).differentiableAt.differentiableWithinAt) isOpen_ball
  have hGt : ∀ z ∈ ball w r, IsPolylogTowerGerm (M + 1) (fun u => Fin.lastCases (g u) (G' u)) z :=
    fun z hz => (hG'tower z hz).lastCases (hgan z hz) <|
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun u hu => by
        have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
        have hu1 : 1 - u ≠ 0 := sub_ne_zero.mpr fun h => h1 (h.symm ▸ hu)
        rw [(hgderiv u hu).deriv]
        by_cases hM : M = 0 <;> simp [hM, rhs, mul_inv_cancel₀ hu1, mul_div_cancel₀ _ hu0]
  exact ⟨fun z => Fin.lastCases (g z) (G' z), fun z hz => (hGt z hz).analyticAt,
    by ext i; refine Fin.lastCases (by simp [hgw]) (fun _ => by simp) i, hGt⟩

/-- Any `v : Fin (N + 1) → ℂ` with `exp (v 0) = w` extends to an analytic `IsPolylogTowerGerm N`
function `G` on any disc `ball w r` avoiding `0` (and `1` when `N ≠ 0`), satisfying `G w = v`. -/
theorem exists_analyticOnNhd_ball_of_exp_eq {N : ℕ} {w : ℂ} {r : ℝ}
    (v : Fin (N + 1) → ℂ) (hv0 : Complex.exp (v 0) = w)
    (h0 : 0 ∉ ball w r) (h1 : N ≠ 0 → 1 ∉ ball w r) :
    ∃ G : ℂ → Fin (N + 1) → ℂ, AnalyticOnNhd ℂ G (ball w r) ∧ G w = v ∧
      ∀ z ∈ ball w r, IsPolylogTowerGerm N G z := by
  rcases le_or_gt r 0 with hr | _
  · rw [Metric.ball_eq_empty.mpr hr]; exact ⟨fun _ => v, fun _ h => h.elim, rfl, fun _ h => h.elim⟩
  induction N with
  | zero =>
    obtain ⟨G, hGan, hGw, hGt⟩ := exists_analyticOnNhd_ball_zero h0 (v 0) hv0
    exact ⟨G, hGan, hGw.trans (by ext i; fin_cases i; rfl), hGt⟩
  | succ M ih =>
    obtain ⟨G', hG'an, hG'w, hG't⟩ := ih (fun j => v j.castSucc) hv0
      (fun _ => h1 (Nat.succ_ne_zero M))
    obtain ⟨G, hGan, hGw, hGt⟩ := exists_analyticOnNhd_ball_succ h0 (h1 (Nat.succ_ne_zero M))
      hG'an hG't (v (Fin.last (M + 1)))
    have hGw' : G w = v := hGw.trans <| funext <| Fin.lastCases Fin.lastCases_last fun j =>
      (Fin.lastCases_castSucc j).trans (congrFun hG'w j)
    exact ⟨G, hGan, hGw', hGt⟩

namespace IsPolylogTowerGerm

variable {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}

/-- Any `IsPolylogTowerGerm N F w` extends analytically as an `IsPolylogTowerGerm N` on any disc
`ball w r` avoiding `0` (and `1` when `N ≠ 0`), agreeing with `F` near `w`. -/
theorem exists_analyticOnNhd_ball (hF : IsPolylogTowerGerm N F w) {r : ℝ}
    (h0 : 0 ∉ ball w r) (h1 : N ≠ 0 → 1 ∉ ball w r) :
    ∃ G : ℂ → Fin (N + 1) → ℂ, AnalyticOnNhd ℂ G (ball w r) ∧ (G =ᶠ[𝓝 w] F) ∧
      ∀ z ∈ ball w r, IsPolylogTowerGerm N G z := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.mpr hr]; exact ⟨F, fun _ h => h.elim, .rfl, fun _ h => h.elim⟩
  obtain ⟨G, hGan, hGw, hGt⟩ := exists_analyticOnNhd_ball_of_exp_eq (F w) hF.exp_zero h0 h1
  exact ⟨G, hGan, ((hGt w (mem_ball_self hr)).eventuallyEq_iff_eq hF).mpr hGw, hGt⟩

/-- Any `IsPolylogTowerGerm N F (c 0)` analytically continues along any continuous path
`c : I → ℂ` avoiding `0` (and `1` when `N ≠ 0`). -/
theorem continuesAlong {c : I → ℂ} (hF : IsPolylogTowerGerm N F (c 0)) (hc : Continuous c)
    (hc0 : ∀ t, c t ≠ 0) (hc1 : N ≠ 0 → ∀ t, c t ≠ 1) : ContinuesAlong F c := by
  let S : Set I := {b | ∃ f : I → ℂ → Fin (N + 1) → ℂ,
    IsAnalyticContinuationAlong f c (Iic b) ∧ f 0 =ᶠ[𝓝 (c 0)] F}
  have h0S : (0 : I) ∈ S := ⟨fun _ => F, .const hc.continuousOn fun t ht =>
    (Subtype.ext (le_antisymm (Subtype.coe_le_coe.mpr (mem_Iic.mp ht)) t.property.left)) ▸
      hF.analyticAt, .rfl⟩
  let b₀ : I := sSup S
  obtain ⟨r, hr, h0_b₀, h1_b₀⟩ := exists_pos_radius_avoiding (hc0 b₀) (fun hN => hc1 hN b₀)
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
        (by rw [coe_projIcc]; exact max_le (by linarith [b₀.property.left]) (min_le_right _ _))
      exact ⟨by linarith [Subtype.coe_le_coe.mpr ht.1], by linarith⟩
    linarith [dist_triangle (c t) (c b₀) (c t₁), hδc ht_dist, dist_comm (c t₁) (c b₀)]
  have hf_ext := hf₁.extend_Iic (.const hc.continuousOn hGan_Icc) hGeq.symm
  have hf_ext0 : (if (0 : I) ≤ t₁ then f₁ 0 else G) =ᶠ[𝓝 (c 0)] F := by simpa [bot_le] using hf₁0
  have ht₂_one : t₂ = 1 := Subtype.ext <| by
    have hle := Subtype.coe_le_coe.mpr (le_csSup (OrderTop.bddAbove S) ⟨_, hf_ext, hf_ext0⟩)
    rw [coe_projIcc, max_eq_right (le_min zero_le_one (by linarith [b₀.property.left]))] at hle ⊢
    by_contra hne; rw [min_eq_right (le_of_not_ge fun h => hne (min_eq_left h))] at hle; linarith
  exact continuesAlong_iff_exists.mpr
    ⟨_, hf_ext.mono fun t _ => ht₂_one ▸ mem_Iic.mpr (Subtype.coe_le_coe.mp t.property.right),
      hf_ext0⟩

/-- Any `IsPolylogTowerGerm N F w` continues inside `{z : ℂ | z ≠ 0 ∧ z ≠ 1}`. -/
theorem continuesInside (hF : IsPolylogTowerGerm N F w) :
    ContinuesInside F {z : ℂ | z ≠ 0 ∧ z ≠ 1} w :=
  ContinuesInside.of_forall fun _ hc hcU hc0 =>
    (hc0 ▸ hF).continuesAlong hc (fun t => (hcU t).1) (fun _ t => (hcU t).2)

/-- At height `0` (`Log z` alone), `F` continues inside `{z : ℂ | z ≠ 0}`. -/
theorem continuesInside_zero {F : ℂ → Fin 1 → ℂ} (hF : IsPolylogTowerGerm 0 F w) :
    ContinuesInside F {z : ℂ | z ≠ 0} w :=
  ContinuesInside.of_forall fun _ hc hcU hc0 =>
    (hc0 ▸ hF).continuesAlong hc hcU (fun h => absurd rfl h)

/-- Composing `H.universalCoverBranch` with any local continuous section `sec` near `u`
satisfies `IsPolylogTowerGerm N (H.universalCoverBranch ∘ sec) u`. -/
theorem universalCoverBranch_comp_of_continuousAt {U : Set ℂ} {z₀ : U}
    (hF : IsPolylogTowerGerm N F (z₀ : ℂ)) (H : ContinuesInside F U (z₀ : ℂ))
    {sec : ℂ → UniversalCover z₀} {u : ℂ} (hsec : ContinuousAt sec u)
    (hproj : (fun z => ((sec z).proj : ℂ)) =ᶠ[𝓝 u] id) :
    IsPolylogTowerGerm N (H.universalCoverBranch ∘ sec) u := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (sec u).path
  obtain ⟨f, hf, hf0, -⟩ := H.exists_isAnalyticContinuationAlong_universalCoverBranch γ
  have hgu : (γ 1 : ℂ) = u := (congrArg Subtype.val γ.target).trans hproj.self_of_nhds
  exact (hgu ▸ of_isAnalyticContinuationAlong isPreconnected_univ (mem_univ 0) (mem_univ 1) hf
    (by simpa [γ.source] using hf0) (by simpa [γ.source] using hF)).congr
      (H.eventuallyEq_universalCoverBranch_comp_of_continuousAt hsec hproj hγ hf hf0).symm

end IsPolylogTowerGerm

/-- Given `v : Fin (N + 1) → ℂ` with `exp (v 0) = w` (and `w ≠ 1` if `N ≠ 0`), there exists
an `IsPolylogTowerGerm N F w` with initial value `F w = v`. -/
theorem exists_isPolylogTowerGerm {N : ℕ} {w : ℂ} (v : Fin (N + 1) → ℂ)
    (hv0 : Complex.exp (v 0) = w) (hw1 : N ≠ 0 → w ≠ 1) :
    ∃ F : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N F w ∧ F w = v := by
  obtain ⟨r, hr, h0, h1⟩ := exists_pos_radius_avoiding (hv0 ▸ Complex.exp_ne_zero (v 0)) hw1
  obtain ⟨G, -, hGw, hGt⟩ := exists_analyticOnNhd_ball_of_exp_eq v hv0 h0 h1
  exact ⟨G, hGt w (mem_ball_self hr), hGw⟩

/-- **The principal polylogarithm tower `polylogTower N` satisfies `IsPolylogTowerGerm N`** at
every `w ∈ Complex.slitPlane` with `N ≠ 0 → 1 - w ∈ Complex.slitPlane`. -/
theorem isPolylogTowerGerm_polylogTower (N : ℕ) {w : ℂ} (hw0 : w ∈ Complex.slitPlane)
    (hw1 : N ≠ 0 → 1 - w ∈ Complex.slitPlane) : IsPolylogTowerGerm N (polylogTower N) w where
  analyticAt := AnalyticAt.pi fun i => by
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.ext hi; subst hi0; simpa [polylogTower] using analyticAt_id.clog hw0
    · rw [funext fun z => polylogTower_apply_of_ne_zero z hi]
      exact analyticAt_polylog (i : ℕ) (hw1 (by omega))
  eventually_exp_zero := (eventually_ne_nhds (Complex.slitPlane_ne_zero hw0)).mono fun _ hz => by
    simp [Complex.exp_log hz]
  eventually_deriv_succ i := by
    rw [funext fun u => polylogTower_succ N u i]
    filter_upwards [Complex.isOpen_setOf_one_sub_mem_slitPlane.mem_nhds
      (hw1 (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)))] with z hz
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, ↓reduceIte, Fin.val_succ, zero_add, Nat.cast_one,
        (hasDerivAt_polylog_one hz).deriv, mul_inv_cancel₀ (Complex.slitPlane_ne_zero hz)]
    · simp only [hi, ↓reduceIte, Fin.val_succ, Nat.cast_add, Nat.cast_one,
        mul_deriv_polylog_add_one (i : ℕ) hz]
      exact (polylogTower_apply_of_ne_zero z (i := i.castSucc) (by simpa using hi)).symm

/-- `polylogTower N` is complex analytic on `{z | z ∈ slitPlane ∧ (N ≠ 0 → 1 - z ∈ slitPlane)}`. -/
theorem analyticOnNhd_polylogTower (N : ℕ) : AnalyticOnNhd ℂ (polylogTower N)
    {z : ℂ | z ∈ Complex.slitPlane ∧ (N ≠ 0 → 1 - z ∈ Complex.slitPlane)} :=
  fun _ hz => (isPolylogTowerGerm_polylogTower N hz.1 hz.2).analyticAt

end TauCeti.Polylog
