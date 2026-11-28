/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Edges
public import TauCeti.NumberTheory.LFunctions.Continued.PoleCleared
import Mathlib.Analysis.Analytic.Polynomial
import TauCeti.Analysis.Complex.PhragmenLindelof.Polynomial
import TauCeti.Analysis.Polynomial.AtInfinity

/-!
# The convexity bound for continued L-functions

For an analytic L-function record `d` of degree `n` with conductor `N`, continued function
`L = d.continuedL` and analytic conductor `𝔮 = d.analyticConductorAt`, fix `δ > 0`. On the two
edges of the strip `-δ ≤ Re s ≤ 1 + δ` the continued function satisfies `‖L(s)‖ ≤ S` on the right
and `‖L(s)‖ ≤ C S 𝔮(s) ^ (1/2 + δ)` on the left, where `S = ∑ ‖a(k)‖ k ^ (-(1 + δ))`
(`TauCeti/NumberTheory/LFunctions/Continued/Edges.lean`). Interpolating these by the
Phragmén–Lindelöf principle gives the **convexity bound**
$$\|L(s)\| \le C\, S\, \mathfrak q(s)^{(1/2 + \delta)(1 + \delta - \sigma)/(1 + 2\delta)},
  \qquad \sigma = \operatorname{Re} s \in [-\delta, 1 + \delta].$$

Phragmén–Lindelöf needs a function holomorphic on the closed strip, so the bound is proved for
the pole-cleared function `d.poleClearedContinuedL P`, the removable extension of `P · L`, for a
polynomial `P` whose roots clear the poles of `L` in the strip; the bound then carries the extra
factor `(1 + |Im s|) ^ deg P` (`exists_norm_poleClearedContinuedL_le_analyticConductorAt_rpow`).
The constant `C` depends only on `δ`, the degree, a bound for the gamma shifts, a margin keeping
the reflected shifts in the right half-plane, and `P`. It does not depend on the arithmetic
conductor: the conductor powers `N ^ (1/2 + δ)` and `N ^ 0` of the two edges are interpolated
together with the archimedean factors, and the result is reassembled into a power of `𝔮` by the
two-sided comparison `𝔮(s) ≍ N (|Im s| + 3) ^ n` on the strip.

When `L` has no pole in the strip, `P = 1` bounds `L` itself
(`exists_norm_continuedL_le_analyticConductorAt_rpow`). On the critical line the exponent is
`1/4 + δ/2`, the convexity bound `L(1/2 + it) ≪ 𝔮(1/2 + it) ^ (1/4 + δ/2)`
(`exists_norm_continuedL_one_half_add_mul_I_le_analyticConductorAt_rpow`).

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.2.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (1986), §5.1.
-/

public section

open Complex Set Polynomial

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- On `|Re s| ≤ B`, a polynomial of degree `m` is at most `K (3 + |Im s|) ^ m`. -/
private theorem exists_norm_eval_le_mul_three_add_abs_im_rpow (P : ℂ[X]) (B : ℝ) :
    ∃ K, 0 < K ∧ ∀ s : ℂ, |s.re| ≤ B →
      ‖P.eval s‖ ≤ K * (3 + |s.im|) ^ (P.natDegree : ℝ) := by
  obtain ⟨K, hK, hP⟩ := Polynomial.exists_norm_eval_le_mul_one_add_norm_eval (A := P)
    (Q := X ^ P.natDegree) (by rw [degree_X_pow]; exact degree_le_natDegree)
  refine ⟨(K + 1) * (1 + (|B| + 1) ^ P.natDegree), by positivity, fun s hs ↦ ?_⟩
  have ht : 1 ≤ 3 + |s.im| := by linarith [abs_nonneg s.im]
  have hs' : ‖s‖ ≤ (|B| + 1) * (3 + |s.im|) := by
    nlinarith [norm_le_abs_re_add_abs_im s, abs_nonneg s.im, le_abs_self B, abs_nonneg B]
  rw [Real.rpow_natCast]
  calc ‖P.eval s‖ ≤ K * (1 + ‖s‖ ^ P.natDegree) := by simpa using hP s
    _ ≤ (K + 1) * ((3 + |s.im|) ^ P.natDegree + ((|B| + 1) * (3 + |s.im|)) ^ P.natDegree) := by
        gcongr
        · linarith
        · exact one_le_pow₀ ht
    _ = (K + 1) * (1 + (|B| + 1) ^ P.natDegree) * (3 + |s.im|) ^ P.natDegree := by
        rw [mul_pow]; ring

variable {d : AnalyticLFunctionData} {P : ℂ[X]}

/-- If `P` clears every pole of the continued function on the closed strip `a ≤ Re s ≤ b`, the
pole-cleared function is holomorphic on the open strip and continuous on its closure. -/
private theorem diffContOnCl_poleClearedContinuedL {a b : ℝ}
    (hclear : ∀ s : ℂ, s.re ∈ Icc a b →
      0 ≤ meromorphicOrderAt d.continuedL s + (P.rootMultiplicity s : ℕ)) :
    DiffContOnCl ℂ (d.poleClearedContinuedL P) (re ⁻¹' Ioo a b) := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [poleClearedContinuedL_zero]
    exact diffContOnCl_const
  rcases lt_or_ge a b with hab | hab
  · refine DifferentiableOn.diffContOnCl fun s hs ↦ ?_
    rw [closure_preimage_re, closure_Ioo hab.ne] at hs
    exact (analyticAt_poleClearedContinuedL ((meromorphicOrderAt_poleClearedContinuedL hP s).symm ▸
      hclear s hs)).differentiableAt.differentiableWithinAt
  · rw [Ioo_eq_empty (not_lt.mpr hab), preimage_empty]
    exact DifferentiableOn.diffContOnCl (by rw [closure_empty]; exact differentiableOn_empty)

/-- The right edge for the pole-cleared function: on `Re w = 1 + δ`, it is `P · L`, bounded by
`K S (3 + |Im w|) ^ deg P`. -/
private theorem norm_poleClearedContinuedL_right_le (hD : d.HasDirichletAgreement) {δ K : ℝ}
    (hδ : 0 < δ)
    (hP : ∀ s : ℂ, |s.re| ≤ 1 + δ → ‖P.eval s‖ ≤ K * (3 + |s.im|) ^ (P.natDegree : ℝ))
    {w : ℂ} (hw : w.re = 1 + δ) :
    ‖d.poleClearedContinuedL P w‖ ≤ K * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
      (3 + |w.im|) ^ (P.natDegree : ℝ) := by
  have hL := hD.analyticAt_continuedL (s := w) (by linarith)
  rw [poleClearedContinuedL_eq_of_analyticAt
    ((AnalyticOnNhd.eval_polynomial P w trivial).mul hL), norm_mul]
  have h1 := hP w (by rw [hw, abs_of_pos (by linarith)])
  have h2 := hD.norm_continuedL_le (σ := 1 + δ) (by linarith) hw.ge
  calc _ ≤ K * (3 + |w.im|) ^ (P.natDegree : ℝ) *
        ∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖ :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = _ := by ring

/-- The left edge for the pole-cleared function: on `Re w = -δ`, it is `P · L`, and the edge
bound `‖L(w)‖ ≤ C S 𝔮(w) ^ (1/2 + δ)` with `𝔮(w) ≤ c N (|Im w| + 3) ^ n` gives
`K S C (c N) ^ (1/2 + δ) (3 + |Im w|) ^ (deg P + n (1/2 + δ))`. -/
private theorem norm_poleClearedContinuedL_left_le (hD : d.HasDirichletAgreement)
    (hfe : d.HasFunctionalEquation) {δ K C c : ℝ} (hδ : 0 < δ)
    (hR : ∀ μ ∈ d.gammaR, 0 < 1 + δ + μ.re) (hC : ∀ ν ∈ d.gammaC, 0 < 1 + δ + ν.re)
    (hP : ∀ s : ℂ, |s.re| ≤ 1 + δ → ‖P.eval s‖ ≤ K * (3 + |s.im|) ^ (P.natDegree : ℝ))
    {w : ℂ} (hw : w.re = -δ)
    (hL : ‖d.continuedL w‖ ≤ C * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
      d.analyticConductorAt w ^ (1 / 2 + δ))
    (hq : d.analyticConductorAt w ≤ c * (d.conductor : ℝ) * (|w.im| + 3) ^ d.degree) :
    ‖d.poleClearedContinuedL P w‖ ≤
      K * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
        (C * (c * (d.conductor : ℝ)) ^ (1 / 2 + δ)) *
        (3 + |w.im|) ^ ((P.natDegree : ℝ) + d.degree * (1 / 2 + δ)) := by
  have ha : AnalyticAt ℂ d.continuedL w :=
    hfe.analyticAt_continuedL
      (d.dual_gammaFactor_one_sub_ne_zero (fun μ hμ ↦ by linarith [hR μ hμ])
        (fun ν hν ↦ by linarith [hC ν hν]))
      (hD.dual.analyticAt_continuedL (by simp only [sub_re, one_re, hw]; linarith))
  rw [poleClearedContinuedL_eq_of_analyticAt
    ((AnalyticOnNhd.eval_polynomial P w trivial).mul ha), norm_mul]
  set S := ∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖
  have h3 : 0 < 3 + |w.im| := by positivity
  have hq0 : 0 ≤ d.analyticConductorAt w := (d.analyticConductorAt_pos w).le
  have hC0 : 0 ≤ C * S := by
    by_contra h
    have := (norm_nonneg _).trans hL
    exact h (nonneg_of_mul_nonneg_left this
      (Real.rpow_pos_of_pos (d.analyticConductorAt_pos w) _))
  have hc0 : 0 ≤ c * (d.conductor : ℝ) * (|w.im| + 3) ^ d.degree := hq0.trans hq
  have hpow : d.analyticConductorAt w ^ (1 / 2 + δ) ≤
      (c * (d.conductor : ℝ)) ^ (1 / 2 + δ) * (3 + |w.im|) ^ (d.degree * (1 / 2 + δ)) := by
    have hc0' : 0 ≤ c * (d.conductor : ℝ) := by
      by_contra h
      exact h (nonneg_of_mul_nonneg_left hc0 (by positivity))
    calc d.analyticConductorAt w ^ (1 / 2 + δ)
        ≤ (c * (d.conductor : ℝ) * (|w.im| + 3) ^ d.degree) ^ (1 / 2 + δ) :=
          Real.rpow_le_rpow hq0 hq (by linarith)
      _ = _ := by
          rw [Real.mul_rpow hc0' (by positivity), add_comm |w.im|, ← Real.rpow_natCast,
            ← Real.rpow_mul h3.le]
  have h1 := hP w (by rw [hw, abs_neg, abs_of_pos hδ]; linarith)
  calc ‖P.eval w‖ * ‖d.continuedL w‖
      ≤ K * (3 + |w.im|) ^ (P.natDegree : ℝ) * (C * S * ((c * (d.conductor : ℝ)) ^ (1 / 2 + δ) *
          (3 + |w.im|) ^ (d.degree * (1 / 2 + δ)))) :=
        mul_le_mul h1 (hL.trans (mul_le_mul_of_nonneg_left hpow hC0)) (norm_nonneg _)
          ((norm_nonneg _).trans h1)
    _ = _ := by rw [Real.rpow_add h3]; ring

/-- The Phragmén–Lindelöf output reassembled: with `Y = C (c₂ N) ^ (1/2 + δ)`, the interpolation
`(A Y) ^ (1 - θ) A ^ θ (3 + u) ^ ((1 - θ) (m + n (1/2 + δ)) + θ m)` of the two edge bounds is at
most a constant times `A (1 + u) ^ m 𝔮 ^ ((1/2 + δ) (1 - θ))` once `c₁ N (u + 3) ^ n ≤ 𝔮`. -/
private theorem interp_le {A C c₁ c₂ N 𝔮 u θ δ : ℝ} (m n : ℕ) (hA : 0 ≤ A) (hC : 0 < C)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hN : 0 < N) (hu : 0 ≤ u) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hδ : 0 < δ) (h𝔮 : c₁ * N * (u + 3) ^ n ≤ 𝔮) :
    (A * (C * (c₂ * N) ^ (1 / 2 + δ))) ^ (1 - θ) * A ^ θ *
        (3 + u) ^ ((1 - θ) * ((m : ℝ) + n * (1 / 2 + δ)) + θ * m) ≤
      A * (max C 1 * max (c₂ / c₁) 1 ^ (1 / 2 + δ) * 3 ^ m) * (1 + u) ^ m *
        𝔮 ^ ((1 / 2 + δ) * (1 - θ)) := by
  set e := (1 / 2 + δ) * (1 - θ)
  have he₁ : e ≤ 1 / 2 + δ := mul_le_of_le_one_right (by linarith) (by linarith)
  have h3 : 0 < 3 + u := by linarith
  have hY : 0 < C * (c₂ * N) ^ (1 / 2 + δ) := by positivity
  have hAY : (A * (C * (c₂ * N) ^ (1 / 2 + δ))) ^ (1 - θ) * A ^ θ =
      A * C ^ (1 - θ) * (c₂ * N) ^ e := by
    rw [Real.mul_rpow hA hY.le, Real.mul_rpow hC.le (by positivity),
      ← Real.rpow_mul (by positivity), mul_right_comm, ← Real.rpow_add' hA (by simp),
      sub_add_cancel, Real.rpow_one]
    ring
  have hT : (3 + u) ^ ((1 - θ) * ((m : ℝ) + n * (1 / 2 + δ)) + θ * m) =
      (3 + u) ^ m * ((3 + u) ^ n) ^ e := by
    rw [show (1 - θ) * ((m : ℝ) + n * (1 / 2 + δ)) + θ * m = m + n * e by ring,
      Real.rpow_add h3, Real.rpow_natCast, ← Real.rpow_natCast (3 + u) n, ← Real.rpow_mul h3.le]
  have hq : (c₂ * N) ^ e * ((3 + u) ^ n) ^ e ≤ max (c₂ / c₁) 1 ^ (1 / 2 + δ) * 𝔮 ^ e := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    calc (c₂ * N * (3 + u) ^ n) ^ e = ((c₂ / c₁) * (c₁ * N * (u + 3) ^ n)) ^ e := by
          congr 1; field_simp; ring
      _ ≤ (max (c₂ / c₁) 1 * 𝔮) ^ e := by gcongr; exact le_max_left _ _
      _ = max (c₂ / c₁) 1 ^ e * 𝔮 ^ e :=
          Real.mul_rpow (by positivity) ((by positivity : (0 : ℝ) ≤ _).trans h𝔮)
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) he₁)
          (Real.rpow_nonneg ((by positivity : (0 : ℝ) ≤ _).trans h𝔮) _)
  have hCθ : C ^ (1 - θ) ≤ max C 1 :=
    (Real.rpow_le_rpow hC.le (le_max_left C 1) (by linarith)).trans
      (Real.rpow_le_self_of_one_le (le_max_right C 1) (by linarith))
  have h3u : (3 + u) ^ m ≤ 3 ^ m * (1 + u) ^ m := by
    rw [← mul_pow]; gcongr; linarith
  rw [hAY, hT]
  calc A * C ^ (1 - θ) * (c₂ * N) ^ e * ((3 + u) ^ m * ((3 + u) ^ n) ^ e)
      = A * C ^ (1 - θ) * (3 + u) ^ m * ((c₂ * N) ^ e * ((3 + u) ^ n) ^ e) := by ring
    _ ≤ A * max C 1 * (3 ^ m * (1 + u) ^ m) * (max (c₂ / c₁) 1 ^ (1 / 2 + δ) * 𝔮 ^ e) := by
        gcongr
    _ = _ := by ring

/-- **The convexity bound for pole-cleared continued functions, uniformly in the conductor.**
Fix `δ > 0`, a degree `n`, a bound `M` for the gamma shifts, a margin `ε > 0` keeping the
reflected shifts in the right half-plane (`ε ≤ 1 + δ + Re μ`) and a polynomial `P`. There is
`C > 0` such that for every record `d` with these data, Dirichlet agreement, a functional
equation and finite order, in which `P` clears the poles of `L = d.continuedL` on the closed strip
`-δ ≤ Re s ≤ 1 + δ`, the pole-cleared function satisfies, for `σ = Re s` in that strip,
`‖(P L)(s)‖ ≤ C S (1 + |Im s|) ^ deg P 𝔮(s) ^ ((1/2 + δ) (1 + δ - σ) / (1 + 2 δ))`,
where `S = ∑ ‖a(k)‖ k ^ (-(1 + δ))` and `𝔮 = d.analyticConductorAt`. The constant `C` does not
depend on the conductor or on the record. -/
theorem exists_norm_poleClearedContinuedL_le_analyticConductorAt_rpow {δ : ℝ} (hδ : 0 < δ)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (M : ℝ) (P : ℂ[X]) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 + δ + ν.re) →
      d.HasDirichletAgreement → d.HasFunctionalEquation → d.IsFiniteOrder →
      (∀ s : ℂ, s.re ∈ Icc (-δ) (1 + δ) →
        0 ≤ meromorphicOrderAt d.continuedL s + (P.rootMultiplicity s : ℕ)) →
      ∀ s : ℂ, s.re ∈ Icc (-δ) (1 + δ) →
        ‖d.poleClearedContinuedL P s‖ ≤ C * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
          (1 + |s.im|) ^ P.natDegree *
          d.analyticConductorAt s ^ ((1 / 2 + δ) * (1 + δ - s.re) / (1 + 2 * δ)) := by
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_norm_continuedL_neg_line_le_analyticConductorAt_rpow hδ hε n M
  obtain ⟨c₁, hc₁, c₂, hc₂, hcond⟩ :=
    exists_analyticConductorAt_strip_bounds (-δ) (1 + δ) n (le_max_right M 0)
  obtain ⟨K, hK, hP⟩ := exists_norm_eval_le_mul_three_add_abs_im_rpow P (1 + δ)
  set p : ℝ := P.natDegree + n * (1 / 2 + δ)
  set q : ℝ := (P.natDegree : ℝ)
  have hpref : 0 < ((1 + δ - -δ) / 3 + 2) ^ (2 * max |p| |q|) :=
    Real.rpow_pos_of_pos (by linarith) _
  refine ⟨((1 + δ - -δ) / 3 + 2) ^ (2 * max |p| |q|) * K *
    (max CL 1 * max (c₂ / c₁) 1 ^ (1 / 2 + δ) * 3 ^ P.natDegree), by positivity, ?_⟩
  intro d hd hR hC hD hfe hfin hclear s hs
  set S := ∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖
  have hS : 0 ≤ S := tsum_nonneg fun _ ↦ norm_nonneg _
  subst hd
  have hM : ∀ μ ∈ d.gammaR, ‖μ‖ ≤ max M 0 := fun μ hμ ↦ (hR μ hμ).1.trans (le_max_left _ _)
  have hM' : ∀ ν ∈ d.gammaC, ‖ν‖ ≤ max M 0 := fun ν hν ↦ (hC ν hν).1.trans (le_max_left _ _)
  have hN : (0 : ℝ) < d.conductor := Nat.cast_pos.mpr d.conductor.pos
  have hPL := TauCeti.PhragmenLindelof.norm_le_mul_rpow_interp_of_isFiniteOrder (p := p)
    (q := q) (C₁ := K * S * (CL * (c₂ * (d.conductor : ℝ)) ^ (1 / 2 + δ))) (C₂ := K * S)
    three_pos (diffContOnCl_poleClearedContinuedL hclear)
    (isFiniteOrder_poleClearedContinuedL (P := P) hfin)
    (fun w hw ↦ norm_poleClearedContinuedL_left_le hD hfe hδ
      (fun μ hμ ↦ hε.trans_le (hR μ hμ).2) (fun ν hν ↦ hε.trans_le (hC ν hν).2) hP hw
      (hleft d rfl hR hC hD hfe w hw)
      (hcond d rfl hM hM' w (by rw [hw]; constructor <;> linarith)).2)
    (fun w hw ↦ norm_poleClearedContinuedL_right_le hD hδ hP hw) hs
  have hθ : (s.re - -δ) / (1 + δ - -δ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1]) (by linarith)
    · rw [div_le_one (by linarith)]; linarith [hs.2]
  have hint := interp_le P.natDegree d.degree (mul_nonneg hK.le hS) hCL hc₁ hc₂ hN
    (abs_nonneg s.im) hθ.1 hθ.2 hδ
    (hcond d rfl hM hM' s hs).1
  refine hPL.trans ?_
  rw [mul_assoc (_ * _), mul_assoc]
  refine (mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hint)
    (by positivity)).trans_eq ?_
  have h2δ : (1 + 2 * δ) ≠ 0 := by positivity
  rw [show (1 / 2 + δ) * (1 - (s.re - -δ) / (1 + δ - -δ)) =
    (1 / 2 + δ) * (1 + δ - s.re) / (1 + 2 * δ) by
      rw [show 1 + δ - -δ = 1 + 2 * δ by ring]; field_simp; ring]
  ring

/-- **The convexity bound for pole-free continued functions, uniformly in the conductor.** Fix
`δ > 0`, a degree `n`, a bound `M` for the gamma shifts and a margin `ε > 0` keeping the
reflected shifts in the right half-plane. There is `C > 0` such that for every record `d` with
these data, Dirichlet agreement, a functional equation and finite order, whose continued function
`L` is analytic on the closed strip `-δ ≤ Re s ≤ 1 + δ`,
`‖L(s)‖ ≤ C S 𝔮(s) ^ ((1/2 + δ) (1 + δ - Re s) / (1 + 2 δ))` on that strip, where
`S = ∑ ‖a(k)‖ k ^ (-(1 + δ))` and `𝔮 = d.analyticConductorAt`. -/
theorem exists_norm_continuedL_le_analyticConductorAt_rpow {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) (M : ℝ) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 + δ + ν.re) →
      d.HasDirichletAgreement → d.HasFunctionalEquation → d.IsFiniteOrder →
      (∀ s : ℂ, s.re ∈ Icc (-δ) (1 + δ) → AnalyticAt ℂ d.continuedL s) →
      ∀ s : ℂ, s.re ∈ Icc (-δ) (1 + δ) →
        ‖d.continuedL s‖ ≤ C * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
          d.analyticConductorAt s ^ ((1 / 2 + δ) * (1 + δ - s.re) / (1 + 2 * δ)) := by
  obtain ⟨C, hC, h⟩ := exists_norm_poleClearedContinuedL_le_analyticConductorAt_rpow hδ hε n M 1
  refine ⟨C, hC, fun d hd hR hC' hD hfe hfin ha s hs ↦ ?_⟩
  simpa using h d hd hR hC' hD hfe hfin (fun z hz ↦ by
    rw [rootMultiplicity_eq_zero (by simp)]
    simpa using (ha z hz).meromorphicOrderAt_nonneg) s hs

/-- **Convexity on the critical line, uniformly in the conductor.** Under the hypotheses of
`exists_norm_continuedL_le_analyticConductorAt_rpow`, the continued function satisfies
`‖L(1/2 + it)‖ ≤ C S 𝔮(1/2 + it) ^ (1/4 + δ/2)` for every real `t`. -/
theorem exists_norm_continuedL_one_half_add_mul_I_le_analyticConductorAt_rpow {δ : ℝ}
    (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) (M : ℝ) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 + δ + ν.re) →
      d.HasDirichletAgreement → d.HasFunctionalEquation → d.IsFiniteOrder →
      (∀ s : ℂ, s.re ∈ Icc (-δ) (1 + δ) → AnalyticAt ℂ d.continuedL s) →
      ∀ t : ℝ, ‖d.continuedL (1 / 2 + t * I)‖ ≤
        C * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
          d.analyticConductorAt (1 / 2 + t * I) ^ (1 / 4 + δ / 2) := by
  obtain ⟨C, hC, h⟩ := exists_norm_continuedL_le_analyticConductorAt_rpow hδ hε n M
  refine ⟨C, hC, fun d hd hR hC' hD hfe hfin ha t ↦ ?_⟩
  have hre : (1 / 2 + t * I).re = 1 / 2 := by simp
  convert h d hd hR hC' hD hfe hfin ha (1 / 2 + t * I)
    (by rw [hre]; constructor <;> linarith) using 3
  rw [hre]
  field_simp
  ring

end TauCeti.LFunctions.AnalyticLFunctionData
