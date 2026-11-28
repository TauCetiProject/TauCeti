/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Convolution.Young
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Function.Lp.Dilation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The Oseen kernel

On a finite-dimensional real inner product space `E` of dimension `d`, the operator
`e^{tΔ} ℙ div`, the heat evolution of the Leray projection of the divergence of a matrix field
`F : E → E →L[ℝ] E` (divergence in the second index), is convolution with the **Oseen kernel**
`O_t`. Since `e^{tΔ} ℙ` has the matrix kernel `K_t 1 + ∫_t^∞ ∇²K_s ds`, with symbol
`e^{-4π²t‖ξ‖²}(1 - ξ ⊗ ξ/‖ξ‖²)`, and `K_s` is the explicit Gaussian heat kernel, `O_t(x)` is an
explicit linear map of the matrix `A = F(y)` built from `K_t(x)` and the two time integrals
`∫_t^∞ K_s(x)/s² ds` and `∫_t^∞ K_s(x)/s³ ds`. This file defines `O_t`, checks it against the
two cases where `e^{tΔ} ℙ div` vanishes, and proves the decay and integrability estimates that
make `e^{tΔ} ℙ div` bounded from `Lᵖ` to `L^q` for all `1 ≤ p ≤ q ≤ ∞`, including the endpoints
where `ℙ` alone is unbounded. These estimates drive the bilinear estimates for mild solutions of
the Navier–Stokes equations.

## Main declarations

* `TauCeti.oseenKernel`, `TauCeti.oseenKernel_apply`: the kernel and its defining formula.
* `TauCeti.oseenKernel_apply_id`: `O_t` annihilates the identity matrix, since `div (φ 1) = ∇φ`
  and `ℙ` kills gradients; `TauCeti.oseenKernel_eq_zero_of_finrank_eq_one`: on the line, where
  `ℙ = 0`, the kernel vanishes.
* `TauCeti.oseenKernel_eq_smul_oseenKernel_one`: parabolic scaling,
  `O_t(x) = t^(-(d+1)/2) O_1(x/√t)`.
* `TauCeti.exists_norm_oseenKernel_le`: `‖O_t(x)‖ ≤ C(d) (‖x‖ + √t)^(-(d + 1))`.
* `TauCeti.exists_eLpNorm_oseenKernel_le`: `‖O_t‖_r ≤ C(d) t^(-1/2 - (d/2)(1 - 1/r))` for
  `1 ≤ r ≤ ∞`; at `r = 1` this is the integrability `‖O_t‖₁ ≤ C(d) t^(-1/2)`.
* `TauCeti.exists_eLpNorm_oseenKernel_convolution_le`: the `Lᵖ`–`L^q` estimate
  `‖O_t ⋆ F‖_q ≤ C(d) t^(-1/2 - (d/2)(1/p - 1/q)) ‖F‖_p`.

## Implementation notes

Writing `K_s(x)/s^n = (4π)^(-d/2) s^(-α-1) exp(-‖x‖²/(4s))` with `α = n + d/2 - 1`, the time
integrals are bounded both by `∫_t^∞ s^(-n) ds` and, after the substitution `s = 1/σ`, by
`Γ(α) (‖x‖²/4)^(-α)`; together these give the decay `(‖x‖ + √t)^(-(d + 1))`. The heat equation
`∂ₛK_s = ΔK_s` gives the identity relating the two time integrals to `K_t(x)/(2t)`, which is
both the cancellation in `TauCeti.oseenKernel_apply_id` and the bound of the heat term by the
time integrals.

## References

* W. S. Ozanski, B. C. Pooley, *Leray's fundamental work on the Navier–Stokes equations: a modern
  review of Sur le mouvement d'un liquide visqueux emplissant l'espace*, arXiv:1708.09787,
  (1.13)–(1.14), for `d = 3`.
* C. Wang, *Introduction of the Navier–Stokes equations*, lecture notes, Beijing Normal
  University, 2013, Lemma 6.10, for every `d`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real Set Filter Topology
open scoped RealInnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section TimeIntegral

/-- Gaussian domination of the integrand: for `0 < t ≤ s`,
`|K_s(x) / s ^ n| ≤ (4πt)^(-d/2) s^(-n)`. -/
private theorem norm_heatKernel_div_pow_le {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (n : ℕ)
    (x : E) :
    ‖heatKernel s x / s ^ n‖ ≤ (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * s ^ (-(n : ℝ)) := by
  have hs : 0 < s := ht.trans_le hts
  rw [Real.norm_of_nonneg (div_nonneg (heatKernel_pos hs x).le (pow_nonneg hs.le _)),
    rpow_neg hs.le, rpow_natCast, ← div_eq_mul_inv]
  gcongr
  refine (heatKernel_le hs x).trans ?_
  exact rpow_le_rpow_of_nonpos (by positivity) (by gcongr)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (Nat.cast_nonneg _)) zero_le_two)

private theorem integral_heatKernel_div_pow_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (x : E) :
    0 ≤ ∫ s in Ioi t, heatKernel s x / s ^ n :=
  setIntegral_nonneg measurableSet_Ioi fun _ hs =>
    div_nonneg (heatKernel_pos (ht.trans_lt hs) x).le (pow_nonneg (ht.trans_lt hs).le _)

/-- The dominating function `(4πt)^(-d/2) s^(-n)` is integrable on `(t, ∞)` for `n ≥ 2`. -/
private theorem integrableOn_heatKernel_bound {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun s : ℝ =>
      (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * s ^ (-(n : ℝ))) (Ioi t) :=
  (integrableOn_Ioi_rpow_of_lt (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith) ht).const_mul _

private theorem ae_norm_heatKernel_div_pow_le {t : ℝ} (ht : 0 < t) (n : ℕ) (x : E) :
    ∀ᵐ s ∂volume.restrict (Ioi t),
      ‖heatKernel s x / s ^ n‖ ≤ (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * s ^ (-(n : ℝ)) :=
  (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun _ hs =>
    norm_heatKernel_div_pow_le ht (le_of_lt hs) n x)

variable [FiniteDimensional ℝ E]

private theorem integrableOn_heatKernel_div_pow {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n)
    (x : E) : IntegrableOn (fun s : ℝ => heatKernel s x / s ^ n) (Ioi t) := by
  refine (integrableOn_heatKernel_bound (E := E) ht hn).mono' ?_
    (ae_norm_heatKernel_div_pow_le ht n x)
  refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioi
  have hs : 0 < s := ht.trans hs
  exact ((hasDerivAt_heatKernel hs x).continuousAt.div (continuousAt_id.pow n)
    (pow_ne_zero _ hs.ne')).continuousWithinAt

private theorem continuous_integral_heatKernel_div_pow {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 2 ≤ n) : Continuous fun x : E => ∫ s in Ioi t, heatKernel s x / s ^ n :=
  continuous_of_dominated (fun x => (integrableOn_heatKernel_div_pow ht hn x).aestronglyMeasurable)
    (ae_norm_heatKernel_div_pow_le ht n) (integrableOn_heatKernel_bound ht hn)
    (Eventually.of_forall fun s => (contDiff_heatKernel (k := 0) s).continuous.div_const _)

omit [FiniteDimensional ℝ E] in
/-- Parabolic scaling of the time integrals: substituting `s = tσ`. -/
private theorem integral_heatKernel_div_pow_eq {t : ℝ} (ht : 0 < t) (n : ℕ) (x : E) :
    ∫ s in Ioi t, heatKernel s x / s ^ n =
      t / t ^ n * (√t)⁻¹ ^ Module.finrank ℝ E *
        ∫ s in Ioi 1, heatKernel s ((√t)⁻¹ • x) / s ^ n := by
  have h := integral_comp_mul_left_Ioi (fun s => heatKernel s x / s ^ n) 1 ht
  rw [mul_one, smul_eq_mul] at h
  have h2 : ∫ σ in Ioi (1 : ℝ), heatKernel (t * σ) x / (t * σ) ^ n =
      (√t)⁻¹ ^ Module.finrank ℝ E / t ^ n *
        ∫ σ in Ioi (1 : ℝ), heatKernel σ ((√t)⁻¹ • x) / σ ^ n := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
    simp only [heatKernel_mul_eq_mul_heatKernel_smul ht.le, mul_pow]
    ring
  rw [h2] at h
  have ht' : t ≠ 0 := ht.ne'
  field_simp at h ⊢
  linarith

omit [FiniteDimensional ℝ E] in
/-- The Gamma-function bound on the time integrals: for `x ≠ 0`, extending the integral to
`(0, ∞)` and substituting `s = 1/σ` gives `Γ(α) (‖x‖²/4)^(-α)` with `α = n + d/2 - 1`. -/
private theorem integral_heatKernel_div_pow_le_of_ne_zero {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 2 ≤ n) {x : E} (hx : x ≠ 0) :
    ∫ s in Ioi t, heatKernel s x / s ^ n ≤
      (4 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Gamma (n + Module.finrank ℝ E / 2 - 1) *
          (‖x‖ ^ 2 / 4) ^ (-(n + Module.finrank ℝ E / 2 - 1 : ℝ)) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  set α : ℝ := n + d / 2 - 1 with hα_def
  set b : ℝ := ‖x‖ ^ 2 / 4 with hb_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ d := Nat.cast_nonneg _
  have : 0 < α := by linarith
  have hb : 0 < b := by have := norm_pos_iff.2 hx; positivity
  set g : ℝ → ℝ := fun s => s ^ (-α - 1) * exp (-b / s) with hg_def
  have heq : ∀ s, 0 < s → heatKernel s x / s ^ n = (4 * π) ^ (-d / 2) * g s := by
    intro s hs
    rw [heatKernel_apply, mul_rpow (by positivity) hs.le, hg_def]
    dsimp only
    rw [show -α - 1 = -d / 2 - n by rw [hα_def]; ring, rpow_sub hs, rpow_natCast,
      show -‖x‖ ^ 2 / (4 * s) = -b / s by rw [hb_def]; ring]
    ring
  have hsub : ∀ y ∈ Ioi (0 : ℝ), (|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) • g (y ^ (-1 : ℝ)) =
      y ^ (α - 1) * exp (-b * y ^ (1 : ℝ)) := by
    intro y hy
    have hy : 0 < y := hy
    rw [hg_def]
    dsimp only
    rw [smul_eq_mul, abs_neg, abs_one, one_mul, rpow_one, ← rpow_mul hy.le, rpow_neg_one,
      div_inv_eq_mul, ← mul_assoc, ← rpow_add hy, neg_mul]
    ring_nf
  have hg_int : IntegrableOn g (Ioi 0) := by
    rw [← integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)]
    exact (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hb).congr_fun
      (fun y hy => (hsub y hy).symm) measurableSet_Ioi
  have hg_val : ∫ s in Ioi 0, g s = Gamma α * b ^ (-α) := by
    rw [← integral_comp_rpow_Ioi g (p := -1) (by norm_num),
      setIntegral_congr_fun measurableSet_Ioi hsub,
      integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith) hb]
    simp only [sub_add_cancel, div_one, mul_one]
    ring
  have hg_nonneg : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ g s := fun s hs => by
    have hs : 0 < s := hs
    rw [hg_def]
    positivity
  calc ∫ s in Ioi t, heatKernel s x / s ^ n = ∫ s in Ioi t, (4 * π) ^ (-d / 2) * g s :=
        setIntegral_congr_fun measurableSet_Ioi fun s hs => heq s (ht.trans hs)
    _ = (4 * π) ^ (-d / 2) * ∫ s in Ioi t, g s := integral_const_mul _ _
    _ ≤ (4 * π) ^ (-d / 2) * ∫ s in Ioi 0, g s := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hg_int
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hg_nonneg))
          (Eventually.of_forall fun y hy => Ioi_subset_Ioi ht.le hy)) (by positivity)
    _ = (4 * π) ^ (-d / 2) * Gamma α * b ^ (-α) := by rw [hg_val]; ring

/-- The time integrals of the heat kernel are related by the heat equation:
`(d + 2)/4 ∫_t^∞ K_s(x)/s² ds - ‖x‖²/8 ∫_t^∞ K_s(x)/s³ ds = K_t(x)/(2t)`, since the integrand is
the time derivative of `-K_s(x)/(2s)`. -/
private theorem integral_heatKernel_div_sq_sub {t : ℝ} (ht : 0 < t) (x : E) :
    (Module.finrank ℝ E + 2) / 4 * (∫ s in Ioi t, heatKernel s x / s ^ 2) -
      ‖x‖ ^ 2 / 8 * (∫ s in Ioi t, heatKernel s x / s ^ 3) = heatKernel t x / (2 * t) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hd_def
  have hderiv : ∀ s ∈ Ioi t, HasDerivAt (fun s => -(heatKernel s x / (2 * s)))
      ((d + 2) / 4 * (heatKernel s x / s ^ 2) - ‖x‖ ^ 2 / 8 * (heatKernel s x / s ^ 3)) s := by
    intro s hs
    have hs0 : 0 < s := ht.trans hs
    have h := ((hasDerivAt_heatKernel hs0 x).div ((hasDerivAt_id s).const_mul 2)
      (mul_ne_zero two_ne_zero hs0.ne')).neg
    convert h using 1
    · funext y
      rfl
    rw [laplacian_heatKernel, hd_def]
    simp only [id]
    field_simp
    ring
  have hlim : Tendsto (fun s => -(heatKernel s x / (2 * s))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => heatKernel s x / (2 * s)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun s : ℝ => (2 * s)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop two_pos)
      refine squeeze_zero' ?_ ?_ hinv
      · filter_upwards [eventually_gt_atTop 0] with s hs
        exact div_nonneg (heatKernel_pos hs x).le (by positivity)
      · filter_upwards [eventually_ge_atTop (1 / (4 * π))] with s hs
        have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
        rw [div_eq_mul_inv]
        refine mul_le_of_le_one_left (by positivity) ((heatKernel_le hs0 x).trans ?_)
        refine rpow_le_one_of_one_le_of_nonpos ?_ (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.2 (Nat.cast_nonneg _)) zero_le_two)
        rw [div_le_iff₀ (by positivity)] at hs
        linarith
    simpa using h0.neg
  have hcont : ContinuousWithinAt (fun s => -(heatKernel s x / (2 * s))) (Ici t) t :=
    (((hasDerivAt_heatKernel ht x).continuousAt.div (continuousAt_id.const_mul 2)
      (mul_ne_zero two_ne_zero ht.ne')).neg).continuousWithinAt
  have hint2 := integrableOn_heatKernel_div_pow ht le_rfl x
  have hint3 := integrableOn_heatKernel_div_pow ht (by norm_num : 2 ≤ 3) x
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    ((hint2.const_mul _).sub (hint3.const_mul _)) hlim
  rw [integral_sub (hint2.const_mul _) (hint3.const_mul _), integral_const_mul,
    integral_const_mul] at h
  rw [h]
  ring

/-- Near field: `∫_1^∞ K_s(x)/s^n ds ≤ (4π)^(-d/2)/(n - 1)`. -/
private theorem integral_Ioi_one_heatKernel_div_pow_le {n : ℕ} (hn : 2 ≤ n) (x : E) :
    ∫ s in Ioi 1, heatKernel s x / s ^ n ≤
      (4 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) / (n - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc ∫ s in Ioi 1, heatKernel s x / s ^ n
      ≤ ∫ s in Ioi 1, (4 * π * 1) ^ (-(Module.finrank ℝ E : ℝ) / 2) * s ^ (-(n : ℝ)) :=
        setIntegral_mono_on (integrableOn_heatKernel_div_pow one_pos hn x)
          (integrableOn_heatKernel_bound one_pos hn) measurableSet_Ioi
          fun s hs => (le_abs_self _).trans (norm_heatKernel_div_pow_le one_pos (le_of_lt hs) n x)
    _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, one_rpow, mul_one,
          show -(n : ℝ) + 1 = -(n - 1) by ring, neg_div_neg_eq, mul_one_div]

omit [FiniteDimensional ℝ E] in
/-- Far field: for `x ≠ 0`,
`‖x‖^(2n - 3) ∫_1^∞ K_s(x)/s^n ds ≤ (4π)^(-d/2) Γ(α) 4^α ‖x‖^(-(d + 1))`, `α = n + d/2 - 1`. -/
private theorem norm_pow_mul_integral_heatKernel_div_pow_le {n : ℕ} (hn : 2 ≤ n) {x : E}
    (hx : x ≠ 0) :
    ‖x‖ ^ (2 * n - 3) * (∫ s in Ioi 1, heatKernel s x / s ^ n) ≤
      (4 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Gamma (n + Module.finrank ℝ E / 2 - 1) *
        4 ^ (n + Module.finrank ℝ E / 2 - 1 : ℝ) * ‖x‖ ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hd_def
  set α : ℝ := n + d / 2 - 1 with hα_def
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hpow : (‖x‖ ^ 2 / 4) ^ (-α) = 4 ^ α * ‖x‖ ^ (-(2 * α)) := by
    rw [div_rpow (by positivity) (by norm_num), ← rpow_natCast, ← rpow_mul hx0.le,
      rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    push_cast
    field_simp
  have hexp : ‖x‖ ^ (2 * n - 3) * ‖x‖ ^ (-(2 * α)) = ‖x‖ ^ (-(d + 1)) := by
    rw [← rpow_natCast, ← rpow_add hx0]
    congr 1
    rw [Nat.cast_sub (by omega), hα_def]
    push_cast
    ring
  have hI := integral_heatKernel_div_pow_le_of_ne_zero one_pos hn hx
  rw [← hd_def, ← hα_def, hpow] at hI
  calc ‖x‖ ^ (2 * n - 3) * (∫ s in Ioi 1, heatKernel s x / s ^ n)
      ≤ ‖x‖ ^ (2 * n - 3) * ((4 * π) ^ (-d / 2) * Gamma α * (4 ^ α * ‖x‖ ^ (-(2 * α)))) := by
        gcongr
    _ = _ := by rw [← hexp]; ring

/-- The time integrals decay at the rate fixed by parabolic scaling: for `n ≥ 2` and
`d = dim E`, `‖x‖^(2n - 3) ∫_1^∞ K_s(x)/s^n ds ≤ C (1 + ‖x‖)^(-(d + 1))`. -/
private theorem exists_norm_pow_mul_integral_heatKernel_div_pow_le {n : ℕ} (hn : 2 ≤ n) :
    ∃ C, ∀ x : E, ‖x‖ ^ (2 * n - 3) * (∫ s in Ioi 1, heatKernel s x / s ^ n) ≤
      C * (1 + ‖x‖) ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  set α : ℝ := n + d / 2 - 1 with hα_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hα : 0 < α := by linarith [hd]
  set c₁ : ℝ := (4 * π) ^ (-d / 2) / (n - 1)
  set c₂ : ℝ := (4 * π) ^ (-d / 2) * Gamma α * 4 ^ α
  have hc₁ : 0 ≤ c₁ := div_nonneg (by positivity) (by linarith)
  have hc₂ : 0 ≤ c₂ := by have := Gamma_pos_of_pos hα; positivity
  have h2 : (2 : ℝ) ^ (d + 1) * 2 ^ (-(d + 1)) = 1 := by simp [← rpow_add two_pos]
  refine ⟨2 ^ (d + 1) * (c₁ + c₂), fun x => ?_⟩
  have hI0 := integral_heatKernel_div_pow_nonneg zero_le_one n x
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · -- Near the origin both factors are bounded and `(1 + ‖x‖)^(-(d + 1)) ≥ 2^(-(d + 1))`.
    have hlow : (2 : ℝ) ^ (-(d + 1)) ≤ (1 + ‖x‖) ^ (-(d + 1)) :=
      rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith [hd])
    calc ‖x‖ ^ (2 * n - 3) * (∫ s in Ioi 1, heatKernel s x / s ^ n) ≤ 1 * c₁ :=
          mul_le_mul (pow_le_one₀ (norm_nonneg _) hx)
            (integral_Ioi_one_heatKernel_div_pow_le hn x) hI0 zero_le_one
      _ ≤ 2 ^ (d + 1) * (c₁ + c₂) * 2 ^ (-(d + 1)) := by
          rw [mul_right_comm, h2]; linarith
      _ ≤ 2 ^ (d + 1) * (c₁ + c₂) * (1 + ‖x‖) ^ (-(d + 1)) := by gcongr
  · -- Far away, `1 + ‖x‖ ≤ 2‖x‖` turns the Gamma-function bound into the claim.
    have hx0 : 0 < ‖x‖ := zero_lt_one.trans hx
    have hfar : (2 * ‖x‖) ^ (-(d + 1)) ≤ (1 + ‖x‖) ^ (-(d + 1)) :=
      rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith [hd])
    rw [mul_rpow (by norm_num) hx0.le] at hfar
    calc ‖x‖ ^ (2 * n - 3) * (∫ s in Ioi 1, heatKernel s x / s ^ n)
        ≤ c₂ * ‖x‖ ^ (-(d + 1)) :=
          norm_pow_mul_integral_heatKernel_div_pow_le hn (norm_pos_iff.1 hx0)
      _ = 2 ^ (d + 1) * c₂ * (2 ^ (-(d + 1)) * ‖x‖ ^ (-(d + 1))) := by
          simp only [c₂]
          linear_combination (-((4 * π) ^ (-d / 2) * Gamma α * 4 ^ α * ‖x‖ ^ (-(d + 1)))) * h2
      _ ≤ 2 ^ (d + 1) * (c₁ + c₂) * (1 + ‖x‖) ^ (-(d + 1)) := by
          gcongr
          linarith

end TimeIntegral

section Kernel

variable [FiniteDimensional ℝ E]

/-- The **Oseen kernel** `O_t(x)`, a linear map from matrices to vectors. The operator
`e^{tΔ} ℙ` is convolution with the matrix kernel `K_t 1 + ∫_t^∞ ∇²K_s ds`, whose symbol is
`e^{-4π²t‖ξ‖²}(1 - ξ ⊗ ξ/‖ξ‖²)`. For a matrix field `F : E → E →L[ℝ] E` with divergence taken in
the second index, `(div F)ⱼ = ∂ₖFⱼₖ`, moving the divergence onto this kernel writes
`e^{tΔ} ℙ div F` as the convolution `∫ O_t(x - y) (F y) dy`, where `O_t(x) A` is
`A(∇K_t(x)) + ∫_t^∞ ∇³K_s(x) ds` contracted with `A`. With the Gaussian `K_s` this is
`-(K_t(x)/(2t)) A x + (∫_t^∞ K_s(x)/s² ds / 4) (tr A x + A x + A† x)
  - (∫_t^∞ K_s(x)/s³ ds / 8) ⟪x, A x⟫ x`,
which is the definition used here. It is meaningful for `t > 0`. -/
def oseenKernel (t : ℝ) (x : E) : (E →L[ℝ] E) →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (-(heatKernel t x / (2 * t))) • A x +
        ((∫ s in Ioi t, heatKernel s x / s ^ 2) / 4) •
          (LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • x + A x + ContinuousLinearMap.adjoint A x) -
        ((∫ s in Ioi t, heatKernel s x / s ^ 3) / 8 * ⟪x, A x⟫) • x
      map_add' := fun A B => by
        simp only [add_apply, ContinuousLinearMap.toLinearMap_add, map_add,
          inner_add_right, mul_add, add_smul, smul_add]
        abel
      map_smul' := fun c A => by
        simp only [smul_apply, ContinuousLinearMap.toLinearMap_smul, map_smul,
          inner_smul_right, RingHom.id_apply, smul_eq_mul]
        module }

/-- The defining formula of the Oseen kernel. -/
theorem oseenKernel_apply (t : ℝ) (x : E) (A : E →L[ℝ] E) :
    oseenKernel t x A = (-(heatKernel t x / (2 * t))) • A x +
      ((∫ s in Ioi t, heatKernel s x / s ^ 2) / 4) •
        (LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • x + A x + ContinuousLinearMap.adjoint A x) -
      ((∫ s in Ioi t, heatKernel s x / s ^ 3) / 8 * ⟪x, A x⟫) • x :=
  (rfl)

/-- The Oseen kernel annihilates the identity matrix: `e^{tΔ} ℙ div (φ 1) = e^{tΔ} ℙ ∇φ = 0`. -/
@[simp]
theorem oseenKernel_apply_id {t : ℝ} (ht : 0 < t) (x : E) :
    oseenKernel t x (ContinuousLinearMap.id ℝ E) = 0 := by
  have h := integral_heatKernel_div_sq_sub ht x
  rw [oseenKernel_apply, ContinuousLinearMap.coe_id, LinearMap.trace_id,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq]
  set I₂ := ∫ s in Ioi t, heatKernel s x / s ^ 2
  set I₃ := ∫ s in Ioi t, heatKernel s x / s ^ 3
  have hc : -(heatKernel t x / (2 * t)) + I₂ / 4 * (Module.finrank ℝ E + 2) -
      I₃ / 8 * ‖x‖ ^ 2 = 0 := by linear_combination h
  calc _ = (-(heatKernel t x / (2 * t)) + I₂ / 4 * (Module.finrank ℝ E + 2) -
        I₃ / 8 * ‖x‖ ^ 2) • x := by
        rw [Nat.cast_smul_eq_nsmul]
        module
    _ = 0 := by rw [hc, zero_smul]

/-- On the real line the Leray projection is zero, and so is the Oseen kernel. -/
theorem oseenKernel_eq_zero_of_finrank_eq_one (hE : Module.finrank ℝ E = 1) {t : ℝ}
    (ht : 0 < t) (x : E) : oseenKernel t x = 0 := by
  ext1 A
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hE (A : E →ₗ[ℝ] E)
  have hA : A = c • ContinuousLinearMap.id ℝ E := by
    ext v
    simpa using LinearMap.congr_fun hc v
  rw [hA, map_smul, oseenKernel_apply_id ht, smul_zero, zero_apply]

/-- **Parabolic scaling of the Oseen kernel.** For `t > 0`,
`O_t(x) = (√t)⁻¹ ^ (d + 1) O_1((√t)⁻¹ • x)`, that is `O_t(x) = t^(-(d+1)/2) O_1(x/√t)`. -/
theorem oseenKernel_eq_smul_oseenKernel_one {t : ℝ} (ht : 0 < t) (x : E) :
    oseenKernel t x =
      (√t)⁻¹ ^ (Module.finrank ℝ E + 1) • oseenKernel 1 ((√t)⁻¹ • x) := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ t = u ^ 2 := ⟨√t, sqrt_pos.2 ht, (sq_sqrt ht.le).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = u • y := ⟨u⁻¹ • x, (smul_inv_smul₀ hu.ne' x).symm⟩
  have hu0 : u ≠ 0 := hu.ne'
  ext1 A
  rw [smul_apply, oseenKernel_apply, oseenKernel_apply, integral_heatKernel_div_pow_eq ht 2,
    integral_heatKernel_div_pow_eq ht 3, heatKernel_eq_mul_heatKernel_one_smul ht.le]
  simp only [sqrt_sq hu.le, inv_smul_smul₀ hu.ne', map_smul, real_inner_smul_left,
    real_inner_smul_right]
  rw [pow_succ u⁻¹ (Module.finrank ℝ E)]
  set c := u⁻¹ ^ Module.finrank ℝ E
  set I₂ := ∫ s in Ioi 1, heatKernel s y / s ^ 2
  set I₃ := ∫ s in Ioi 1, heatKernel s y / s ^ 3
  match_scalars <;> field_simp

/-- The Oseen kernel is continuous in the space variable at every positive time. -/
theorem continuous_oseenKernel {t : ℝ} (ht : 0 < t) :
    Continuous (oseenKernel t : E → (E →L[ℝ] E) →L[ℝ] E) := by
  refine continuous_clm_apply.2 fun A => ?_
  simp only [oseenKernel_apply]
  have h2 := continuous_integral_heatKernel_div_pow (E := E) ht le_rfl
  have h3 := continuous_integral_heatKernel_div_pow (E := E) ht (by norm_num : 2 ≤ 3)
  have hK := (contDiff_heatKernel (E := E) (k := 0) t).continuous
  fun_prop

/-- The operator bound on `O_t(x) A` by the time integrals, given a bound `|tr A| ≤ T ‖A‖`:
the heat term is absorbed using `K_t(x)/(2t) ≤ (d + 2)/4 ∫_t^∞ K_s(x)/s² ds`. -/
private theorem norm_oseenKernel_apply_le {T : ℝ}
    (hτ : ∀ A : E →L[ℝ] E, |LinearMap.trace ℝ E (A : E →ₗ[ℝ] E)| ≤ T * ‖A‖) {t : ℝ}
    (ht : 0 < t) (x : E) (A : E →L[ℝ] E) :
    ‖oseenKernel t x A‖ ≤ ‖A‖ * ((Module.finrank ℝ E + T + 4) / 4 *
      (‖x‖ * ∫ s in Ioi t, heatKernel s x / s ^ 2) +
        ‖x‖ ^ 3 * (∫ s in Ioi t, heatKernel s x / s ^ 3) / 8) := by
  set I₂ := ∫ s in Ioi t, heatKernel s x / s ^ 2
  set I₃ := ∫ s in Ioi t, heatKernel s x / s ^ 3
  have hI : ∀ n : ℕ, 0 ≤ ∫ s in Ioi t, heatKernel s x / s ^ n := fun n =>
    integral_heatKernel_div_pow_nonneg ht.le n x
  have hK : heatKernel t x / (2 * t) ≤ (Module.finrank ℝ E + 2) / 4 * I₂ := by
    rw [← integral_heatKernel_div_sq_sub ht x]
    nlinarith [mul_nonneg (sq_nonneg ‖x‖) (hI 3)]
  have hAx : ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
  have hA'x : ‖ContinuousLinearMap.adjoint A x‖ ≤ ‖A‖ * ‖x‖ := by
    simpa only [LinearIsometryEquiv.norm_map] using (ContinuousLinearMap.adjoint A).le_opNorm x
  have hin : |⟪x, A x⟫| ≤ ‖A‖ * ‖x‖ ^ 2 :=
    (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg x, norm_nonneg A])
  have hK0 : 0 ≤ heatKernel t x / (2 * t) := div_nonneg (heatKernel_pos ht x).le (by positivity)
  have hI₂ := hI 2
  have hI₃ := hI 3
  rw [oseenKernel_apply]
  calc ‖(-(heatKernel t x / (2 * t))) • A x + (I₂ / 4) • (LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • x
        + A x + ContinuousLinearMap.adjoint A x) - (I₃ / 8 * ⟪x, A x⟫) • x‖
      ≤ heatKernel t x / (2 * t) * ‖A x‖ +
          I₂ / 4 * (|LinearMap.trace ℝ E (A : E →ₗ[ℝ] E)| * ‖x‖ + ‖A x‖ +
            ‖ContinuousLinearMap.adjoint A x‖) + I₃ / 8 * |⟪x, A x⟫| * ‖x‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add ?_ ?_)) ?_)
        · rw [norm_smul, norm_neg, Real.norm_of_nonneg hK0]
        · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          gcongr
          refine norm_add₃_le.trans_eq ?_
          rw [norm_smul, Real.norm_eq_abs]
        · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (Module.finrank ℝ E + 2) / 4 * I₂ * (‖A‖ * ‖x‖) +
          I₂ / 4 * (T * ‖A‖ * ‖x‖ + ‖A‖ * ‖x‖ + ‖A‖ * ‖x‖) +
            I₃ / 8 * (‖A‖ * ‖x‖ ^ 2) * ‖x‖ := by
        gcongr
        exact hτ A
    _ = _ := by ring

/-- The pointwise bound at time one: `‖O_1(x)‖ ≤ C (1 + ‖x‖)^(-(d + 1))`. -/
private theorem exists_norm_oseenKernel_one_le :
    ∃ C, 0 ≤ C ∧ ∀ x : E,
      ‖oseenKernel 1 x‖ ≤ C * (1 + ‖x‖) ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
  obtain ⟨C₂, hC₂⟩ := exists_norm_pow_mul_integral_heatKernel_div_pow_le (E := E) le_rfl
  obtain ⟨C₃, hC₃⟩ :=
    exists_norm_pow_mul_integral_heatKernel_div_pow_le (E := E) (by norm_num : 2 ≤ 3)
  have hC₂0 : 0 ≤ C₂ := by simpa using hC₂ 0
  have hC₃0 : 0 ≤ C₃ := by simpa using hC₃ 0
  -- The trace is a continuous linear functional on the finite-dimensional space `E →L[ℝ] E`.
  let τ : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ))
  have hτ : ∀ A : E →L[ℝ] E, |LinearMap.trace ℝ E (A : E →ₗ[ℝ] E)| ≤ ‖τ‖ * ‖A‖ := fun A => by
    simpa [τ, Real.norm_eq_abs] using τ.le_opNorm A
  set a : ℝ := (Module.finrank ℝ E + ‖τ‖ + 4) / 4
  refine ⟨a * C₂ + C₃ / 8, by positivity, fun x => ?_⟩
  have h2 : ‖x‖ * (∫ s in Ioi 1, heatKernel s x / s ^ 2) ≤
      C₂ * (1 + ‖x‖) ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
    have := hC₂ x
    rwa [show 2 * 2 - 3 = 1 from rfl, pow_one] at this
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
  refine (norm_oseenKernel_apply_le hτ one_pos x A).trans ?_
  calc ‖A‖ * (a * (‖x‖ * ∫ s in Ioi 1, heatKernel s x / s ^ 2) +
        ‖x‖ ^ 3 * (∫ s in Ioi 1, heatKernel s x / s ^ 3) / 8)
      ≤ ‖A‖ * (a * (C₂ * (1 + ‖x‖) ^ (-(Module.finrank ℝ E + 1 : ℝ))) +
          C₃ * (1 + ‖x‖) ^ (-(Module.finrank ℝ E + 1 : ℝ)) / 8) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity))
          (div_le_div_of_nonneg_right (hC₃ x) (by norm_num))) (norm_nonneg A)
    _ = _ := by ring

/-- **Pointwise bound on the Oseen kernel.** There is a constant `C` depending only on the
dimension `d` such that `‖O_t(x)‖ ≤ C (‖x‖ + √t)^(-(d + 1))` for all `t > 0` and `x`. -/
theorem exists_norm_oseenKernel_le :
    ∃ C, 0 ≤ C ∧ ∀ ⦃t : ℝ⦄, 0 < t → ∀ x : E,
      ‖oseenKernel t x‖ ≤ C * (‖x‖ + √t) ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_oseenKernel_one_le (E := E)
  refine ⟨C, hC0, fun t ht x => ?_⟩
  have hu : 0 < √t := sqrt_pos.2 ht
  have e1 : (√t)⁻¹ ^ (Module.finrank ℝ E + 1) =
      √t ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
    rw [rpow_neg hu.le, inv_pow, ← rpow_natCast]
    push_cast
    rfl
  have e2 : √t * (1 + ‖(√t)⁻¹ • x‖) = ‖x‖ + √t := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hu.le]
    field_simp
    ring
  have : NormSMulClass ℝ ((E →L[ℝ] E) →L[ℝ] E) :=
    @NormedSpace.toNormSMulClass ℝ ((E →L[ℝ] E) →L[ℝ] E) _ _ _
  rw [oseenKernel_eq_smul_oseenKernel_one ht, norm_smul, norm_pow, norm_inv,
    Real.norm_of_nonneg hu.le]
  calc (√t)⁻¹ ^ (Module.finrank ℝ E + 1) * ‖oseenKernel 1 ((√t)⁻¹ • x)‖
      ≤ (√t)⁻¹ ^ (Module.finrank ℝ E + 1) *
          (C * (1 + ‖(√t)⁻¹ • x‖) ^ (-(Module.finrank ℝ E + 1 : ℝ))) := by
        gcongr
        exact hC _
    _ = C * (‖x‖ + √t) ^ (-(Module.finrank ℝ E + 1 : ℝ)) := by
        rw [e1, mul_left_comm, ← mul_rpow hu.le (by positivity), e2]

/-- The norm of the Oseen kernel is dominated by its majorant, in extended form. -/
private theorem eNorm_oseenKernel_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ⦃t : ℝ⦄, 0 < t → ∀ x : E,
      ‖oseenKernel t x‖ ≤ C * (‖x‖ + √t) ^ (-(Module.finrank ℝ E + 1 : ℝ)))
    {t : ℝ} (ht : 0 < t) (x : E) :
    ‖oseenKernel t x‖ₑ ≤ ‖C * (‖x‖ + √t) ^ (-(Module.finrank ℝ E + 1 : ℝ))‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hC ht x)

variable [MeasurableSpace E] [BorelSpace E]

/-- Scaling of the `Lʳ` norms of the majorant `(‖x‖ + √t)^(-(d + 1))`: they equal
`t^(-1/2 - (d/2)(1 - 1/r))` times those of `(‖x‖ + 1)^(-(d + 1))`. -/
private theorem eLpNorm_rpow_norm_add_sqrt {t : ℝ} (ht : 0 < t) (r : ℝ≥0∞) :
    eLpNorm (fun x : E => (‖x‖ + √t) ^ (-(Module.finrank ℝ E + 1 : ℝ))) r volume =
      ENNReal.ofReal (t ^ (-(1 / 2 : ℝ) - Module.finrank ℝ E / 2 * (1 - 1 / r.toReal))) *
        eLpNorm (fun x : E => (‖x‖ + 1) ^ (-(Module.finrank ℝ E + 1 : ℝ))) r volume := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hu : 0 < √t := sqrt_pos.2 ht
  have hfun : (fun x : E => (‖x‖ + √t) ^ (-(d + 1))) =
      (√t ^ (-(d + 1))) • fun x : E => (‖(√t)⁻¹ • x‖ + 1) ^ (-(d + 1)) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← mul_rpow hu.le (by positivity), norm_smul, norm_inv,
      Real.norm_of_nonneg hu.le, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]
  rw [hfun, eLpNorm_const_smul,
    Measure.eLpNorm_comp_inv_smul volume (fun x : E => (‖x‖ + 1) ^ (-(d + 1))) hu.ne' r,
    ← mul_assoc, Real.eNorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [abs_of_nonneg hu.le, sqrt_eq_rpow, ← rpow_mul ht.le, ← rpow_mul ht.le, ← rpow_add ht]
  congr 1
  ring

/-- `Lʳ` bounds on the majorant `(‖x‖ + √t)^(-(d + 1))` of the Oseen kernel, uniform in
`1 ≤ r ≤ ∞`. -/
private theorem exists_eLpNorm_rpow_norm_add_sqrt_le :
    ∃ M, 0 ≤ M ∧ ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ≥0∞⦄, 1 ≤ r →
      eLpNorm (fun x : E => (‖x‖ + √t) ^ (-(Module.finrank ℝ E + 1 : ℝ))) r volume ≤
        ENNReal.ofReal (M * t ^ (-(1 / 2 : ℝ) - Module.finrank ℝ E / 2 * (1 - 1 / r.toReal))) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  set g : E → ℝ := fun x => (‖x‖ + 1) ^ (-(d + 1))
  have hgm : AEStronglyMeasurable g volume := by fun_prop
  have hg1 : eLpNorm g 1 volume ≠ ∞ := by
    refine (memLp_one_iff_integrable.2 ((integrable_one_add_norm
      (μ := (volume : Measure E)) (by linarith : d < d + 1)).congr ?_)).eLpNorm_ne_top
    exact Eventually.of_forall fun x => by simp only [g, add_comm]
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hg1' : ∀ x, g x ≤ 1 := fun x =>
    rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith [hd])
  have hgtop : eLpNorm g ∞ volume ≠ ∞ := by
    refine ((eLpNorm_le_of_ae_bound hgm (Eventually.of_forall fun x =>
      (Real.norm_of_nonneg (hg0 x)).trans_le (hg1' x))).trans_lt ?_).ne
    simp
  -- Every `Lʳ` norm with `1 ≤ r ≤ ∞` is at most the larger of the `L¹` and `L^∞` norms.
  set M := max (eLpNorm g 1 volume) (eLpNorm g ∞ volume)
  have hM : M ≠ ∞ := max_ne_top hg1 hgtop
  refine ⟨M.toReal, by positivity, fun t ht r hr => ?_⟩
  rw [eLpNorm_rpow_norm_add_sqrt ht r, mul_comm M.toReal, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal hM]
  gcongr
  exact eLpNorm_le_max_of_le_of_le one_ne_zero hr le_top

/-- **`Lʳ` bounds on the Oseen kernel.** There is a constant `C` depending only on the
dimension such that `‖O_t‖_r ≤ C t^(-1/2 - (d/2)(1 - 1/r))` for all `t > 0` and `1 ≤ r ≤ ∞`.
At `r = 1` this is the integrability `‖O_t‖₁ ≤ C t^(-1/2)`. -/
theorem exists_eLpNorm_oseenKernel_le :
    ∃ C, 0 ≤ C ∧ ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ≥0∞⦄, 1 ≤ r →
      eLpNorm (oseenKernel t : E → (E →L[ℝ] E) →L[ℝ] E) r volume ≤
        ENNReal.ofReal (C * t ^ (-(1 / 2 : ℝ) - Module.finrank ℝ E / 2 * (1 - 1 / r.toReal))) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_norm_oseenKernel_le (E := E)
  obtain ⟨M, hM, hMb⟩ := exists_eLpNorm_rpow_norm_add_sqrt_le (E := E)
  refine ⟨C₀ * M, by positivity, fun t ht r hr => ?_⟩
  calc eLpNorm (oseenKernel t : E → (E →L[ℝ] E) →L[ℝ] E) r volume
      ≤ eLpNorm (C₀ • fun x : E => (‖x‖ + √t) ^ (-(Module.finrank ℝ E + 1 : ℝ))) r volume :=
        eLpNorm_mono_eNorm (continuous_oseenKernel ht).aestronglyMeasurable
          (eNorm_oseenKernel_le hC₀ hb ht)
    _ ≤ _ := by
        rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal hC₀, mul_assoc,
          ENNReal.ofReal_mul hC₀]
        gcongr
        exact hMb ht hr

/-- The exponent of Young's inequality between `Lᵖ` and `L^q` for `1 ≤ p ≤ q ≤ ∞`:
`r` with `1/r + 1/p = 1 + 1/q`, so that `1 - 1/r = 1/p - 1/q`. -/
private theorem exists_young_exponent {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ r : ℝ≥0∞, 1 ≤ r ∧ r⁻¹ + p⁻¹ = 1 + q⁻¹ ∧
      1 - 1 / r.toReal = 1 / p.toReal - 1 / q.toReal := by
  set r : ℝ≥0∞ := (1 + q⁻¹ - p⁻¹)⁻¹
  have hpi : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hqi : q⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpq
  have hr : 1 ≤ r := by
    apply ENNReal.one_le_inv.2
    exact tsub_le_iff_right.2 (by simpa [add_comm] using add_le_add_left hqi 1)
  have hrp : r⁻¹ + p⁻¹ = 1 + q⁻¹ := by
    simp only [r, inv_inv]
    exact tsub_add_cancel_of_le (hpi.trans le_self_add)
  have hreal : 1 / r.toReal + 1 / p.toReal = 1 + 1 / q.toReal := by
    have h := congrArg ENNReal.toReal hrp
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hr).ne')
        (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp).ne'),
      ENNReal.toReal_add ENNReal.one_ne_top
        (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le (hp.trans hpq)).ne')] at h
    simpa only [ENNReal.toReal_inv, ENNReal.toReal_one, one_div] using h
  exact ⟨r, hr, hrp, by linarith⟩

/-- **The `Lᵖ`–`L^q` estimate for `e^{tΔ} ℙ div`.** There is a constant `C` depending only on the
dimension such that, for all `t > 0`, all `1 ≤ p ≤ q ≤ ∞` and every matrix field `F`,
`‖O_t ⋆ F‖_q ≤ C t^(-1/2 - (d/2)(1/p - 1/q)) ‖F‖_p`. The endpoints `p = 1` and `q = ∞` are
included, although the Leray projection alone is unbounded there. -/
theorem exists_eLpNorm_oseenKernel_convolution_le :
    ∃ C, 0 ≤ C ∧ ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃p q : ℝ≥0∞⦄, 1 ≤ p → p ≤ q →
      ∀ ⦃F : E → E →L[ℝ] E⦄, AEStronglyMeasurable F volume →
        eLpNorm (convolution (𝕜 := ℝ) (oseenKernel t) F
            (ContinuousLinearMap.id ℝ ((E →L[ℝ] E) →L[ℝ] E)) volume) q volume ≤
          ENNReal.ofReal (C * t ^ (-(1 / 2 : ℝ) - Module.finrank ℝ E / 2 *
            (1 / p.toReal - 1 / q.toReal))) * eLpNorm F p volume := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  obtain ⟨C₀, hC₀, hb⟩ := exists_norm_oseenKernel_le (E := E)
  obtain ⟨M, hM, hMb⟩ := exists_eLpNorm_rpow_norm_add_sqrt_le (E := E)
  refine ⟨C₀ * M, by positivity, fun t ht p q hp hpq F hF => ?_⟩
  -- Young's inequality with the exponent `r` given by `1/r + 1/p = 1 + 1/q`.
  obtain ⟨r, hr, hrp, he⟩ := exists_young_exponent hp hpq
  -- The kernel is dominated by the scalar majorant `m(y) = C₀ (‖y‖ + √t)^(-(d + 1))`.
  set m : E → ℝ := fun y => C₀ * (‖y‖ + √t) ^ (-(d + 1))
  have hm : AEStronglyMeasurable m volume := by fun_prop
  have hO : AEStronglyMeasurable (oseenKernel t : E → (E →L[ℝ] E) →L[ℝ] E) volume :=
    (continuous_oseenKernel ht).aestronglyMeasurable
  -- Pointwise, `‖(O_t ⋆ F)(x)‖ ≤ ∫ m(y) ‖F(x - y)‖ dy`.
  have hpt : ∀ x, ‖convolution (𝕜 := ℝ) (oseenKernel t) F
      (ContinuousLinearMap.id ℝ ((E →L[ℝ] E) →L[ℝ] E)) volume x‖ₑ ≤
      ‖((fun y => ‖m y‖ₑ) ⋆ₗ[volume] fun y => ‖F y‖ₑ) x‖ₑ := fun x => by
    rw [eNorm_eq_self, lconvolution_def, convolution_def]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun y => ?_)
    rw [neg_add_eq_sub, ContinuousLinearMap.id_apply]
    exact ((oseenKernel t y).le_opENorm _).trans (by gcongr; exact eNorm_oseenKernel_le hC₀ hb ht y)
  calc eLpNorm (convolution (𝕜 := ℝ) (oseenKernel t) F
        (ContinuousLinearMap.id ℝ ((E →L[ℝ] E) →L[ℝ] E)) volume) q volume
      ≤ eLpNorm ((fun y => ‖m y‖ₑ) ⋆ₗ[volume] fun y => ‖F y‖ₑ) q volume :=
        eLpNorm_mono_eNorm (hO.convolution _ hF) hpt
    _ ≤ eLpNorm (fun y => ‖m y‖ₑ) r volume * eLpNorm (fun y => ‖F y‖ₑ) p volume :=
        eLpNorm_lconvolution_le hr hp hrp hm.eNorm hF.eNorm
    _ = eLpNorm (C₀ • fun x : E => (‖x‖ + √t) ^ (-(d + 1))) r volume * eLpNorm F p volume := by
        rw [eLpNorm_eNorm _ hm, eLpNorm_eNorm _ hF]
        rfl
    _ ≤ _ := by
        rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal hC₀, mul_assoc C₀,
          ENNReal.ofReal_mul hC₀, ← he]
        gcongr
        exact hMb ht hr

end Kernel

end TauCeti
