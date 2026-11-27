/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Sobolev.W1p.Truncation
import TauCeti.MeasureTheory.Function.L1Space.Integrable

/-!
# The `Lᵖ` bound for divergence-form equations with a positive zero-order term

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, with lower constant `λ` and
not necessarily symmetric, and let `c` be measurable and bounded with `c ≥ κ > 0` almost
everywhere. This file proves that every weak solution `u ∈ H¹₀(Ω)` of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f + div F` in `Ω`, `u = 0` on `∂Ω`,

with `f ∈ L²(Ω)` and `F ∈ L²(Ω; ℝⁿ)`, satisfies for every `2 ≤ p < ∞`

`‖u‖_{Lᵖ(Ω)} ≤ κ⁻¹ ‖f‖_{Lᵖ(Ω)} + √((p - 1) / (4λκ)) ‖F‖_{Lᵖ(Ω)}`

(`TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq`). No integrability
of `u` beyond `L²` is assumed and nothing about `Ω` or the regularity of `a`. For the constant
shift `c = κ` the estimate reads `√κ ‖u‖_p ≤ κ^{-1/2} ‖f‖_p + √((p - 1) / (4λ)) ‖F‖_p`. This is
the zero-order part of Krylov's whole-space `W^{1,p}` estimate for `-div(a∇u) + κu = f + div F`
with coefficients of vanishing mean oscillation: the gradient estimate carries a lower-order term
`r₀⁻¹ ‖u‖_p`, which this bound controls by the data with the factor `r₀⁻¹ κ^{-1/2}`. With `F = 0`
it is the contraction bound `‖u‖_p ≤ κ⁻¹ ‖f‖_p`
(`TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_isWeakSolutionDirichlet`).

## The argument

Formally one tests the equation against `|u|^{p-2} u`. Since
`∇(|u|^{p-2} u) = (p - 1) |u|^{p-2} ∇u`, the principal part contributes
`(p - 1) ∫ |u|^{p-2} ⟨a ∇u, ∇u⟩ ≥ 0`, the zero-order part at least `κ ‖u‖_p^p`, and the divergence
datum `(p - 1) ∫ |u|^{p-2} ⟨F, ∇u⟩`, which the principal part absorbs up to
`(p - 1) / (4λ) ∫ |u|^{p-2} ‖F‖²`. Hölder's inequality with the exponents `(p, p / (p - 1))` and
`(p / 2, p / (p - 2))` gives

`κ X^p ≤ ‖f‖_p X^{p-1} + (p - 1) / (4λ) ‖F‖_p² X^{p-2}`, `X = ‖u‖_p`,

and the quadratic inequality `κ X² ≤ ‖f‖_p X + (p - 1) / (4λ) ‖F‖_p²` gives the bound.

The power `|u|^{p-2} u` need not lie in `H¹₀(Ω)`, so it is replaced by the truncated power
`φ_k(t) = ∫₀ᵗ (p - 1) min(|s|, k)^{p-2} ds`, which equals `|t|^{p-2} t` for `|t| ≤ k` and continues
linearly beyond. It is `C¹` with bounded derivative and odd, so `φ_k(u) ∈ H¹₀(Ω)` with gradient
`φ_k'(u) ∇u`. The computation above goes through with `Z = ∫ u φ_k(u)` in place of `‖u‖_p^p`, since
`min(|t|, k)^p ≤ t φ_k(t)`, `|φ_k(t)|^{p/(p-1)} ≤ t φ_k(t)` and
`φ_k'(t)^{p/(p-2)} ≤ (p - 1)^{p/(p-2)} t φ_k(t)`. This bounds `‖min(|u|, k)‖_p` uniformly in `k`,
and the bound passes to `u` as `k → ∞`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq`: the `Lᵖ` bound for
  `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f + div F`.
* `TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_isWeakSolutionDirichlet`: its case `F = 0`,
  `‖u‖_p ≤ κ⁻¹ ‖f‖_p`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations 32 (2007), Theorem 2.8 (the whole-space estimate this bound feeds).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

/-! ### The truncated power profile -/

/-- The derivative `(p - 1) min(|s|, k)^{p-2}` of the truncated power profile. -/
private def lpProfileDeriv (p k s : ℝ) : ℝ := (p - 1) * min |s| k ^ (p - 2)

/-- The truncated power profile `φ(t) = ∫₀ᵗ (p - 1) min(|s|, k)^{p-2} ds`: it equals
`|t|^{p-2} t` for `|t| ≤ k` and continues linearly beyond. -/
private def lpProfile (p k t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, lpProfileDeriv p k s

variable {p k : ℝ}

private theorem continuous_lpProfileDeriv (hp : 2 ≤ p) : Continuous (lpProfileDeriv p k) :=
  continuous_const.mul ((Real.continuous_rpow_const (by linarith)).comp
    (continuous_abs.min continuous_const))

private theorem lpProfileDeriv_nonneg (hp : 2 ≤ p) (hk : 0 ≤ k) (s : ℝ) :
    0 ≤ lpProfileDeriv p k s :=
  mul_nonneg (by linarith) (Real.rpow_nonneg (le_min (abs_nonneg s) hk) _)

private theorem lpProfileDeriv_le (hp : 2 ≤ p) (hk : 0 ≤ k) (s : ℝ) :
    lpProfileDeriv p k s ≤ (p - 1) * k ^ (p - 2) :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_min (abs_nonneg s) hk) (min_le_right _ _)
    (by linarith)) (by linarith)

private theorem lpProfileDeriv_neg (s : ℝ) : lpProfileDeriv p k (-s) = lpProfileDeriv p k s := by
  simp [lpProfileDeriv]

private theorem hasDerivAt_lpProfile (hp : 2 ≤ p) (t : ℝ) :
    HasDerivAt (lpProfile p k) (lpProfileDeriv p k t) t :=
  ((continuous_lpProfileDeriv hp).integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem deriv_lpProfile (hp : 2 ≤ p) :
    deriv (lpProfile p k) = lpProfileDeriv p k :=
  funext fun t => (hasDerivAt_lpProfile hp t).deriv

private theorem contDiff_lpProfile (hp : 2 ≤ p) : ContDiff ℝ 1 (lpProfile p k) :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_lpProfile hp t).differentiableAt,
    by rw [deriv_lpProfile hp]; exact continuous_lpProfileDeriv hp⟩

private theorem lpProfile_zero : lpProfile p k 0 = 0 := by simp [lpProfile]

private theorem lpProfile_neg (t : ℝ) : lpProfile p k (-t) = -lpProfile p k t := by
  have h := intervalIntegral.integral_comp_neg (a := t) (b := 0) (lpProfileDeriv p k)
  simp only [lpProfileDeriv_neg, neg_zero] at h
  rw [lpProfile, lpProfile, ← intervalIntegral.integral_symm, ← h]

private theorem lpProfile_nonneg (hp : 2 ≤ p) (hk : 0 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ lpProfile p k t :=
  intervalIntegral.integral_nonneg ht fun s _ => lpProfileDeriv_nonneg hp hk s

private theorem lpProfile_mono (hp : 2 ≤ p) (hk : 0 ≤ k) : Monotone (lpProfile p k) :=
  monotone_of_deriv_nonneg ((contDiff_lpProfile hp).differentiable one_ne_zero) fun t => by
    rw [deriv_lpProfile hp]; exact lpProfileDeriv_nonneg hp hk t

private theorem integral_mul_rpow_sub_two (hp : 2 ≤ p) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (p - 1) * s ^ (p - 2) = t ^ (p - 1) := by
  have hp1 : p - 1 ≠ 0 := by linarith
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    show p - 2 + 1 = p - 1 by ring, Real.zero_rpow hp1]
  field_simp
  ring

/-- Below the truncation level the profile is the power `t^{p-1}`. -/
private theorem lpProfile_eq_rpow (hp : 2 ≤ p) {t : ℝ} (ht : 0 ≤ t) (htk : t ≤ k) :
    lpProfile p k t = t ^ (p - 1) := by
  have h : ∫ s in (0 : ℝ)..t, lpProfileDeriv p k s = ∫ s in (0 : ℝ)..t, (p - 1) * s ^ (p - 2) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    simp only [lpProfileDeriv, abs_of_nonneg hs.1, min_eq_left (hs.2.trans htk)]
  rw [lpProfile, h, integral_mul_rpow_sub_two hp]

/-- The profile lies below the power `t^{p-1}`. -/
private theorem lpProfile_le_rpow (hp : 2 ≤ p) (hk : 0 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    lpProfile p k t ≤ t ^ (p - 1) := by
  rw [← integral_mul_rpow_sub_two hp, lpProfile]
  refine intervalIntegral.integral_mono_on ht
    ((continuous_lpProfileDeriv hp).intervalIntegrable _ _)
    ((continuous_const.mul (Real.continuous_rpow_const (by linarith))).intervalIntegrable _ _)
    fun s hs => ?_
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_min (abs_nonneg s) hk) ?_
    (by linarith)) (by linarith)
  rw [abs_of_nonneg hs.1]
  exact min_le_left _ _

private theorem lpProfile_abs (hp : 2 ≤ p) (hk : 0 ≤ k) (t : ℝ) :
    lpProfile p k |t| = |lpProfile p k t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (lpProfile_nonneg hp hk ht)]
  · have h := lpProfile_nonneg hp hk (neg_nonneg.2 ht)
    rw [lpProfile_neg] at h
    rw [abs_of_nonpos ht, abs_of_nonpos (neg_nonneg.1 h), lpProfile_neg]

private theorem mul_lpProfile_abs (t : ℝ) : t * lpProfile p k t = |t| * lpProfile p k |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, lpProfile_neg]
    ring

/-- `min(|t|, k)^p ≤ t φ(t)`: the tested quantity controls the truncated `p`-th power. -/
private theorem min_rpow_le_mul_lpProfile (hp : 2 ≤ p) (hk : 0 ≤ k) (t : ℝ) :
    min |t| k ^ p ≤ t * lpProfile p k t := by
  rw [mul_lpProfile_abs]
  set s := |t|
  have hs : 0 ≤ s := abs_nonneg t
  have hpow (x : ℝ) (hx : 0 ≤ x) : x * x ^ (p - 1) = x ^ p := by
    rw [← Real.rpow_one_add' hx (by linarith)]
    ring_nf
  rcases le_total s k with hsk | hks
  · rw [min_eq_left hsk, lpProfile_eq_rpow hp hs hsk, hpow s hs]
  · rw [min_eq_right hks, ← hpow k hk]
    have hφ : k ^ (p - 1) ≤ lpProfile p k s := by
      rw [← lpProfile_eq_rpow hp hk le_rfl]
      exact lpProfile_mono hp hk hks
    exact mul_le_mul hks hφ (Real.rpow_nonneg hk _) hs

private theorem mul_lpProfile_nonneg (hp : 2 ≤ p) (hk : 0 ≤ k) (t : ℝ) :
    0 ≤ t * lpProfile p k t :=
  (min_rpow_le_mul_lpProfile hp hk t).trans' (Real.rpow_nonneg (le_min (abs_nonneg t) hk) _)

/-- `|φ(t)|^{p/(p-1)} ≤ t φ(t)`, the bound used for the Hölder pairing with the datum. -/
private theorem abs_lpProfile_rpow_le (hp : 2 ≤ p) (hk : 0 ≤ k) (t : ℝ) :
    |lpProfile p k t| ^ (p / (p - 1)) ≤ t * lpProfile p k t := by
  rw [mul_lpProfile_abs, ← lpProfile_abs hp hk]
  set s := |t|
  have hs : 0 ≤ s := abs_nonneg t
  have hφ0 := lpProfile_nonneg hp hk hs
  have hp1 : p - 1 ≠ 0 := by linarith
  have hsplit : p / (p - 1) = 1 + (p - 1)⁻¹ := by field_simp; ring
  have hpos : 0 < 1 + (p - 1)⁻¹ := by
    have : 0 < (p - 1)⁻¹ := inv_pos.2 (by linarith)
    linarith
  rw [hsplit, Real.rpow_add' hφ0 hpos.ne', Real.rpow_one, mul_comm s]
  refine mul_le_mul_of_nonneg_left ?_ hφ0
  calc lpProfile p k s ^ (p - 1)⁻¹ ≤ (s ^ (p - 1)) ^ (p - 1)⁻¹ :=
        Real.rpow_le_rpow hφ0 (lpProfile_le_rpow hp hk hs) (inv_nonneg.2 (by linarith))
    _ = s := Real.rpow_rpow_inv hs hp1

/-- `φ'(t)^{p/(p-2)} ≤ (p - 1)^{p/(p-2)} t φ(t)` for `p > 2`, the bound used for the Hölder
pairing with the divergence datum. -/
private theorem lpProfileDeriv_rpow_le (hp : 2 < p) (hk : 0 ≤ k) (t : ℝ) :
    lpProfileDeriv p k t ^ (p / (p - 2)) ≤ (p - 1) ^ (p / (p - 2)) * (t * lpProfile p k t) := by
  have hm : 0 ≤ min |t| k := le_min (abs_nonneg t) hk
  rw [lpProfileDeriv, Real.mul_rpow (by linarith) (Real.rpow_nonneg hm _), ← Real.rpow_mul hm,
    show (p - 2) * (p / (p - 2)) = p by field_simp]
  exact mul_le_mul_of_nonneg_left (min_rpow_le_mul_lpProfile hp.le hk t)
    (Real.rpow_nonneg (by linarith) _)

/-- The scalar step of the estimate: `κ Z ≤ A Z^{(p-1)/p} + B Z^{(p-2)/p}` forces
`Z^{1/p} ≤ A / κ + √(B / κ)`. With `X = Z^{1/p}` it reads `κ X² ≤ A X + B` after division by
`X^{p-2}`. -/
private theorem rpow_inv_le_of_mul_le (hp : 2 ≤ p) {κ A B Z : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (h : κ * Z ≤ A * Z ^ ((p - 1) / p) + B * Z ^ ((p - 2) / p)) :
    Z ^ p⁻¹ ≤ A / κ + √(B / κ) := by
  have hp0 : p ≠ 0 := by linarith
  set X := Z ^ p⁻¹ with hXdef
  have hX : 0 ≤ X := Real.rpow_nonneg hZ _
  have hs := Real.sqrt_nonneg (B / κ)
  have hAκ : 0 ≤ A / κ := div_nonneg hA hκ.le
  rcases hX.eq_or_lt with hX0 | hXpos
  · rw [← hX0]
    positivity
  have hZX : Z = X ^ p := (Real.rpow_inv_rpow hZ hp0).symm
  have h1 : Z ^ ((p - 1) / p) = X ^ (p - 2) * X := by
    rw [div_eq_inv_mul, Real.rpow_mul hZ, ← hXdef, ← Real.rpow_add_one hXpos.ne']
    ring_nf
  have h2 : Z ^ ((p - 2) / p) = X ^ (p - 2) := by
    rw [div_eq_inv_mul, Real.rpow_mul hZ]
  have h3 : Z = X ^ (p - 2) * X ^ 2 := by
    rw [hZX, ← Real.rpow_natCast, ← Real.rpow_add hXpos]
    norm_num
  rw [h1, h2, h3] at h
  have hXp : 0 < X ^ (p - 2) := Real.rpow_pos_of_pos hXpos _
  have hq : κ * X ^ 2 ≤ A * X + B := by
    have : X ^ (p - 2) * (κ * X ^ 2) ≤ X ^ (p - 2) * (A * X + B) := by nlinarith
    exact le_of_mul_le_mul_left this hXp
  have hss : √(B / κ) ^ 2 = B / κ := Real.sq_sqrt (div_nonneg hB hκ.le)
  have hκs : κ * √(B / κ) ^ 2 = B := by rw [hss]; field_simp
  have hAκ' : κ * (A / κ) = A := by field_simp
  refine le_of_not_gt fun hlt => ?_
  nlinarith [mul_le_mul_of_nonneg_left hlt.le hκ.le, mul_pos hκ hXpos]

private theorem nnnorm_deriv_lpProfile_le (hp : 2 ≤ p) (hk : 0 ≤ k) (t : ℝ) :
    ‖deriv (lpProfile p k) t‖₊ ≤ ((p - 1) * k ^ (p - 2)).toNNReal := by
  have h0 := lpProfileDeriv_nonneg hp hk t
  have h1 := lpProfileDeriv_le hp hk t
  rw [deriv_lpProfile hp, ← NNReal.coe_le_coe, coe_nnNorm, Real.norm_of_nonneg h0,
    Real.coe_toNNReal _ (h0.trans h1)]
  exact h1

/-! ### Hölder's inequality against the truncated power -/

section Holder

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : α → ℝ}

/-- Hölder's inequality with the exponents `p` and `p / (p - 1)`, followed by
`|φ(t)|^{p/(p-1)} ≤ t φ(t)`: `∫ |g| |φ(U)| ≤ ‖g‖_p (∫ U φ(U))^{(p-1)/p}`. -/
private theorem integral_abs_mul_abs_lpProfile_le (hp : 2 ≤ p) (hk : 0 ≤ k)
    (hU : AEStronglyMeasurable U μ) (hUφ : Integrable (fun x => U x * lpProfile p k (U x)) μ)
    {g : α → ℝ} (hg : MemLp g (ENNReal.ofReal p) μ) :
    ∫ x, |g x| * |lpProfile p k (U x)| ∂μ ≤
      (∫ x, |g x| ^ p ∂μ) ^ p⁻¹ * (∫ x, U x * lpProfile p k (U x) ∂μ) ^ ((p - 1) / p) := by
  have hp1 : 0 < p - 1 := by linarith
  have hmeas : AEStronglyMeasurable (fun x => |lpProfile p k (U x)|) μ :=
    continuous_abs.comp_aestronglyMeasurable
      ((contDiff_lpProfile hp).continuous.comp_aestronglyMeasurable hU)
  have hconj : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 rfl
  have hint : Integrable (fun x => |lpProfile p k (U x)| ^ (p / (p - 1))) μ := by
    refine hUφ.mono' (hmeas.aemeasurable.pow_const _).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact abs_lpProfile_rpow_le hp hk _
  have hmem : MemLp (fun x => |lpProfile p k (U x)|) (ENNReal.ofReal (p / (p - 1))) μ :=
    (memLp_ofReal_iff_integrable_norm_rpow (by positivity) hmeas).2
      (by simpa only [Real.norm_eq_abs, abs_abs] using hint)
  calc _ ≤ _ := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
        (Eventually.of_forall fun x => abs_nonneg (g x))
        (Eventually.of_forall fun x => abs_nonneg (lpProfile p k (U x))) hg.abs hmem
    _ = (∫ x, |g x| ^ p ∂μ) ^ p⁻¹ *
        (∫ x, |lpProfile p k (U x)| ^ (p / (p - 1)) ∂μ) ^ ((p - 1) / p) := by
      rw [one_div_div, one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _)
        (integral_mono hint hUφ fun x => abs_lpProfile_rpow_le hp hk _) (by positivity))
        (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _)

/-- `φ'(U)^{p/(p-2)}` is integrable when `U φ(U)` is, for `p > 2`. -/
private theorem integrable_lpProfileDeriv_rpow (hp : 2 < p) (hk : 0 ≤ k)
    (hU : AEStronglyMeasurable U μ) (hUφ : Integrable (fun x => U x * lpProfile p k (U x)) μ) :
    Integrable (fun x => lpProfileDeriv p k (U x) ^ (p / (p - 2))) μ := by
  refine (hUφ.const_mul ((p - 1) ^ (p / (p - 2)))).mono'
    (((continuous_lpProfileDeriv hp.le).comp_aestronglyMeasurable hU).aemeasurable.pow_const
      _).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (lpProfileDeriv_nonneg hp.le hk _) _)]
  exact lpProfileDeriv_rpow_le hp hk _

/-- `(∫ φ'(U)^{p/(p-2)})^{(p-2)/p} ≤ (p - 1) (∫ U φ(U))^{(p-2)/p}` for `p > 2`. -/
private theorem integral_lpProfileDeriv_rpow_rpow_le (hp : 2 < p) (hk : 0 ≤ k)
    (hU : AEStronglyMeasurable U μ) (hUφ : Integrable (fun x => U x * lpProfile p k (U x)) μ) :
    (∫ x, lpProfileDeriv p k (U x) ^ (p / (p - 2)) ∂μ) ^ (1 / (p / (p - 2))) ≤
      (p - 1) * (∫ x, U x * lpProfile p k (U x) ∂μ) ^ ((p - 2) / p) := by
  have hp1 : 0 < p - 1 := by linarith
  have hZ : 0 ≤ ∫ x, U x * lpProfile p k (U x) ∂μ :=
    integral_nonneg fun x => mul_lpProfile_nonneg hp.le hk _
  calc _ ≤ ((p - 1) ^ (p / (p - 2)) * ∫ x, U x * lpProfile p k (U x) ∂μ) ^
        (1 / (p / (p - 2))) := by
        refine Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg
          (lpProfileDeriv_nonneg hp.le hk _) _) ?_ (by positivity)
        rw [← integral_const_mul]
        exact integral_mono (integrable_lpProfileDeriv_rpow hp hk hU hUφ) (hUφ.const_mul _)
          fun x => lpProfileDeriv_rpow_le hp hk _
    _ = _ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hp1.le _) hZ, ← Real.rpow_mul hp1.le, one_div_div,
          show p / (p - 2) * ((p - 2) / p) = 1 by field_simp, Real.rpow_one]

/-- `(∫ (‖G‖²)^{p/2})^{2/p} = ‖G‖_p²`, the `L^{p/2}` norm of `‖G‖²`. -/
private theorem integral_norm_sq_rpow_rpow_eq {F : Type*} [NormedAddCommGroup F] (G : α → F) :
    (∫ x, (‖G x‖ ^ 2) ^ (p / 2) ∂μ) ^ (1 / (p / 2)) = ((∫ x, ‖G x‖ ^ p ∂μ) ^ p⁻¹) ^ 2 := by
  have hint : ∫ x, (‖G x‖ ^ 2) ^ (p / 2) ∂μ = ∫ x, ‖G x‖ ^ p ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => by
      beta_reduce
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_ofNat,
        mul_div_cancel₀ p two_ne_zero])
  rw [hint, ← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg
    (norm_nonneg _) _), Nat.cast_ofNat, one_div_div, inv_mul_eq_div]

/-- Hölder's inequality with the exponents `p / 2` and `p / (p - 2)`, followed by
`φ'(t)^{p/(p-2)} ≤ (p - 1)^{p/(p-2)} t φ(t)`:
`∫ φ'(U) ‖G‖² ≤ (p - 1) ‖G‖_p² (∫ U φ(U))^{(p-2)/p}`. For `p = 2` it is the identity `φ' = 1`. -/
private theorem integral_lpProfileDeriv_mul_sq_le (hp : 2 ≤ p) (hk : 0 ≤ k)
    (hU : AEStronglyMeasurable U μ) (hUφ : Integrable (fun x => U x * lpProfile p k (U x)) μ)
    {F : Type*} [NormedAddCommGroup F] {G : α → F} (hG : MemLp G (ENNReal.ofReal p) μ) :
    ∫ x, lpProfileDeriv p k (U x) * ‖G x‖ ^ 2 ∂μ ≤
      (p - 1) * ((∫ x, ‖G x‖ ^ p ∂μ) ^ p⁻¹) ^ 2 *
        (∫ x, U x * lpProfile p k (U x) ∂μ) ^ ((p - 2) / p) := by
  have hp0 : 0 < p := by linarith
  have hGmem : MemLp (fun x => ‖G x‖ ^ 2) (ENNReal.ofReal (p / 2)) μ := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hG.norm_rpow_div 2
  have hfirst := integral_norm_sq_rpow_rpow_eq (p := p) (μ := μ) G
  rcases hp.eq_or_lt with rfl | hp2
  · have h1 (s : ℝ) : lpProfileDeriv 2 k s = 1 := by norm_num [lpProfileDeriv]
    simp only [h1, one_mul, sub_self, zero_div, Real.rpow_zero, mul_one]
    rw [← hfirst]
    norm_num
  have hconj : (p / 2).HolderConjugate (p / (p - 2)) :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 (by field_simp)
  have hmeas : AEStronglyMeasurable (fun x => lpProfileDeriv p k (U x)) μ :=
    (continuous_lpProfileDeriv hp).comp_aestronglyMeasurable hU
  have hdmem : MemLp (fun x => lpProfileDeriv p k (U x)) (ENNReal.ofReal (p / (p - 2))) μ :=
    (memLp_ofReal_iff_integrable_norm_rpow (div_pos hp0 (by linarith)) hmeas).2
      (by simpa only [Real.norm_of_nonneg (lpProfileDeriv_nonneg hp hk _)] using
        integrable_lpProfileDeriv_rpow hp2 hk hU hUφ)
  calc ∫ x, lpProfileDeriv p k (U x) * ‖G x‖ ^ 2 ∂μ
      = ∫ x, ‖G x‖ ^ 2 * lpProfileDeriv p k (U x) ∂μ := by simp only [mul_comm]
    _ ≤ _ := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
        (Eventually.of_forall fun x => sq_nonneg ‖G x‖)
        (Eventually.of_forall fun x => lpProfileDeriv_nonneg hp hk (U x)) hGmem hdmem
    _ ≤ ((∫ x, ‖G x‖ ^ p ∂μ) ^ p⁻¹) ^ 2 *
        ((p - 1) * (∫ x, U x * lpProfile p k (U x) ∂μ) ^ ((p - 2) / p)) := by
      rw [hfirst]
      exact mul_le_mul_of_nonneg_left (integral_lpProfileDeriv_rpow_rpow_le hp2 hk hU hUφ)
        (sq_nonneg _)
    _ = _ := by ring

/-- `φ'(U) ‖G‖²` is integrable for `G ∈ L²`, since `φ'` is bounded. -/
private theorem integrable_lpProfileDeriv_mul_sq (hp : 2 ≤ p) (hk : 0 ≤ k)
    (hU : AEStronglyMeasurable U μ) {F : Type*} [NormedAddCommGroup F] {G : α → F}
    (hG : MemLp G 2 μ) :
    Integrable (fun x => lpProfileDeriv p k (U x) * ‖G x‖ ^ 2) μ := by
  refine ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG).bdd_mul
    (c := (p - 1) * k ^ (p - 2)) ((continuous_lpProfileDeriv hp).comp_aestronglyMeasurable hU)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (lpProfileDeriv_nonneg hp hk _)]
  exact lpProfileDeriv_le hp hk _

/-- A bound on `(∫ U φ(U))^{1/p}` bounds `‖min(|U|, k)‖_p`, since `min(|t|, k)^p ≤ t φ(t)`. -/
private theorem eLpNorm_min_abs_le (hp : 2 ≤ p) (hk : 0 ≤ k) (hU : AEStronglyMeasurable U μ)
    (hUφ : Integrable (fun x => U x * lpProfile p k (U x)) μ) {R : ℝ}
    (hR : (∫ x, U x * lpProfile p k (U x) ∂μ) ^ p⁻¹ ≤ R) :
    eLpNorm (fun x => min |U x| k) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R := by
  have hp0 : 0 < p := by linarith
  have hmeas : AEStronglyMeasurable (fun x => min |U x| k) μ :=
    (continuous_abs.min continuous_const).comp_aestronglyMeasurable hU
  have hint : Integrable (fun x => ‖min |U x| k‖ ^ p) μ :=
    hUφ.mono' (hmeas.norm.aemeasurable.pow_const _).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
          Real.norm_of_nonneg (le_min (abs_nonneg _) hk)]
        exact min_rpow_le_mul_lpProfile hp hk _)
  have hmem : MemLp (fun x => min |U x| k) (ENNReal.ofReal p) μ :=
    (memLp_ofReal_iff_integrable_norm_rpow hp0 hmeas).2 hint
  rw [hmem.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  refine ENNReal.ofReal_le_ofReal (le_trans (Real.rpow_le_rpow (integral_nonneg fun x =>
    Real.rpow_nonneg (norm_nonneg _) _) (integral_mono hint hUφ fun x => ?_)
    (inv_nonneg.2 hp0.le)) hR)
  rw [Real.norm_of_nonneg (le_min (abs_nonneg _) hk)]
  exact min_rpow_le_mul_lpProfile hp hk _

end Holder

/-! ### The truncated power of a Sobolev function -/

section Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}

/-- The truncated power `φ(u)` of `u ∈ H¹(Ω)`, with value `φ ∘ u` and gradient `φ'(u) ∇u`. -/
private def lpProfileComp (hp : 2 ≤ p) (hk : 0 ≤ k) (u : W1p mu Omega 2) : W1p mu Omega 2 :=
  W1p.contDiffComp ENNReal.ofNat_ne_top (contDiff_lpProfile hp) (nnnorm_deriv_lpProfile_le hp hk)
    lpProfile_zero u

private theorem value_lpProfileComp_ae (hp : 2 ≤ p) (hk : 0 ≤ k) (u : W1p mu Omega 2) :
    ⇑(W1p.value (lpProfileComp hp hk u)) =ᵐ[mu.restrict Omega]
      fun x => lpProfile p k (W1p.value u x) :=
  W1p.value_contDiffComp_ae _ _ _ _ u

private theorem gradient_lpProfileComp_ae (hp : 2 ≤ p) (hk : 0 ≤ k) (u : W1p mu Omega 2) :
    ⇑(W1p.gradient (lpProfileComp hp hk u)) =ᵐ[mu.restrict Omega]
      fun x => lpProfileDeriv p k (W1p.value u x) • W1p.gradient u x := by
  have h := W1p.gradient_contDiffComp_ae ENNReal.ofNat_ne_top (contDiff_lpProfile hp)
    (nnnorm_deriv_lpProfile_le hp hk) lpProfile_zero u
  rw [deriv_lpProfile hp] at h
  exact h

/-- `u φ(u)` is integrable for `u ∈ H¹(Ω)`: both factors lie in `L²(Ω)`. -/
private theorem integrable_mul_lpProfile (hp : 2 ≤ p) (hk : 0 ≤ k) (u : W1p mu Omega 2) :
    Integrable (fun x => W1p.value u x * lpProfile p k (W1p.value u x)) (mu.restrict Omega) := by
  refine ((Lp.memLp (W1p.value u)).integrable_mul
    (Lp.memLp (W1p.value (lpProfileComp hp hk u)))).congr ?_
  filter_upwards [value_lpProfileComp_ae hp hk u] with x hx
  simp only [Pi.mul_apply, hx]

end Sobolev

/-! ### Testing the equation against the truncated power -/

section Estimate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma kappa : ℝ}

omit [DecidableEq ι] in
/-- The pointwise form of the tested equation. At a point where `u = t`, `∇u = g`, `f = s` and
`F = G`, with `φ = φ(t)` and `d = φ'(t) ≥ 0`, the energy density of `(u, φ(u))` minus the forcing
density dominates `κ t φ - |s| |φ| - d ‖G‖² / (4λ)`: the principal part gives `d λ ‖g‖²`, which
absorbs `d ⟪G, g⟫` up to `d ‖G‖² / (4λ)`. -/
private theorem mul_mul_lpProfile_le (hp : 2 ≤ p) (hk : 0 ≤ k) {A : Matrix ι ι ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm A ξ ξ) {γ : ℝ} (hγ : kappa ≤ γ) (t s : ℝ)
    (g G : EuclideanSpace ℝ ι) :
    kappa * (t * lpProfile p k t) ≤
      energyIntegrand A 0 γ (t, g) (lpProfile p k t, lpProfileDeriv p k t • g) -
        (s * lpProfile p k t - ⟪G, lpProfileDeriv p k t • g⟫_ℝ) +
        |s| * |lpProfile p k t| + (4 * lam)⁻¹ * (lpProfileDeriv p k t * ‖G‖ ^ 2) := by
  set φ := lpProfile p k t
  set d := lpProfileDeriv p k t
  have hd : 0 ≤ d := lpProfileDeriv_nonneg hp hk t
  have htφ : 0 ≤ t * φ := mul_lpProfile_nonneg hp hk t
  have hQ := hA g
  have hGg : -(‖G‖ * ‖g‖) ≤ ⟪G, g⟫_ℝ := neg_le_of_abs_le (abs_real_inner_le_norm G g)
  have hsφ' : s * φ ≤ |s| * |φ| := by rw [← abs_mul]; exact le_abs_self _
  simp only [energyIntegrand_apply, map_smul, smul_apply, smul_eq_mul,
    driftForm_apply, inner_zero_left, zero_mul, add_zero, massForm_apply, real_inner_smul_right]
  have hsq : 0 ≤ d * (lam * ‖g‖ ^ 2) - d * (‖G‖ * ‖g‖) + (4 * lam)⁻¹ * (d * ‖G‖ ^ 2) := by
    have h : d * (lam * ‖g‖ ^ 2) - d * (‖G‖ * ‖g‖) + (4 * lam)⁻¹ * (d * ‖G‖ ^ 2) =
        (4 * lam)⁻¹ * (d * (2 * lam * ‖g‖ - ‖G‖) ^ 2) := by
      field_simp
      ring
    rw [h]
    positivity
  have hκ : kappa * (t * φ) ≤ γ * t * φ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hγ htφ
  linarith [mul_le_mul_of_nonneg_left hQ hd, mul_le_mul_of_nonneg_left hGg hd]

/-- **The tested equation.** For a weak solution `u ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f + div F`
with `c ≥ κ`, testing against `φ(u) ∈ H¹₀(Ω)` gives

`κ ∫_Ω u φ(u) ≤ ∫_Ω |f| |φ(u)| + (4λ)⁻¹ ∫_Ω φ'(u) ‖F‖²`. -/
private theorem mul_integral_mul_lpProfile_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ᵐ x ∂mu.restrict Omega, kappa ≤ c x)
    (hp : 2 ≤ p) (hk : 0 ≤ k) {f : Lp ℝ 2 (mu.restrict Omega)}
    {F : Lp (EuclideanSpace ℝ ι) 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        dirichletForcing f v + divergenceForcing F v) :
    kappa * ∫ x in Omega, W1p.value (u : W1p mu Omega 2) x *
        lpProfile p k (W1p.value (u : W1p mu Omega 2) x) ∂mu ≤
      ∫ x in Omega, |f x| * |lpProfile p k (W1p.value (u : W1p mu Omega 2) x)| ∂mu +
        (4 * lam)⁻¹ * ∫ x in Omega,
          lpProfileDeriv p k (W1p.value (u : W1p mu Omega 2) x) * ‖F x‖ ^ 2 ∂mu := by
  set w : W1p mu Omega 2 := (u : W1p mu Omega 2)
  set z : W1p mu Omega 2 := lpProfileComp hp hk w
  have heq := hu ⟨z, W1p.contDiffComp_mem_w1p0Submodule _ _ _ _ u.property⟩
  rw [energyFormH1_def, dirichletForcing_apply_eq_setIntegral,
    divergenceForcing_apply_eq_neg_setIntegral] at heq
  have hval : ⇑(W1p.value z) =ᵐ[mu.restrict Omega] fun x => lpProfile p k (W1p.value w x) :=
    value_lpProfileComp_ae hp hk w
  have hgrad : ⇑(W1p.gradient z) =ᵐ[mu.restrict Omega]
      fun x => lpProfileDeriv p k (W1p.value w x) • W1p.gradient w x :=
    gradient_lpProfileComp_ae hp hk w
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (beta := 0) ha
    aestronglyMeasurable_const hc (fun _ _ => by simp) hc_bound w z
  have hRf : Integrable (fun x => f x * W1p.value z x) (mu.restrict Omega) :=
    (Lp.memLp f).integrable_mul (Lp.memLp (W1p.value z))
  have hRF : Integrable (fun x => ⟪F x, W1p.gradient z x⟫_ℝ) (mu.restrict Omega) :=
    L2.integrable_inner F (W1p.gradient z)
  have hP1 := integrable_mul_lpProfile hp hk w
  have hP2 : Integrable (fun x => |f x| * |lpProfile p k (W1p.value w x)|)
      (mu.restrict Omega) := by
    refine hRf.norm.congr ?_
    filter_upwards [hval] with x hx
    simp only [hx, Real.norm_eq_abs, abs_mul]
  have hP3 := integrable_lpProfileDeriv_mul_sq hp hk (Lp.aestronglyMeasurable (W1p.value w))
    (Lp.memLp F)
  have hRfF : Integrable (fun x => f x * W1p.value z x - ⟪F x, W1p.gradient z x⟫_ℝ)
      (mu.restrict Omega) := hRf.sub hRF
  have hER : Integrable (fun x => energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι) x) (c x) (jetField w x) (jetField z x) -
        (f x * W1p.value z x - ⟪F x, W1p.gradient z x⟫_ℝ)) (mu.restrict Omega) := hE.sub hRfF
  have hERP : Integrable (fun x => energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι) x) (c x) (jetField w x) (jetField z x) -
        (f x * W1p.value z x - ⟪F x, W1p.gradient z x⟫_ℝ) +
          |f x| * |lpProfile p k (W1p.value w x)|) (mu.restrict Omega) := hER.add hP2
  have hP3' : Integrable (fun x => (4 * lam)⁻¹ *
      (lpProfileDeriv p k (W1p.value w x) * ‖F x‖ ^ 2)) (mu.restrict Omega) :=
    hP3.const_mul _
  have hmono := integral_mono_ae (hP1.const_mul kappa) (hERP.add hP3') (by
      filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet, hval, hgrad, hc_lower]
        with x hx hvx hgx hcx
      simp only [Pi.add_apply, jetField_apply, hvx, hgx, Pi.zero_apply]
      exact mul_mul_lpProfile_le (A := a x) hp hk h.pos
        (fun ξ => by rw [matrixBilinearForm_self]; exact h.lower_bound hx ξ) hcx _ _
        _ _)
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul, integral_add hERP hP3', integral_add hER hP2, integral_sub hE hRfF,
    integral_sub hRf hRF, integral_const_mul] at hmono
  linarith

/-- **The estimate at a fixed truncation level.** For data in `Lᵖ`, the truncation
`min(|u|, k)` of a weak solution satisfies
`‖min(|u|, k)‖_p ≤ κ⁻¹ ‖f‖_p + √((p - 1) / (4λκ)) ‖F‖_p`, a bound independent of `k`. -/
private theorem eLpNorm_min_abs_value_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ᵐ x ∂mu.restrict Omega, kappa ≤ c x) (hkappa : 0 < kappa)
    (hp : 2 ≤ p) (hk : 0 ≤ k) {f : Lp ℝ 2 (mu.restrict Omega)}
    {F : Lp (EuclideanSpace ℝ ι) 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        dirichletForcing f v + divergenceForcing F v)
    (hfp : MemLp f (ENNReal.ofReal p) (mu.restrict Omega))
    (hFp : MemLp F (ENNReal.ofReal p) (mu.restrict Omega)) :
    eLpNorm (fun x => min |W1p.value (u : W1p mu Omega 2) x| k) (ENNReal.ofReal p)
        (mu.restrict Omega) ≤
      ENNReal.ofReal (kappa⁻¹ * (∫ x in Omega, |f x| ^ p ∂mu) ^ p⁻¹ +
        √((p - 1) / (4 * lam * kappa)) * (∫ x in Omega, ‖F x‖ ^ p ∂mu) ^ p⁻¹) := by
  set w : W1p mu Omega 2 := (u : W1p mu Omega 2)
  have hlam := h.pos
  have hp1 : 0 < p - 1 := by linarith
  have hmeasU : AEStronglyMeasurable (fun x => W1p.value w x) (mu.restrict Omega) :=
    Lp.aestronglyMeasurable _
  have hP1 := integrable_mul_lpProfile hp hk w
  set Z := ∫ x in Omega, W1p.value w x * lpProfile p k (W1p.value w x) ∂mu
  have hZ : 0 ≤ Z := integral_nonneg fun x => mul_lpProfile_nonneg hp hk _
  set A := (∫ x in Omega, |f x| ^ p ∂mu) ^ p⁻¹
  set N := (∫ x in Omega, ‖F x‖ ^ p ∂mu) ^ p⁻¹
  have hA : 0 ≤ A := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg
    (abs_nonneg _) _) _
  have hN : 0 ≤ N := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg
    (norm_nonneg _) _) _
  have hI1 := integral_abs_mul_abs_lpProfile_le hp hk hmeasU hP1 hfp
  have hI2 := integral_lpProfileDeriv_mul_sq_le hp hk hmeasU hP1 hFp
  -- The scalar inequality.
  have htest := mul_integral_mul_lpProfile_le h ha hc hc_bound hc_lower hp hk hu
  have hB : 0 ≤ (p - 1) * N ^ 2 / (4 * lam) := by positivity
  have hkey : kappa * Z ≤ A * Z ^ ((p - 1) / p) +
      (p - 1) * N ^ 2 / (4 * lam) * Z ^ ((p - 2) / p) := by
    have h4 : (4 * lam)⁻¹ * ((p - 1) * N ^ 2 * Z ^ ((p - 2) / p)) =
        (p - 1) * N ^ 2 / (4 * lam) * Z ^ ((p - 2) / p) := by ring
    rw [← h4]
    exact htest.trans (add_le_add hI1 (mul_le_mul_of_nonneg_left hI2 (by positivity)))
  have hroot := rpow_inv_le_of_mul_le hp hkappa hA hB hZ hkey
  have hsqrt : √((p - 1) * N ^ 2 / (4 * lam) / kappa) = √((p - 1) / (4 * lam * kappa)) * N := by
    rw [show (p - 1) * N ^ 2 / (4 * lam) / kappa = (p - 1) / (4 * lam * kappa) * N ^ 2 by
      field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hN]
  rw [hsqrt, div_eq_inv_mul] at hroot
  exact eLpNorm_min_abs_le hp hk hmeasU hP1 hroot

/-- **The `Lᵖ` bound for the Dirichlet problem with a zero-order term bounded below.** Let `a` be
measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ` with lower constant `λ`, not
necessarily symmetric, let `c` be measurable and bounded with `c ≥ κ > 0` a.e. on `Ω`, and let
`u ∈ H¹₀(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f + div F` in `Ω`, `u = 0` on `∂Ω`,

with `f ∈ L²(Ω)` and `F ∈ L²(Ω; ℝⁿ)`. Then for every `2 ≤ p < ∞`

`‖u‖_{Lᵖ(Ω)} ≤ κ⁻¹ ‖f‖_{Lᵖ(Ω)} + √((p - 1) / (4λκ)) ‖F‖_{Lᵖ(Ω)}`.

No a priori integrability of `u` beyond `L²` is assumed, no regularity or boundedness of `Ω` and
no regularity of `a`; the right side is infinite unless `f, F ∈ Lᵖ`. For a constant shift
`c = κ` this is `√κ ‖u‖_p ≤ κ^{-1/2} ‖f‖_p + √((p - 1) / (4λ)) ‖F‖_p`, the zero-order part of
Krylov's whole-space estimate for divergence-form equations. -/
theorem UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ᵐ x ∂mu.restrict Omega, kappa ≤ c x) (hkappa : 0 < kappa)
    {q : ℝ≥0∞} (hq : 2 ≤ q) (hq_top : q ≠ ∞) {f : Lp ℝ 2 (mu.restrict Omega)}
    {F : Lp (EuclideanSpace ℝ ι) 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        dirichletForcing f v + divergenceForcing F v) :
    eLpNorm (W1p.value (u : W1p mu Omega 2)) q (mu.restrict Omega) ≤
      ENNReal.ofReal kappa⁻¹ * eLpNorm f q (mu.restrict Omega) +
        ENNReal.ofReal √((q.toReal - 1) / (4 * lam * kappa)) *
          eLpNorm F q (mu.restrict Omega) := by
  have hlam := h.pos
  have hp : 2 ≤ q.toReal := by
    simpa using ENNReal.toReal_mono hq_top hq
  have hq0 : q ≠ 0 := by
    intro h0
    simp [h0] at hq
  have hqp : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hq_top).symm
  have hs : 0 < √((q.toReal - 1) / (4 * lam * kappa)) :=
    Real.sqrt_pos.2 (div_pos (by linarith) (by positivity))
  by_cases hf : eLpNorm f q (mu.restrict Omega) = ∞
  · rw [hf, ENNReal.mul_top (by simpa using hkappa), top_add]
    exact le_top
  by_cases hF : eLpNorm F q (mu.restrict Omega) = ∞
  · rw [hF, ENNReal.mul_top (by simpa using hs), add_top]
    exact le_top
  have hfq : MemLp f q (mu.restrict Omega) := memLp_iff.2 (Ne.lt_top hf)
  have hFq : MemLp F q (mu.restrict Omega) := memLp_iff.2 (Ne.lt_top hF)
  have hbound (n : ℕ) := eLpNorm_min_abs_value_le (k := n) h ha hc hc_bound hc_lower hkappa hp
    n.cast_nonneg hu (hqp ▸ hfq) (hqp ▸ hFq)
  rw [← hqp] at hbound
  have hlim := Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hbound)
    (fun n => ((continuous_abs.min continuous_const).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (W1p.value (u : W1p mu Omega 2)))))
    (Lp.aestronglyMeasurable (W1p.value (u : W1p mu Omega 2))).norm
    (Eventually.of_forall fun x => tendsto_atTop_of_eventually_const (i₀ := ⌈|W1p.value
      (u : W1p mu Omega 2) x|⌉₊) fun n hn => by
        rw [Real.norm_eq_abs, min_eq_left (Nat.ceil_le.1 hn)])
  rw [eLpNorm_norm _ (Lp.aestronglyMeasurable _)] at hlim
  refine hlim.trans_eq ?_
  rw [hfq.eLpNorm_eq_integral_rpow_norm hq0 hq_top, hFq.eLpNorm_eq_integral_rpow_norm hq0 hq_top,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hkappa.le), ← ENNReal.ofReal_mul hs.le,
    ← ENNReal.ofReal_add (mul_nonneg (inv_nonneg.2 hkappa.le) (Real.rpow_nonneg
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _))
      (mul_nonneg hs.le (Real.rpow_nonneg
        (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _))]
  simp only [Real.norm_eq_abs]

/-- **The `Lᵖ` bound for the Dirichlet problem without divergence datum.** Under the hypotheses
of `TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq`, a weak solution
`u ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f` with `c ≥ κ > 0` satisfies
`‖u‖_{Lᵖ(Ω)} ≤ κ⁻¹ ‖f‖_{Lᵖ(Ω)}` for every `2 ≤ p < ∞`. -/
theorem UniformlyEllipticOn.eLpNorm_value_le_of_isWeakSolutionDirichlet
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ᵐ x ∂mu.restrict Omega, kappa ≤ c x) (hkappa : 0 < kappa)
    {q : ℝ≥0∞} (hq : 2 ≤ q) (hq_top : q ≠ ∞) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} (hu : IsWeakSolutionDirichlet a 0 c f u) :
    eLpNorm (W1p.value (u : W1p mu Omega 2)) q (mu.restrict Omega) ≤
      ENNReal.ofReal kappa⁻¹ * eLpNorm f q (mu.restrict Omega) := by
  have h0 := h.eLpNorm_value_le_of_forall_energyFormH1_eq ha hc hc_bound hc_lower hkappa hq
    hq_top (f := f) (F := 0) fun v => by
      rw [(isWeakSolutionDirichlet_iff f u).1 hu v, divergenceForcing_apply, inner_zero_left,
        neg_zero, add_zero, dirichletForcing_apply_eq_setIntegral]
  rwa [eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero, mul_zero, add_zero] at h0

end Estimate

end PDE

end TauCeti
