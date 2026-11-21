/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Integral.Dilation

/-!
# Morrey spaces

Let `μ` be a measure on a metric space and `Ω` a set. For exponents `p` and `λ`, the
**Morrey norm** of `f` on `Ω` is

`‖f‖_{L^{p,λ}(Ω)} = (sup_{x ∈ Ω, r > 0} r^(-λ) ∫_{B(x, r) ∩ Ω} ‖f‖^p)^(1/p)`,

and the Morrey space `L^{p,λ}(Ω)` consists of the functions for which it is finite. As for the
Campanato seminorm `TauCeti.MeasureTheory.campanatoSeminormPow`, and following
Giaquinta–Martinazzi, the declaration `TauCeti.MeasureTheory.morreyNormPow` is the `p`-th power
`‖f‖_{L^{p,λ}(Ω)}^p`, the supremum itself, without the `p`-th root.

For a Haar measure in dimension `n`, the Morrey condition with `λ = n` says that `‖f‖^p` has
bounded averages on balls, so it is implied by `f ∈ L^∞`, and on a nonempty set the condition with
`λ = 0` says that `f ∈ Lᵖ(Ω)`. In between, the Morrey spaces measure how fast the mass of `‖f‖^p`
on small balls decays. They serve as spaces of data and lower-order coefficients for elliptic
equations: Morrey's `C^{1,α}` estimates for divergence-form equations admit zero-order
coefficients and data in `L^{1, n - 1 + α}`, `0 < α < 1`, a class that contains `L^q` for
`q = n / (1 - α)` by Hölder's inequality. This is the class of zero-order coefficients in Rosales'
divergence-form Hopf lemma, where the Morrey space `L^{1,α}(U)` of the paper is
`L^{1, n - 1 + α}(U)` here, with centres in the whole space rather than in `U`.

## Main declarations

All declarations are in the `TauCeti.MeasureTheory` namespace.

* `morreyNormPow`: the `p`-th power `‖f‖_{L^{p,λ}(Ω)}^p` of the Morrey norm on a set.
* `morreyNormPow_le_iff`, `le_morreyNormPow`: the characterization of upper bounds.
* `setLIntegral_closedBall_le_morreyNormPow`: the Morrey norm also controls the balls centred
  outside `Ω`, at the cost of a factor `2^λ` for `λ ≥ 0`. So the Morrey norms defined with all
  centres in the ambient space, as in Rosales' paper, and with centres in `Ω` are equivalent.
* `morreyNormPow_mono_set`, `morreyNormPow_smul`, `morreyNormPow_add_rpow_le`: monotonicity in the
  set, homogeneity, and for `p ≥ 1` the triangle inequality for the Morrey norm itself.
* `morreyNormPow_le_eLpNorm_rpow_mul`: **Hölder's inequality** `L^q ⊆ L^{p, n (1 - p / q)}` for
  `0 < p ≤ q < ∞` on a finite-dimensional space with a Haar measure, with an explicit constant. For
  `p = 1` and `q > n` this is `L^q ⊆ L^{1, n - 1 + α}` with `α = 1 - n / q`.
* `morreyNormPow_comp_add_smul`: **scaling**. Under the affine change of variables
  `y ↦ x₀ + ε y`, `ε > 0`, the Morrey norm is multiplied by `ε^(λ - n)`. This is how a coefficient
  in a Morrey space behaves under the blow-up of an equation at a boundary point.
* `morreyNormPow_one_convolution_le`: convolution with an integrable kernel does not leave
  `L^{1,λ}`: the Morrey norm of the convolution is at most `2^λ ‖v‖_{L¹}` times the Morrey norm of
  the function. This is the mollification step of the existence theory for equations with
  coefficients in Morrey spaces.

## References

* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Springer, 1966, §3.5.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Definition 5.1.
* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. (2019),
  arXiv:1806.07003, Definition 2.1, Remark 2.2, Lemma 2.7 and estimate (4.4).
-/

public section

noncomputable section

open Metric Set MeasureTheory Module
open scoped ENNReal Convolution

namespace TauCeti

namespace MeasureTheory

/-- The cancellation `r^a r^b = r^(a + b)` behind each rescaling of a radius in this file, with
the factors already in `ℝ≥0∞`. -/
private theorem ofReal_rpow_mul_ofReal_rpow {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    ENNReal.ofReal (r ^ a) * ENNReal.ofReal (r ^ b) = ENNReal.ofReal (r ^ (a + b)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hr]

section Basic

variable {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [NormedAddCommGroup F]
  {μ : Measure X} {Ω Ω' : Set X} {p lam : ℝ} {f g : X → F} {x : X} {r : ℝ}

variable (μ Ω p lam f) in
/-- The `p`-th power `‖f‖_{L^{p,λ}(Ω)}^p` of the **Morrey norm** of `f` on `Ω` with exponents `p`
and `λ`: the supremum, over the points `x ∈ Ω` and the radii `r > 0`, of

`r^(-λ) ∫_{B(x, r) ∩ Ω} ‖f‖^p`,

where `B(x, r)` is the closed ball and the integral is taken for `μ.restrict Ω`. Following
Giaquinta–Martinazzi, no `p`-th root is taken; the Morrey norm itself is its `p`-th root. The
**Morrey space** `L^{p,λ}(Ω)` consists of the functions for which it is finite. -/
def morreyNormPow : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (r ^ (-lam)) *
    ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω

/-- The defining formula of `morreyNormPow`, the supremum of the rescaled `p`-th power masses over
the points of `Ω` and the positive radii. -/
theorem morreyNormPow_def :
    morreyNormPow μ Ω p lam f = ⨆ x ∈ Ω, ⨆ (r : ℝ) (_ : 0 < r), ENNReal.ofReal (r ^ (-lam)) *
      ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω := by
  simp only [morreyNormPow]

/-- The Morrey norm is at most `C` exactly when each of the quantities of which it is the supremum
is. -/
theorem morreyNormPow_le_iff {C : ℝ≥0∞} :
    morreyNormPow μ Ω p lam f ≤ C ↔ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ (-lam)) * ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω ≤ C := by
  simp only [morreyNormPow, iSup_le_iff]

/-- The quantity attached to a point `x ∈ Ω` and a radius `r > 0` is at most the Morrey norm. -/
theorem le_morreyNormPow (hx : x ∈ Ω) (hr : 0 < r) :
    ENNReal.ofReal (r ^ (-lam)) * ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω ≤
      morreyNormPow μ Ω p lam f :=
  morreyNormPow_le_iff.1 le_rfl x hx r hr

/-- The Morrey norm only depends on the almost-everywhere class of `f` on `Ω`. -/
theorem morreyNormPow_congr_ae (h : f =ᵐ[μ.restrict Ω] g) :
    morreyNormPow μ Ω p lam f = morreyNormPow μ Ω p lam g := by
  simp only [morreyNormPow]
  refine iSup_congr fun x ↦ iSup_congr fun _ ↦ iSup_congr fun r ↦ iSup_congr fun _ ↦ ?_
  congr 1
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with y hy
  rw [hy]

/-- The Morrey norm on the empty set vanishes. -/
@[simp]
theorem morreyNormPow_empty : morreyNormPow μ ∅ p lam f = 0 := by
  simp [morreyNormPow]

/-- For `p > 0`, the Morrey norm of the zero function vanishes. -/
@[simp]
theorem morreyNormPow_zero (hp : 0 < p) : morreyNormPow μ Ω p lam (0 : X → F) = 0 := by
  simp [morreyNormPow, ENNReal.zero_rpow_of_pos hp]

/-- **Mass on balls centred in `Ω`.** The `p`-th power mass of `f` on `B(x, r) ∩ Ω`, `x ∈ Ω`, is
at most `r^λ` times the Morrey norm. -/
theorem setLIntegral_closedBall_le_morreyNormPow_of_mem (hx : x ∈ Ω) (hr : 0 < r) :
    ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω ≤
      ENNReal.ofReal (r ^ lam) * morreyNormPow μ Ω p lam f := by
  have h1 : ENNReal.ofReal (r ^ lam) * ENNReal.ofReal (r ^ (-lam)) = 1 := by
    simp [ofReal_rpow_mul_ofReal_rpow hr]
  calc _ = ENNReal.ofReal (r ^ lam) * (ENNReal.ofReal (r ^ (-lam)) *
        ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω) := by rw [← mul_assoc, h1, one_mul]
    _ ≤ _ := by gcongr; exact le_morreyNormPow hx hr

/-- **Mass on arbitrary balls.** The `p`-th power mass of `f` on `B(x, r) ∩ Ω` is at most
`(2 r)^λ` times the Morrey norm, for every centre `x`, in `Ω` or not: a ball `B(x, r)` meeting `Ω`
in positive measure lies in a ball `B(y, 2 r)` centred at a point `y ∈ Ω`. So the Morrey norm with
centres in `Ω` is equivalent to the one with all centres, up to the factor `2^λ`. -/
theorem setLIntegral_closedBall_le_morreyNormPow [OpensMeasurableSpace X] (hr : 0 < r) :
    ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω ≤
      ENNReal.ofReal ((2 * r) ^ lam) * morreyNormPow μ Ω p lam f := by
  by_cases h0 : μ.restrict Ω (closedBall x r) = 0
  · rw [setLIntegral_measure_zero _ _ h0]
    exact zero_le
  rw [Measure.restrict_apply measurableSet_closedBall] at h0
  obtain ⟨y, hyx, hyΩ⟩ := nonempty_of_measure_ne_zero h0
  have hsub : closedBall x r ⊆ closedBall y (2 * r) := by
    refine closedBall_subset_closedBall' ?_
    rw [mem_closedBall] at hyx
    rw [dist_comm]
    linarith
  calc _ ≤ ∫⁻ z in closedBall y (2 * r), ‖f z‖ₑ ^ p ∂μ.restrict Ω := lintegral_mono_set hsub
    _ ≤ _ := setLIntegral_closedBall_le_morreyNormPow_of_mem hyΩ (by positivity)

/-- The Morrey norm is monotone in the set: shrinking `Ω` removes centres and mass. -/
theorem morreyNormPow_mono_set (h : Ω' ⊆ Ω) :
    morreyNormPow μ Ω' p lam f ≤ morreyNormPow μ Ω p lam f := by
  refine morreyNormPow_le_iff.2 fun x hx r hr ↦ ?_
  calc _ ≤ ENNReal.ofReal (r ^ (-lam)) * ∫⁻ y in closedBall x r, ‖f y‖ₑ ^ p ∂μ.restrict Ω := by
        gcongr
    _ ≤ _ := le_morreyNormPow (h hx) hr

/-- **Homogeneity.** For `p ≥ 0`, multiplying `f` by a scalar `c` multiplies the `p`-th power of
the Morrey norm by `‖c‖^p`. -/
theorem morreyNormPow_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] (hp : 0 ≤ p) (c : 𝕜) :
    morreyNormPow μ Ω p lam (c • f) = ‖c‖ₑ ^ p * morreyNormPow μ Ω p lam f := by
  have hc : ‖c‖ₑ ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp eNorm_ne_top
  simp only [morreyNormPow, ENNReal.mul_iSup]
  refine iSup_congr fun x ↦ iSup_congr fun _ ↦ iSup_congr fun r ↦ iSup_congr fun _ ↦ ?_
  simp only [Pi.smul_apply, eNorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp]
  rw [lintegral_const_mul' _ _ hc, mul_left_comm]

/-- **The triangle inequality** for the Morrey norm
`‖f‖_{L^{p,λ}(Ω)} = (morreyNormPow μ Ω p λ f)^(1/p)` with `p ≥ 1`, from Minkowski's inequality on
each ball. -/
theorem morreyNormPow_add_rpow_le (hp : 1 ≤ p) (hf : AEStronglyMeasurable f (μ.restrict Ω))
    (hg : AEStronglyMeasurable g (μ.restrict Ω)) :
    morreyNormPow μ Ω p lam (f + g) ^ (1 / p) ≤
      morreyNormPow μ Ω p lam f ^ (1 / p) + morreyNormPow μ Ω p lam g ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  set M := morreyNormPow μ Ω p lam f ^ (1 / p) + morreyNormPow μ Ω p lam g ^ (1 / p)
  suffices h : morreyNormPow μ Ω p lam (f + g) ≤ M ^ p by
    calc _ ≤ (M ^ p) ^ (1 / p) := by gcongr
      _ = M := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  refine morreyNormPow_le_iff.2 fun x hx r hr ↦ ?_
  set c := ENNReal.ofReal (r ^ (-lam))
  set ν := (μ.restrict Ω).restrict (closedBall x r)
  -- Minkowski's inequality on the ball, then the bounds on each ball by the two Morrey norms.
  have hmink : (∫⁻ y, ‖(f + g) y‖ₑ ^ p ∂ν) ^ (1 / p) ≤
      (∫⁻ y, ‖f y‖ₑ ^ p ∂ν) ^ (1 / p) + (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) ^ (1 / p) := by
    calc _ ≤ (∫⁻ y, ((fun y ↦ ‖f y‖ₑ) + fun y ↦ ‖g y‖ₑ) y ^ p ∂ν) ^ (1 / p) := by
          gcongr with y
          exact eNorm_add_le _ _
      _ ≤ _ := ENNReal.lintegral_Lp_add_le (hf.restrict.eNorm) (hg.restrict.eNorm) hp
  have hterm : ∀ h : X → F, (c * ∫⁻ y, ‖h y‖ₑ ^ p ∂ν) ^ (1 / p) ≤
      morreyNormPow μ Ω p lam h ^ (1 / p) := fun h ↦ by
    gcongr
    exact le_morreyNormPow hx hr
  calc c * ∫⁻ y, ‖(f + g) y‖ₑ ^ p ∂ν = ((c * ∫⁻ y, ‖(f + g) y‖ₑ ^ p ∂ν) ^ (1 / p)) ^ p := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    _ ≤ M ^ p := by
        gcongr
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        calc c ^ (1 / p) * (∫⁻ y, ‖(f + g) y‖ₑ ^ p ∂ν) ^ (1 / p)
            ≤ c ^ (1 / p) * ((∫⁻ y, ‖f y‖ₑ ^ p ∂ν) ^ (1 / p) +
                (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) ^ (1 / p)) := by gcongr
          _ = (c * ∫⁻ y, ‖f y‖ₑ ^ p ∂ν) ^ (1 / p) + (c * ∫⁻ y, ‖g y‖ₑ ^ p ∂ν) ^ (1 / p) := by
            rw [mul_add, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          _ ≤ M := add_le_add (hterm f) (hterm g)

end Basic

section Haar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] {Ω : Set E} {p q lam : ℝ} {f : E → F}

/-- **Hölder's inequality** `L^q ⊆ L^{p, n (1 - p / q)}`. For `0 < p ≤ q < ∞`, on a
finite-dimensional space of dimension `n` with an additive Haar measure, the `p`-th power of the
Morrey norm with exponent `λ = n (1 - p / q)` is at most `‖f‖_{L^q(Ω)}^p μ(B(0, 1))^(1 - p / q)`.
For `p = 1` and `q > n` this is the inclusion `L^q ⊆ L^{1, n - 1 + α}` with `α = 1 - n / q`. -/
theorem morreyNormPow_le_eLpNorm_rpow_mul (hp : 0 < p) (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f (μ.restrict Ω)) :
    morreyNormPow μ Ω p (finrank ℝ E * (1 - p / q)) f ≤
      eLpNorm f (ENNReal.ofReal q) (μ.restrict Ω) ^ p * μ (closedBall 0 1) ^ (1 - p / q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hs : 0 ≤ 1 - p / q := sub_nonneg.2 ((div_le_one hq).2 hpq)
  refine morreyNormPow_le_iff.2 fun x _ r hr ↦ ?_
  set ν := (μ.restrict Ω).restrict (closedBall x r)
  -- Hölder's inequality on the ball, then the volume of the ball.
  have hν : ν univ ≤ ENNReal.ofReal (r ^ (finrank ℝ E : ℝ)) * μ (closedBall 0 1) := by
    rw [Measure.restrict_apply_univ, Real.rpow_natCast, ← Measure.addHaar_closedBall' μ x hr.le]
    exact Measure.restrict_apply_le _ _
  have hq' : eLpNorm' f q ν ≤ eLpNorm f (ENNReal.ofReal q) (μ.restrict Ω) := by
    rw [eLpNorm_eq_eLpNorm' (by simpa using hq) ENNReal.ofReal_ne_top hf,
      ENNReal.toReal_ofReal hq.le]
    exact eLpNorm'_mono_measure _ Measure.restrict_le_self hq.le
  have hexp : (1 / p - 1 / q) * p = 1 - p / q := by field_simp
  have hone : ENNReal.ofReal (r ^ (-(finrank ℝ E * (1 - p / q)))) *
      ENNReal.ofReal (r ^ (finrank ℝ E : ℝ)) ^ (1 - p / q) = 1 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs, ← Real.rpow_mul hr.le,
      ofReal_rpow_mul_ofReal_rpow hr]
    simp
  calc ENNReal.ofReal (r ^ (-(finrank ℝ E * (1 - p / q)))) * ∫⁻ y, ‖f y‖ₑ ^ p ∂ν
      = ENNReal.ofReal (r ^ (-(finrank ℝ E * (1 - p / q)))) * eLpNorm' f p ν ^ p := by
        rw [lintegral_rpow_eNorm_eq_rpow_eLpNorm' hp]
    _ ≤ ENNReal.ofReal (r ^ (-(finrank ℝ E * (1 - p / q)))) *
        (eLpNorm f (ENNReal.ofReal q) (μ.restrict Ω) *
          (ENNReal.ofReal (r ^ (finrank ℝ E : ℝ)) * μ (closedBall 0 1)) ^ (1 / p - 1 / q)) ^ p := by
        gcongr
        calc eLpNorm' f p ν ≤ eLpNorm' f q ν * ν univ ^ (1 / p - 1 / q) :=
              eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp hpq hf.restrict
          _ ≤ _ := by
              gcongr
              · exact sub_nonneg.2 (one_div_le_one_div_of_le hp hpq)
    _ = eLpNorm f (ENNReal.ofReal q) (μ.restrict Ω) ^ p * μ (closedBall 0 1) ^ (1 - p / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, hexp,
          ENNReal.mul_rpow_of_nonneg _ _ hs, ← mul_assoc, ← mul_assoc,
          mul_right_comm _ (eLpNorm f _ _ ^ p), hone, one_mul]

/-- One direction of `morreyNormPow_comp_add_smul`. -/
private theorem morreyNormPow_comp_add_smul_le (x₀ : E) {ε : ℝ} (hε : 0 < ε) :
    morreyNormPow μ ((fun y ↦ x₀ + ε • y) ⁻¹' Ω) p lam (fun y ↦ f (x₀ + ε • y)) ≤
      ENNReal.ofReal (ε ^ (lam - finrank ℝ E)) * morreyNormPow μ Ω p lam f := by
  refine morreyNormPow_le_iff.2 fun x hx r hr ↦ ?_
  have hpre : closedBall x r ∩ (fun y ↦ x₀ + ε • y) ⁻¹' Ω =
      (fun y ↦ x₀ + ε • y) ⁻¹' (closedBall (x₀ + ε • x) (ε * r) ∩ Ω) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_closedBall, dist_add_left, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos hε]
    rw [mul_le_mul_iff_of_pos_left hε]
  -- The change of variables `z = x₀ + ε y` maps `B(x, r)` onto `B(x₀ + ε x, ε r)`.
  rw [Measure.restrict_restrict measurableSet_closedBall, hpre,
    Measure.setLIntegral_comp_add_smul μ (fun z ↦ ‖f z‖ₑ ^ p) x₀ hε.ne',
    ← Measure.restrict_restrict measurableSet_closedBall]
  have hfac : ENNReal.ofReal (r ^ (-lam)) * ENNReal.ofReal |(ε ^ finrank ℝ E)⁻¹| =
      ENNReal.ofReal (ε ^ (lam - finrank ℝ E)) * ENNReal.ofReal ((ε * r) ^ (-lam)) := by
    rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hε.le,
      Real.mul_rpow hε.le hr.le, ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ofReal_rpow_mul_ofReal_rpow hε, mul_comm]
    congr 3
    ring
  rw [← mul_assoc, hfac, mul_assoc]
  gcongr
  exact le_morreyNormPow hx (mul_pos hε hr)

/-- **Scaling of the Morrey norm.** Under the affine change of variables `y ↦ x₀ + ε y`, `ε > 0`,
of a finite-dimensional space of dimension `n` with an additive Haar measure, the `p`-th power of
the Morrey norm with exponent `λ` is multiplied by `ε^(λ - n)`. For instance a coefficient
`d ∈ L^{1, n - 1 + α}` becomes `ε² d(x₀ + ε ·)`, of Morrey norm `ε^(1 + α) ‖d‖`, under the blow-up
of a second-order equation at `x₀`. -/
theorem morreyNormPow_comp_add_smul (x₀ : E) {ε : ℝ} (hε : 0 < ε) :
    morreyNormPow μ ((fun y ↦ x₀ + ε • y) ⁻¹' Ω) p lam (fun y ↦ f (x₀ + ε • y)) =
      ENNReal.ofReal (ε ^ (lam - finrank ℝ E)) * morreyNormPow μ Ω p lam f := by
  refine le_antisymm (morreyNormPow_comp_add_smul_le x₀ hε) ?_
  -- The inverse change of variables is again affine, `z ↦ -ε⁻¹ x₀ + ε⁻¹ z`.
  have hinv : ∀ z : E, x₀ + ε • (-(ε⁻¹ • x₀) + ε⁻¹ • z) = z := fun z ↦ by
    rw [smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hε.ne', one_smul, one_smul,
      add_neg_cancel_left]
  have h := morreyNormPow_comp_add_smul_le (μ := μ) (Ω := (fun y ↦ x₀ + ε • y) ⁻¹' Ω) (p := p)
    (lam := lam) (f := fun y ↦ f (x₀ + ε • y)) (-(ε⁻¹ • x₀)) (inv_pos.2 hε)
  simp only [hinv, preimage_preimage, preimage_id'] at h
  have hone : ENNReal.ofReal (ε ^ (lam - finrank ℝ E)) *
      ENNReal.ofReal (ε⁻¹ ^ (lam - finrank ℝ E)) = 1 := by
    rw [← Real.rpow_neg_eq_inv_rpow, ofReal_rpow_mul_ofReal_rpow hε]
    simp
  calc _ ≤ ENNReal.ofReal (ε ^ (lam - finrank ℝ E)) * (ENNReal.ofReal (ε⁻¹ ^ (lam - finrank ℝ E)) *
        morreyNormPow μ ((fun y ↦ x₀ + ε • y) ⁻¹' Ω) p lam (fun y ↦ f (x₀ + ε • y))) := by gcongr
    _ = _ := by rw [← mul_assoc, hone, one_mul]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The mass of a translate of `Ω.indicator f` on a ball, for the full measure, is controlled by
the Morrey norm of `f` on `Ω`, whatever the centre of the ball. -/
private theorem setLIntegral_closedBall_indicator_sub_le (x t : E) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y in closedBall x r, ‖Ω.indicator f (y - t)‖ₑ ∂μ ≤
      ENNReal.ofReal ((2 * r) ^ lam) * morreyNormPow μ Ω 1 lam f := by
  calc ∫⁻ y in closedBall x r, ‖Ω.indicator f (y - t)‖ₑ ∂μ
      = ∫⁻ z in closedBall (x - t) r, ‖Ω.indicator f z‖ₑ ∂μ := by
        rw [← lintegral_indicator measurableSet_closedBall,
          ← lintegral_indicator measurableSet_closedBall,
          ← lintegral_sub_right_eq_self
            (fun z ↦ (closedBall (x - t) r).indicator (fun z ↦ ‖Ω.indicator f z‖ₑ) z) t]
        congr 1
        ext y
        have hmem : y - t ∈ closedBall (x - t) r ↔ y ∈ closedBall x r := by
          simp only [mem_closedBall, dist_sub_right]
        by_cases hy : y ∈ closedBall x r
        · rw [indicator_of_mem hy, indicator_of_mem (hmem.2 hy)]
        · rw [indicator_of_notMem hy, indicator_of_notMem (mt hmem.1 hy)]
    _ ≤ ∫⁻ z in closedBall (x - t) r, ‖f z‖ₑ ∂μ.restrict Ω := by
        simp only [eNorm_indicator_eq_indicator_eNorm]
        refine (lintegral_indicator_le _ _).trans_eq ?_
        rw [Measure.restrict_restrict' measurableSet_closedBall,
          Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    _ ≤ _ := by
        simpa only [ENNReal.rpow_one] using
          setLIntegral_closedBall_le_morreyNormPow (μ := μ) (Ω := Ω) (p := 1) (lam := lam)
            (f := f) (x := x - t) hr

/-- **Convolution stays in `L^{1,λ}`.** For a kernel `v` and the extension `Ω.indicator f` of `f`
by zero, the Morrey norm of the convolution `v ⋆ Ω.indicator f` on any set `V` is at most
`2^λ ‖v‖_{L¹}` times the Morrey norm of `f` on `Ω`. With a mollifier of unit mass this is the
mollification of a coefficient in a Morrey space, at the cost of the factor `2^λ` that the
centres in `V` rather than in `Ω` require. -/
theorem morreyNormPow_one_convolution_le [NormedSpace ℝ F] (V : Set E) {v : E → ℝ}
    (hv : AEStronglyMeasurable v μ) (hf : AEStronglyMeasurable (Ω.indicator f) μ) :
    morreyNormPow μ V 1 lam (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Ω.indicator f) ≤
      ENNReal.ofReal (2 ^ lam) * eLpNorm v 1 μ * morreyNormPow μ Ω 1 lam f := by
  refine morreyNormPow_le_iff.2 fun x _ r hr ↦ ?_
  set M := morreyNormPow μ Ω 1 lam f
  set B := closedBall x r
  have hmeas : AEMeasurable (Function.uncurry fun y t ↦ ‖v t‖ₑ * ‖Ω.indicator f (y - t)‖ₑ)
      ((μ.restrict B).prod μ) := by
    have h := (hv.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf).eNorm.restrict
      (s := B ×ˢ univ)
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h
    simpa only [ContinuousLinearMap.lsmul_apply, eNorm_smul, Function.uncurry_def] using h
  -- Bound the convolution pointwise, swap the integrals and use the bound on translated balls.
  have hint : ∫⁻ y in B, ‖(v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Ω.indicator f) y‖ₑ ^ (1 : ℝ)
      ∂μ.restrict V ≤ eLpNorm v 1 μ * (ENNReal.ofReal ((2 * r) ^ lam) * M) := by
    calc _ ≤ ∫⁻ y in B, ‖(v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Ω.indicator f) y‖ₑ ∂μ := by
          simp only [ENNReal.rpow_one]
          exact lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl
      _ ≤ ∫⁻ y in B, ∫⁻ t, ‖v t‖ₑ * ‖Ω.indicator f (y - t)‖ₑ ∂μ ∂μ := by
          refine lintegral_mono fun y ↦ ?_
          rw [convolution_def]
          refine (eNorm_integral_le_lintegral_eNorm _).trans_eq ?_
          simp only [ContinuousLinearMap.lsmul_apply, eNorm_smul]
      _ = ∫⁻ t, ‖v t‖ₑ * ∫⁻ y in B, ‖Ω.indicator f (y - t)‖ₑ ∂μ ∂μ := by
          rw [lintegral_lintegral_swap hmeas]
          exact lintegral_congr fun t ↦ lintegral_const_mul' _ _ eNorm_ne_top
      _ ≤ ∫⁻ t, ‖v t‖ₑ * (ENNReal.ofReal ((2 * r) ^ lam) * M) ∂μ :=
          lintegral_mono fun t ↦ by gcongr; exact setLIntegral_closedBall_indicator_sub_le x t hr
      _ = _ := by
          rw [lintegral_mul_const'' _ hv.eNorm, eLpNorm_one_eq_lintegral_eNorm]
          exact hv
  have hfac : ENNReal.ofReal (r ^ (-lam)) * ENNReal.ofReal ((2 * r) ^ lam) =
      ENNReal.ofReal (2 ^ lam) := by
    rw [Real.mul_rpow zero_le_two hr.le, ENNReal.ofReal_mul (by positivity), mul_left_comm,
      ofReal_rpow_mul_ofReal_rpow hr]
    simp
  calc _ ≤ ENNReal.ofReal (r ^ (-lam)) *
        (eLpNorm v 1 μ * (ENNReal.ofReal ((2 * r) ^ lam) * M)) := by gcongr
    _ = eLpNorm v 1 μ * (ENNReal.ofReal (r ^ (-lam)) * ENNReal.ofReal ((2 * r) ^ lam)) * M := by
        ring
    _ = _ := by rw [hfac]; ring

end Haar

end MeasureTheory

end TauCeti
