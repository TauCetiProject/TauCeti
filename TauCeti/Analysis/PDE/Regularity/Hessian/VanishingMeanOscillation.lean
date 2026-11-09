/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Contraction
public import TauCeti.Analysis.PDE.Regularity.Hessian.MeanOscillation
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.MeasureTheory.Integral.SharpMaximalFunction

/-!
# The `W^{2,p}` estimate for coefficients of vanishing mean oscillation

Let `a` be a measurable coefficient field on `ℝ^{n+1}`, uniformly elliptic with constants
`0 < λ ≤ Λ`, and let `u ∈ W^{2,2}(ℝ^{n+1})` be a strong solution of

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f`

whose Hessian `D²u` lies in `Lᵖ`, `2 < p < ∞`. This file proves the a priori estimate

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`

when `D²u` vanishes outside a ball of radius `R` on which the coefficients oscillate little: there
are `C` and `γ > 0`, depending only on `n`, `p`, `λ` and `Λ`, such that the estimate holds whenever
every entry of `a` has VMO modulus at most `γ` at radius `R`
(`TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_vmoModulus_le`). No
continuity of `a` is assumed. A coefficient field of vanishing mean oscillation admits such a
radius `R` for every `γ`, so the estimate applies to every `u` whose Hessian is supported in a
sufficiently small ball. When `a` is uniformly close to a constant matrix on the support of `u`,
`TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le` gives
the same conclusion by a direct perturbation; here only the mean oscillation of `a` is small,
which a discontinuous field of vanishing mean oscillation allows.

## The argument

The proof is Krylov's sharp function method.

* **Freezing.** On a ball `B_r`, replace `a` by a constant elliptic matrix `A` and treat
  `∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu` as part of the right-hand side. The mean oscillation estimate for constant
  coefficients then bounds the square mean oscillation of `D²u` on `B_ρ ⊆ B_r` by
  `(ρ / r)^(n + 3) ∫_{B_r} ‖D²u‖²` plus the `L²` norms on `B_r` of `f` and of the error.
  On a small ball `A` is the matrix of averages of `a` over `B_r`, which is uniformly elliptic
  (`TauCeti.PDE.UniformlyEllipticOn.setAverage`); on a large ball it is the matrix of averages over
  the ball outside which `D²u` vanishes.
* **Hölder.** The error is at most a constant times `w ‖D²u‖`, with `w = ∑ᵢⱼ |A - a|ᵢⱼ` bounded by
  `2 (n + 1)² Λ`, so for `2 < 2t < p` its mean square is at most a constant times
  `(⨍ w)^(1/t') (⨍ ‖D²u‖^(2t))^(1/t)`, and `⨍ w ≤ (n + 1)² γ` by the VMO hypothesis.
* **The sharp function.** For `x ∈ B_ρ` and `r = κ ρ`, every average over `B_r` is at most
  `2^(n + 1)` times a maximal function at `x`. This bounds the square of the sharp maximal
  function of `D²u` at `x`, up to constants, by
  `κ⁻² M(‖D²u‖²) + κ^(n + 1) M(f²) + κ^(n + 1) γ^(1/t') M(‖D²u‖^(2t))^(1/t)`.
* **Absorption.** The Fefferman–Stein inequality
  (`TauCeti.exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow`) and the strong
  maximal inequality with exponents `p / 2` and `p / (2t)` turn this into
  `∫ ‖D²u‖^p ≤ (c₁ κ^(-p) + c₃ γ^(p/(2t'))) ∫ ‖D²u‖^p + c₂ ∫ |f|^p`. Choosing `κ` large and then
  `γ` small, the first term is absorbed, since `∫ ‖D²u‖^p` is finite.

The restriction `p > 2` comes from the `L²` mean oscillation estimate; the range `1 < p ≤ 2` and
the passage from functions supported in small balls to general solutions by cutoffs are not
treated here.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setAverage`: averages of uniformly elliptic coefficients are
  uniformly elliptic with the same constants.
* `TauCeti.PDE.lintegral_ball_enorm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq`:
  the mean oscillation estimate for the Hessian with frozen coefficients.
* `TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_vmoModulus_le`: the
  `W^{2,p}` estimate for coefficients of small mean oscillation.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate
  Studies in Mathematics **96**, AMS, 2008 (the sharp function method).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
-/

public section

open Filter InnerProductSpace Matrix MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

namespace PDE

/-- **Averages of uniformly elliptic coefficients are uniformly elliptic.** If `a` is uniformly
elliptic with constants `λ, Λ` on a set `s` of finite positive measure, and its entries are
integrable on `s`, then the constant matrix of the averages `⨍_s aᵢⱼ` is uniformly elliptic with
the same constants. -/
theorem UniformlyEllipticOn.setAverage {X Y ι : Type*} [MeasurableSpace X] [Fintype ι]
    [DecidableEq ι] {μ : Measure X} {s : Set X} {a : X → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn s a lam Lam) (hs0 : μ s ≠ 0) (hstop : μ s ≠ ∞)
    (hint : ∀ i j, IntegrableOn (fun x => a x i j) s μ) (Ω : Set Y) :
    UniformlyEllipticOn Ω (fun _ => Matrix.of fun i j => ⨍ x in s, a x i j ∂μ) lam Lam := by
  have hint' : ∀ η ξ : EuclideanSpace ℝ ι,
      IntegrableOn (fun x => η ⬝ᵥ (a x *ᵥ ξ)) s μ := fun η ξ => by
    simp only [dotProduct, mulVec]
    exact integrable_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (hint i j).mul_const _).const_mul _
  -- The bilinear form of the averaged matrix is the average of the bilinear forms.
  have hform : ∀ η ξ : EuclideanSpace ℝ ι,
      η ⬝ᵥ ((Matrix.of fun i j => ⨍ x in s, a x i j ∂μ) *ᵥ ξ) = ⨍ x in s, η ⬝ᵥ (a x *ᵥ ξ) ∂μ := by
    intro η ξ
    simp only [dotProduct, mulVec, of_apply, setAverage_eq, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (hint i j).mul_const _).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const _,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    ring
  refine uniformlyEllipticOn_iff.2 ⟨h.pos, h.le, fun _ _ => ⟨fun ξ => ?_, fun η ξ => ?_⟩⟩
  · -- Lower bound: some point of `s` lies below the average.
    rw [toQuadraticForm'_apply, hform]
    obtain ⟨x, hx, hle⟩ := exists_le_setAverage hs0 hstop (hint' ξ ξ)
    refine le_trans ?_ hle
    rw [← toQuadraticForm'_apply]
    exact (h.lower_bound hx) ξ
  · -- Upper bound: the average lies between two values of the bilinear form.
    rw [hform, abs_le]
    obtain ⟨x, hx, hle⟩ := exists_le_setAverage hs0 hstop (hint' η ξ)
    obtain ⟨y, hy, hge⟩ := exists_setAverage_le hs0 hstop (hint' η ξ)
    exact ⟨(neg_le_of_abs_le ((h.upper_bound hx) η ξ)).trans hle,
      hge.trans (le_of_abs_le ((h.upper_bound hy) η ξ))⟩

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {c : EuclideanSpace ℝ (Fin (n + 1))} {ρ r lam Lam : ℝ}

/-- The contraction `x ↦ ∑ᵢⱼ bᵢⱼ(x) ⟪H(x) eᵢ, eⱼ⟫` of almost everywhere strongly measurable fields
`b` and `H` is almost everywhere strongly measurable. -/
private theorem aestronglyMeasurable_contraction {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {m : ℕ} {b : X → Matrix (Fin m) (Fin m) ℝ} (hb : AEStronglyMeasurable b μ)
    {H : X → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hH : AEStronglyMeasurable H μ) :
    AEStronglyMeasurable (fun x => contraction (b x) (H x)) μ := by
  simp only [contraction_apply]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _
    fun j _ => ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable hb).mul ?_
  exact ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i (1 : ℝ))).continuous.inner
    continuous_const).comp_aestronglyMeasurable hH

/-- **Freezing the coefficients.** Let `u ∈ W^{2,2}(Ω)` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere
on `B_r = ball c r ⊆ Ω`, and let `A` be any constant matrix, uniformly elliptic with constants
`λ, Λ`. Then the square mean oscillation of the Hessian `H = D²u` on `B_ρ`, `0 < ρ ≤ r`, is bounded
by a decaying multiple of `∫_{B_r} ‖H‖²`, the `L²` norm of `f` on `B_r`, and the `L²` norm on `B_r`
of the error `∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu` made by freezing `a` at `A`:

`∫_{B_ρ} ‖H - H_{B_ρ}‖² ≤ 16 (n + 1)² D (ρ / r)^(n + 3) ∫_{B_r} ‖H‖²
  + 2 (n + 1)² (4 D + 2) / λ² (∫_{B_r} f² + ∫_{B_r} (∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu)²)`,

with `D = 2^(3n + 13) (n + 2)² (Λ / λ)^((n + 3) / 2)`. -/
theorem lintegral_ball_enorm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (ball c r)))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hball : ball c r ⊆ Omega)
    (heq : ∀ᵐ x ∂(volume.restrict (ball c r)), ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫⁻ x in ball c ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball c ρ, Wkp.iteratedGradient 1 u y‖ₑ ^ 2 ≤
      ENNReal.ofReal (16 * (n + 1) ^ 2 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) *
          (ρ / r) ^ (n + 3)) * (∫⁻ x in ball c r, ‖Wkp.iteratedGradient 1 u x‖ₑ ^ 2) +
        ENNReal.ofReal (2 * (n + 1) ^ 2 *
          (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2) *
          ((∫⁻ x in ball c r, ‖f x‖ₑ ^ 2) +
            ∫⁻ x in ball c r, ‖contraction (A - a x) (Wkp.iteratedGradient 1 u x)‖ₑ ^ 2) := by
  set H := Wkp.iteratedGradient 1 u
  set D : ℝ := 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)
  have hD : 0 ≤ D := by positivity
  have hr : 0 < r := hρ.trans_le hρr
  have hρΩ : ball c ρ ⊆ Omega := (ball_subset_ball hρr).trans hball
  have hH : MemLp H 2 (volume.restrict Omega) := Lp.memLp _
  -- The frozen equation `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = g` with `g = f + ∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu`.
  set err : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => contraction (A - a x) (H x)
  have heqA : ∀ᵐ x ∂(volume.restrict (ball c r)), ∑ i, ∑ j, A i j *
      ⟪H x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = f x + err x := by
    filter_upwards [heq] with x hx
    rw [← hx, ← contraction_apply, ← contraction_apply]
    simp only [err, contraction_sub, sub_apply, add_sub_cancel]
  have key := setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq
    hA u hball heqA hρ hρr
  -- Square integrals of `L²` functions are lower integrals.
  have hconv : ∀ {G : Type} [NormedAddCommGroup G] {g : EuclideanSpace ℝ (Fin (n + 1)) → G}
      {s t : Set (EuclideanSpace ℝ (Fin (n + 1)))}, MemLp g 2 (volume.restrict t) → s ⊆ t →
      volume s ≠ ∞ → ∀ b : G,
      ENNReal.ofReal (∫ x in s, ‖g x - b‖ ^ 2) = ∫⁻ x in s, ‖g x - b‖ₑ ^ 2 :=
    fun hg hst hs b => by
      rw [ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_norm_sub_sq_of_subset hst hs b)
        (ae_of_all _ fun _ => by positivity)]
      exact lintegral_congr fun x => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  -- `g` is square integrable on `B_r`, being a contraction of the Hessian.
  have hHr : MemLp H 2 (volume.restrict (ball c r)) := by
    simpa [Measure.restrict_restrict_of_subset hball] using hH.restrict (ball c r)
  have hg : MemLp (fun x => f x + err x) 2 (volume.restrict (ball c r)) := by
    refine ((contraction A).comp_memLp' hHr).ae_eq ?_
    filter_upwards [heqA] with x hx
    rw [Function.comp_apply, contraction_apply, hx]
  -- Pass to lower integrals.
  have hψρ := hconv hH hρΩ measure_ball_lt_top.ne
    (⨍ y in ball c ρ, H y)
  have hψr : ENNReal.ofReal (∫ x in ball c r, ‖H x - ⨍ y in ball c r, H y‖ ^ 2) ≤
      4 * ∫⁻ x in ball c r, ‖H x‖ₑ ^ 2 := by
    have h4 := setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hH.integrableOn_of_subset one_le_two hball measure_ball_lt_top.ne) (c := 0)
      (hH.integrableOn_norm_sub_sq_of_subset hball measure_ball_lt_top.ne 0)
    have h0 := hconv hH hball measure_ball_lt_top.ne 0
    simp only [sub_zero] at h4 h0
    calc _ ≤ ENNReal.ofReal (4 * ∫ x in ball c r, ‖H x‖ ^ 2) := ENNReal.ofReal_le_ofReal h4
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), h0, ENNReal.ofReal_ofNat]
  have herr : AEMeasurable (fun x => ‖err x‖ₑ ^ 2) (volume.restrict (ball c r)) := by
    exact (aestronglyMeasurable_contraction (aestronglyMeasurable_const.sub ha)
      hHr.aestronglyMeasurable).enorm.pow_const 2
  have hgr : ENNReal.ofReal (∫ x in ball c r, (f x + err x) ^ 2) ≤
      2 * ((∫⁻ x in ball c r, ‖f x‖ₑ ^ 2) + ∫⁻ x in ball c r, ‖err x‖ₑ ^ 2) := by
    have h := hconv hg subset_rfl measure_ball_lt_top.ne 0
    simp only [sub_zero, Real.norm_eq_abs, sq_abs] at h
    rw [h, ← lintegral_add_right' _ herr, ← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_mono fun x => ?_
    have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖f x‖ₑ ‖err x‖ₑ (p := 2) one_le_two
    norm_num at h2
    calc ‖f x + err x‖ₑ ^ 2 ≤ (‖f x‖ₑ + ‖err x‖ₑ) ^ 2 := by gcongr; exact enorm_add_le _ _
      _ ≤ _ := by exact_mod_cast h2
  -- Assemble.
  rw [← hψρ]
  refine (ENNReal.ofReal_le_ofReal key).trans ?_
  have hψ0 : 0 ≤ ∫ x in ball c r, ‖H x - ⨍ y in ball c r, H y‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hg0 : 0 ≤ ∫ x in ball c r, (f x + err x) ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hα : 0 ≤ (n + 1 : ℝ) ^ 2 * (4 * D * (ρ / r) ^ (n + 3)) := by positivity
  have hβ : 0 ≤ (n + 1 : ℝ) ^ 2 * ((4 * D + 2) / lam ^ 2) := by positivity
  calc ENNReal.ofReal ((n + 1) ^ 2 * (4 * D * (ρ / r) ^ (n + 3) *
          (∫ x in ball c r, ‖H x - ⨍ y in ball c r, H y‖ ^ 2) +
          (4 * D + 2) / lam ^ 2 * ∫ x in ball c r, (f x + err x) ^ 2))
      = ENNReal.ofReal ((n + 1) ^ 2 * (4 * D * (ρ / r) ^ (n + 3))) *
          ENNReal.ofReal (∫ x in ball c r, ‖H x - ⨍ y in ball c r, H y‖ ^ 2) +
        ENNReal.ofReal ((n + 1) ^ 2 * ((4 * D + 2) / lam ^ 2)) *
          ENNReal.ofReal (∫ x in ball c r, (f x + err x) ^ 2) := by
        rw [← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_add
          (mul_nonneg hα hψ0) (mul_nonneg hβ hg0)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ((n + 1) ^ 2 * (4 * D * (ρ / r) ^ (n + 3))) *
          (4 * ∫⁻ x in ball c r, ‖H x‖ₑ ^ 2) +
        ENNReal.ofReal ((n + 1) ^ 2 * ((4 * D + 2) / lam ^ 2)) *
          (2 * ((∫⁻ x in ball c r, ‖f x‖ₑ ^ 2) + ∫⁻ x in ball c r, ‖err x‖ₑ ^ 2)) := by
        gcongr
    _ = _ := by
        have e4 : ENNReal.ofReal (16 * (n + 1) ^ 2 * D * (ρ / r) ^ (n + 3)) =
            ENNReal.ofReal ((n + 1) ^ 2 * (4 * D * (ρ / r) ^ (n + 3))) * 4 := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul hα]
          ring_nf
        have e2 : ENNReal.ofReal (2 * (n + 1) ^ 2 * (4 * D + 2) / lam ^ 2) =
            ENNReal.ofReal ((n + 1) ^ 2 * ((4 * D + 2) / lam ^ 2)) * 2 := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hβ]
          ring_nf
        rw [e4, e2]
        ring

/-- **The coefficient error in mean.** Let `H` vanish almost everywhere on `s ∖ S`, and let the
entries of `A - a` have absolute values summing to at most `W` on `s`. For Hölder conjugate
exponents `t, t'`, the mean square of the error `∑ᵢⱼ (A - a)ᵢⱼ ⟪H eᵢ, eⱼ⟫` on `s` is controlled by
the mean of `w = ∑ᵢⱼ ‖A - a‖ᵢⱼ` on `S ∩ s` and the `L^{2t}` mean of `H` on `s`:

`⨍_s (∑ᵢⱼ (A - a)ᵢⱼ ⟪H eᵢ, eⱼ⟫)² ≤ m⁴ (W^(2t' - 1) ⨍_s 1_S w)^(1/t') (⨍_s ‖H‖^(2t))^(1/t)`. -/
private theorem setLAverage_enorm_contraction_sq_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s S : Set X} {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    {a : X → Matrix (Fin m) (Fin m) ℝ}
    {H : X → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)} {W : ℝ}
    (hW : ∀ᵐ x ∂μ.restrict s, ∑ i, ∑ j, |A i j - a x i j| ≤ W) (hS : MeasurableSet S)
    (hw : AEMeasurable (fun x => ∑ i, ∑ j, ‖A i j - a x i j‖ₑ) (μ.restrict s))
    (hH : AEMeasurable (fun x => ‖H x‖ₑ) (μ.restrict s))
    (hsupp : ∀ᵐ x ∂μ.restrict s, x ∉ S → H x = 0) {t t' : ℝ} (htt : t.HolderConjugate t') :
    ⨍⁻ x in s, ‖contraction (A - a x) (H x)‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal (m ^ 4) * (ENNReal.ofReal W ^ (2 * t' - 1) *
        ⨍⁻ x in s, S.indicator (fun x => ∑ i, ∑ j, ‖A i j - a x i j‖ₑ) x ∂μ) ^ (1 / t') *
        (⨍⁻ x in s, ‖H x‖ₑ ^ (2 * t) ∂μ) ^ (1 / t) := by
  set w : X → ℝ≥0∞ := fun x => ∑ i, ∑ j, ‖A i j - a x i j‖ₑ
  set v : X → ℝ≥0∞ := S.indicator w
  set ν : Measure X := (μ s)⁻¹ • μ.restrict s
  have hν : ν ≪ μ.restrict s := Measure.smul_absolutelyContinuous
  have ht' : 1 < t' := htt.symm.lt
  have ht0 : 0 < t := htt.pos
  -- Pointwise: `‖err‖ₑ² ≤ m⁴ v² ‖H‖ₑ²`, since `H = 0` off `S`.
  have hpt : ∀ᵐ x ∂ν, ‖contraction (A - a x) (H x)‖ₑ ^ 2 ≤
      ENNReal.ofReal (m ^ 4) * (v x ^ 2 * ‖H x‖ₑ ^ 2) := by
    filter_upwards [hν.ae_le hsupp] with x hx
    by_cases hxS : x ∈ S
    · have h := enorm_contraction_le (A - a x) (H x)
      simp only [Matrix.sub_apply] at h
      calc ‖contraction (A - a x) (H x)‖ₑ ^ 2
          ≤ (ENNReal.ofReal (m ^ 2) * w x * ‖H x‖ₑ) ^ 2 := by gcongr
        _ = _ := by
          have h4 : ENNReal.ofReal ((m : ℝ) ^ 4) = ENNReal.ofReal ((m : ℝ) ^ 2) ^ 2 := by
            rw [← ENNReal.ofReal_pow (by positivity)]
            ring_nf
          rw [show v x = w x from Set.indicator_of_mem hxS w, h4]
          ring
    · simp [hx hxS]
  -- The bound `v ≤ W` on `s`.
  have hvW : ∀ᵐ x ∂ν, v x ≤ ENNReal.ofReal W := by
    filter_upwards [hν.ae_le hW] with x hx
    refine (Set.indicator_le_self S w x).trans ?_
    refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hx)
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun i => ∑ j, |A i j - a x i j|)
      fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun j => |A i j - a x i j|) fun _ _ => abs_nonneg _]
    exact Finset.sum_congr rfl fun j _ => Real.enorm_eq_ofReal_abs _
  have hvm : AEMeasurable v ν := ((hw.indicator hS)).mono_ac hν
  have hHm : AEMeasurable (fun x => ‖H x‖ₑ) ν := hH.mono_ac hν
  have hv2 : ∀ᵐ x ∂ν, (v x ^ 2) ^ t' ≤ ENNReal.ofReal W ^ (2 * t' - 1) * v x := by
    filter_upwards [hvW] with x hx
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat]
    conv_lhs => rw [show 2 * t' = (2 * t' - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
    gcongr
    linarith
  have hH2 : ∀ x, (‖H x‖ₑ ^ 2) ^ t = ‖H x‖ₑ ^ (2 * t) := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat]
  simp only [setLAverage_eq']
  calc ∫⁻ x, ‖contraction (A - a x) (H x)‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (m ^ 4) * (v x ^ 2 * ‖H x‖ₑ ^ 2) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (m ^ 4) *
          ∫⁻ x, ((fun x => v x ^ 2) * fun x => ‖H x‖ₑ ^ 2) x ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
    _ ≤ ENNReal.ofReal (m ^ 4) * ((∫⁻ x, (v x ^ 2) ^ t' ∂ν) ^ (1 / t') *
          (∫⁻ x, (‖H x‖ₑ ^ 2) ^ t ∂ν) ^ (1 / t)) := by
        gcongr
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq ν htt.symm (hvm.pow_const 2) (hHm.pow_const 2)
    _ ≤ ENNReal.ofReal (m ^ 4) * ((∫⁻ x, ENNReal.ofReal W ^ (2 * t' - 1) * v x ∂ν) ^ (1 / t') *
          (∫⁻ x, ‖H x‖ₑ ^ (2 * t) ∂ν) ^ (1 / t)) := by
        simp_rw [hH2]
        gcongr _ * (?_ * _)
        exact ENNReal.rpow_le_rpow (lintegral_mono_ae hv2)
          (one_div_nonneg.2 (zero_le_one.trans ht'.le))
    _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          ENNReal.ofReal_ne_top), mul_assoc]

/-- The constant of the decaying term in the frozen-coefficient estimate. -/
private noncomputable def decayConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  16 * (n + 1) ^ 2 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3))

/-- The constant of the forcing term in the frozen-coefficient estimate. -/
private noncomputable def forcingConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 * (n + 1) ^ 2 * (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2

private theorem decayConst_nonneg (n : ℕ) (lam Lam : ℝ) : 0 ≤ decayConst n lam Lam := by
  unfold decayConst; positivity

private theorem forcingConst_nonneg (n : ℕ) (lam Lam : ℝ) : 0 ≤ forcingConst n lam Lam := by
  unfold forcingConst; positivity

/-- **The mean oscillation estimate on one ball.** Let `u ∈ W^{2,2}(ℝ^{n+1})` solve
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f`, let `x ∈ B_ρ = ball c ρ` and `κ ≥ 1`, and freeze the coefficients on
`B_{κρ}` at an elliptic constant matrix `A` whose deviation `w = ∑ᵢⱼ ‖A - a‖ᵢⱼ` has mean at most `δ`
over the part of `B_{κρ}` where `D²u` may be nonzero. Then the square of the mean oscillation of
`H = D²u` on `B_ρ` is bounded by the maximal functions at `x` of `‖H‖²`, of `f²` and of `‖H‖^(2t)`,
the first with the small factor `κ⁻²` and the last with the factor `δ^(1/t')`. -/
private theorem sq_setLAverage_enorm_iteratedGradient_sub_le
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : UniformlyEllipticOn univ (fun _ : EuclideanSpace ℝ (Fin (n + 1)) => A) lam Lam)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ 2 2)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (heq : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hS : MeasurableSet S)
    {x : EuclideanSpace ℝ (Fin (n + 1))} {κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ) (hδ : 0 ≤ δ)
    (hx : x ∈ ball c ρ)
    (hsupp : ∀ᵐ y ∂volume.restrict (ball c (κ * ρ)), y ∉ S → Wkp.iteratedGradient 1 u y = 0)
    (hw : ⨍⁻ y in ball c (κ * ρ), S.indicator (fun y => ∑ i, ∑ j, ‖A i j - a y i j‖ₑ) y ≤
      ENNReal.ofReal δ)
    {t t' : ℝ} (htt : t.HolderConjugate t') :
    (⨍⁻ y in ball c ρ,
        ‖Wkp.iteratedGradient 1 u y - ⨍ z in ball c ρ, Wkp.iteratedGradient 1 u z‖ₑ) ^ 2 ≤
      ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖Wkp.iteratedGradient 1 u y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖f y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * (n + 1) ^ 4 *
            ((2 * (n + 1) ^ 2 * Lam) ^ (2 * t' - 1) * δ) ^ (1 / t') * (2 ^ (n + 1)) ^ (1 / t)) *
          maximalFunction volume (fun y => ‖Wkp.iteratedGradient 1 u y‖ₑ ^ (2 * t)) x ^
            (1 / t) := by
  set H := Wkp.iteratedGradient 1 u
  set r := κ * ρ with hr_def
  set Hρ := ⨍ z in ball c ρ, H z
  set M₁ := maximalFunction volume (fun y => ‖H y‖ₑ ^ 2) x
  set M₂ := maximalFunction volume (fun y => ‖f y‖ₑ ^ 2) x
  set M₃ := maximalFunction volume (fun y => ‖H y‖ₑ ^ (2 * t)) x
  set W : ℝ := 2 * (n + 1) ^ 2 * Lam
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  have hr : 0 < r := mul_pos hκ0 hρ
  have hρr : ρ ≤ r := le_mul_of_one_le_left hρ.le hκ
  have hxc : dist x c ≤ r := (mem_ball.1 hx).le.trans hρr
  have hLam : 0 ≤ Lam := hell.upper_nonneg
  have ht0 : 0 < t := htt.pos
  have ht'0 : 0 < t' := htt.symm.pos
  have htop : ball c r ⊆ ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
      Set (EuclideanSpace ℝ (Fin (n + 1)))) := by simp
  have hHm : AEStronglyMeasurable H volume := by
    simpa using (Lp.aestronglyMeasurable H)
  -- The frozen-coefficient estimate on `B_ρ ⊆ B_r`.
  have key : ∫⁻ y in ball c ρ, ‖H y - Hρ‖ₑ ^ 2 ≤
      ENNReal.ofReal (decayConst n lam Lam * (ρ / r) ^ (n + 3)) *
          (∫⁻ y in ball c r, ‖H y‖ₑ ^ 2) +
        ENNReal.ofReal (forcingConst n lam Lam) * ((∫⁻ y in ball c r, ‖f y‖ₑ ^ 2) +
          ∫⁻ y in ball c r, ‖contraction (A - a y) (H y)‖ₑ ^ 2) :=
    lintegral_ball_enorm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq
      (hA.mono_set (subset_univ _)) u ha.restrict htop (ae_restrict_of_ae heq) hρ hρr
  -- Averages over `B_ρ` are `κ^(n + 1)` times averages over `B_r`.
  have hdiv : ∀ I : ℝ≥0∞, I / volume (ball c ρ) =
      ENNReal.ofReal (κ ^ (n + 1)) * (I / volume (ball c r)) := fun I => by
    have hk0 : ENNReal.ofReal (κ ^ (n + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hκ0 _)).ne'
    rw [hr_def, Measure.addHaar_ball_mul _ _ hκ0.le, ← Measure.addHaar_ball_center volume c,
      finrank_euclideanSpace, Fintype.card_fin, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hk0 ENNReal.ofReal_ne_top]
  -- Jensen's inequality on `B_ρ`.
  have hjensen : (⨍⁻ y in ball c ρ, ‖H y - Hρ‖ₑ) ^ 2 ≤ ⨍⁻ y in ball c ρ, ‖H y - Hρ‖ₑ ^ 2 := by
    have h := rpow_laverage_le_laverage_rpow (μ := volume.restrict (ball c ρ))
      (u := fun y => ‖H y - Hρ‖ₑ) (hHm.sub aestronglyMeasurable_const).enorm.restrict one_le_two
    simpa only [ENNReal.rpow_two] using h
  -- The maximal function bounds on `B_r`.
  have hmax : ∀ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞,
      ⨍⁻ y in ball c r, g y ≤ 2 ^ (n + 1) * maximalFunction volume g x := fun g => by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, enorm_eq_self] using
      setLAverage_ball_le_two_pow_mul_maximalFunction volume g hr hxc
  -- The coefficient error on `B_r`.
  have hW : ∀ y, ∑ i, ∑ j, |A i j - a y i j| ≤ W := fun y => by
    have hij : ∀ i j, |A i j - a y i j| ≤ 2 * Lam := fun i j =>
      (abs_sub _ _).trans (by linarith [(hA.abs_apply_le (mem_univ y)) i j,
        (hell.abs_apply_le (mem_univ y)) i j])
    calc ∑ i, ∑ j, |A i j - a y i j| ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), 2 * Lam :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
      _ = W := by simp [W]; ring
  have hwm : AEMeasurable (fun y => ∑ i, ∑ j, ‖A i j - a y i j‖ₑ)
      (volume.restrict (ball c r)) := by
    refine Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => ?_
    exact (aestronglyMeasurable_const.sub
      ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable ha)).enorm.restrict
  have herr := setLAverage_enorm_contraction_sq_le (μ := volume) (s := ball c r)
    (ae_of_all _ hW) hS hwm hHm.enorm.restrict hsupp htt
  have herr' : ⨍⁻ y in ball c r, ‖contraction (A - a y) (H y)‖ₑ ^ 2 ≤
      ENNReal.ofReal ((n + 1) ^ 4) *
        (ENNReal.ofReal W ^ (2 * t' - 1) * ENNReal.ofReal δ) ^ (1 / t') *
        (2 ^ (n + 1) * M₃) ^ (1 / t) := by
    refine herr.trans ?_
    push_cast
    gcongr
    exact hmax _
  calc (⨍⁻ y in ball c ρ, ‖H y - Hρ‖ₑ) ^ 2
      ≤ (∫⁻ y in ball c ρ, ‖H y - Hρ‖ₑ ^ 2) / volume (ball c ρ) := by
        rw [← setLAverage_eq]; exact hjensen
    _ ≤ (ENNReal.ofReal (decayConst n lam Lam * (ρ / r) ^ (n + 3)) *
          (∫⁻ y in ball c r, ‖H y‖ₑ ^ 2) +
        ENNReal.ofReal (forcingConst n lam Lam) * ((∫⁻ y in ball c r, ‖f y‖ₑ ^ 2) +
          ∫⁻ y in ball c r, ‖contraction (A - a y) (H y)‖ₑ ^ 2)) / volume (ball c ρ) := by
        gcongr
    _ = ENNReal.ofReal (decayConst n lam Lam * (ρ / r) ^ (n + 3)) *
          (ENNReal.ofReal (κ ^ (n + 1)) * ⨍⁻ y in ball c r, ‖H y‖ₑ ^ 2) +
        ENNReal.ofReal (forcingConst n lam Lam) *
          (ENNReal.ofReal (κ ^ (n + 1)) * (⨍⁻ y in ball c r, ‖f y‖ₑ ^ 2) +
            ENNReal.ofReal (κ ^ (n + 1)) *
              ⨍⁻ y in ball c r, ‖contraction (A - a y) (H y)‖ₑ ^ 2) := by
        rw [ENNReal.add_div, mul_div_assoc, mul_div_assoc, ENNReal.add_div, hdiv, hdiv, hdiv,
          ← setLAverage_eq, ← setLAverage_eq, ← setLAverage_eq]
    _ ≤ ENNReal.ofReal (decayConst n lam Lam * (ρ / r) ^ (n + 3)) *
          (ENNReal.ofReal (κ ^ (n + 1)) * (2 ^ (n + 1) * M₁)) +
        ENNReal.ofReal (forcingConst n lam Lam) *
          (ENNReal.ofReal (κ ^ (n + 1)) * (2 ^ (n + 1) * M₂) +
            ENNReal.ofReal (κ ^ (n + 1)) * (ENNReal.ofReal ((n + 1) ^ 4) *
              (ENNReal.ofReal W ^ (2 * t' - 1) * ENNReal.ofReal δ) ^ (1 / t') *
                (2 ^ (n + 1) * M₃) ^ (1 / t))) := by
        gcongr
        exacts [hmax _, hmax _]
    _ = _ := by
        have hdc := decayConst_nonneg n lam Lam
        have hfc := forcingConst_nonneg n lam Lam
        have hW0 : 0 ≤ W := by positivity
        have hX : 0 ≤ W ^ (2 * t' - 1) * δ := by positivity
        have h2 : (2 : ℝ≥0∞) ^ (n + 1) = ENNReal.ofReal (2 ^ (n + 1)) := by
          rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
        have hWδ : ENNReal.ofReal W ^ (2 * t' - 1) * ENNReal.ofReal δ =
            ENNReal.ofReal (W ^ (2 * t' - 1) * δ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hW0 (by linarith [htt.symm.lt]),
            ENNReal.ofReal_mul (by positivity)]
        have e1 : ENNReal.ofReal (decayConst n lam Lam * (ρ / r) ^ (n + 3)) *
            ENNReal.ofReal (κ ^ (n + 1)) = ENNReal.ofReal (decayConst n lam Lam / κ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hr_def, show ρ / (κ * ρ) = κ⁻¹ by field_simp, inv_pow]
          field_simp
          ring
        have c1 : ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) =
            ENNReal.ofReal (decayConst n lam Lam / κ ^ 2) * ENNReal.ofReal (2 ^ (n + 1)) :=
          ENNReal.ofReal_mul (by positivity)
        have c2 : ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) =
            ENNReal.ofReal (forcingConst n lam Lam) * ENNReal.ofReal (κ ^ (n + 1)) *
              ENNReal.ofReal (2 ^ (n + 1)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        have c3 : ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * (n + 1) ^ 4 *
              (W ^ (2 * t' - 1) * δ) ^ (1 / t') * (2 ^ (n + 1)) ^ (1 / t)) =
            ENNReal.ofReal (forcingConst n lam Lam) * ENNReal.ofReal (κ ^ (n + 1)) *
              ENNReal.ofReal ((n + 1) ^ 4) * ENNReal.ofReal ((W ^ (2 * t' - 1) * δ) ^ (1 / t')) *
              ENNReal.ofReal ((2 ^ (n + 1)) ^ (1 / t)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        rw [c1, c2, c3, ← e1, h2, hWδ, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg hX (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
        ring

/-- Freezing at the ball averages: on a ball of radius `s ≤ R`, the matrix of averages of `a` is
elliptic, and the mean deviation `∑ᵢⱼ ‖A - a‖ᵢⱼ` from it is at most `(n + 1)² γ` when every entry
of `a` has VMO modulus at most `γ` at radius `R`. -/
private theorem exists_setAverage_deviation_le {a : EuclideanSpace ℝ (Fin (n + 1)) →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) {R γ s : ℝ}
    (hvmo : ∀ i j, vmoModulus (fun x => a x i j) volume R ≤ ENNReal.ofReal γ)
    (c' : EuclideanSpace ℝ (Fin (n + 1))) (hs : 0 < s) (hsR : s ≤ R) :
    UniformlyEllipticOn univ (fun _ : EuclideanSpace ℝ (Fin (n + 1)) =>
        Matrix.of fun i j => ⨍ x in ball c' s, a x i j) lam Lam ∧
      ⨍⁻ y in ball c' s, (∑ i, ∑ j,
          ‖(Matrix.of fun i j => ⨍ x in ball c' s, a x i j) i j - a y i j‖ₑ) ≤
        ENNReal.ofReal ((n + 1) ^ 2 * γ) := by
  have hentry : ∀ i j, AEStronglyMeasurable (fun x => a x i j) volume := fun i j =>
    (continuous_id.matrix_elem i j).comp_aestronglyMeasurable ha
  have hint : ∀ i j, IntegrableOn (fun x => a x i j) (ball c' s) volume := fun i j =>
    Measure.integrableOn_of_bounded (M := Lam) measure_ball_lt_top.ne (hentry i j)
      (ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using (hell.abs_apply_le (mem_univ x)) i j)
  refine ⟨(hell.mono_set (subset_univ _)).setAverage
    (measure_ball_pos _ _ hs).ne' measure_ball_lt_top.ne hint univ, ?_⟩
  have hmeas : ∀ i j, AEMeasurable (fun y => ‖(Matrix.of fun i j => ⨍ x in ball c' s, a x i j) i j -
      a y i j‖ₑ) (volume.restrict (ball c' s)) := fun i j =>
    (aestronglyMeasurable_const.sub (hentry i j)).enorm.restrict
  have hmeas' : ∀ i j, AEMeasurable
      (fun y => ‖(Matrix.of fun i j => ⨍ x in ball c' s, a x i j) i j - a y i j‖ₑ)
      ((volume (ball c' s))⁻¹ • volume.restrict (ball c' s)) := fun i j =>
    (hmeas i j).mono_ac Measure.smul_absolutelyContinuous
  simp only [setLAverage_eq']
  rw [lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => hmeas' i j]
  simp_rw [lintegral_finsetSum' _ fun j _ => hmeas' _ j, ← setLAverage_eq']
  calc ∑ i, ∑ j, ⨍⁻ y in ball c' s,
        ‖(Matrix.of fun i j => ⨍ x in ball c' s, a x i j) i j - a y i j‖ₑ
      ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), ENNReal.ofReal γ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        simp_rw [Matrix.of_apply, enorm_sub_rev (⨍ x in ball c' s, a x i j)]
        exact (setLAverage_enorm_sub_setAverage_le_vmoModulus _ volume c' hsR).trans (hvmo i j)
    _ = ENNReal.ofReal ((n + 1) ^ 2 * γ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [ENNReal.ofReal_add (by positivity) zero_le_one]
        simp [sq, mul_assoc]

/-- The choice of frozen coefficients on a ball `B_r`. On a small ball, `r ≤ R`, freeze at the
averages over `B_r` itself; on a large ball, where only the part inside the support `B(z, R)` of the
Hessian matters, freeze at the averages over `B(z, R)`. Either way the frozen matrix is elliptic,
and the deviation from it has mean at most `(n + 1)² γ` over the part of `B_r` inside `B(z, R)`. -/
private theorem exists_frozen_coefficients {a : EuclideanSpace ℝ (Fin (n + 1)) →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) {R γ : ℝ}
    (hR : 0 < R) (hvmo : ∀ i j, vmoModulus (fun x => a x i j) volume R ≤ ENNReal.ofReal γ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) (hr : 0 < r) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (S : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      UniformlyEllipticOn univ (fun _ : EuclideanSpace ℝ (Fin (n + 1)) => A) lam Lam ∧
        MeasurableSet S ∧ ball c r ∩ ball z R ⊆ S ∧
        ⨍⁻ y in ball c r, S.indicator (fun y => ∑ i, ∑ j, ‖A i j - a y i j‖ₑ) y ≤
          ENNReal.ofReal ((n + 1) ^ 2 * γ) := by
  rcases le_or_gt r R with hrR | hRr
  · obtain ⟨hA, hw⟩ := exists_setAverage_deviation_le ha hell hvmo c hr hrR
    refine ⟨_, ball c r, hA, measurableSet_ball, inter_subset_left, ?_⟩
    rwa [setLAverage_eq, setLIntegral_indicator measurableSet_ball, inter_self, ← setLAverage_eq]
  · obtain ⟨hA, hw⟩ := exists_setAverage_deviation_le ha hell hvmo z hR le_rfl
    refine ⟨_, ball z R, hA, measurableSet_ball, inter_subset_right, ?_⟩
    have hvol : volume (ball z R) ≤ volume (ball c r) := by
      rw [Measure.addHaar_ball _ _ hR.le, Measure.addHaar_ball _ _ hr.le]
      gcongr
    refine le_trans ?_ hw
    rw [setLAverage_eq, setLIntegral_indicator measurableSet_ball, setLAverage_eq]
    exact ENNReal.div_le_div (lintegral_mono_set inter_subset_left) hvol

/-- **Krylov's pointwise estimate for the sharp maximal function of the Hessian.** Let
`u ∈ W^{2,2}(ℝ^{n+1})` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` with `D²u` vanishing outside `B(z, R)`, and let
every entry of `a` have VMO modulus at most `γ` at radius `R`. Then for every `κ ≥ 1` the square of
the sharp maximal function of `H = D²u` is bounded pointwise by the maximal functions of `‖H‖²`,
of `f²` and of `‖H‖^(2t)`. -/
private theorem sq_sharpMaximalFunction_iteratedGradient_le
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) {R γ : ℝ}
    (hR : 0 < R) (hγ : 0 ≤ γ)
    (hvmo : ∀ i j, vmoModulus (fun x => a x i j) volume R ≤ ENNReal.ofReal γ)
    (z : EuclideanSpace ℝ (Fin (n + 1)))
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ 2 2)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hsupp : ∀ᵐ x, x ∉ ball z R → Wkp.iteratedGradient 1 u x = 0)
    (heq : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    {κ : ℝ} (hκ : 1 ≤ κ) {t t' : ℝ} (htt : t.HolderConjugate t')
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    sharpMaximalFunction volume (Wkp.iteratedGradient 1 u) x ^ 2 ≤
      ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖Wkp.iteratedGradient 1 u y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) *
          maximalFunction volume (fun y => ‖f y‖ₑ ^ 2) x +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * (n + 1) ^ 4 *
            ((2 * (n + 1) ^ 2 * Lam) ^ (2 * t' - 1) * ((n + 1) ^ 2 * γ)) ^ (1 / t') *
              (2 ^ (n + 1)) ^ (1 / t)) *
          maximalFunction volume (fun y => ‖Wkp.iteratedGradient 1 u y‖ₑ ^ (2 * t)) x ^
            (1 / t) := by
  rw [← ENNReal.rpow_two, ← ENNReal.le_rpow_inv_iff two_pos]
  refine sharpMaximalFunction_le fun c ρ hx => ?_
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.1 hx)
  have hr : 0 < κ * ρ := mul_pos (zero_lt_one.trans_le hκ) hρ
  obtain ⟨A, S, hA, hS, hsub, hw⟩ := exists_frozen_coefficients ha hell hR hvmo z (c := c) hr
  have hsuppS : ∀ᵐ y ∂volume.restrict (ball c (κ * ρ)), y ∉ S →
      Wkp.iteratedGradient 1 u y = 0 := by
    filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_ball] with y hy hyB hyS
    exact hy fun hyz => hyS (hsub ⟨hyB, hyz⟩)
  rw [ENNReal.le_rpow_inv_iff two_pos, ENNReal.rpow_two]
  exact sq_setLAverage_enorm_iteratedGradient_sub_le hA ha hell u heq hS hρ hκ (by positivity) hx
    hsuppS hw htt

/-- Integrating a pointwise bound of `g²` by three maximal functions: if
`g² ≤ α₁ M h₁ + α₂ M h₂ + α₃ (M h₃)^(1/t)` and `2t < q`, then the strong-type maximal inequality
with exponents `r = q / 2` and `r / t` bounds `∫ g^q` by the integrals of `h₁^r`, `h₂^r` and
`h₃^(r/t)`. -/
private theorem lintegral_rpow_le_of_sq_le_maximalFunction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {g h₁ h₂ h₃ : E → ℝ≥0∞} (h₁m : AEMeasurable h₁ μ)
    (h₂m : AEMeasurable h₂ μ) (h₃m : AEMeasurable h₃ μ) {α₁ α₂ α₃ : ℝ≥0∞} {t q : ℝ}
    (ht : 1 < t) (htq : 2 * t < q)
    (hg : ∀ x, g x ^ 2 ≤ α₁ * maximalFunction μ h₁ x + α₂ * maximalFunction μ h₂ x +
      α₃ * maximalFunction μ h₃ x ^ (1 / t)) :
    ∫⁻ x, g x ^ q ∂μ ≤ 2 ^ (q / 2 - 1) * (2 ^ (q / 2 - 1) *
        (α₁ ^ (q / 2) * (ENNReal.ofReal (2 * (q / 2) * 2 ^ (q / 2 - 1) / (q / 2 - 1)) *
            4 ^ Module.finrank ℝ E * ∫⁻ x, h₁ x ^ (q / 2) ∂μ) +
          α₂ ^ (q / 2) * (ENNReal.ofReal (2 * (q / 2) * 2 ^ (q / 2 - 1) / (q / 2 - 1)) *
            4 ^ Module.finrank ℝ E * ∫⁻ x, h₂ x ^ (q / 2) ∂μ)) +
        α₃ ^ (q / 2) * (ENNReal.ofReal (2 * (q / 2 / t) * 2 ^ (q / 2 / t - 1) / (q / 2 / t - 1)) *
            4 ^ Module.finrank ℝ E * ∫⁻ x, h₃ x ^ (q / 2 / t) ∂μ)) := by
  set r := q / 2
  have hr : 1 < r := by simp only [r]; linarith
  have hrt : 1 < r / t := by rw [one_lt_div (by linarith)]; simp only [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  have ht0 : 0 < t := by linarith
  set M₁ := maximalFunction μ h₁
  set M₂ := maximalFunction μ h₂
  set M₃ := maximalFunction μ h₃
  have hM₁ : Measurable M₁ := measurable_maximalFunction μ h₁
  have hM₂ : Measurable M₂ := measurable_maximalFunction μ h₂
  have hM₃ : Measurable M₃ := measurable_maximalFunction μ h₃
  -- The maximal inequality for the three functions; the `‖·‖ₑ` of `ℝ≥0∞` is the identity.
  have hmax : ∀ {h : E → ℝ≥0∞}, AEMeasurable h μ → ∀ {e : ℝ}, 1 < e →
      ∫⁻ x, maximalFunction μ h x ^ e ∂μ ≤
        ENNReal.ofReal (2 * e * 2 ^ (e - 1) / (e - 1)) * 4 ^ Module.finrank ℝ E *
          ∫⁻ x, h x ^ e ∂μ := fun {h} hh {e} he => by
    simpa only [enorm_eq_self] using lintegral_rpow_maximalFunction_le μ (f := h) hh he
  -- Pointwise: `g^q = (g²)^r ≤ 2^(r-1) (2^(r-1) ((α₁ M₁)^r + (α₂ M₂)^r) + (α₃ M₃^(1/t))^r)`.
  have hpt : ∀ x, g x ^ q ≤ 2 ^ (r - 1) * (2 ^ (r - 1) *
      (α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r) + α₃ ^ r * M₃ x ^ (r / t)) := fun x => by
    have hgq : g x ^ q = (g x ^ 2) ^ r := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; congr 1; simp only [r]; push_cast; ring
    rw [hgq]
    refine (ENNReal.rpow_le_rpow (hg x) hr0).trans ?_
    refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr.le).trans ?_
    gcongr
    · refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr.le).trans_eq ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ENNReal.mul_rpow_of_nonneg _ _ hr0]
    · rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, ← ENNReal.rpow_mul, one_div_mul_eq_div]
  have m₁ : Measurable fun x => α₁ ^ r * M₁ x ^ r := (hM₁.pow_const r).const_mul _
  have m₂ : Measurable fun x => α₂ ^ r * M₂ x ^ r := (hM₂.pow_const r).const_mul _
  have m₃ : Measurable fun x => α₃ ^ r * M₃ x ^ (r / t) := (hM₃.pow_const _).const_mul _
  have m₁₂ : Measurable fun x => α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r := m₁.add m₂
  have m : Measurable fun x => 2 ^ (r - 1) * (α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r) +
      α₃ ^ r * M₃ x ^ (r / t) := (m₁₂.const_mul _).add m₃
  calc ∫⁻ x, g x ^ q ∂μ
      ≤ ∫⁻ x, 2 ^ (r - 1) * (2 ^ (r - 1) *
          (α₁ ^ r * M₁ x ^ r + α₂ ^ r * M₂ x ^ r) + α₃ ^ r * M₃ x ^ (r / t)) ∂μ :=
        lintegral_mono hpt
    _ = 2 ^ (r - 1) * (2 ^ (r - 1) * (α₁ ^ r * ∫⁻ x, M₁ x ^ r ∂μ +
          α₂ ^ r * ∫⁻ x, M₂ x ^ r ∂μ) + α₃ ^ r * ∫⁻ x, M₃ x ^ (r / t) ∂μ) := by
        rw [lintegral_const_mul _ m, lintegral_add_right _ m₃, lintegral_const_mul _ m₁₂,
          lintegral_add_right _ m₂, lintegral_const_mul _ (hM₁.pow_const r),
          lintegral_const_mul _ (hM₂.pow_const r), lintegral_const_mul _ (hM₃.pow_const _)]
    _ ≤ _ := by
        gcongr
        · exact hmax h₁m hr
        · exact hmax h₂m hr
        · exact hmax h₃m hrt

/-- If `g → 0` along `l`, then eventually `K ofReal(g)^e < ε` for finite `K`, `e > 0` and
`ε > 0`; this is how the absorbed terms are made small. -/
private theorem eventually_mul_ofReal_rpow_lt {α : Type*} {l : Filter α} {g : α → ℝ}
    (hg : Tendsto g l (𝓝 0)) {K : ℝ≥0∞} (hK : K ≠ ∞) {e : ℝ} (he : 0 < e) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∀ᶠ x in l, K * ENNReal.ofReal (g x) ^ e < ε := by
  have h := ENNReal.Tendsto.const_mul
    (((ENNReal.continuous_rpow_const (y := e)).tendsto _).comp (ENNReal.tendsto_ofReal hg))
    (Or.inr hK)
  rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos he, mul_zero] at h
  exact h.eventually (gt_mem_nhds hε)

/-- A function determined almost everywhere by the equation `∑ᵢⱼ aᵢⱼ ⟪H eᵢ, eⱼ⟫ = f` is almost
everywhere strongly measurable. -/
private theorem aestronglyMeasurable_of_sum_mul_inner_eq
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    {H : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    (hH : AEStronglyMeasurable H volume) {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (heq : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪H x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = f x) :
    AEStronglyMeasurable f volume := by
  refine (aestronglyMeasurable_contraction ha hH).congr (heq.mono fun x hx => ?_)
  simp only [contraction_apply, hx]

/-- The estimate before absorption: `∫ ‖D²u‖^q` is bounded by the Fefferman–Stein constant times
the integrated pointwise bound for the sharp maximal function, in which `∫ ‖D²u‖^q` reappears with
the factors `κ⁻²` and `γ^(1/t')`. -/
private theorem lintegral_enorm_iteratedGradient_rpow_le
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) {R γ : ℝ}
    (hR : 0 < R) (hγ : 0 ≤ γ)
    (hvmo : ∀ i j, vmoModulus (fun x => a x i j) volume R ≤ ENNReal.ofReal γ)
    (z : EuclideanSpace ℝ (Fin (n + 1)))
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ 2 2)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hsupp : ∀ᵐ x, x ∉ ball z R → Wkp.iteratedGradient 1 u x = 0)
    (heq : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    (hint : Integrable (Wkp.iteratedGradient 1 u) volume) {κ : ℝ} (hκ : 1 ≤ κ) {t q : ℝ}
    (ht : 1 < t) (htq : 2 * t < q) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖Wkp.iteratedGradient 1 u x‖ₑ ^ q ≤
      CFS * ∫⁻ x, sharpMaximalFunction volume (Wkp.iteratedGradient 1 u) x ^ q) :
    ∫⁻ x, ‖Wkp.iteratedGradient 1 u x‖ₑ ^ q ≤ CFS * (2 ^ (q / 2 - 1) * (2 ^ (q / 2 - 1) *
        (ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) ^ (q / 2) *
          (ENNReal.ofReal (2 * (q / 2) * 2 ^ (q / 2 - 1) / (q / 2 - 1)) *
            4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) *
              ∫⁻ x, ‖Wkp.iteratedGradient 1 u x‖ₑ ^ q) +
        ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) ^ (q / 2) *
          (ENNReal.ofReal (2 * (q / 2) * 2 ^ (q / 2 - 1) / (q / 2 - 1)) *
            4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) * ∫⁻ x, ‖f x‖ₑ ^ q)) +
      ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * (n + 1) ^ 4 *
          ((2 * (n + 1) ^ 2 * Lam) ^ (2 * t.conjExponent - 1) * ((n + 1) ^ 2 * γ)) ^
            (1 / t.conjExponent) * (2 ^ (n + 1)) ^ (1 / t)) ^ (q / 2) *
        (ENNReal.ofReal (2 * (q / 2 / t) * 2 ^ (q / 2 / t - 1) / (q / 2 / t - 1)) *
          4 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) *
            ∫⁻ x, ‖Wkp.iteratedGradient 1 u x‖ₑ ^ q))) := by
  set H := Wkp.iteratedGradient 1 u
  have hHm : AEStronglyMeasurable H volume := hint.aestronglyMeasurable
  have hfm : AEStronglyMeasurable f volume := aestronglyMeasurable_of_sum_mul_inner_eq ha hHm heq
  have ht0 : 0 < t := by linarith
  have hsq : ∀ (y : ℝ≥0∞) (e : ℝ), e * (q / e) = q → (y ^ e) ^ (q / e) = y ^ q :=
    fun y e he => by rw [← ENNReal.rpow_mul, he]
  have h2 : ∀ y : ℝ≥0∞, (y ^ 2) ^ (q / 2) = y ^ q := fun y => by
    rw [← ENNReal.rpow_natCast, Nat.cast_ofNat]
    exact hsq y 2 (by ring)
  have h3 : ∀ y : ℝ≥0∞, (y ^ (2 * t)) ^ (q / 2 / t) = y ^ q := fun y => by
    rw [div_div]; exact hsq y (2 * t) (by field_simp)
  refine hFS.trans (mul_le_mul_right ?_ _)
  have hbound := lintegral_rpow_le_of_sq_le_maximalFunction (g := fun x =>
      sharpMaximalFunction volume H x) volume
    (h₁ := fun y => ‖H y‖ₑ ^ 2) (h₂ := fun y => ‖f y‖ₑ ^ 2) (h₃ := fun y => ‖H y‖ₑ ^ (2 * t))
    (hHm.enorm.pow_const 2) (hfm.enorm.pow_const 2) (hHm.enorm.pow_const _) ht htq
    (sq_sharpMaximalFunction_iteratedGradient_le ha hell hR hγ hvmo z u hsupp heq hκ
      (Real.HolderConjugate.conjExponent ht))
  simp only [h2, h3] at hbound
  exact hbound

/-- **The `W^{2,p}` estimate for coefficients of small mean oscillation.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `γ > 0`, depending only on `n`, `p`, `λ` and `Λ`, such that
the following holds. Let `a` be a measurable coefficient field on `ℝ^{n+1}`, uniformly elliptic
with constants `λ, Λ`, each of whose entries has VMO modulus at most `γ` at some radius `R`, and let
`u ∈ W^{2,2}(ℝ^{n+1})` have Hessian `D²u ∈ Lᵖ` vanishing outside a ball of radius `R`. If
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, then

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`.

Coefficients of vanishing mean oscillation have, for every `γ > 0`, a radius `R` at which their
VMO modulus is at most `γ`; so the estimate holds for all `u` whose Hessian is supported in a
sufficiently small ball. -/
theorem exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_vmoModulus_le {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ γ : ℝ, 0 < γ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        ∀ {R : ℝ} (z : EuclideanSpace ℝ (Fin (n + 1))),
          (∀ i j, vmoModulus (fun x => a x i j) volume R ≤ ENNReal.ofReal γ) →
          ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ 2 2)
            (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
            (∀ᵐ x, x ∉ ball z R → Wkp.iteratedGradient 1 u x = 0) →
            MemLp (Wkp.iteratedGradient 1 u) p volume →
            (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
              EuclideanSpace.single j 1⟫_ℝ = f x) →
            eLpNorm (Wkp.iteratedGradient 1 u) p volume ≤ C * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans hp).ne'
  set q := p.toReal with hq_def
  have hq : 2 < q := by
    simpa [q] using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp_top).2 hp
  set t := (1 + q / 2) / 2
  have ht : 1 < t := by simp only [t]; linarith
  have htq : 2 * t < q := by simp only [t]; linarith
  set t' := t.conjExponent
  obtain ⟨CFS, hFS⟩ := exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow
    (ι := Fin (n + 1)) (F := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (show 1 < q by linarith)
  set d := Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  set cM : ℝ≥0∞ := ENNReal.ofReal (2 * (q / 2) * 2 ^ (q / 2 - 1) / (q / 2 - 1)) * 4 ^ d
  set cM' : ℝ≥0∞ := ENNReal.ofReal (2 * (q / 2 / t) * 2 ^ (q / 2 / t - 1) / (q / 2 / t - 1)) * 4 ^ d
  have hcM : cM ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have hcM' : cM' ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  set K₁ : ℝ≥0∞ := (CFS : ℝ≥0∞) * 2 ^ (q / 2 - 1) * 2 ^ (q / 2 - 1) * cM
  set K₃ : ℝ≥0∞ := (CFS : ℝ≥0∞) * 2 ^ (q / 2 - 1) * cM'
  have h2 : (2 : ℝ≥0∞) ^ (q / 2 - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  have hK₁ : K₁ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.coe_ne_top h2) h2) hcM
  have hK₃ : K₃ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) hcM'
  have hquarter : (0 : ℝ≥0∞) < 2⁻¹ / 2 :=
    ENNReal.div_pos (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ENNReal.ofNat_ne_top
  -- Choose `κ ≥ 1` making the decaying term small.
  obtain ⟨κ, hκ, hκ1⟩ : ∃ κ : ℝ, 1 ≤ κ ∧
      K₁ * ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) ^ (q / 2) < 2⁻¹ / 2 := by
    have h1 : Tendsto (fun κ : ℝ => decayConst n lam Lam / κ ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    have h0 := h1.mul_const ((2 : ℝ) ^ (n + 1))
    rw [zero_mul] at h0
    exact ((eventually_ge_atTop 1).and (eventually_mul_ofReal_rpow_lt h0 hK₁ (by positivity)
      hquarter)).exists
  -- Then choose `γ > 0` making the coefficient term small.
  set c₃ : ℝ → ℝ := fun γ => forcingConst n lam Lam * κ ^ (n + 1) * (n + 1) ^ 4 *
    ((2 * (n + 1) ^ 2 * Lam) ^ (2 * t' - 1) * ((n + 1) ^ 2 * γ)) ^ (1 / t') *
      (2 ^ (n + 1)) ^ (1 / t)
  obtain ⟨γ, hγ1, hγ⟩ : ∃ γ : ℝ, K₃ * ENNReal.ofReal (c₃ γ) ^ (q / 2) < 2⁻¹ / 2 ∧ 0 < γ := by
    have ht' : 0 < 1 / t' := one_div_pos.2 (Real.HolderConjugate.conjExponent ht).symm.pos
    have hc : ContinuousAt c₃ 0 := by
      refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) continuousAt_const
      exact (Real.continuousAt_rpow_const _ _ (Or.inr ht'.le)).comp (by fun_prop)
    have h0 : Tendsto c₃ (𝓝[>] 0) (𝓝 0) := by
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      have hc0 : c₃ 0 = 0 := by
        have : t'⁻¹ ≠ 0 := by simpa [one_div] using ht'.ne'
        simp [c₃, Real.zero_rpow this]
      rwa [hc0] at h
    exact ((eventually_mul_ofReal_rpow_lt h0 hK₃ (by positivity) hquarter).and
      self_mem_nhdsWithin).exists
  set K₂ : ℝ≥0∞ := (CFS : ℝ≥0∞) * 2 ^ (q / 2 - 1) * 2 ^ (q / 2 - 1) *
    ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1)) ^ (q / 2) * cM
  have hK₂ : K₂ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)) hcM
  refine ⟨((2 * K₂) ^ (1 / q)).toNNReal, γ, hγ, fun {a} ha hell {R} z hvmo u f hsupp hHp heq => ?_⟩
  set H := Wkp.iteratedGradient 1 u
  have hHm : AEStronglyMeasurable H volume := hHp.aestronglyMeasurable
  rcases le_or_gt R 0 with hR | hR
  · -- For `R ≤ 0` the Hessian vanishes almost everywhere.
    have h0 : (H : EuclideanSpace ℝ (Fin (n + 1)) → _) =ᵐ[volume] 0 := by
      filter_upwards [hsupp] with x hx
      exact hx (by simp [ball_eq_empty.2 hR])
    rw [eLpNorm_congr_ae h0,
      eLpNorm_zero (ε := IteratedGradient (EuclideanSpace ℝ (Fin (n + 1))) 1)]
    exact bot_le
  rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hK₂)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hHm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top
      (aestronglyMeasurable_of_sum_mul_inner_eq ha hHm heq),
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← hq_def]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  -- The Hessian is integrable, being in `Lᵖ` and supported in a ball.
  have hint : Integrable H volume := by
    have : IsFiniteMeasure (volume.restrict (ball z R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hon : IntegrableOn H (ball z R) volume :=
      (hHp.restrict (ball z R)).integrable (one_le_two.trans hp.le)
    refine ((integrable_indicator_iff measurableSet_ball).2 hon).congr ?_
    filter_upwards [hsupp] with x hx
    by_cases hxz : x ∈ ball z R
    · rw [indicator_of_mem hxz]
    · rw [indicator_of_notMem hxz, hx hxz]
  set I := ∫⁻ x, ‖H x‖ₑ ^ q
  set J := ∫⁻ x, ‖f x‖ₑ ^ q
  have hI : I ≠ ∞ := (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp_top
    hHp.eLpNorm_lt_top).ne
  have key := lintegral_enorm_iteratedGradient_rpow_le ha hell hR hγ.le hvmo z u hsupp heq hint
    hκ ht htq (hFS H hint)
  -- Absorb the two terms carrying `I` on the right.
  have hsplit : I ≤ K₁ * ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) ^ (q / 2) * I +
      K₂ * J + K₃ * ENNReal.ofReal (c₃ γ) ^ (q / 2) * I := by
    refine key.trans_eq ?_
    simp only [K₁, K₂, K₃, c₃, t']
    ring
  have hhalf : 2⁻¹ * I + 2⁻¹ * I ≤ 2⁻¹ * I + K₂ * J := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    refine hsplit.trans ?_
    calc K₁ * ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)) ^ (q / 2) * I +
          K₂ * J + K₃ * ENNReal.ofReal (c₃ γ) ^ (q / 2) * I
        ≤ 2⁻¹ / 2 * I + K₂ * J + 2⁻¹ / 2 * I := by gcongr
      _ = 2⁻¹ * I + K₂ * J := by
        rw [add_right_comm, ← add_mul, ENNReal.add_halves]
  calc I = 2 * (2⁻¹ * I) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * (K₂ * J) := by
        gcongr 2 * ?_
        exact ENNReal.le_of_add_le_add_left (a := 2⁻¹ * I) (ENNReal.mul_ne_top (by simp) hI) hhalf
    _ = 2 * K₂ * J := (mul_assoc _ _ _).symm

end PDE

end TauCeti
