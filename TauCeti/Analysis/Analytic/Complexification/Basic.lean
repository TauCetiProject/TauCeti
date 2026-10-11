/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Complexification of real analytic functions

A real analytic function of finitely many real variables extends, near each point, to a
holomorphic function of the same number of complex variables. This file constructs that extension
from a power series.

Let `p n` be a continuous `ℝ`-multilinear map on `ι → ℝ` with values in `ℝ`, where `ι` is finite.
Expanding each argument in the standard basis, `p n v = ∑ r, (∏ k, v k (r k)) * p n (e_r)`, where
`r` runs over the maps from the arguments to `ι` and `e_r` is the tuple of basis vectors it
selects. The same formula with complex `v` defines a continuous `ℂ`-multilinear map on `ι → ℂ`,
the *complexification* `ContinuousMultilinearMap.complexifyPi`. It agrees with `p n` on real
arguments, it commutes with complex conjugation because its coefficients `p n (e_r)` are real, and
its norm is at most `(card ι) ^ n` times that of `p n`. Applied to every term of a formal power
series, this gives `FormalMultilinearSeries.complexifyPi`, whose radius of convergence is at least
the original radius divided by `card ι`.

Summing the complexified series of a real analytic function `f` at a point `a` gives a function
`F` that is complex analytic on a ball around `a` (a polydisc, since `ι → ℂ` carries the sup norm),
agrees with `f` on the real points of that ball, and satisfies `F (conj z) = conj (F z)` for every
`z`. The same holds coordinatewise for real analytic maps `(ι → ℝ) → (κ → ℝ)`, such as the chart
maps of a real analytic submanifold. This is the form in which statements about complex analytic
functions, such as the local behaviour of roots of a polynomial with analytic coefficients, are
applied to real analytic data.

The complexification is determined by the real function: a complex analytic function vanishing at
the real points near a real point vanishes near it. The proof restricts the power series to the
real points, where it represents zero, so each homogeneous term vanishes on real vectors; along the
complex line through two real vectors such a term is an entire function vanishing on the real
axis, hence zero. Consequently every complex analytic extension of a real-valued real analytic germ
commutes with complex conjugation near the point, not only the one constructed here.

## Main declarations

* `ContinuousMultilinearMap.complexifyPi`: the complexification of a real multilinear form on
  `ι → ℝ`, with `complexifyPi_apply_ofReal`, `eq_complexifyPi_of_forall_ofReal`,
  `complexifyPi_apply_star` and `norm_complexifyPi_le`; it is `ℝ`-linear (`complexifyPi_zero`,
  `complexifyPi_add`, `complexifyPi_smul`).
* `FormalMultilinearSeries.complexifyPi`: the termwise complexification of a power series, with
  `FormalMultilinearSeries.le_radius_complexifyPi`.
* `AnalyticAt.exists_complexification`: a real analytic function has, on a polydisc around the
  point, a complex analytic extension compatible with conjugation.
* `AnalyticAt.exists_complexification_pi`: the same for real analytic maps to `κ → ℝ`.
* `AnalyticAt.eventually_eq_zero_of_eventually_real`, `AnalyticAt.eventuallyEq_of_eventually_real`:
  the identity theorem for complex analytic functions on the real points.
* `AnalyticAt.eventually_comp_eq_id_of_eventually_real`: complex analytic extensions preserve a
  composition law equal to the identity near a real point.
* `AnalyticAt.eventually_apply_star`: a complex analytic function that is real at the real points
  near a real point commutes with conjugation near it.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002.
-/

public section

open Filter Metric Set
open scoped NNReal ENNReal Topology

namespace ContinuousMultilinearMap

variable {ν ι : Type*} [Fintype ν] [Fintype ι]

open scoped Classical in
/-- The complexification of a continuous real multilinear form `f` on `ι → ℝ`, for finite `ι`: the
complex multilinear form on `ι → ℂ` given by `v ↦ ∑ r, f (e_r) * ∏ k, v k (r k)`, where `r` runs
over the maps `ν → ι` and `e_r` is the tuple of standard basis vectors `Pi.single (r k) 1`. It
agrees with `f` on real arguments (`complexifyPi_apply_ofReal`). -/
noncomputable def complexifyPi (f : ContinuousMultilinearMap ℝ (fun _ : ν ↦ ι → ℝ) ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : ν ↦ ι → ℂ) ℂ :=
  ∑ r : ν → ι, ((f fun k ↦ Pi.single (r k) 1 : ℝ) : ℂ) •
    (ContinuousMultilinearMap.mkPiAlgebra ℂ ν ℂ).compContinuousLinearMap
      fun k ↦ ContinuousLinearMap.proj (r k)

variable (f : ContinuousMultilinearMap ℝ (fun _ : ν ↦ ι → ℝ) ℝ)

/-- The complexification of `f` evaluates to `∑ r, f (e_r) * ∏ k, v k (r k)`. -/
theorem complexifyPi_apply [DecidableEq ν] [DecidableEq ι] (v : ν → ι → ℂ) :
    f.complexifyPi v = ∑ r : ν → ι, ((f fun k ↦ Pi.single (r k) 1 : ℝ) : ℂ) * ∏ k, v k (r k) := by
  simp only [complexifyPi, sum_apply, smul_apply, compContinuousLinearMap_apply,
    ContinuousLinearMap.proj_apply, mkPiAlgebra_apply, smul_eq_mul]
  congr!

/-- The complexification of a real multilinear form agrees with it on real arguments. -/
@[simp]
theorem complexifyPi_apply_ofReal (v : ν → ι → ℝ) :
    f.complexifyPi (fun k i ↦ (v k i : ℂ)) = f v := by
  classical
  -- expand each argument of `f` in the standard basis
  have hv : f v = ∑ r : ν → ι, (∏ k, v k (r k)) * f fun k ↦ Pi.single (r k) 1 := by
    have hbasis : v = fun k ↦ ∑ i, v k i • Pi.single (M := fun _ ↦ ℝ) i 1 :=
      funext fun k ↦ pi_eq_sum_univ' (v k)
    conv_lhs => rw [hbasis]
    simp [map_sum, map_smul_univ]
  simp [complexifyPi_apply, hv, mul_comm]

/-- The complexification of a real multilinear form is the only complex multilinear form on
`ι → ℂ` that agrees with it on real arguments. -/
theorem eq_complexifyPi_of_forall_ofReal {g : ContinuousMultilinearMap ℂ (fun _ : ν ↦ ι → ℂ) ℂ}
    (hg : ∀ v : ν → ι → ℝ, g (fun k i ↦ (v k i : ℂ)) = f v) : g = f.complexifyPi := by
  classical
  refine toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ ↦ Pi.basisFun ℂ ι) fun r ↦ ?_)
  have hr : (fun k ↦ Pi.basisFun ℂ ι (r k)) =
      fun k i ↦ ((Pi.single (M := fun _ ↦ ℝ) (r k) 1 i : ℝ) : ℂ) := by
    ext k i
    simp [Pi.single_apply, apply_ite]
  simp only [coe_coe, hr, hg, complexifyPi_apply_ofReal]

/-- The complexification of a real multilinear form commutes with complex conjugation. -/
@[simp]
theorem complexifyPi_apply_star (v : ν → ι → ℂ) :
    f.complexifyPi (star v) = star (f.complexifyPi v) := by
  classical
  simp [complexifyPi_apply, star_sum, star_prod]

/-- The complexification of the zero form is zero. -/
@[simp]
theorem complexifyPi_zero :
    (0 : ContinuousMultilinearMap ℝ (fun _ : ν ↦ ι → ℝ) ℝ).complexifyPi = 0 :=
  (eq_complexifyPi_of_forall_ofReal _ fun v ↦ by simp).symm

/-- Complexification is additive. -/
@[simp]
theorem complexifyPi_add (g : ContinuousMultilinearMap ℝ (fun _ : ν ↦ ι → ℝ) ℝ) :
    (f + g).complexifyPi = f.complexifyPi + g.complexifyPi :=
  (eq_complexifyPi_of_forall_ofReal _ fun v ↦ by simp).symm

/-- Complexification commutes with real scalar multiplication. -/
@[simp]
theorem complexifyPi_smul (c : ℝ) : (c • f).complexifyPi = (c : ℂ) • f.complexifyPi :=
  (eq_complexifyPi_of_forall_ofReal _ fun v ↦ by simp).symm

/-- Complexification multiplies the norm of a real multilinear form on `ι → ℝ` by at most
`(card ι) ^ (card ν)`. -/
theorem norm_complexifyPi_le :
    ‖f.complexifyPi‖ ≤ Fintype.card ι ^ Fintype.card ν * ‖f‖ := by
  classical
  refine opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [complexifyPi_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm (r : ν → ι) :
      ‖((f fun k ↦ Pi.single (r k) 1 : ℝ) : ℂ) * ∏ k, v k (r k)‖ ≤ ‖f‖ * ∏ k, ‖v k‖ := by
    rw [norm_mul, Complex.norm_real, norm_prod]
    refine mul_le_mul ?_ (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      (fun k _ ↦ norm_le_pi_norm (v k) (r k))) (by positivity) (norm_nonneg f)
    refine (f.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg f) ?_)
    exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun k _ ↦ by simp [Pi.norm_single])
  refine (Finset.sum_le_sum fun r _ ↦ hterm r).trans_eq ?_
  simp [mul_assoc]

end ContinuousMultilinearMap

namespace ContinuousMultilinearMap

variable {ν ι E : Type*} [Finite ν] [Finite ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A complex multilinear map on `ι → ℂ` whose values on constant tuples of real vectors vanish
also vanishes on constant tuples of complex vectors. -/
theorem apply_const_eq_zero_of_forall_ofReal {Q : ContinuousMultilinearMap ℂ (fun _ : ν ↦ ι → ℂ) E}
    (h : ∀ y : ι → ℝ, Q (fun _ ↦ fun i ↦ (y i : ℂ)) = 0) (z : ι → ℂ) : Q (fun _ ↦ z) = 0 := by
  have := Fintype.ofFinite ν
  have := Fintype.ofFinite ι
  set x : ι → ℂ := fun i ↦ ((z i).re : ℂ)
  set y : ι → ℂ := fun i ↦ ((z i).im : ℂ)
  have hz : z = x + Complex.I • y := by
    ext i; simp [x, y, mul_comm Complex.I, Complex.re_add_im]
  -- `t ↦ Q (x + t y, …, x + t y)` is entire and vanishes on the real line, so it vanishes at `I`
  set φ : ℂ → E := fun t ↦ Q (fun _ ↦ x + t • y)
  have hφ : AnalyticOnNhd ℂ φ univ := fun t _ ↦ by
    have : AnalyticAt ℂ (fun t : ℂ ↦ fun _ : ν ↦ x + t • y) t :=
      AnalyticAt.pi fun _ ↦ analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    exact Q.analyticAt.comp this
  have hreal (t : ℝ) : φ t = 0 := by
    convert h fun i ↦ (z i).re + t * (z i).im using 2
    ext _; simp [x, y]
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), φ t = 0 := by
    have hT : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun t ht ↦ by simpa using ht)
    exact hT.frequently (Frequently.of_forall hreal)
  simpa [φ, ← hz] using hφ.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ 0) hfreq (mem_univ Complex.I)

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

variable {ι : Type*} [Fintype ι]

/-- The termwise complexification of a real formal power series on `ι → ℝ` with values in `ℝ`. -/
noncomputable def complexifyPi (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (ι → ℂ) ℂ :=
  fun n ↦ (p n).complexifyPi

variable (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ)

/-- The terms of the complexified series are the complexified terms. -/
@[simp]
theorem complexifyPi_apply (n : ℕ) : p.complexifyPi n = (p n).complexifyPi := (rfl)

/-- The complexification of the zero series is zero. -/
@[simp]
theorem complexifyPi_zero : (0 : FormalMultilinearSeries ℝ (ι → ℝ) ℝ).complexifyPi = 0 := by
  ext1 n
  simp

/-- Termwise complexification is additive. -/
@[simp]
theorem complexifyPi_add (q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) :
    (p + q).complexifyPi = p.complexifyPi + q.complexifyPi := by
  ext1 n
  simp

/-- Termwise complexification commutes with real scalar multiplication. -/
@[simp]
theorem complexifyPi_smul (c : ℝ) : (c • p).complexifyPi = (c : ℂ) • p.complexifyPi := by
  ext1 n
  simp

/-- Complexification divides the radius of convergence by at most `card ι`. -/
theorem le_radius_complexifyPi {r : ℝ≥0} (hr : ((Fintype.card ι * r : ℝ≥0) : ℝ≥0∞) < p.radius) :
    (r : ℝ≥0∞) ≤ p.complexifyPi.radius := by
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  refine le_radius_of_bound _ C fun n ↦ ?_
  calc ‖p.complexifyPi n‖ * (r : ℝ) ^ n
      ≤ Fintype.card ι ^ n * ‖p n‖ * (r : ℝ) ^ n := by
        gcongr
        simpa using (p n).norm_complexifyPi_le
    _ = ‖p n‖ * ((Fintype.card ι * r : ℝ≥0) : ℝ) ^ n := by push_cast; ring
    _ ≤ C := hC n

/-- On real arguments, the sum of the complexified series is the sum of the real series. -/
@[simp]
theorem complexifyPi_sum_ofReal (y : ι → ℝ) :
    p.complexifyPi.sum (fun i ↦ (y i : ℂ)) = (p.sum y : ℂ) := by
  simp only [FormalMultilinearSeries.sum, complexifyPi_apply]
  simp [Complex.ofReal_tsum]

/-- The sum of the complexified series commutes with complex conjugation. -/
@[simp]
theorem complexifyPi_sum_star (z : ι → ℂ) :
    p.complexifyPi.sum (star z) = star (p.complexifyPi.sum z) := by
  simp only [FormalMultilinearSeries.sum, complexifyPi_apply, tsum_star]
  congr 1
  ext n
  exact (p n).complexifyPi_apply_star fun _ ↦ z

end FormalMultilinearSeries

namespace AnalyticAt

variable {ι κ : Type*} [Fintype ι]

/-- **Identity theorem on the real points.** A complex analytic function of finitely many
variables that vanishes at the real points near a real point vanishes near that point. -/
theorem eventually_eq_zero_of_eventually_real {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F : (ι → ℂ) → E} {a : ι → ℝ} (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ)))
    (h : ∀ᶠ x in 𝓝 a, F (fun i ↦ (x i : ℂ)) = 0) :
    ∀ᶠ z in 𝓝 (fun i ↦ (a i : ℂ)), F z = 0 := by
  obtain ⟨Q, r, hQ⟩ := hF
  let u : (ι → ℝ) →L[ℝ] (ι → ℂ) := ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
  have hu (x : ι → ℝ) : u x = fun i ↦ (x i : ℂ) := by ext i; simp [u]
  -- restricted to the real points, the power series of `F` represents the zero function
  have h0 : HasFPowerSeriesAt 0 ((Q.restrictScalars ℝ).compContinuousLinearMap u) a :=
    (hQ.hasFPowerSeriesAt.restrictScalars (𝕜 := ℝ)).compContinuousLinearMap (u := u)
      |>.congr (h.mono fun x hx ↦ by simpa [hu] using hx)
  have hQ0 (n : ℕ) (z : ι → ℂ) : Q n (fun _ ↦ z) = 0 :=
    (Q n).apply_const_eq_zero_of_forall_ofReal (fun y ↦ by
      simpa [Function.comp_def, hu] using h0.apply_eq_zero n y) z
  filter_upwards [Metric.eball_mem_nhds _ hQ.r_pos] with z hz
  have hz' : z - (fun i ↦ (a i : ℂ)) ∈ Metric.eball 0 r := by
    rwa [Metric.mem_eball, edist_zero_right, ← edist_eq_enorm_sub]
  have hsum := hQ.hasSum hz'
  rw [add_sub_cancel] at hsum
  simp only [hQ0] at hsum
  exact hsum.unique hasSum_zero

/-- Two complex analytic functions of finitely many variables that agree at the real points near a
real point agree near that point. -/
theorem eventuallyEq_of_eventually_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F G : (ι → ℂ) → E} {a : ι → ℝ} (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ)))
    (hG : AnalyticAt ℂ G (fun i ↦ (a i : ℂ)))
    (h : ∀ᶠ x in 𝓝 a, F (fun i ↦ (x i : ℂ)) = G fun i ↦ (x i : ℂ)) :
    F =ᶠ[𝓝 fun i ↦ (a i : ℂ)] G := by
  filter_upwards [(hF.sub hG).eventually_eq_zero_of_eventually_real
    (h.mono fun x hx ↦ sub_eq_zero.2 hx)] with z hz using sub_eq_zero.1 hz

/-- If real maps have composition `g ∘ f` equal to the identity near a real point, their complex
analytic extensions compose to the identity near the corresponding complex point. -/
theorem eventually_comp_eq_id_of_eventually_real [Fintype κ]
    {f : (ι → ℝ) → κ → ℝ} {g : (κ → ℝ) → ι → ℝ} {a : ι → ℝ}
    {F : (ι → ℂ) → κ → ℂ} {G : (κ → ℂ) → ι → ℂ}
    (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ)))
    (hG : AnalyticAt ℂ G (fun i ↦ (f a i : ℂ)))
    (hFr : ∀ᶠ x in 𝓝 a, F (fun i ↦ (x i : ℂ)) = fun i ↦ (f x i : ℂ))
    (hGr : ∀ᶠ y in 𝓝 (f a), G (fun i ↦ (y i : ℂ)) = fun i ↦ (g y i : ℂ))
    (hgf : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    ∀ᶠ z in 𝓝 (fun i ↦ (a i : ℂ)), G (F z) = z := by
  have hFc : ContinuousAt (fun x : ι → ℝ ↦ F (fun i ↦ (x i : ℂ))) a :=
    hF.continuousAt.comp
      (continuous_pi fun i ↦ Complex.continuous_ofReal.comp (continuous_apply i)).continuousAt
  have hreal : ContinuousAt (fun x : ι → ℝ ↦ fun k ↦ (F (fun i ↦ (x i : ℂ)) k).re) a :=
    continuousAt_pi.2 fun k ↦ Complex.continuous_re.continuousAt.comp
      ((continuous_apply k).continuousAt.comp hFc)
  have hf : ContinuousAt f a :=
    hreal.congr (hFr.mono fun x hx ↦ by simp only [hx, Complex.ofReal_re])
  have hFa := hFr.self_of_nhds
  apply (hG.comp_of_eq hF hFa).eventuallyEq_of_eventually_real analyticAt_id
  filter_upwards [hFr, hf.eventually hGr, hgf] with x hFx hGx hgfx
  simp only [Function.comp_apply, id_eq, hFx, hGx, hgfx]

/-- **Complexification of a real analytic function.** A function of finitely many real variables
that is analytic at `a` extends to a function `F` of as many complex variables that is complex
analytic on a ball (a polydisc) around `a`, agrees with `f` at the real points of that ball, and
commutes with complex conjugation. -/
theorem exists_complexification {f : (ι → ℝ) → ℝ} {a : ι → ℝ} (hf : AnalyticAt ℝ f a) :
    ∃ r > (0 : ℝ), ∃ F : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ F (ball (fun i ↦ (a i : ℂ)) r) ∧
      (∀ x ∈ ball a r, F (fun i ↦ (x i : ℂ)) = f x) ∧ ∀ z, F (star z) = star (F z) := by
  obtain ⟨p, R, hR⟩ := hf
  obtain ⟨s, hs0, hsR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hR.r_pos
  -- shrink the radius by `card ι + 1` so that it lies inside both disks of convergence
  set m : ℝ≥0 := (Fintype.card ι : ℝ≥0)
  set r : ℝ≥0 := s / (m + 1) with hr
  have hs0' : (0 : ℝ≥0) < s := by exact_mod_cast hs0
  have hr0 : 0 < r := div_pos hs0' (by positivity)
  have hmr : m * r < s := by
    rw [hr, mul_div_assoc', div_lt_iff₀ (by positivity), mul_comm]
    exact mul_lt_mul_of_pos_left (lt_add_one m) hs0'
  have hrs : r ≤ s := div_le_self zero_le (le_add_of_nonneg_left zero_le)
  have hrP : (r : ℝ≥0∞) ≤ p.complexifyPi.radius :=
    p.le_radius_complexifyPi ((ENNReal.coe_lt_coe.2 hmr).trans (hsR.trans_le hR.r_le))
  have hP := (p.complexifyPi.hasFPowerSeriesOnBall ((ENNReal.coe_pos.2 hr0).trans_le hrP)).comp_sub
    (fun i ↦ (a i : ℂ))
  rw [zero_add] at hP
  refine ⟨r, hr0, fun z ↦ p.complexifyPi.sum (z - fun i ↦ (a i : ℂ)), ?_, fun x hx ↦ ?_,
    fun z ↦ ?_⟩
  · exact hP.analyticOnNhd.mono (by rw [← Metric.eball_coe]; exact Metric.eball_subset_eball hrP)
  · have hxa : x - a ∈ Metric.eball (0 : ι → ℝ) R := by
      refine Metric.eball_subset_eball ((ENNReal.coe_le_coe.2 hrs).trans hsR.le) ?_
      rwa [Metric.eball_coe, mem_ball_zero_iff, ← dist_eq_norm, ← mem_ball]
    have hsub : ((fun i ↦ (x i : ℂ)) - fun i ↦ (a i : ℂ)) = fun i ↦ ((x - a) i : ℂ) := by
      ext i; simp
    beta_reduce
    rw [hsub, p.complexifyPi_sum_ofReal, ← hR.sum hxa, add_sub_cancel]
  · have hsub : star z - (fun i ↦ (a i : ℂ)) = star (z - fun i ↦ (a i : ℂ)) := by
      ext i; simp
    beta_reduce
    rw [hsub, p.complexifyPi_sum_star]

/-- **Complexification of a real analytic map.** A map from `ι → ℝ` to `κ → ℝ`, with `ι` and `κ`
finite, that is analytic at `a` extends to a map `F : (ι → ℂ) → (κ → ℂ)` that is complex analytic
on a ball (a polydisc) around `a`, agrees with `f` at the real points of that ball, and commutes
with complex conjugation. -/
theorem exists_complexification_pi [Fintype κ] {f : (ι → ℝ) → κ → ℝ} {a : ι → ℝ}
    (hf : AnalyticAt ℝ f a) :
    ∃ r > (0 : ℝ), ∃ F : (ι → ℂ) → κ → ℂ, AnalyticOnNhd ℂ F (ball (fun i ↦ (a i : ℂ)) r) ∧
      (∀ x ∈ ball a r, F (fun i ↦ (x i : ℂ)) = fun k ↦ (f x k : ℂ)) ∧
        ∀ z, F (star z) = star (F z) := by
  choose r hr F hF hfF hFstar using fun k ↦
    ((analyticAt_pi_iff (f := fun k x ↦ f x k)).1 hf k).exists_complexification
  -- a common radius for the finitely many coordinates
  obtain ⟨ρ, hρ, hρr⟩ := (Filter.Eventually.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
    (Filter.eventually_all.2 fun k ↦ Ioo_mem_nhdsGT (hr k))).exists
  refine ⟨ρ, hρ, fun z k ↦ F k z, ?_, fun x hx ↦ funext fun k ↦ ?_, fun z ↦ funext fun k ↦ ?_⟩
  · exact analyticOnNhd_pi_iff.2 fun k ↦ (hF k).mono (ball_subset_ball (hρr k).2.le)
  · exact hfF k x (ball_subset_ball (hρr k).2.le hx)
  · exact hFstar k z

/-- **Conjugation compatibility of complexifications.** A complex analytic function of finitely
many variables that takes real values at the real points near a real point `a` commutes with
complex conjugation near `a`. -/
theorem eventually_apply_star {F : (ι → ℂ) → ℂ} {a : ι → ℝ}
    (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ))) (hreal : ∀ᶠ x in 𝓝 a, (F fun i ↦ (x i : ℂ)).im = 0) :
    ∀ᶠ z in 𝓝 (fun i ↦ (a i : ℂ)), F (star z) = star (F z) := by
  let u : (ι → ℝ) →L[ℝ] (ι → ℂ) := ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
  -- `F` is the complexification of the real part of its restriction to the real points
  have hf : AnalyticAt ℝ (fun x : ι → ℝ ↦ (F fun i ↦ (x i : ℂ)).re) a :=
    Complex.reCLM.analyticAt _ |>.comp
      ((hF.restrictScalars (𝕜 := ℝ)).compContinuousLinearMap (u := u))
  obtain ⟨r, hr, G, hG, hGf, hGstar⟩ := hf.exists_complexification
  have hFG : F =ᶠ[𝓝 fun i ↦ (a i : ℂ)] G := by
    refine hF.eventuallyEq_of_eventually_real (hG _ (mem_ball_self hr)) ?_
    filter_upwards [hreal, ball_mem_nhds a hr] with x hx hxr
    rw [hGf x hxr]
    exact Complex.ext (by simp) (by simp [hx])
  have hstar : Tendsto star (𝓝 fun i ↦ (a i : ℂ)) (𝓝 fun i ↦ (a i : ℂ)) := by
    have ha : (star fun i ↦ (a i : ℂ)) = fun i ↦ (a i : ℂ) := by ext i; simp
    have h := continuous_star.tendsto (fun i ↦ (a i : ℂ))
    rwa [ha] at h
  filter_upwards [hFG, hstar.eventually hFG] with z hz hz'
  rw [hz', hz, hGstar]

end AnalyticAt
