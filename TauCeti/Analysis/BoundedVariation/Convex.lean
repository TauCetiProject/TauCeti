/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Normed.Module.LipschitzHyperplane
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cutting by half-spaces and the perimeter of convex sets

Let `μ` be a measure on a finite-dimensional real inner product space `E`, finite on compact sets
(an additive Haar measure for the results on convex sets). This file proves that cutting a set of
finite measure by a closed half-space does not increase its perimeter, and deduces that the
perimeter is monotone under inclusion of convex sets: a convex set has perimeter at most that of
any null-measurable set of finite measure containing it. In particular bounded convex sets have
finite perimeter.

Monotonicity under convex inclusion is how perimeters of convex bodies are compared. For a
convex body `K` containing the ball `closedBall c r`, the outer parallel body
`K + t • closedBall 0 1` lies in the dilate of `K` about `c` by `1 + t / r`, so its perimeter is at
most `(1 + t / r) ^ (n - 1) P(K)`. This is the upper bound needed to identify the right derivative
of the volume of outer parallel bodies with the perimeter.

The half-space estimate is proved by duality, without any boundary regularity. Given an admissible
test vector field `φ`, the field `ψ` that extends the normal component of `φ` on the hyperplane
`{f = c}` constantly in the normal direction is divergence-free above the hyperplane, so pairing
`s` with `φ` below the hyperplane and with `ψ` above it gives `∫_{s ∩ {f ≤ c}} div φ` up to a
term controlled by `μ (s ∩ {f ≥ c + n})`. The glued field is not smooth, but it can be smoothed
across a slab of width `1 / (n + 1)` because the normal components agree on the hyperplane
(`TauCeti.ofReal_setIntegral_add_setIntegral_le_perimeter`).

## Main results

* `TauCeti.ofReal_setIntegral_add_setIntegral_le_perimeter`: two admissible test vector fields
  whose normal components agree on a hyperplane can be glued along it.
* `TauCeti.perimeter_inter_halfSpace_le`: `P(s ∩ {f ≤ c}) ≤ P(s)` for `s` of finite measure.
* `Convex.perimeter_le_of_subset`: `P(K) ≤ P(L)` for `K` convex and `K ⊆ L`, `μ L < ∞`.
* `Convex.perimeter_lt_top`: a bounded convex set has finite perimeter.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 12.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Filter TopologicalSpace TestFunction
open scoped ENNReal Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The slab error term of the gluing: if `|y| ≤ C |t|` then `ψ₀'((n + 1) t) (n + 1) y` is bounded
by `M C`, where `M` bounds the derivative of the smooth transition `ψ₀`, supported in `[0, 1]`. -/
private theorem abs_deriv_smoothTransition_mul_le {M C : ℝ}
    (hM : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ M) (hC : 0 ≤ C) (n : ℕ) {t y : ℝ}
    (hy : |y| ≤ C * |t|) :
    |deriv Real.smoothTransition ((n + 1) * t) * ((n + 1) * y)| ≤ M * C := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rcases lt_or_ge ((n + 1) * t) 0 with ht | ht
  · simpa [Real.smoothTransition.deriv_of_neg ht] using mul_nonneg hM0 hC
  rcases lt_or_ge 1 ((n + 1) * t) with ht' | ht'
  · simpa [Real.smoothTransition.deriv_of_one_lt ht'] using mul_nonneg hM0 hC
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [abs_mul, abs_mul, abs_of_pos hn]
  refine mul_le_mul (hM _) ?_ (by positivity) hM0
  calc (n + 1) * |y| ≤ (n + 1) * (C * |t|) := by gcongr
    _ = C * |(n + 1) * t| := by rw [abs_mul, abs_of_pos hn]; ring
    _ ≤ C * 1 := by rw [abs_of_nonneg ht]; gcongr
    _ = C := mul_one _

variable [FiniteDimensional ℝ E]

/-- **Extending the normal component of a test vector field off a hyperplane.** For an admissible
`φ ∈ 𝓓(E, E)` and `n : ℕ`, there is an admissible `ψ` with the same normal component `f ∘ ψ` as `φ`
on the hyperplane `{f = c}`, whose divergence above the hyperplane is bounded by `M ‖f‖` and
vanishes on the slab `c < f < c + n`. Here `M` bounds the derivative of the smooth transition. -/
private theorem exists_normal_extension (f : StrongDual ℝ E) (hf : f ≠ 0) (c : ℝ)
    {φ : 𝓓(⊤, E)} (hφ : ∀ x, ‖φ x‖ ≤ 1) {M : ℝ}
    (hM : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ M) (n : ℕ) :
    ∃ ψ : 𝓓(⊤, E), (∀ x, ‖ψ x‖ ≤ 1) ∧ (∀ x, f x = c → f (φ x) = f (ψ x)) ∧
      (∀ x, c < f x → ‖divergenceCLM ψ x‖ ≤ M * ‖f‖) ∧
      ∀ x, c < f x → f x < c + n → divergenceCLM ψ x = 0 := by
  -- The normal direction: `w` is normal to `{f = c}`, with `f w = 1` and `‖f‖ ‖w‖ = 1`.
  set u := (InnerProductSpace.toDual ℝ E).symm f
  have hnu : ‖u‖ = ‖f‖ := LinearIsometryEquiv.norm_map _ _
  have hf0 : ‖f‖ ≠ 0 := norm_ne_zero_iff.2 hf
  set w := (‖f‖ ^ 2)⁻¹ • u
  have hw : f w = 1 := by
    rw [map_smul, smul_eq_mul, ← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq,
      hnu, inv_mul_cancel₀ (pow_ne_zero 2 hf0)]
  have hnw : ‖f‖ * ‖w‖ = 1 := by
    rw [norm_smul, hnu, norm_inv, norm_pow, Real.norm_of_nonneg (norm_nonneg f)]
    field_simp
  have hφc := φ.contDiff
  -- `x - (f x - c) • w` is the projection of `x` to the hyperplane `{f = c}` along `w`, and
  -- `ψ = η (f x) f (φ (x - (f x - c) • w)) • w`, with `η` a cutoff equal to one on
  -- `[c, c + n]` and supported in `(c - 1, c + n + 1)`.
  have hP (x : E) (t : ℝ) : x + t • w - (f (x + t • w) - c) • w = x - (f x - c) • w := by
    simp only [map_add, map_smul, hw, smul_eq_mul, mul_one]
    module
  obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(⊤, E), ⇑ψ = fun x =>
      ((Real.smoothTransition (f x - c + 1) * (1 - Real.smoothTransition (f x - (c + n)))) *
        f (φ (x - (f x - c) • w))) • w := by
    refine ⟨⟨_, ContDiff.smul (by fun_prop) contDiff_const, HasCompactSupport.intro
      ((φ.hasCompactSupport.isCompact.prod (isCompact_Icc (a := (-1 : ℝ)) (b := n + 1))).image
        (f := fun p : E × ℝ => p.1 + p.2 • w) (by fun_prop)) fun x hx => ?_, by simp⟩, rfl⟩
    by_contra h
    refine hx ⟨(x - (f x - c) • w, f x - c), ⟨subset_tsupport _ fun h' => h ?_, ?_⟩, by simp⟩
    · simp [h']
    have h₁ : Real.smoothTransition (f x - c + 1) ≠ 0 := fun h' => h (by simp [h'])
    have h₂ : Real.smoothTransition (f x - (c + n)) ≠ 1 := fun h' => h (by simp [h'])
    rw [Ne, Real.smoothTransition.zero_iff_nonpos] at h₁
    rw [Ne, Real.smoothTransition.eq_one_iff_one_le] at h₂
    constructor <;> linarith
  have hfφ (x : E) : ‖f (φ (x - (f x - c) • w))‖ ≤ ‖f‖ :=
    (f.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg f) (hφ _))
  -- Above the hyperplane, the divergence of `ψ` only sees the upper cutoff.
  have hdivψ (x : E) (hx : c < f x) : divergenceCLM ψ x =
      -(deriv Real.smoothTransition (f x - (c + n)) * f (φ (x - (f x - c) • w))) := by
    set h : E → ℝ := fun y => (1 - Real.smoothTransition (f y - (c + n))) *
      f (φ (y - (f y - c) • w))
    have hloc : (ψ : E → E) =ᶠ[𝓝 x] fun y => h y • w := by
      filter_upwards [(isOpen_lt continuous_const f.continuous).mem_nhds hx] with y hy
      have hy : c < f y := hy
      simp [hψ, h, Real.smoothTransition.one_of_one_le (show 1 ≤ f y - c + 1 by linarith)]
    have hhd : DifferentiableAt ℝ h x := by
      have := hφc.differentiable (by simp)
      fun_prop
    have hline : (fun t : ℝ => h (x + t • w)) =
        fun t => (1 - Real.smoothTransition (f x + t - (c + n))) *
          f (φ (x - (f x - c) • w)) := by
      ext t
      simp only [h, hP]
      simp [hw]
    have hd : HasDerivAt (fun t : ℝ => (1 - Real.smoothTransition (f x + t - (c + n))) *
        f (φ (x - (f x - c) • w)))
        (-(deriv Real.smoothTransition (f x - (c + n)) * f (φ (x - (f x - c) • w)))) 0 := by
      have := (((((hasDerivAt_id (0 : ℝ)).const_add (f x)).sub_const (c + n)).smoothTransition
        ).const_sub 1).mul_const (f (φ (x - (f x - c) • w)))
      simpa using this
    rw [divergenceCLM_apply, hloc.fderiv_eq, trace_fderiv_smul_const hhd,
      ← hhd.lineDeriv_eq_fderiv, lineDeriv, hline, hd.deriv]
  refine ⟨ψ, fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx hxn => ?_⟩
  · have h₀ := Real.smoothTransition.nonneg (f x - c + 1)
    have h₁ := Real.smoothTransition.le_one (f x - c + 1)
    have h₂ := Real.smoothTransition.nonneg (f x - (c + n))
    have h₃ := Real.smoothTransition.le_one (f x - (c + n))
    have hη : ‖Real.smoothTransition (f x - c + 1) * (1 - Real.smoothTransition (f x - (c + n)))‖
        ≤ 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg h₀ (by linarith))]
      nlinarith
    rw [hψ, norm_smul, norm_mul]
    calc _ ≤ (1 * ‖f‖) * ‖w‖ := by gcongr; exact hfφ x
      _ = 1 := by rw [one_mul, hnw]
  · have h₀ : (-(n : ℝ)) ≤ 0 := by simp
    simp [hψ, hx, hw, Real.smoothTransition.zero_of_nonpos h₀]
  · rw [hdivψ x hx, norm_neg, norm_mul]
    exact mul_le_mul (hM _) (hfφ x) (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
  · rw [hdivψ x hx, Real.smoothTransition.deriv_of_neg (by linarith), zero_mul, neg_zero]

variable [MeasurableSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E}

/-- **Gluing admissible vector fields along a hyperplane.** Let `φ` and `ψ` be test vector fields
on `Ω` with `‖φ‖, ‖ψ‖ ≤ 1` whose normal components `f ∘ φ` and `f ∘ ψ` agree on the hyperplane
`{f = a}`. Then the field equal to `φ` on the half-space `{f ≤ a}` and to `ψ` on `{f > a}` still
pairs with a null-measurable set `s` to at most its perimeter:
`∫_{s ∩ {f ≤ a}} div φ + ∫_{s ∩ {f > a}} div ψ ≤ P(s; Ω)`. -/
theorem ofReal_setIntegral_add_setIntegral_le_perimeter [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (f : StrongDual ℝ E) (a : ℝ) {φ ψ : 𝓓(Ω, E)}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hψ : ∀ x, ‖ψ x‖ ≤ 1) (hφψ : ∀ x, f x = a → f (φ x) = f (ψ x))
    (hs : NullMeasurableSet s μ) :
    ENNReal.ofReal ((∫ x in s ∩ {x | f x ≤ a}, divergenceCLM φ x ∂μ) +
      ∫ x in s ∩ {x | a < f x}, divergenceCLM ψ x ∂μ) ≤ perimeter μ Ω s := by
  -- Interpolate by `Φₙ = φ + σₙ (ψ - φ)`, where `σₙ = ψ₀ ((n + 1) (f - a))` for the smooth
  -- transition `ψ₀`; the error term `σₙ' f (ψ - φ)` lives on a slab of width `1 / (n + 1)`, where
  -- `f (ψ - φ) = O (1 / (n + 1))`.
  set χ : 𝓓(Ω, E) := ψ - φ
  set σ : ℕ → E → ℝ := fun n x => Real.smoothTransition ((n + 1) * (f x - a))
  have hσ (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (σ n) := by fun_prop
  have hσd (n : ℕ) (x : E) : HasFDerivAt (σ n)
      (deriv Real.smoothTransition ((n + 1) * (f x - a)) • (((n : ℝ) + 1) • f)) x := by
    refine HasFDerivAt.smoothTransition ?_
    have := ((f.hasFDerivAt (x := x)).sub_const a).const_mul ((n : ℝ) + 1)
    simpa using this
  choose θ hθ using fun n => exists_coe_eq_smul_of_contDiffOn (hσ n).contDiffOn χ
  set Φ : ℕ → 𝓓(Ω, E) := fun n => φ + θ n
  have hΦ (n : ℕ) (x : E) : ‖Φ n x‖ ≤ 1 := by
    have h0 : 0 ≤ σ n x := Real.smoothTransition.nonneg _
    have h1 : 0 ≤ 1 - σ n x := sub_nonneg.2 (Real.smoothTransition.le_one _)
    have : Φ n x = (1 - σ n x) • φ x + σ n x • ψ x := by
      simp only [Φ, χ, add_apply, hθ, sub_apply]
      module
    rw [this, ← mem_closedBall_zero_iff]
    exact convex_closedBall (0 : E) 1 (mem_closedBall_zero_iff.2 (hφ x))
      (mem_closedBall_zero_iff.2 (hψ x)) h1 h0 (by ring)
  have hdiv (n : ℕ) (x : E) : divergenceCLM (Φ n) x = divergenceCLM φ x +
      σ n x * divergenceCLM χ x +
        deriv Real.smoothTransition ((n + 1) * (f x - a)) * ((n + 1) * f (χ x)) := by
    have hχd : DifferentiableAt ℝ χ x := χ.contDiff.differentiable (by simp) x
    simp only [Φ, map_add, add_apply]
    rw [add_assoc, divergenceCLM_apply (θ n), hθ, trace_fderiv_smul (hσd n x).differentiableAt hχd,
      ← divergenceCLM_apply, (hσd n x).fderiv]
    simp [smul_eq_mul]
  -- The normal component of `χ` is `O (|f - a|)`, and the derivative of `ψ₀` is bounded.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, |f (χ x)| ≤ C * |f x - a| := by
    by_cases hf : f = 0
    · exact ⟨0, fun x => by simp [hf]⟩
    obtain ⟨v, hv⟩ : ∃ v, f v = 1 := by
      obtain ⟨v₀, hv₀⟩ : ∃ v₀, f v₀ ≠ 0 := by
        by_contra! h
        exact hf (ContinuousLinearMap.ext h)
      exact ⟨(f v₀)⁻¹ • v₀, by simp [hv₀]⟩
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
      (χ.hasCompactSupport.comp_left (g := f) f.map_zero)
      (f.contDiff.comp (χ.contDiff.of_le (by simp))) one_ne_zero
    exact ⟨L * ‖v‖, fun x => by
      simpa using hL.norm_le_mul_abs_sub_of_eq_zero (f := f) hv
        (fun x hx => by simp [χ, hφψ x hx]) x⟩
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
    Real.smoothTransition.hasCompactSupport_deriv
  set C' := max C 0
  have hC' (x : E) : |f (χ x)| ≤ C' * |f x - a| :=
    (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have herr (n : ℕ) (x : E) :
      |deriv Real.smoothTransition ((n + 1) * (f x - a)) * ((n + 1) * f (χ x))| ≤
        (tsupport χ).indicator (fun _ => M * C') x := by
    by_cases hx : x ∈ tsupport χ
    · rw [indicator_of_mem hx]
      exact abs_deriv_smoothTransition_mul_le hM (le_max_right _ _) n (hC' x)
    · simp [image_eq_zero_of_notMem_tsupport hx, hx]
  -- Dominated convergence on `s`.
  set g : E → ℝ := fun x => {x | f x ≤ a}.indicator (divergenceCLM φ) x +
    {x | a < f x}.indicator (divergenceCLM ψ) x
  have hint (φ' : 𝓓(Ω, ℝ)) : Integrable φ' μ :=
    φ'.continuous.integrable_of_hasCompactSupport φ'.hasCompactSupport
  have hmeas_le : MeasurableSet {x | f x ≤ a} := measurableSet_le f.continuous.measurable
    measurable_const
  have hmeas_lt : MeasurableSet {x | a < f x} := measurableSet_lt measurable_const
    f.continuous.measurable
  have hlim : Tendsto (fun n => ∫ x in s, divergenceCLM (Φ n) x ∂μ) atTop
      (𝓝 (∫ x in s, g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |divergenceCLM φ x| + |divergenceCLM χ x| +
        (tsupport χ).indicator (fun _ => M * C') x)
      (fun n => (divergenceCLM (Φ n)).continuous.aestronglyMeasurable) ?_ ?_ ?_
    · refine (((hint _).abs.add (hint _).abs).add ?_).integrableOn
      exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).2
        (integrableOn_const χ.hasCompactSupport.isCompact.measure_lt_top.ne)
    · refine fun n => Eventually.of_forall fun x => ?_
      rw [hdiv, Real.norm_eq_abs]
      have hσ0 : 0 ≤ σ n x := Real.smoothTransition.nonneg _
      have hσ1 : σ n x ≤ 1 := Real.smoothTransition.le_one _
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_))
        (herr n x))
      rw [abs_mul, abs_of_nonneg hσ0]
      exact mul_le_of_le_one_left (abs_nonneg _) hσ1
    · refine Eventually.of_forall fun x => ?_
      rcases lt_trichotomy (f x) a with hx | hx | hx
      · -- Below the hyperplane, `σₙ` and its derivative vanish.
        have ht (n : ℕ) : ((n : ℝ) + 1) * (f x - a) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) (by linarith)
        simp only [hdiv, σ, Real.smoothTransition.zero_of_nonpos (ht _).le,
          Real.smoothTransition.deriv_of_neg (ht _), g, indicator_of_mem (show x ∈ {x | f x ≤ a}
            from hx.le), indicator_of_notMem (show x ∉ {x | a < f x} from not_lt.2 hx.le)]
        simp
      · -- On the hyperplane, `σₙ` and the normal component of `χ` vanish.
        have hχx : f (χ x) = 0 := by simp [χ, hφψ x hx]
        have h₁ : x ∈ {x | f x ≤ a} := hx.le
        have h₂ : x ∉ {x | a < f x} := fun h => lt_irrefl a (hx ▸ h)
        simp only [hdiv, σ, hx, sub_self, mul_zero, Real.smoothTransition.zero, hχx, g,
          indicator_of_mem h₁, indicator_of_notMem h₂]
        simp
      · -- Above the hyperplane, eventually `σₙ = 1` and its derivative vanishes.
        have hev : ∀ᶠ n : ℕ in atTop, 1 < ((n : ℝ) + 1) * (f x - a) :=
          (Tendsto.atTop_mul_const (sub_pos.2 hx) (tendsto_natCast_atTop_atTop.atTop_add
            tendsto_const_nhds)).eventually_gt_atTop 1
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        simp only [hdiv, σ, Real.smoothTransition.one_of_one_le hn.le,
          Real.smoothTransition.deriv_of_one_lt hn, g,
          indicator_of_notMem (show x ∉ {x | f x ≤ a} from not_le.2 hx),
          indicator_of_mem (show x ∈ {x | a < f x} from hx), χ, map_sub, sub_apply]
        ring
  have hg : ∫ x in s, g x ∂μ = (∫ x in s ∩ {x | f x ≤ a}, divergenceCLM φ x ∂μ) +
      ∫ x in s ∩ {x | a < f x}, divergenceCLM ψ x ∂μ := by
    rw [integral_add (((hint _).indicator hmeas_le).integrableOn)
      (((hint _).indicator hmeas_lt).integrableOn), setIntegral_indicator hmeas_le,
      setIntegral_indicator hmeas_lt]
  rw [← hg]
  refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => ?_
  rw [perimeter_eq_iSup hs]
  exact le_iSup₂_of_le (f := fun (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
    ENNReal.ofReal (∫ x in s, divergenceCLM φ x ∂μ)) (Φ n) (hΦ n) le_rfl

/-- **Cutting by a half-space does not increase the perimeter.** For a null-measurable set `s` of
finite measure and a closed half-space `{f ≤ c}`, `P(s ∩ {f ≤ c}) ≤ P(s)`.

The finiteness of `μ s` cannot be dropped: for an additive Haar measure the whole space has
perimeter zero, while a half-space `{f ≤ c}` with `f ≠ 0` has positive perimeter (infinite in
dimension at least two). -/
theorem perimeter_inter_halfSpace_le [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]
    (f : StrongDual ℝ E) (c : ℝ) (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ∞) :
    perimeter μ ⊤ (s ∩ {x | f x ≤ c}) ≤ perimeter μ ⊤ s := by
  by_cases hf : f = 0
  · by_cases hc : 0 ≤ c <;> simp [hf, hc]
  have hmeas_le : MeasurableSet {x | f x ≤ c} := measurableSet_le f.continuous.measurable
    measurable_const
  have hmeas_lt : MeasurableSet {x | c < f x} := measurableSet_lt measurable_const
    f.continuous.measurable
  have hmeas_ge (n : ℕ) : MeasurableSet {x | c + n ≤ f x} :=
    measurableSet_le measurable_const f.continuous.measurable
  rw [perimeter_eq_iSup (hs.inter hmeas_le.nullMeasurableSet)]
  refine iSup₂_le fun φ hφ => ?_
  -- Glue `φ` below the hyperplane to the normal extensions `ψₙ` above it; the pairings of `s`
  -- with `div ψₙ` above the hyperplane are bounded by `M ‖f‖ μ (s ∩ {f ≥ c + n}) → 0`.
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
    Real.smoothTransition.hasCompactSupport_deriv
  choose ψ hψn hφψ hψM hψ0 using exists_normal_extension f hf c hφ hM
  have hbound (n : ℕ) : ‖∫ x in s ∩ {x | c < f x}, divergenceCLM (ψ n) x ∂μ‖ ≤
      M * ‖f‖ * μ.real (s ∩ {x | c + n ≤ f x}) := by
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (hs.inter hmeas_lt.nullMeasurableSet) (inter_subset_left (t := {x | c + n ≤ f x}))
      (Eventually.of_forall fun x hx => hψ0 n x hx.1.2 (not_le.1 fun h => hx.2 ⟨hx.1, h⟩))]
    refine (norm_setIntegral_le_of_norm_le_const ((measure_mono
      (inter_subset_left.trans inter_subset_left)).trans_lt hμs.lt_top)
      fun x hx => hψM n x hx.1.2).trans
      (mul_le_mul_of_nonneg_left (measureReal_mono (inter_subset_inter_left _
        inter_subset_left) (measure_ne_top_of_subset inter_subset_left hμs))
        (mul_nonneg ((norm_nonneg _).trans (hM 0)) (norm_nonneg f)))
  have hμ : Tendsto (fun n : ℕ => μ (s ∩ {x | c + n ≤ f x})) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n : ℕ => s ∩ {x | c + n ≤ f x})
      (fun n => hs.inter (hmeas_ge n).nullMeasurableSet)
      (fun m n hmn x hx => ⟨hx.1, le_trans (by simpa using hmn : c + (m : ℝ) ≤ c + n) hx.2⟩)
      ⟨0, measure_ne_top_of_subset inter_subset_left hμs⟩
    have hempty : ⋂ n : ℕ, s ∩ {x | c + n ≤ f x} = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (f x - c)
      have := (mem_iInter.1 hx N).2
      simp only [mem_ofPred_eq] at this
      linarith
    rwa [hempty, measure_empty] at h
  have hlim : Tendsto (fun n : ℕ => (∫ x in s ∩ {x | f x ≤ c}, divergenceCLM φ x ∂μ) +
      ∫ x in s ∩ {x | c < f x}, divergenceCLM (ψ n) x ∂μ) atTop
      (𝓝 (∫ x in s ∩ {x | f x ≤ c}, divergenceCLM φ x ∂μ)) := by
    have h0 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hμ).const_mul (M * ‖f‖)
    simp only [ENNReal.toReal_zero, mul_zero] at h0
    simpa only [add_zero] using tendsto_const_nhds.add (squeeze_zero_norm hbound h0)
  refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => ?_
  exact ofReal_setIntegral_add_setIntegral_le_perimeter f c hφ (hψn n) (hφψ n) hs

/-- **The perimeter is monotone under inclusion of a convex set.** If a convex set `K` is
contained in a null-measurable set `L` of finite measure, then `P(K) ≤ P(L)`. In particular the
perimeter is monotone on bounded convex sets.

The finiteness of `μ L` cannot be dropped: a half-space `{f ≤ c}` with `f ≠ 0` is convex and has
positive perimeter (infinite in dimension at least two), while the whole space has perimeter
zero. -/
theorem _root_.Convex.perimeter_le_of_subset [BorelSpace E] [μ.IsAddHaarMeasure] {K L : Set E}
    (hK : Convex ℝ K) (hKL : K ⊆ L) (hL : NullMeasurableSet L μ) (hμL : μ L ≠ ∞) :
    perimeter μ ⊤ K ≤ perimeter μ ⊤ L := by
  -- The closure `C` of `K` is the intersection of countably many closed half-spaces, and `K`
  -- agrees with `L ∩ C` up to a null set. Each cut of `L` by one of these half-spaces decreases
  -- the perimeter, and the perimeter is lower semicontinuous along the decreasing cuts.
  set C := closure K
  -- Separate each point outside `C` from `C` by a closed half-space containing `C`; countably
  -- many of the complementary open half-spaces already cover the complement of `C`.
  choose g u hgx hgC using fun x : ↥Cᶜ =>
    geometric_hahn_banach_point_closed hK.closure isClosed_closure x.2
  obtain ⟨T, hTc, hTU⟩ := isOpen_iUnion_countable (fun x : ↥Cᶜ => {y | g x y < u x})
    fun x => isOpen_lt (g x).continuous continuous_const
  have : Countable ↥T := hTc.to_subtype
  have hmemC (y : E) (hy : ∀ i : ↥T, u i ≤ g i y) : y ∈ C := by
    by_contra hyC
    have hy' : y ∈ ⋃ i ∈ T, {y | g i y < u i} := hTU ▸ mem_iUnion.2 ⟨⟨y, hyC⟩, hgx _⟩
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy'
    exact (hy ⟨i, hi⟩).not_gt hyi
  set H : ↥T → Set E := fun i => {y | (-g i) y ≤ -u i}
  have hH (i : ↥T) : MeasurableSet (H i) :=
    measurableSet_le (-g i).continuous.measurable measurable_const
  have hCH (i : ↥T) : C ⊆ H i := fun y hy => by simpa [H] using (hgC i y hy).le
  -- Cutting `L` by finitely many of these half-spaces decreases the perimeter.
  set F : Finset ↥T → Set E := fun S => L ∩ ⋂ i ∈ S, H i
  have hF (S : Finset ↥T) : NullMeasurableSet (F S) μ :=
    hL.inter (S.measurableSet_biInter fun i _ => hH i).nullMeasurableSet
  have hFμ (S : Finset ↥T) : μ (F S) ≠ ∞ := measure_ne_top_of_subset inter_subset_left hμL
  have hFP (S : Finset ↥T) : perimeter μ ⊤ (F S) ≤ perimeter μ ⊤ L := by
    classical
    induction S using Finset.induction_on with
    | empty => simp [F]
    | insert i S _ ih =>
      have h : F (insert i S) = F S ∩ H i := by
        simp only [F, Finset.set_biInter_insert]
        ext y
        simp only [mem_inter_iff]
        tauto
      rw [h]
      exact (perimeter_inter_halfSpace_le _ _ (hF S) (hFμ S)).trans ih
  -- These cuts decrease to `L ∩ C`, which agrees with `K` up to the null frontier of `K`.
  have hLC : NullMeasurableSet (L ∩ C) μ :=
    hL.inter isClosed_closure.measurableSet.nullMeasurableSet
  have hLCF (S : Finset ↥T) : L ∩ C ⊆ F S := fun y hy =>
    ⟨hy.1, mem_iInter₂.2 fun i _ => hCH i hy.2⟩
  have hlim : Tendsto (fun S => μ (F S \ (L ∩ C))) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun S => F S \ (L ∩ C))
      (fun S => (hF S).diff hLC)
      (fun S S' hSS' y hy => ⟨⟨hy.1.1, mem_iInter₂.2 fun i hi => mem_iInter₂.1 hy.1.2 i
        (hSS' hi)⟩, hy.2⟩)
      ⟨∅, measure_ne_top_of_subset (sdiff_subset.trans inter_subset_left) hμL⟩
    have hempty : ⋂ S, F S \ (L ∩ C) = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      have hy' (S : Finset ↥T) := mem_iInter.1 hy S
      refine (hy' ∅).2 ⟨(hy' ∅).1.1, hmemC y fun i => ?_⟩
      have := mem_iInter₂.1 (hy' {i}).1.2 i (Finset.mem_singleton_self i)
      simpa [H] using this
    rwa [hempty, measure_empty] at h
  have hae : K =ᵐ[μ] L ∩ C := by
    refine ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 (subset_inter hKL subset_closure), measure_empty],
      measure_mono_null (fun y hy => ?_) (hK.addHaar_frontier μ)⟩
    exact ⟨hy.1.2, fun hyi => hy.2 (interior_subset hyi)⟩
  calc perimeter μ ⊤ K = perimeter μ ⊤ (L ∩ C) := perimeter_congr_ae (ae_restrict_of_ae hae)
    _ ≤ liminf (fun S => perimeter μ ⊤ (F S)) atTop := by
      refine perimeter_le_liminf (Eventually.of_forall hF) hLC fun K' _ _ => ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
        fun S => measure_mono fun y hy => ?_
      rcases hy.1 with hy' | hy'
      · exact hy'
      · exact absurd (hLCF S hy'.1) hy'.2
    _ ≤ perimeter μ ⊤ L := liminf_le_of_frequently_le' (Frequently.of_forall hFP)

/-- **A bounded convex set has finite perimeter.** -/
theorem _root_.Convex.perimeter_lt_top [BorelSpace E] [μ.IsAddHaarMeasure] {K : Set E}
    (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) : perimeter μ ⊤ K < ∞ := by
  obtain ⟨r, hr, hKr⟩ := hKb.subset_ball_lt 0 0
  refine (hK.perimeter_le_of_subset hKr measurableSet_ball.nullMeasurableSet
    measure_ball_lt_top.ne).trans_lt ?_
  rw [perimeter_ball hr]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)
    measure_ball_lt_top

end TauCeti
