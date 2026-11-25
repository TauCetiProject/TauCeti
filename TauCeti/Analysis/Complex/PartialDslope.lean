/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.PartialDeriv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Complex.AbsMax
import TauCeti.Analysis.Calculus.DSlope.Integral
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.Normed.Group.Pi

/-!
# Dividing an entire function by a coordinate

For a function `f : (ι → ℂ) → E`, a coordinate `i : ι` and `ζ : ℂ`, let `f₀ z = f (update z i ζ)`
be `f` with its `i`-th variable replaced by `ζ`. The *divided difference of `f` in the `i`-th
variable at `ζ`* is the function `g = TauCeti.partialDslope i f ζ` with

  `f z = f₀ z + (zᵢ - ζ) • g z`:

on `zᵢ ≠ ζ` it is the difference quotient `(f z - f₀ z) / (zᵢ - ζ)`, and on the hyperplane
`zᵢ = ζ` it is the derivative of `f` along the `i`-th coordinate axis, which is the partial
derivative `∂ᵢ f z` for `f` differentiable at `z`. On each line parallel to the `i`-th coordinate
axis it is Mathlib's `dslope`. Repeating this division along the roots of a polynomial `P(zᵢ)` is
how an entire function is divided by `P(zᵢ)` with a remainder that is a polynomial in `zᵢ`, the
first step of Schwarz's lemma for Cartesian products in the transcendence method of Schneider,
Lang and Baker.

For entire `f` the quotient is again entire. This follows from its integral representation
`g z = ∫₀¹ ∂ᵢ f (z with zᵢ replaced by ζ + t (zᵢ - ζ)) dt`, an integral of a jointly analytic
integrand over a compact parameter interval. The quotient is moreover controlled in size and in
degree:

* if `‖ζ‖ ≤ r < R` and `‖f‖ ≤ M` on the closed polydisc of radius `R`, then `‖f₀‖ ≤ M` and
  `‖g‖ ≤ 2 M / (R - r)` there: on the circle `|zᵢ| = R` the difference quotient is bounded by
  `2 M / (R - r)`, and the maximum modulus principle in the variable `zᵢ` extends the bound inside;
* the partial derivatives `∂ⱼ` with `j ≠ i` commute with `f ↦ f₀` and `f ↦ g`, while `∂ᵢ f₀ = 0`;
  so for `j ≠ i`, if `f` is a polynomial of degree at most `e` in `zⱼ`, in the sense that
  `∂ⱼ^(e+1) f = 0`, so are `f₀` and `g`. Separately, if `∂ᵢ^(e+1) f = 0` then `∂ᵢ^e g = 0`: `g` has
  degree less than `e` in `zᵢ`.

## Main definitions and results

* `TauCeti.partialDslope`: the divided difference `g` of `f` in the `i`-th variable at `ζ`.
* `TauCeti.add_sub_smul_partialDslope`: `f₀ z + (zᵢ - ζ) • g z = f z`.
* `TauCeti.partialDslope_of_ne`, `TauCeti.partialDslope_of_eq`: the values of `g` off and on the
  hyperplane `zᵢ = ζ`.
* `TauCeti.eq_partialDslope`: for entire `f`, `g` is the only continuous function with this
  property.
* `TauCeti.partialDslope_eq_integral`: the integral representation of `g`.
* `TauCeti.differentiable_partialDslope`: `g` is entire when `f` is.
* `TauCeti.norm_apply_update_le`, `TauCeti.norm_partialDslope_le`: the bounds `‖f₀‖ ≤ M` and
  `‖g‖ ≤ 2 M / (R - r)` on the polydisc of radius `R`.
* `TauCeti.partialDeriv_partialDslope_of_ne`, `TauCeti.iterate_partialDeriv_partialDslope_of_ne`:
  `∂ⱼ` commutes with `f ↦ g` for `j ≠ i`; the corresponding statements for `f ↦ f₀` are
  `TauCeti.partialDeriv_comp_update_of_ne`, `TauCeti.iterate_partialDeriv_comp_update_of_ne` and
  `TauCeti.partialDeriv_comp_update_self`.
* `TauCeti.iterate_partialDeriv_partialDslope_eq_zero`: `g` has lower degree in `zᵢ` than `f`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, §4.3, proof of Lemma 4.8, Step 2
  (pp. 124–125).
-/

public section

open Function Metric Set MeasureTheory

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The divided difference of `f : (ι → ℂ) → E` in the `i`-th variable at `ζ`: the function `g`
with `f z = f (update z i ζ) + (z i - ζ) • g z`. It is the difference quotient
`(z i - ζ)⁻¹ • (f z - f (update z i ζ))` off the hyperplane `z i = ζ` and, for `f` differentiable
at `z`, the partial derivative `∂ᵢ f z` on it. On each line parallel to the `i`-th axis it is
Mathlib's `dslope`. -/
noncomputable def partialDslope (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) : (ι → ℂ) → E :=
  fun z ↦ dslope (fun s ↦ f (update z i s)) ζ (z i)

variable {i : ι} {f : (ι → ℂ) → E} {ζ : ℂ} {z : ι → ℂ}

theorem partialDslope_apply (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) (z : ι → ℂ) :
    partialDslope i f ζ z = dslope (fun s ↦ f (update z i s)) ζ (z i) := (rfl)

/-- On a line parallel to the `i`-th axis, the divided difference is `dslope`. -/
theorem partialDslope_update (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) (z : ι → ℂ) (s : ℂ) :
    partialDslope i f ζ (update z i s) = dslope (fun t ↦ f (update z i t)) ζ s := by
  simp [partialDslope_apply]

/-- The defining identity of the divided difference, in the form of Mathlib's `sub_smul_dslope`. -/
theorem sub_smul_partialDslope (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) (z : ι → ℂ) :
    (z i - ζ) • partialDslope i f ζ z = f z - f (update z i ζ) := by
  rw [partialDslope_apply, sub_smul_dslope, update_eq_self]

/-- **Division by a coordinate.** `f z = f (update z i ζ) + (z i - ζ) • partialDslope i f ζ z`. -/
theorem add_sub_smul_partialDslope (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) (z : ι → ℂ) :
    f (update z i ζ) + (z i - ζ) • partialDslope i f ζ z = f z := by
  rw [sub_smul_partialDslope, add_sub_cancel]

/-- Off the hyperplane `z i = ζ`, the divided difference is the difference quotient. -/
theorem partialDslope_of_ne (h : z i ≠ ζ) :
    partialDslope i f ζ z = (z i - ζ)⁻¹ • (f z - f (update z i ζ)) := by
  rw [← sub_smul_partialDslope, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 h), one_smul]

/-- On the hyperplane `z i = ζ`, the divided difference of a function differentiable at `z` is
its partial derivative in the `i`-th variable. -/
theorem partialDslope_of_eq [Finite ι] (hf : DifferentiableAt ℂ f z) (h : z i = ζ) :
    partialDslope i f ζ z = partialDeriv i f z := by
  rw [partialDslope_apply, h, dslope_same, ← h, partialDeriv_eq_deriv_update hf]

/-- The divided difference of the zero function is zero. -/
@[simp]
theorem partialDslope_zero_fun (i : ι) (ζ : ℂ) : partialDslope i (0 : (ι → ℂ) → E) ζ = 0 := by
  ext z
  by_cases h : z i = ζ
  · rw [partialDslope_apply, h, dslope_same]
    simp
  · simp [partialDslope_of_ne h]

/-- **Uniqueness of the divided difference.** For entire `f`, a continuous function `g` with
`f z = f (update z i ζ) + (z i - ζ) • g z` for every `z` is the divided difference of `f`. -/
theorem eq_partialDslope [Finite ι] [CompleteSpace E] {g : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (hg : Continuous g) (hfg : ∀ z, f (update z i ζ) + (z i - ζ) • g z = f z) :
    g = partialDslope i f ζ := by
  ext z
  -- On the line through `z` parallel to the `i`-th axis both functions are continuous and agree
  -- off `ζ`, hence everywhere.
  have hline : (fun s ↦ g (update z i s)) = fun s ↦ partialDslope i f ζ (update z i s) := by
    refine Continuous.ext_on (dense_compl_singleton ζ)
      (hg.comp (continuous_const.update i continuous_id)) ?_ ?_
    · simp only [partialDslope_update]
      exact (continuous_iff_continuousAt.2 fun s ↦
        (((differentiable_comp_update hf z i).analyticAt s).dslope ζ).continuousAt)
    · intro s hs
      have hs : s - ζ ≠ 0 := sub_ne_zero.2 hs
      have h₁ := hfg (update z i s)
      have h₂ := add_sub_smul_partialDslope i f ζ (update z i s)
      simp only [update_self, update_idem] at h₁ h₂
      exact smul_right_injective E hs (add_left_cancel (h₁.trans h₂.symm))
  simpa using congrFun hline (z i)

/-- **Integral representation of the divided difference.** For an entire `f`,
`partialDslope i f ζ z = ∫₀¹ ∂ᵢ f (update z i (ζ + t (z i - ζ))) dt`. -/
theorem partialDslope_eq_integral [Finite ι] [CompleteSpace E] (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) (z : ι → ℂ) :
    partialDslope i f ζ z =
      ∫ t in (0 : ℝ)..1, partialDeriv i f (update z i (ζ + t * (z i - ζ))) := by
  rw [partialDslope_apply, dslope_eq_integral_deriv isOpen_univ
    (differentiable_comp_update hf z i).contDiff.contDiffOn (subset_univ _)]
  congr 1 with t
  rw [Complex.real_smul, (hasDerivAt_comp_update (hf _)).deriv]

/-- **The divided difference of an entire function is entire.** -/
theorem differentiable_partialDslope [Finite ι] [CompleteSpace E] (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) : Differentiable ℂ (partialDslope i f ζ) := by
  have := Fintype.ofFinite ι
  -- The integrand of `TauCeti.partialDslope_eq_integral`, as a function of the point and of a
  -- complex parameter `w` in place of `t`, is entire, hence analytic.
  set F : (ι → ℂ) × ℂ → E := fun p ↦ partialDeriv i f (update p.1 i (ζ + p.2 * (p.1 i - ζ)))
  have hupd : Differentiable ℂ fun p : (ι → ℂ) × ℂ ↦ update p.1 i (ζ + p.2 * (p.1 i - ζ)) := by
    refine differentiable_pi.2 fun j ↦ ?_
    by_cases hj : j = i
    · subst hj
      simp only [update_self]
      fun_prop
    · simp only [update_of_ne hj]
      fun_prop
  have hF (p) : AnalyticAt ℂ F p :=
    ((differentiable_partialDeriv hf i).comp hupd).differentiableOn.analyticAt_of_finiteDimensional
      Filter.univ_mem
  -- Parametrize the segment `[0, 1]` by a continuous map of `ℝ` into the closed unit disc.
  set φ : ℝ → ℂ := fun t ↦ ((projIcc (0 : ℝ) 1 zero_le_one t : ℝ) : ℂ)
  have hφ : Continuous φ := Complex.continuous_ofReal.comp (continuous_subtypeVal.comp
    continuous_projIcc)
  have hφK (t : ℝ) : φ t ∈ closedBall (0 : ℂ) 1 := by
    have := (projIcc (0 : ℝ) 1 zero_le_one t).property
    simp only [φ, mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [this.1], this.2⟩
  have heq : partialDslope i f ζ = fun q ↦
      ∫ t, (1 : ℂ) • F (q, φ t) ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    ext q
    rw [partialDslope_eq_integral hf, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    simp [F, φ, projIcc_of_mem zero_le_one (Ioc_subset_Icc_self ht)]
  rw [heq]
  exact fun q ↦ (analyticAt_integral_smul (isCompact_closedBall 0 1) hφ hφK (fun _ _ ↦ hF _)
    (integrable_const 1)).differentiableAt

/-! ### Size on polydiscs -/

section Bounds

variable [Fintype ι] {r R M : ℝ}

omit [NormedSpace ℂ E] in
/-- If `‖ζ‖ ≤ R` and `‖f‖ ≤ M` on the closed polydisc of radius `R`, then `f` with its `i`-th
variable replaced by `ζ` is bounded by `M` there. -/
theorem norm_apply_update_le (hζ : ‖ζ‖ ≤ R) (hM : ∀ w : ι → ℂ, ‖w‖ ≤ R → ‖f w‖ ≤ M)
    (hz : ‖z‖ ≤ R) : ‖f (update z i ζ)‖ ≤ M :=
  hM _ (Pi.norm_update_le hz hζ)

/-- **Size of the divided difference.** If `f` is entire, `‖ζ‖ ≤ r < R` and `‖f‖ ≤ M` on the
closed polydisc of radius `R`, then `‖partialDslope i f ζ‖ ≤ 2 M / (R - r)` on that polydisc. -/
theorem norm_partialDslope_le [CompleteSpace E] (hf : Differentiable ℂ f) (hζ : ‖ζ‖ ≤ r)
    (hrR : r < R) (hM : ∀ w : ι → ℂ, ‖w‖ ≤ R → ‖f w‖ ≤ M) (hz : ‖z‖ ≤ R) :
    ‖partialDslope i f ζ z‖ ≤ 2 * M / (R - r) := by
  have hR : 0 < R := (norm_nonneg ζ).trans_lt (hζ.trans_lt hrR)
  -- By the maximum modulus principle in the `i`-th variable, it suffices to bound the difference
  -- quotient on the circle `|s| = R`, where `|s - ζ| ≥ R - r`.
  have hg := differentiable_comp_update (differentiable_partialDslope hf i ζ) z i
  have hzi : z i ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball 0 hR.ne', mem_closedBall_zero_iff]
    exact (norm_le_pi_norm z i).trans hz
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg.diffContOnCl
    (C := 2 * M / (R - r)) ?_ hzi
  · simpa using key
  intro s hs
  rw [frontier_ball 0 hR.ne', mem_sphere_zero_iff_norm] at hs
  have hsζ : R - r ≤ ‖s - ζ‖ := by
    linarith [norm_sub_norm_le s ζ]
  have hne : s ≠ ζ := fun h ↦ by
    rw [h, sub_self, norm_zero] at hsζ
    linarith
  rw [partialDslope_update, dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv,
    inv_mul_eq_div]
  have hf₁ := hM _ (Pi.norm_update_le (i := i) hz hs.le)
  have hf₂ := norm_apply_update_le (i := i) (hζ.trans hrR.le) hM hz
  -- The numerator is at most `M + M = 2 M` and the denominator at least `R - r > 0`.
  have hnum : ‖f (update z i s) - f (update z i ζ)‖ ≤ 2 * M := by
    linarith [norm_sub_le (f (update z i s)) (f (update z i ζ))]
  have hM0 : 0 ≤ 2 * M := (norm_nonneg _).trans hnum
  exact div_le_div₀ hM0 hnum (sub_pos.2 hrR) hsζ

end Bounds

/-! ### Degree in each variable -/

section Degree

variable [Finite ι] [CompleteSpace E]

/-- The partial derivative `∂ⱼ` in another variable `j ≠ i` commutes with the divided difference
in the `i`-th variable. -/
theorem partialDeriv_partialDslope_of_ne (hf : Differentiable ℂ f) {i j : ι} (hji : j ≠ i)
    (ζ : ℂ) : partialDeriv j (partialDslope i f ζ) = partialDslope i (partialDeriv j f) ζ := by
  ext z
  rw [partialDeriv_eq_deriv_update (differentiable_partialDslope hf i ζ z)]
  have hupd (s : ℂ) : update z j s i = z i := update_of_ne hji.symm _ _
  by_cases h : z i = ζ
  · -- On the hyperplane `z i = ζ` the divided difference is `∂ᵢ f`, and partial derivatives
    -- commute.
    have hline : (fun s ↦ partialDslope i f ζ (update z j s)) =
        fun s ↦ partialDeriv i f (update z j s) :=
      funext fun s ↦ partialDslope_of_eq (hf _) ((hupd s).trans h)
    rw [hline, ← partialDeriv_eq_deriv_update (differentiable_partialDeriv hf i z),
      partialDslope_of_eq (differentiable_partialDeriv hf j z) h, partialDeriv_comm hf]
  · -- Off the hyperplane, differentiate the difference quotient.
    have hline : (fun s ↦ partialDslope i f ζ (update z j s)) =
        fun s ↦ (z i - ζ)⁻¹ • (f (update z j s) - f (update (update z i ζ) j s)) := by
      funext s
      rw [partialDslope_of_ne ((hupd s).trans_ne h), hupd, update_comm hji]
    have hz : update (update z i ζ) j (z j) = update z i ζ := by
      rw [← update_of_ne hji ζ z, update_eq_self]
    rw [hline, partialDslope_of_ne h]
    refine (((hasDerivAt_comp_update (hf _)).sub (hasDerivAt_comp_update (hf _))).const_smul
      (z i - ζ)⁻¹).deriv.trans ?_
    rw [update_eq_self, hz]

/-- The iterated partial derivatives `∂ⱼ^m` in another variable `j ≠ i` commute with the divided
difference in the `i`-th variable. In particular, if `f` is a polynomial of degree at most `e` in
`zⱼ`, in the sense that `∂ⱼ^(e+1) f = 0`, then so is `partialDslope i f ζ`. -/
theorem iterate_partialDeriv_partialDslope_of_ne (hf : Differentiable ℂ f) {i j : ι}
    (hji : j ≠ i) (ζ : ℂ) (m : ℕ) :
    (partialDeriv j)^[m] (partialDslope i f ζ) = partialDslope i ((partialDeriv j)^[m] f) ζ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_partialDslope_of_ne (differentiable_iterate_partialDeriv hf j m) hji]

/-- **Dividing by `zᵢ - ζ` lowers the degree in `zᵢ`.** If `f` is entire and a polynomial of
degree at most `e` in `zᵢ`, in the sense that `∂ᵢ^(e+1) f = 0`, then `partialDslope i f ζ` is a
polynomial of degree less than `e` in `zᵢ`: `∂ᵢ^e (partialDslope i f ζ) = 0`. -/
theorem iterate_partialDeriv_partialDslope_eq_zero (hf : Differentiable ℂ f) {e : ℕ}
    (he : (partialDeriv i)^[e + 1] f = 0) (ζ : ℂ) :
    (partialDeriv i)^[e] (partialDslope i f ζ) = 0 := by
  ext z
  have hline := congrFun (iteratedDeriv_comp_update (differentiable_partialDslope hf i ζ) i z e)
    (z i)
  rw [update_eq_self] at hline
  rw [Pi.zero_apply, ← hline]
  simp only [partialDslope_update]
  refine congrFun
    (Differentiable.iteratedDeriv_dslope_eq_zero (differentiable_comp_update hf z i) ?_ ζ) (z i)
  rw [iteratedDeriv_comp_update hf, he]
  funext _
  simp

end Degree

end TauCeti
