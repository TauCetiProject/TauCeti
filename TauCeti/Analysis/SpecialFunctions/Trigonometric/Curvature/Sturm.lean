/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Cotangent
import TauCeti.Analysis.Calculus.Deriv.Slope

/-!
# Sturm comparison with the constant-curvature model sine

Let `s_κ = curvatureSine κ` be the solution of `y'' + κ y = 0` with `y(0) = 0`, `y'(0) = 1`. A
function `f` with `f(0) = 0`, right derivative `a` at `0` and `f'' + κ f ≥ 0` is bounded below by
`a s_κ` before the first positive zero `π / √κ` of `s_κ`. This is the scalar form of the Rauch
comparison under an upper curvature bound: along a unit-speed geodesic whose sectional curvatures
are at most `κ`, the norm of a normal Jacobi field satisfies `|J|'' + κ |J| ≥ 0` wherever `J ≠ 0`.
For this reason the comparison is also proved when the differential inequality, and the
differentiability of `f`, are only assumed where `f` is positive: then `f` has no zero before the
model zero.

The proof uses the Wronskian `w = f' s_κ - f s_κ'`, which satisfies `w' = (f'' + κ f) s_κ ≥ 0`, so
that `f / s_κ` has derivative `w / s_κ²`. The right derivative of `f` at the origin need not be a
limit of the derivatives `f'`, so `w` need not tend to zero at the origin. A negative value of `w`
would instead make `f / s_κ` decrease at least as fast as a positive multiple of `s_κ' / s_κ`,
which tends to infinity at the origin, while `f / s_κ` tends to `a`. Hence `w ≥ 0`, and `f / s_κ`
is nondecreasing from its initial value `a`.

As a consequence, the model sine is antitone in the curvature parameter on the common positivity
range: `s_κ ≤ s_μ` on `[0, π / √κ]` when `μ ≤ κ`.

## Main results

* `TauCeti.mul_curvatureSine_le_of_hasDerivAt`: the Sturm comparison `a s_κ ≤ f`.
* `TauCeti.mul_curvatureSine_le_of_pos`: the comparison for `a > 0` when the differential
  inequality is assumed only where `f > 0`.
* `TauCeti.mul_curvatureSine_le_of_nonneg`: the same for a nonnegative `f` and any `a`.
* `TauCeti.curvatureSine_le_curvatureSine_of_le`: the model sine is antitone in `κ`.

## References

* J.-H. Eschenburg, *Comparison theorems in Riemannian geometry*, Lecture Notes, Trento (1994),
  Section 3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 11.
-/

public section

namespace TauCeti

open Filter Set Real
open scoped Topology

variable {κ a b t : ℝ} {f f' f'' : ℝ → ℝ}

/-- A function vanishing at `0` with right derivative `a` there has `f / s_κ → a` at `0⁺`. -/
private theorem tendsto_div_curvatureSine_nhdsGT_zero (hf0 : f 0 = 0)
    (hfa : HasDerivWithinAt f a (Ici 0) 0) :
    Tendsto (fun t ↦ f t / curvatureSine κ t) (𝓝[>] 0) (𝓝 a) := by
  have h := (hfa.tendsto_div_self_nhdsGT_zero hf0).div
    ((tendsto_curvatureSine_div_zero κ).mono_left (nhdsWithin_mono 0 fun t ht ↦ ne_of_gt ht))
    one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (ne_of_gt ht) _ _

/-- The key step of the Sturm comparison: the Wronskian `w = f' s_κ - f s_κ'` is nonnegative on
`(0, b)` when it is monotone there and `f / s_κ` tends to a finite limit at `0⁺`. A negative value
`w(t₀) = -m` would make `f / s_κ - m s_κ' / s_κ` antitone on `(0, t₀]`, which is impossible since
`s_κ' / s_κ → ∞` at `0⁺`. -/
private theorem wronskian_curvatureSine_nonneg
    (hs : ∀ r ∈ Ioo 0 b, 0 < curvatureSine κ r)
    (hg : ∀ r ∈ Ioo 0 b, HasDerivAt (fun r ↦ f r / curvatureSine κ r)
      ((f' r * curvatureSine κ r - f r * curvatureCosine κ r) / curvatureSine κ r ^ 2) r)
    (hwmono : MonotoneOn (fun r ↦ f' r * curvatureSine κ r - f r * curvatureCosine κ r)
      (Ioo 0 b))
    (hlim : Tendsto (fun t ↦ f t / curvatureSine κ t) (𝓝[>] 0) (𝓝 a)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo 0 b) : 0 ≤ f' t₀ * curvatureSine κ t₀ - f t₀ * curvatureCosine κ t₀ := by
  by_contra hneg
  set m := -(f' t₀ * curvatureSine κ t₀ - f t₀ * curvatureCosine κ t₀)
  have hm0 : 0 < m := by linarith
  have hsub : Ioc 0 t₀ ⊆ Ioo 0 b := fun r hr ↦ ⟨hr.1, hr.2.trans_lt ht₀.2⟩
  have hd (r : ℝ) (hr : r ∈ Ioc 0 t₀) : HasDerivAt
      (fun r ↦ f r / curvatureSine κ r - m * curvatureCotangent κ r)
      ((f' r * curvatureSine κ r - f r * curvatureCosine κ r + m) /
        curvatureSine κ r ^ 2) r := by
    refine ((hg r (hsub hr)).sub
      ((hasDerivAt_curvatureCotangent (hs r (hsub hr)).ne').const_mul m)).congr_deriv ?_
    have hpyth := curvatureCosine_sq_add_mul_curvatureSine_sq κ r
    have hsr := (hs r (hsub hr)).ne'
    rw [curvatureCotangent_def]
    field_simp
    linear_combination m * hpyth
  have hanti : AntitoneOn
      (fun r ↦ f r / curvatureSine κ r - m * curvatureCotangent κ r) (Ioc 0 t₀) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 t₀)
      (fun r hr ↦ (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr ↦ (hd r (interior_subset hr)).hasDerivWithinAt) fun r hr ↦ ?_
    rw [interior_Ioc] at hr
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    have := hwmono (hsub (Ioo_subset_Ioc_self hr)) ht₀ hr.2.le
    linarith
  have hcot := (tendsto_curvatureCotangent_nhdsGT_zero κ).const_mul_atTop hm0
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioc 0 t₀ := Ioc_mem_nhdsGT ht₀.1
  obtain ⟨r, hr, hcotr, hgr⟩ := (hev.and
    ((tendsto_atTop.1 hcot (a + 1 - (f t₀ / curvatureSine κ t₀ -
      m * curvatureCotangent κ t₀))).and (hlim.eventually (gt_mem_nhds (lt_add_one a))))).exists
  have := hanti hr (right_mem_Ioc.2 ht₀.1) hr.2
  linarith

/-- The Sturm comparison on an open interval, without assumptions at its right endpoint. -/
private theorem mul_curvatureSine_le_of_mem_Ioo (hb : 0 < κ → b ≤ π / √κ)
    (hf0 : f 0 = 0) (hfa : HasDerivWithinAt f a (Ici 0) 0)
    (hf' : ∀ t ∈ Ioo 0 b, HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo 0 b, HasDerivAt f' (f'' t) t)
    (hineq : ∀ t ∈ Ioo 0 b, 0 ≤ f'' t + κ * f t) (ht : t ∈ Ioo 0 b) :
    a * curvatureSine κ t ≤ f t := by
  have hs (r : ℝ) (hr : r ∈ Ioo 0 b) : 0 < curvatureSine κ r :=
    curvatureSine_pos hr.1 fun hκ ↦ hr.2.trans_le (hb hκ)
  -- The Wronskian of `f` and the model sine, and the derivative of their quotient.
  have hw (r : ℝ) (hr : r ∈ Ioo 0 b) : HasDerivAt
      (fun r ↦ f' r * curvatureSine κ r - f r * curvatureCosine κ r)
      ((f'' r + κ * f r) * curvatureSine κ r) r :=
    (((hf'' r hr).mul (hasDerivAt_curvatureSine κ r)).sub
      ((hf' r hr).mul (hasDerivAt_curvatureCosine κ r))).congr_deriv (by ring)
  have hg (r : ℝ) (hr : r ∈ Ioo 0 b) : HasDerivAt (fun r ↦ f r / curvatureSine κ r)
      ((f' r * curvatureSine κ r - f r * curvatureCosine κ r) / curvatureSine κ r ^ 2) r :=
    (hf' r hr).div (hasDerivAt_curvatureSine κ r) (hs r hr).ne'
  have hwmono : MonotoneOn (fun r ↦ f' r * curvatureSine κ r - f r * curvatureCosine κ r)
      (Ioo 0 b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 b)
      (fun r hr ↦ (hw r hr).continuousAt.continuousWithinAt)
      (fun r hr ↦ (hw r (interior_subset hr)).hasDerivWithinAt)
      (fun r hr ↦ mul_nonneg (hineq r (interior_subset hr)) (hs r (interior_subset hr)).le)
  have hlim := tendsto_div_curvatureSine_nhdsGT_zero (κ := κ) hf0 hfa
  -- The Wronskian is nonnegative, so `f / s_κ` is nondecreasing from its initial value `a`.
  have hgmono : MonotoneOn (fun r ↦ f r / curvatureSine κ r) (Ioo 0 b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 b)
      (fun r hr ↦ (hg r hr).continuousAt.continuousWithinAt)
      (fun r hr ↦ (hg r (interior_subset hr)).hasDerivWithinAt)
      (fun r hr ↦ div_nonneg (wronskian_curvatureSine_nonneg hs hg hwmono hlim
        (interior_subset hr)) (sq_nonneg _))
  have hat : a ≤ f t / curvatureSine κ t := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht.1] with r hr
    exact hgmono ⟨hr.1, hr.2.trans ht.2⟩ ht hr.2.le
  exact (le_div_iff₀ (hs t ht)).1 hat

/-- **Sturm comparison** with the model sine. Let `f` be continuous on `[0, b]`, with `f(0) = 0`,
right derivative `a` at `0`, and `f'' + κ f ≥ 0` on `(0, b)`, where `b ≤ π / √κ` if `κ > 0`.
Then `a s_κ(t) ≤ f(t)` for `t ∈ [0, b]`. No sign condition on `f` is required. -/
theorem mul_curvatureSine_le_of_hasDerivAt (hb : 0 < κ → b ≤ π / √κ)
    (hf : ContinuousOn f (Icc 0 b)) (hf0 : f 0 = 0) (hfa : HasDerivWithinAt f a (Ici 0) 0)
    (hf' : ∀ t ∈ Ioo 0 b, HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo 0 b, HasDerivAt f' (f'' t) t)
    (hineq : ∀ t ∈ Ioo 0 b, 0 ≤ f'' t + κ * f t) (ht : t ∈ Icc 0 b) :
    a * curvatureSine κ t ≤ f t := by
  obtain rfl | hb0 := ht.1.eq_or_lt
  · simp [hf0]
  have hcl : t ∈ closure (Ioo 0 b) := by rwa [closure_Ioo (hb0.trans_le ht.2).ne]
  exact ContinuousWithinAt.closure_le hcl
    (((contDiff_curvatureSine κ).continuous.const_mul a).continuousWithinAt)
    ((hf t ht).mono Ioo_subset_Icc_self)
    fun r hr ↦ mul_curvatureSine_le_of_mem_Ioo hb hf0 hfa hf' hf'' hineq hr

/-- A function continuous on `[0, b]`, positive just to the right of `0` and nonpositive somewhere
in `(0, b)`, has a first nonpositive point `t₁ ∈ (0, b)`: `f t₁ ≤ 0` and `f > 0` on `(0, t₁)`. -/
private theorem exists_first_nonpos (hf : ContinuousOn f (Icc 0 b))
    (hpos : ∃ ε > 0, ∀ r ∈ Ioo 0 ε, 0 < f r) (hne : ∃ t ∈ Ioo 0 b, f t ≤ 0) :
    ∃ t₁ ∈ Ioo 0 b, f t₁ ≤ 0 ∧ ∀ r ∈ Ioo 0 t₁, 0 < f r := by
  obtain ⟨ε, hε, hεf⟩ := hpos
  set Z := Ioo 0 b ∩ {t | f t ≤ 0}
  have hZ : Z.Nonempty := by
    obtain ⟨t, ht, hft⟩ := hne
    exact ⟨t, ht, hft⟩
  have hbdd : BddBelow Z := ⟨0, fun z hz ↦ hz.1.1.le⟩
  have hεt₁ : ε ≤ sInf Z := le_csInf hZ fun z hz ↦ le_of_not_gt fun h ↦
    hz.2.not_gt (hεf z ⟨hz.1.1, h⟩)
  have ht₁ : sInf Z ∈ Ioo 0 b := by
    obtain ⟨z, hz⟩ := hZ
    exact ⟨hε.trans_le hεt₁, (csInf_le hbdd hz).trans_lt hz.1.2⟩
  refine ⟨sInf Z, ht₁, ?_, fun r hr ↦ lt_of_not_ge fun h ↦
    hr.2.not_ge (csInf_le hbdd ⟨⟨hr.1, hr.2.trans ht₁.2⟩, h⟩)⟩
  have hclosed := hf.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
  have hZsub : Z ⊆ Icc 0 b ∩ f ⁻¹' Iic 0 := fun z hz ↦ ⟨Ioo_subset_Icc_self hz.1, hz.2⟩
  exact (closure_minimal hZsub hclosed (csInf_mem_closure hZ hbdd)).2

/-- **Sturm comparison** with the model sine, for a positive initial slope, assuming the
differential inequality only where `f` is positive. Let `f` be continuous on `[0, b]`, with
`f(0) = 0` and right derivative `a > 0` at `0`, and with `f'' + κ f ≥ 0` at the points of `(0, b)`
where `f > 0`, where `b ≤ π / √κ` if `κ > 0`. Then `a s_κ(t) ≤ f(t)` for `t ∈ [0, b]`; in
particular `f` has no zero in `(0, b)`. -/
theorem mul_curvatureSine_le_of_pos (ha : 0 < a) (hb : 0 < κ → b ≤ π / √κ)
    (hf : ContinuousOn f (Icc 0 b)) (hf0 : f 0 = 0) (hfa : HasDerivWithinAt f a (Ici 0) 0)
    (hf' : ∀ t ∈ Ioo 0 b, 0 < f t → HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo 0 b, 0 < f t → HasDerivAt f' (f'' t) t)
    (hineq : ∀ t ∈ Ioo 0 b, 0 < f t → 0 ≤ f'' t + κ * f t) (ht : t ∈ Icc 0 b) :
    a * curvatureSine κ t ≤ f t := by
  suffices hpos : ∀ t ∈ Ioo 0 b, 0 < f t from
    mul_curvatureSine_le_of_hasDerivAt hb hf hf0 hfa (fun t ht ↦ hf' t ht (hpos t ht))
      (fun t ht ↦ hf'' t ht (hpos t ht)) (fun t ht ↦ hineq t ht (hpos t ht)) ht
  -- Otherwise apply the comparison before the first nonpositive value `t₁` of `f`.
  by_contra! hne
  have hεpos : ∃ ε > 0, ∀ r ∈ Ioo 0 ε, 0 < f r := by
    have h := ((hfa.tendsto_div_self_nhdsGT_zero hf0).eventually (lt_mem_nhds ha)).and
      self_mem_nhdsWithin
    obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
    exact ⟨ε, hε, fun r hr ↦ (div_pos_iff_of_pos_right (hsub hr).2).1 (hsub hr).1⟩
  obtain ⟨t₁, ht₁, hft₁, hbelow⟩ := exists_first_nonpos hf hεpos hne
  have hmem (r : ℝ) (hr : r ∈ Ioo 0 t₁) : r ∈ Ioo 0 b := ⟨hr.1, hr.2.trans ht₁.2⟩
  have hcomp := mul_curvatureSine_le_of_hasDerivAt (b := t₁)
    (fun hκ ↦ ht₁.2.le.trans (hb hκ)) (hf.mono (Icc_subset_Icc_right ht₁.2.le)) hf0 hfa
    (fun r hr ↦ hf' r (hmem r hr) (hbelow r hr)) (fun r hr ↦ hf'' r (hmem r hr) (hbelow r hr))
    (fun r hr ↦ hineq r (hmem r hr) (hbelow r hr)) (right_mem_Icc.2 ht₁.1.le)
  have hs := curvatureSine_pos ht₁.1 fun hκ ↦ ht₁.2.trans_le (hb hκ)
  nlinarith [mul_pos ha hs]

/-- **Sturm comparison** with the model sine for a nonnegative function, assuming the
differential inequality only where `f` is positive. Let `f ≥ 0` be continuous on `[0, b]`, with
`f(0) = 0` and right derivative `a` at `0`, and with `f'' + κ f ≥ 0` at the points of `(0, b)`
where `f > 0`, where `b ≤ π / √κ` if `κ > 0`. Then `a s_κ(t) ≤ f(t)` for `t ∈ [0, b]`. -/
theorem mul_curvatureSine_le_of_nonneg (hb : 0 < κ → b ≤ π / √κ)
    (hf : ContinuousOn f (Icc 0 b)) (hfnonneg : ∀ t ∈ Icc 0 b, 0 ≤ f t) (hf0 : f 0 = 0)
    (hfa : HasDerivWithinAt f a (Ici 0) 0)
    (hf' : ∀ t ∈ Ioo 0 b, 0 < f t → HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo 0 b, 0 < f t → HasDerivAt f' (f'' t) t)
    (hineq : ∀ t ∈ Ioo 0 b, 0 < f t → 0 ≤ f'' t + κ * f t) (ht : t ∈ Icc 0 b) :
    a * curvatureSine κ t ≤ f t := by
  rcases le_or_gt a 0 with ha | ha
  · exact (mul_nonpos_of_nonpos_of_nonneg ha
      (curvatureSine_nonneg ht.1 fun hκ ↦ ht.2.trans (hb hκ))).trans (hfnonneg t ht)
  · exact mul_curvatureSine_le_of_pos ha hb hf hf0 hfa hf' hf'' hineq ht

/-- The model sine is antitone in the curvature parameter on the positivity range of the larger
parameter: if `μ ≤ κ`, `0 ≤ t`, and `t ≤ π / √κ` when `κ > 0`, then `s_κ(t) ≤ s_μ(t)`. -/
theorem curvatureSine_le_curvatureSine_of_le {μ : ℝ} (hμκ : μ ≤ κ) (ht : 0 ≤ t)
    (hbound : 0 < κ → t ≤ π / √κ) : curvatureSine κ t ≤ curvatureSine μ t := by
  simpa using mul_curvatureSine_le_of_pos (f := curvatureSine μ) (f' := curvatureCosine μ)
    (f'' := fun r ↦ -μ * curvatureSine μ r) one_pos hbound
    (contDiff_curvatureSine μ).continuous.continuousOn (curvatureSine_zero_right μ)
    (by simpa using (hasDerivAt_curvatureSine μ 0).hasDerivWithinAt)
    (fun r _ _ ↦ hasDerivAt_curvatureSine μ r) (fun r _ _ ↦ hasDerivAt_curvatureCosine μ r)
    (fun r _ hr ↦ by nlinarith) ⟨ht, le_rfl⟩

end TauCeti
