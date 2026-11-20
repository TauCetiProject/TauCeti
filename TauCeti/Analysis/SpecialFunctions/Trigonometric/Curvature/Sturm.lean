/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Cotangent
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Topology.Order.IntermediateValue

/-!
# Sturm comparison with the constant-curvature model sine

Let `s_κ = curvatureSine κ` be the solution of `y'' + κ y = 0` with `y(0) = 0`, `y'(0) = 1`. A
function `f` with `f(0) = 0`, right derivative `a` at `0` and `f'' + κ f ≥ 0` is bounded below by
`a s_κ` before the first positive zero `π / √κ` of `s_κ`. This is the scalar form of the Rauch
comparison under an upper curvature bound: along a unit-speed geodesic whose sectional curvatures
are at most `κ`, the norm of a normal Jacobi field satisfies `|J|'' + κ |J| ≥ 0` wherever `J ≠ 0`.
For this reason the comparison is also proved when the differential inequality, and the
differentiability of `f`, are only assumed where `f` is positive, in two forms: for a positive
initial slope `a > 0`, where it shows that `f` has no zero before the model zero, and for a
nonnegative `f` with any initial slope.

The proof uses the Wronskian `w = f' s_κ - f s_κ'`, which satisfies `w' = (f'' + κ f) s_κ ≥ 0`, so
that `f / s_κ` has derivative `w / s_κ²`. Only `f → 0` at `0⁺` is assumed for this step, so `w`
need not tend to zero at the origin. A negative value `w(t₀) = -m` would instead make
`f / s_κ - m s_κ' / s_κ` antitone on `(0, t₀]`, so that `f - m s_κ' ≥ c s_κ` there for a
constant `c`; letting `t → 0⁺` gives `0 ≥ m`. Hence `w ≥ 0`, and `f / s_κ` is nondecreasing.
When `f` has right derivative `a` at the origin, `f / s_κ` starts from the value `a`.

As a consequence, the model sine is antitone in the curvature parameter on the common positivity
range: `s_κ ≤ s_μ` on `[0, π / √κ]` when `μ ≤ κ`.

## Main results

* `TauCeti.tendsto_div_curvatureSine_nhdsGT_zero`: `f / s_κ → a` at `0⁺`.
* `TauCeti.monotoneOn_div_curvatureSine`: the quotient `f / s_κ` is monotone before the model
  zero when `f → 0` at `0⁺`.
* `TauCeti.mul_curvatureSine_le_of_hasDerivAt`: the Sturm comparison `a s_κ ≤ f`.
* `TauCeti.mul_curvatureSine_le_of_pos`: the comparison for `a > 0` when the differential
  inequality is assumed only where `f > 0`.
* `TauCeti.mul_curvatureSine_le_of_nonneg`: the same for a nonnegative `f` and any `a`.
* `TauCeti.curvatureSine_le_curvatureSine_of_ge`: the model sine is antitone in `κ`.

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
theorem tendsto_div_curvatureSine_nhdsGT_zero (hf0 : f 0 = 0)
    (hfa : HasDerivWithinAt f a (Ici 0) 0) :
    Tendsto (fun t ↦ f t / curvatureSine κ t) (𝓝[>] 0) (𝓝 a) := by
  have h := (hfa.tendsto_div_nhdsGT_zero hf0).div
    ((tendsto_curvatureSine_div_zero κ).mono_left (nhdsWithin_mono 0 fun t ht ↦ ne_of_gt ht))
    one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (ne_of_gt ht) _ _

/-- The key step of the Sturm comparison: the Wronskian `w = f' s_κ - f s_κ'` is nonnegative on
`(0, b)` when it is monotone there and `f → 0` at `0⁺`. A negative value `w(t₀) = -m` would make
`f / s_κ - m s_κ' / s_κ` antitone on `(0, t₀]`, so `f - m s_κ' - c s_κ ≥ 0` there for a constant
`c`, which is impossible since the left side tends to `-m < 0` at `0⁺`. -/
private theorem wronskian_curvatureSine_nonneg
    (hs : ∀ r ∈ Ioo 0 b, 0 < curvatureSine κ r)
    (hg : ∀ r ∈ Ioo 0 b, HasDerivAt (fun r ↦ f r / curvatureSine κ r)
      ((f' r * curvatureSine κ r - f r * curvatureCosine κ r) / curvatureSine κ r ^ 2) r)
    (hwmono : MonotoneOn (fun r ↦ f' r * curvatureSine κ r - f r * curvatureCosine κ r)
      (Ioo 0 b))
    (hlim : Tendsto f (𝓝[>] 0) (𝓝 0)) {t₀ : ℝ}
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
  set c := f t₀ / curvatureSine κ t₀ - m * curvatureCotangent κ t₀
  have hcont : Tendsto (fun r ↦ f r - m * curvatureCosine κ r - c * curvatureSine κ r)
      (𝓝[>] 0) (𝓝 (-m)) := by
    have hc := ((contDiff_curvatureCosine κ).continuous.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    have hs0 := ((contDiff_curvatureSine κ).continuous.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using (hlim.sub (hc.const_mul m)).sub (hs0.const_mul c)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioc 0 t₀ := Ioc_mem_nhdsGT ht₀.1
  obtain ⟨r, hr, hneg'⟩ :=
    (hev.and (hcont.eventually (gt_mem_nhds (neg_neg_of_pos hm0)))).exists
  have hc : c ≤ (f r - m * curvatureCosine κ r) / curvatureSine κ r := by
    have : c ≤ f r / curvatureSine κ r - m * curvatureCotangent κ r :=
      hanti hr (right_mem_Ioc.2 ht₀.1) hr.2
    rwa [curvatureCotangent_def, mul_div_assoc', ← sub_div] at this
  have := (le_div_iff₀ (hs r (hsub hr))).1 hc
  linarith

/-- **Sturm comparison**, quotient form. Let `f → 0` at `0⁺`, and `f'' + κ f ≥ 0` on `(0, b)`,
where `b ≤ π / √κ` if `κ > 0`. Then `f / s_κ` is monotone on `(0, b)`. If `f(0) = 0` and `f` has
right derivative `a` at `0`, then by `tendsto_div_curvatureSine_nhdsGT_zero` it starts from the
value `a`. -/
theorem monotoneOn_div_curvatureSine (hb : 0 < κ → b ≤ π / √κ)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    (hf' : ∀ t ∈ Ioo 0 b, HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo 0 b, HasDerivAt f' (f'' t) t)
    (hineq : ∀ t ∈ Ioo 0 b, 0 ≤ f'' t + κ * f t) :
    MonotoneOn (fun r ↦ f r / curvatureSine κ r) (Ioo 0 b) := by
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
  -- The Wronskian is nonnegative, so `f / s_κ` is nondecreasing.
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 b)
    (fun r hr ↦ (hg r hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hg r (interior_subset hr)).hasDerivWithinAt)
    (fun r hr ↦ div_nonneg (wronskian_curvatureSine_nonneg hs hg hwmono hf0
      (interior_subset hr)) (sq_nonneg _))

/-- The Sturm comparison on an open interval, without assumptions at its right endpoint. -/
private theorem mul_curvatureSine_le_of_mem_Ioo (hb : 0 < κ → b ≤ π / √κ)
    (hf0 : f 0 = 0) (hfa : HasDerivWithinAt f a (Icc 0 b) 0)
    (hf' : ∀ t ∈ Ioo 0 b, HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo 0 b, HasDerivAt f' (f'' t) t)
    (hineq : ∀ t ∈ Ioo 0 b, 0 ≤ f'' t + κ * f t) (ht : t ∈ Ioo 0 b) :
    a * curvatureSine κ t ≤ f t := by
  have hfa' := (hfa.mono Ioo_subset_Icc_self).Ioi_of_Ioo (ht.1.trans ht.2)
  have hlim := tendsto_div_curvatureSine_nhdsGT_zero (κ := κ) hf0 hfa'.Ici_of_Ioi
  have hgmono := monotoneOn_div_curvatureSine hb
    (by simpa [hf0] using hfa'.continuousWithinAt.tendsto) hf' hf'' hineq
  have hat : a ≤ f t / curvatureSine κ t := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht.1] with r hr
    exact hgmono ⟨hr.1, hr.2.trans ht.2⟩ ht hr.2.le
  exact (le_div_iff₀ (curvatureSine_pos ht.1 fun hκ ↦ ht.2.trans_le (hb hκ))).1 hat

/-- **Sturm comparison** with the model sine. Let `f` be continuous on `[0, b]`, with `f(0) = 0`,
right derivative `a` at `0`, and `f'' + κ f ≥ 0` on `(0, b)`, where `b ≤ π / √κ` if `κ > 0`.
Then `a s_κ(t) ≤ f(t)` for `t ∈ [0, b]`. No sign condition on `f` is required. -/
theorem mul_curvatureSine_le_of_hasDerivAt (hb : 0 < κ → b ≤ π / √κ)
    (hf : ContinuousOn f (Icc 0 b)) (hf0 : f 0 = 0) (hfa : HasDerivWithinAt f a (Icc 0 b) 0)
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

/-- **Sturm comparison** with the model sine, for a positive initial slope, assuming the
differential inequality only where `f` is positive. Let `f` be continuous on `[0, b]`, with
`f(0) = 0` and right derivative `a > 0` at `0`, and with `f'' + κ f ≥ 0` at the points of `(0, b)`
where `f > 0`, where `b ≤ π / √κ` if `κ > 0`. Then `a s_κ(t) ≤ f(t)` for `t ∈ [0, b]`; in
particular `f` has no zero in `(0, b)`. -/
theorem mul_curvatureSine_le_of_pos (ha : 0 < a) (hb : 0 < κ → b ≤ π / √κ)
    (hf : ContinuousOn f (Icc 0 b)) (hf0 : f 0 = 0) (hfa : HasDerivWithinAt f a (Icc 0 b) 0)
    (hf' : ∀ t ∈ Ioo 0 b, 0 < f t → HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo 0 b, 0 < f t → HasDerivAt f' (f'' t) t)
    (hineq : ∀ t ∈ Ioo 0 b, 0 < f t → 0 ≤ f'' t + κ * f t) (ht : t ∈ Icc 0 b) :
    a * curvatureSine κ t ≤ f t := by
  suffices hpos : ∀ t ∈ Ioo 0 b, 0 < f t from
    mul_curvatureSine_le_of_hasDerivAt hb hf hf0 hfa (fun t ht ↦ hf' t ht (hpos t ht))
      (fun t ht ↦ hf'' t ht (hpos t ht)) (fun t ht ↦ hineq t ht (hpos t ht)) ht
  -- Otherwise apply the comparison before the first nonpositive value `t₁` of `f`.
  by_contra! hne
  obtain ⟨t₀, ht₀, hft₀⟩ := hne
  have hεpos : ∀ᶠ r in 𝓝[>] 0, 0 < f r := by
    simpa [hf0] using ((hfa.mono Ioo_subset_Icc_self).Ioi_of_Ioo
      (ht₀.1.trans ht₀.2)).eventually_nhdsGT_lt_of_pos ha
  obtain ⟨t₁, ht₁, hft₁, hbelow⟩ :=
    (hf.mono Ioo_subset_Icc_self).exists_mem_Ioo_le_and_forall_gt hεpos ⟨t₀, ht₀, hft₀⟩
  have hmem (r : ℝ) (hr : r ∈ Ioo 0 t₁) : r ∈ Ioo 0 b := ⟨hr.1, hr.2.trans ht₁.2⟩
  have hcomp := mul_curvatureSine_le_of_hasDerivAt (b := t₁)
    (fun hκ ↦ ht₁.2.le.trans (hb hκ)) (hf.mono (Icc_subset_Icc_right ht₁.2.le)) hf0
    (hfa.mono (Icc_subset_Icc_right ht₁.2.le))
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
    (hfa : HasDerivWithinAt f a (Icc 0 b) 0)
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
theorem curvatureSine_le_curvatureSine_of_ge {μ : ℝ} (hμκ : μ ≤ κ) (ht : 0 ≤ t)
    (hbound : 0 < κ → t ≤ π / √κ) : curvatureSine κ t ≤ curvatureSine μ t := by
  simpa using mul_curvatureSine_le_of_pos (f := curvatureSine μ) (f' := curvatureCosine μ)
    (f'' := fun r ↦ -μ * curvatureSine μ r) one_pos hbound
    (contDiff_curvatureSine μ).continuous.continuousOn (curvatureSine_zero_right μ)
    (by simpa using (hasDerivAt_curvatureSine μ 0).hasDerivWithinAt)
    (fun r _ _ ↦ hasDerivAt_curvatureSine μ r) (fun r _ _ ↦ hasDerivAt_curvatureCosine μ r)
    (fun r _ hr ↦ by nlinarith) ⟨ht, le_rfl⟩

end TauCeti
