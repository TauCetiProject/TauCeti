module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Fundamental theorem of calculus for a logarithmic-derivative integrand

For a curve `γ : ℝ → ℂ` continuous on `[a, b]`, differentiable off a countable set `P`, and such
that the normalized ratio `(γ t - w) / (γ a - w)` stays in `Complex.slitPlane` on `[a, b]`, the
integral of the logarithmic-derivative-type integrand `γ' t / (γ t - w)` evaluates in closed form:

`∫ t in a..b, γ' t / (γ t - w) = Complex.log ((γ b - w) / (γ a - w))`.

The antiderivative is `t ↦ Complex.log ((γ t - w) / (γ a - w))`: on the slit plane the principal
`Complex.log` is a single-valued branch, its `t`-derivative is exactly the integrand, and its value
at `a` is `Complex.log 1 = 0`. The exceptional set `P` accommodates the finitely many breakpoints of
a piecewise-`C¹` contour, and the oriented interval `[a, b]` needs no `a ≤ b` orientation
assumption. This is the per-segment step used downstream to turn the winding-number integral into a
sum of `Complex.log` argument increments.

## Provenance

Adapted from `segment_log_FTC` in `WindingInteger.lean` of the AINTLIB `LeanModularForms`
development, split from the argument-lift PR (#759) as an independent contour prerequisite.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **FTC for a logarithmic-derivative integrand.** For `γ` continuous on `[a, b]`, differentiable
off a countable set `P`, with the normalized ratio `(γ t - w) / (γ a - w)` in `Complex.slitPlane`
throughout `[a, b]`, and with `t ↦ γ' t / (γ t - w)` interval-integrable, the integral of that
integrand over `a..b` equals `Complex.log ((γ b - w) / (γ a - w))`. -/
theorem integral_deriv_div_sub_eq_log {γ γ' : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, HasDerivAt γ (γ' t) t)
    (h_slit : ∀ t ∈ uIcc a b, (γ t - w) / (γ a - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ γ' t / (γ t - w)) volume a b) :
    ∫ t in a..b, γ' t / (γ t - w) = Complex.log ((γ b - w) / (γ a - w)) := by
  -- The basepoint is off the target, since the ratio at `a` would otherwise be `0 ∉ slitPlane`.
  have h_a_ne : γ a - w ≠ 0 := by
    intro h0
    have h1 := h_slit a left_mem_uIcc
    rw [h0, div_zero] at h1
    exact zero_notMem_slitPlane h1
  -- The antiderivative `F t = log ((γ t - w) / (γ a - w))` is continuous on `[a, b]`.
  have hF_cont : ContinuousOn (fun t ↦ Complex.log ((γ t - w) / (γ a - w))) (uIcc a b) :=
    ((hγ_cont.sub continuousOn_const).div_const _).clog h_slit
  -- Off `P`, its derivative is the integrand `γ' t / (γ t - w)`.
  have hF_deriv : ∀ t ∈ Ioo (min a b) (max a b) \ P,
      HasDerivAt (fun t ↦ Complex.log ((γ t - w) / (γ a - w))) (γ' t / (γ t - w)) t := by
    intro t ht
    have ht_uIcc : t ∈ uIcc a b := Ioo_subset_Icc_self ht.1
    have h_ratio := h_slit t ht_uIcc
    have ht_ne : γ t - w ≠ 0 := (div_ne_zero_iff.mp (slitPlane_ne_zero h_ratio)).1
    have hgd : HasDerivAt (fun t ↦ (γ t - w) / (γ a - w)) (γ' t / (γ a - w)) t :=
      ((hγ_diff t ht).sub_const w).div_const _
    have hclog := hgd.clog_real h_ratio
    have heq : γ' t / (γ a - w) / ((γ t - w) / (γ a - w)) = γ' t / (γ t - w) := by
      field_simp
    rwa [heq] at hclog
  -- Apply the off-countable FTC and simplify the endpoints.
  rw [integral_eq_of_hasDerivAt_off_countable (fun t ↦ Complex.log ((γ t - w) / (γ a - w)))
    (fun t ↦ γ' t / (γ t - w)) hP hF_cont hF_deriv h_int, div_self h_a_ne, Complex.log_one,
    sub_zero]

end TauCeti.Contour
