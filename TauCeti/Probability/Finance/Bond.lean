/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The deterministic money-market account

The bond of a one-factor market is a money-market account with a deterministic short rate `r`:
its price, starting from `β₀`, is

`β_t = β₀ exp (∫₀ᵗ r_u du)`  (`TauCeti.Finance.bondPrice r β₀ t`).

It is positive when `β₀` is (`TauCeti.Finance.bondPrice_pos`), it grows between two dates by the
exponential of the rate accumulated between them
(`TauCeti.Finance.bondPrice_eq_mul_exp_integral`), and for a constant rate it is `β₀ e^{r t}`
(`TauCeti.Finance.bondPrice_const`).

On a horizon `[0, T]` on which `r` is continuous, the account accrues interest at the short rate,
`dβ_t = r_t β_t dt`: in differential form (`TauCeti.Finance.hasDerivWithinAt_bondPrice`) and in
integral form `β_b - β_a = ∫ₐᵇ r_u β_u du` (`TauCeti.Finance.integral_mul_bondPrice`). It is the
unique continuous solution of this equation with initial value `β₀`
(`TauCeti.Finance.eqOn_bondPrice`).

Since `dβ_t = r_t β_t dt`, trading the bond is pathwise integration against a function of finite
variation. For a simple bond holding `b` starting at a nonnegative date, the elementary integral
`∫₀ᵗ b dβ` of `TauCeti.Finance.simpleGains` is the time integral `∫₀ᵗ b_u r_u β_u du`
(`TauCeti.Finance.simpleGains_bondPrice`). This is the bond part `∫₀ᵗ b_u dβ_u` of the
self-financing equation `V_t = V₀ + ∫₀ᵗ a_u dS_u + ∫₀ᵗ b_u dβ_u`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
* I. Karatzas, S. E. Shreve, *Methods of Mathematical Finance*, Springer, 1998, §1.1.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti.Finance

variable {r : ℝ → ℝ} {β₀ t T a b : ℝ}

/-- The price at time `t` of the money-market account with deterministic short rate `r` and
initial price `β₀`: `β_t = β₀ exp (∫₀ᵗ r_u du)`. -/
def bondPrice (r : ℝ → ℝ) (β₀ t : ℝ) : ℝ :=
  β₀ * exp (∫ u in 0..t, r u)

/-- Unfolding lemma for `bondPrice`. -/
theorem bondPrice_def (r : ℝ → ℝ) (β₀ t : ℝ) :
    bondPrice r β₀ t = β₀ * exp (∫ u in 0..t, r u) :=
  (rfl)

/-- The account starts at its initial price. -/
@[simp]
theorem bondPrice_zero (r : ℝ → ℝ) (β₀ : ℝ) : bondPrice r β₀ 0 = β₀ := by
  simp [bondPrice_def]

/-- With a constant short rate `r` the account is `β₀ e^{r t}`. -/
@[simp]
theorem bondPrice_const (r β₀ t : ℝ) : bondPrice (fun _ ↦ r) β₀ t = β₀ * exp (r * t) := by
  simp [bondPrice_def, mul_comm]

/-- The account is positive exactly when its initial price is. -/
@[simp]
theorem bondPrice_pos_iff : 0 < bondPrice r β₀ t ↔ 0 < β₀ := by
  rw [bondPrice_def, mul_pos_iff_of_pos_right (exp_pos _)]

/-- An account with positive initial price stays positive. -/
theorem bondPrice_pos (hβ₀ : 0 < β₀) (r : ℝ → ℝ) (t : ℝ) : 0 < bondPrice r β₀ t :=
  bondPrice_pos_iff.2 hβ₀

/-- The account vanishes exactly when its initial price does. -/
@[simp]
theorem bondPrice_eq_zero_iff : bondPrice r β₀ t = 0 ↔ β₀ = 0 := by
  simp [bondPrice_def]

/-- Between two dates, which need not be ordered, the account grows by the exponential of the
short rate accumulated between them. -/
theorem bondPrice_eq_mul_exp_integral (h0a : IntervalIntegrable r volume 0 a)
    (hab : IntervalIntegrable r volume a b) (β₀ : ℝ) :
    bondPrice r β₀ b = bondPrice r β₀ a * exp (∫ u in a..b, r u) := by
  rw [bondPrice_def, bondPrice_def, mul_assoc, ← exp_add,
    intervalIntegral.integral_add_adjacent_intervals h0a hab]

/-- On a horizon on which the short rate is integrable, the account is continuous. -/
theorem continuousOn_bondPrice (hr : IntegrableOn r (Icc 0 T)) (β₀ : ℝ) :
    ContinuousOn (bondPrice r β₀) (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Icc_eq_empty_of_lt hT]
    exact continuousOn_empty _
  rw [← uIcc_of_le hT] at hr ⊢
  exact (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_interval hr).rexp).congr
    fun u _ ↦ bondPrice_def r β₀ u

/-- On a horizon `[0, T]` on which the short rate is continuous, the account accrues interest at
the short rate, `β'_t = r_t β_t`, with one-sided derivatives at the endpoints. -/
theorem hasDerivWithinAt_bondPrice (hr : ContinuousOn r (Icc 0 T)) (β₀ : ℝ)
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (bondPrice r β₀) (r t * bondPrice r β₀ t) (Icc 0 T) t := by
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hint : IntervalIntegrable r volume 0 t :=
    (hr.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)).intervalIntegrable
  have hI := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 T) hint
    (hr.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hr t ht)
  have hfun : bondPrice r β₀ = fun u ↦ β₀ * exp (∫ v in 0..u, r v) :=
    funext (bondPrice_def r β₀)
  rw [hfun]
  convert hI.exp.const_mul β₀ using 1
  ring

/-- Inside a horizon on which the short rate is continuous, `β'_t = r_t β_t`. -/
theorem hasDerivAt_bondPrice (hr : ContinuousOn r (Icc 0 T)) (β₀ : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (bondPrice r β₀) (r t * bondPrice r β₀ t) t :=
  (hasDerivWithinAt_bondPrice hr β₀ (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- The interest earned between two dates of a horizon on which the short rate is continuous is
the change in the account: `∫ₐᵇ r_u β_u du = β_b - β_a`. The dates need not be ordered. -/
theorem integral_mul_bondPrice (hr : ContinuousOn r (Icc 0 T)) (β₀ : ℝ) (ha : a ∈ Icc 0 T)
    (hb : b ∈ Icc 0 T) :
    ∫ u in a..b, r u * bondPrice r β₀ u = bondPrice r β₀ b - bondPrice r β₀ a := by
  have hsub : uIcc a b ⊆ Icc 0 T := uIcc_subset_Icc ha hb
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right
    ((continuousOn_bondPrice (hr.integrableOn_Icc) β₀).mono hsub) (fun x hx ↦ ?_)
    ((hr.mul (continuousOn_bondPrice hr.integrableOn_Icc β₀)).mono hsub).intervalIntegrable
  refine (hasDerivAt_bondPrice hr β₀ ⟨?_, ?_⟩).hasDerivWithinAt
  · exact (le_min ha.1 hb.1).trans_lt hx.1
  · exact hx.2.trans_le (max_le ha.2 hb.2)

/-- On a horizon on which the short rate is continuous, the account is the unique continuous
solution of `dB_t = r_t B_t dt` with initial value `β₀`. Only right derivatives are needed. -/
theorem eqOn_bondPrice (hr : ContinuousOn r (Icc 0 T)) {B : ℝ → ℝ}
    (hB : ContinuousOn B (Icc 0 T)) (hB₀ : B 0 = β₀)
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt B (r t * B t) (Ici t) t) :
    EqOn B (bondPrice r β₀) (Icc 0 T) := by
  -- The right-hand side `x ↦ r t x` is Lipschitz in `x`, uniformly on the compact horizon.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  have hlip : ∀ t ∈ Ico 0 T, LipschitzOnWith (Real.toNNReal C) (fun x ↦ r t * x) univ := by
    intro t ht
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y ↦ ?_)
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hC t (Ico_subset_Icc_self ht)).trans (le_coe_toNNReal C))
      (abs_nonneg _)
  refine ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ) hlip hB hd
    (fun _ _ ↦ mem_univ _) (continuousOn_bondPrice hr.integrableOn_Icc β₀) (fun t ht ↦ ?_)
    (fun _ _ ↦ mem_univ _) (by rw [hB₀, bondPrice_zero])
  exact (hasDerivWithinAt_bondPrice hr β₀ (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)

/-- Trading the bond with a simple holding `b` whose first date is nonnegative gains the time
integral of the holding against the interest rate: the elementary integral `∫₀ᵗ b dβ` is
`∫₀ᵗ b_u r_u β_u du` whenever the short rate is continuous on `[0, t]`. -/
theorem simpleGains_bondPrice {Ω : Type*} {τ : ℕ → ℝ} {n : ℕ} (hr : ContinuousOn r (Icc 0 t))
    (β₀ : ℝ) (hτ : MonotoneOn τ (Iic n)) (hτ₀ : 0 ≤ τ 0) (b : ℕ → Ω → ℝ) (ω : Ω) :
    simpleGains τ n b (fun s _ ↦ bondPrice r β₀ s) t ω =
      ∫ u in 0..t, simpleHolding τ n b u ω * (r u * bondPrice r β₀ u) := by
  refine simpleGains_eq_integral (X' := fun u _ ↦ r u * bondPrice r β₀ u) hτ hτ₀ ω
    (hr.mul (continuousOn_bondPrice hr.integrableOn_Icc β₀)).integrableOn_Icc
    (fun x hx ↦ ?_) b
  rw [integral_mul_bondPrice hr β₀ ⟨le_rfl, hx.1.trans hx.2⟩ hx, bondPrice_zero]
  ring

end TauCeti.Finance
