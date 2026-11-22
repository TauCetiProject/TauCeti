/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Linear differential equations with integrable coefficients

Let `E` be a Banach space and consider the linear initial value problem

`x' = M(t) x + F(t)`, `x(t₀) = x₀`

on `[a, b]`, with `t₀ ∈ [a, b]`, where the coefficient `M : ℝ → E →L[ℝ] E` and the forcing term
`F : ℝ → E` are integrable on `[a, b]`. Neither need be continuous in `t`, and `M` need not be
essentially bounded, so Mathlib's Picard–Lindelöf theorem does not apply; the equation is
understood in Carathéodory's sense, as the integral equation

`x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)`,

that is `x = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x` on `[a, b]`, for `x` continuous on
`[a, b]`.

## Main results

* `TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard`: the integral equation
  has a solution continuous on `[a, b]`.
* `TauCeti.eqOn_of_forall_mem_Icc_eq_picard`: two such solutions agree on
  `[a, b]`.
* `TauCeti.absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard` and
  `TauCeti.ae_hasDerivAt_of_forall_mem_Icc_eq_picard`: every solution is absolutely continuous
  on `[a, b]`, with derivative `M t (x t) + F t` at almost every `t ∈ (a, b)`.
* `TauCeti.forall_mem_Icc_eq_picard_of_absolutelyContinuousOnInterval`: conversely, an absolutely
  continuous curve with `x t₀ = x₀` and this derivative almost everywhere solves the integral
  equation.
* `TauCeti.norm_le_mul_exp_of_forall_mem_Icc_eq_picard`: every solution satisfies
  `‖x t‖ ≤ (‖x₀‖ + |∫ s in t₀..t, ‖F s‖|) exp |∫ s in t₀..t, ‖M s‖|`.

Such equations arise as the Galerkin approximations of linear parabolic equations, whose
coefficients are only measurable in time; integrable but unbounded coefficients arise for Dirac and
Schrödinger systems with locally integrable potentials.
For continuous coefficients and classical solutions on the whole line,
`Continuous.eq_of_hasDerivAt_clm_apply` deduces uniqueness for `v' = B(t) v` from Mathlib's
`ODE_solution_unique_of_mem_Ioo`, and `Continuous.eqOn_Ici_of_hasDerivAt_clm_apply` does the same
in forward time on a half-line `[a, ∞)` from `ODE_solution_unique_of_mem_Icc_right`. A solution of
`v' = B(t) v` that lies at one time in a closed complemented subspace invariant under every `B(t)`
lies in it at all times (`Continuous.mem_of_hasDerivAt_clm_apply`).

## Implementation notes

Some iterate of the Picard map on `C([a, b], E)` is a contraction: its `n`-th iterate moves two
curves at time `t` at most `|∫ s in t₀..t, ‖M s‖| ^ n / n!` times their distance apart. The
factorial comes from `IntervalIntegrable.integral_mul_pow_integral`. The norm bound follows from
Grönwall's inequality with an integrable kernel.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 2, §1.
* Mathlib's `Mathlib/Analysis/ODE/PicardLindelof.lean` (Yury Kudryashov, Winston Yin). The
  existence and uniqueness proofs here follow its argument that some iterate of the Picard map is
  a contraction.
-/

public section

open Function MeasureTheory Set intervalIntegral Real
open scoped Nat NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : ℝ → E →L[ℝ] E} {F : ℝ → E}
  {a b t₀ : ℝ} {x₀ : E}

/-- The right-hand side `s ↦ M s (x s) + F s` of a linear equation whose coefficient `M` and
forcing term `F` are integrable on `[a, b]` is integrable on `[a, b]` along every curve `x`
continuous on `[a, b]`. -/
theorem integrableOn_Icc_clm_apply_add (hM : IntegrableOn M (Icc a b))
    (hF : IntegrableOn F (Icc a b)) {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntegrableOn (fun s ↦ M s (x s) + F s) (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  exact ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).integrable_of_bilin_of_bdd_right C hM
    (hx.aestronglyMeasurable measurableSet_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hC))).add hF

/-- The right-hand side `s ↦ M s (x s) + F s` of a linear equation whose coefficient `M` and
forcing term `F` are integrable on `[a, b]`, with `a ≤ b`, is interval integrable on `a..b` along
every curve `x` continuous on `[a, b]`. -/
theorem intervalIntegrable_clm_apply_add (hab : a ≤ b) (hM : IntegrableOn M (Icc a b))
    (hF : IntegrableOn F (Icc a b)) {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntervalIntegrable (fun s ↦ M s (x s) + F s) volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 (integrableOn_Icc_clm_apply_add hM hF hx)

namespace CaratheodoryLinear

/-- The integral of `‖M‖` between two points of `[a, b]` is at most its integral over `[a, b]`. -/
private theorem abs_integral_norm_le (hM : IntegrableOn M (Icc a b)) {c d : ℝ}
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    |∫ s in c..d, ‖M s‖| ≤ ∫ s in a..b, ‖M s‖ := by
  rw [abs_integral_eq_abs_integral_uIoc, abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc
    fun _ _ ↦ norm_nonneg _), integral_of_le (hc.1.trans hc.2)]
  have hsub : uIoc c d ⊆ Ioc a b := fun x hx ↦
    ⟨(le_min hc.1 hd.1).trans_lt hx.1, hx.2.trans (max_le hc.2 hd.2)⟩
  exact setIntegral_mono_set (IntegrableOn.mono_set hM.norm Ioc_subset_Icc_self)
    (ae_of_all _ fun _ ↦ norm_nonneg _) hsub.eventuallySubset

/-- With `Λ s = ∫ r in t₀..s, ‖M r‖`, the integral of `‖M‖ |Λ| ^ n` from `t₀` to `t` is
`|Λ t| ^ (n + 1) / (n + 1)`, in either order of `t₀` and `t`. -/
private theorem abs_integral_norm_mul_abs_pow {t : ℝ}
    (hM : IntervalIntegrable (fun s ↦ ‖M s‖) volume t₀ t) (n : ℕ) :
    |∫ s in t₀..t, ‖M s‖ * |∫ r in t₀..s, ‖M r‖| ^ n| =
      |∫ s in t₀..t, ‖M s‖| ^ (n + 1) / (n + 1) := by
  set Λ : ℝ → ℝ := fun s ↦ ∫ r in t₀..s, ‖M r‖
  -- `Λ` has a constant sign `σ` between `t₀` and `t`.
  obtain ⟨σ, hσ, hΛ⟩ : ∃ σ : ℝ, |σ| = 1 ∧ ∀ s ∈ uIcc t₀ t, |Λ s| = σ * Λ s := by
    rcases le_total t₀ t with h | h
    · refine ⟨1, abs_one, fun s hs ↦ ?_⟩
      rw [uIcc_of_le h] at hs
      rw [one_mul, abs_of_nonneg (integral_nonneg hs.1 fun _ _ ↦ norm_nonneg _)]
    · refine ⟨-1, by simp, fun s hs ↦ ?_⟩
      rw [uIcc_of_ge h] at hs
      rw [neg_one_mul, abs_of_nonpos]
      simp only [Λ]
      rw [integral_symm, neg_nonpos]
      exact integral_nonneg hs.2 fun _ _ ↦ norm_nonneg _
  have h : ∫ s in t₀..t, ‖M s‖ * |Λ s| ^ n = σ ^ n * ∫ s in t₀..t, ‖M s‖ * Λ s ^ n := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s hs ↦ ?_
    simp only [hΛ s hs, mul_pow]
    ring
  rw [h, hM.integral_mul_pow_integral]
  simp [abs_mul, abs_div, abs_pow, hσ, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]

/-- The Picard map `y ↦ x₀ + ∫_{t₀}^t (M s (y s) + F s) ds` on `C([a, b], E)`. -/
private noncomputable def next (ht₀ : t₀ ∈ Icc a b) (hM : IntegrableOn M (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (x₀ : E) (y : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ODE.picard (fun s z ↦ M s z + F s) t₀ x₀ (IccExtend (ht₀.1.trans ht₀.2) y) t
  continuous_toFun := by
    have hab := ht₀.1.trans ht₀.2
    have hI : IntervalIntegrable (fun s ↦ M s (IccExtend hab y s) + F s) volume a b :=
      intervalIntegrable_clm_apply_add hab hM hF y.continuous.Icc_extend'.continuousOn
    have h := continuousOn_primitive_interval' hI (by rwa [uIcc_of_le hab])
    rw [uIcc_of_le hab] at h
    exact (continuousOn_const.add h).comp_continuous continuous_subtypeVal Subtype.prop

private theorem next_apply (ht₀ : t₀ ∈ Icc a b) (hM : IntegrableOn M (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (y : C(Icc a b, E)) (t : Icc a b) :
    next ht₀ hM hF x₀ y t =
      ODE.picard (fun s z ↦ M s z + F s) t₀ x₀ (IccExtend (ht₀.1.trans ht₀.2) y) t :=
  rfl

variable (ht₀ : t₀ ∈ Icc a b) (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b))

include ht₀ hM hF in
/-- The `n`-th iterate of the Picard map moves two curves at time `t` at most
`|∫ s in t₀..t, ‖M s‖| ^ n / n!` times their distance apart. -/
private theorem dist_iterate_next_apply_le (n : ℕ) (y z : C(Icc a b, E)) (t : Icc a b) :
    dist ((next ht₀ hM hF x₀)^[n] y t) ((next ht₀ hM hF x₀)^[n] z t) ≤
      |∫ s in t₀..t, ‖M s‖| ^ n / n ! * dist y z := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
  | succ n ih =>
    set Y := (next ht₀ hM hF x₀)^[n] y
    set Z := (next ht₀ hM hF x₀)^[n] z
    have hab := ht₀.1.trans ht₀.2
    have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ t.property
    have hint (W : C(Icc a b, E)) :
        IntervalIntegrable (fun s ↦ M s (IccExtend hab W s) + F s) volume t₀ t :=
      ((integrableOn_Icc_clm_apply_add hM hF W.continuous.Icc_extend'.continuousOn).mono_set
        hsub).intervalIntegrable
    have hnorm : IntervalIntegrable (fun s ↦ ‖M s‖) volume t₀ t :=
      (IntegrableOn.mono_set hM.norm hsub).intervalIntegrable
    have hΛ : ContinuousOn (fun s ↦ ∫ r in t₀..s, ‖M r‖) (uIcc t₀ t) :=
      continuousOn_primitive_interval (IntegrableOn.mono_set hM.norm hsub)
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      ODE.picard_apply, ODE.picard_apply, add_sub_add_left_eq_sub,
      ← integral_sub (hint Y) (hint Z)]
    calc _ ≤ |∫ s in t₀..t, ‖M s‖ * (|∫ r in t₀..s, ‖M r‖| ^ n / n ! * dist y z)| := by
          refine norm_integral_le_abs_of_norm_le ?_
            (hnorm.mul_continuousOn ((hΛ.abs.pow n).div_const _ |>.mul continuousOn_const))
          refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs ↦ ?_)
          have hs' : s ∈ Icc a b := hsub (uIoc_subset_uIcc hs)
          rw [add_sub_add_right_eq_sub, ← map_sub, IccExtend_of_mem hab _ hs',
            IccExtend_of_mem hab _ hs']
          exact ((M s).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (by simpa [dist_eq_norm] using ih ⟨s, hs'⟩) (norm_nonneg _))
      _ = |∫ s in t₀..t, ‖M s‖| ^ (n + 1) / (n + 1)! * dist y z := by
          have : (fun s ↦ ‖M s‖ * (|∫ r in t₀..s, ‖M r‖| ^ n / n ! * dist y z)) =
              fun s ↦ dist y z / n ! * (‖M s‖ * |∫ r in t₀..s, ‖M r‖| ^ n) := by
            ext s
            ring
          rw [this, intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity),
            abs_integral_norm_mul_abs_pow hnorm, Nat.factorial_succ]
          push_cast
          field_simp

include ht₀ hM hF in
/-- Some iterate of the Picard map is a contraction. -/
private theorem exists_contractingWith_iterate_next :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next ht₀ hM hF x₀)^[n] := by
  set L := ∫ s in a..b, ‖M s‖
  have hL₀ : 0 ≤ L := (abs_nonneg _).trans (abs_integral_norm_le hM ht₀ ht₀)
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop L
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  refine ⟨n, (L ^ n / n !).toNNReal, Real.toNNReal_lt_one.2 hn,
    LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  rw [Real.coe_toNNReal _ (by positivity), ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_next_apply_le ht₀ hM hF n y z t).trans ?_
  gcongr
  exact abs_integral_norm_le hM ht₀ t.property

include ht₀ hM hF in
/-- A curve continuous on `[a, b]` solving the integral equation there restricts to a fixed point of
the Picard map. -/
private theorem isFixedPt_next {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) :
    IsFixedPt (next ht₀ hM hF x₀) ⟨(Icc a b).domRestrict x, hx.domRestrict⟩ := by
  ext t
  rw [next_apply, ContinuousMap.coe_mk, domRestrict_apply, h t t.property, ODE.picard_apply,
    ODE.picard_apply]
  congr 1
  refine integral_congr fun s hs ↦ ?_
  have hs' : s ∈ Icc a b := uIcc_subset_Icc ht₀ t.property hs
  simp [IccExtend_of_mem (ht₀.1.trans ht₀.2) _ hs']

include hM hF in
/-- Between two points `c ≤ d` of `[a, b]`, the integral of `M s (x s) + F s` has norm at most
`∫ s in c..d, ‖F s‖ + ∫ s in c..d, ‖M s‖ * ‖x s‖`. -/
private theorem norm_integral_le_integral {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
    ‖∫ s in c..d, (M s (x s) + F s)‖ ≤
      (∫ s in c..d, ‖F s‖) + ∫ s in c..d, ‖M s‖ * ‖x s‖ := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hc.1 hd.2
  have hF' : IntervalIntegrable (fun s ↦ ‖F s‖) volume c d :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).2 (IntegrableOn.mono_set hF.norm hsub)
  have hMx : IntervalIntegrable (fun s ↦ ‖M s‖ * ‖x s‖) volume c d :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).2
      ((IntegrableOn.mono_set hM.norm hsub).mul_continuousOn (hx.mono hsub).norm isCompact_Icc)
  rw [← integral_add hF' hMx]
  refine norm_integral_le_of_norm_le hcd (ae_of_all _ fun s _ ↦ ?_) (hF'.add hMx)
  rw [add_comm (‖F s‖)]
  exact (norm_add_le _ _).trans (add_le_add_left ((M s).le_opNorm _) _)

include ht₀ hM hF in
/-- The norm bound for a solution at a time `t ≥ t₀`. -/
private theorem norm_le_of_le {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) {t : ℝ}
    (ht : t ∈ Icc a b) (hle : t₀ ≤ t) :
    ‖x t‖ ≤ (‖x₀‖ + ∫ s in t₀..t, ‖F s‖) * exp (∫ s in t₀..t, ‖M s‖) := by
  have hsub : Icc t₀ t ⊆ Icc a b := Icc_subset_Icc ht₀.1 ht.2
  refine le_mul_exp_integral_of_le_add_integral_mul (u := fun s ↦ ‖x s‖)
    (IntegrableOn.mono_set hM.norm hsub) (ae_of_all _ fun _ ↦ norm_nonneg _)
    ((IntegrableOn.mono_set hM.norm hsub).mul_continuousOn (hx.mono hsub).norm isCompact_Icc)
    (fun s hs ↦ ?_) t ⟨hle, le_rfl⟩
  have hs' := hsub hs
  rw [h s hs', ODE.picard_apply]
  have hFmono : ∫ r in t₀..s, ‖F r‖ ≤ ∫ r in t₀..t, ‖F r‖ :=
    integral_mono_interval le_rfl hs.1 hs.2 (ae_of_all _ fun _ ↦ norm_nonneg _)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).2 (IntegrableOn.mono_set hF.norm hsub))
  linarith [norm_add_le x₀ (∫ r in t₀..s, (M r (x r) + F r)),
    norm_integral_le_integral hM hF hx ht₀ hs' hs.1]

include ht₀ hM hF in
/-- The norm bound for a solution at a time `t ≤ t₀`. -/
private theorem norm_le_of_ge {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) {t : ℝ}
    (ht : t ∈ Icc a b) (hle : t ≤ t₀) :
    ‖x t‖ ≤ (‖x₀‖ + ∫ s in t..t₀, ‖F s‖) * exp (∫ s in t..t₀, ‖M s‖) := by
  have hsub : Icc t t₀ ⊆ Icc a b := Icc_subset_Icc ht.1 ht₀.2
  refine le_mul_exp_integral_of_le_add_integral_mul_rev (u := fun s ↦ ‖x s‖)
    (IntegrableOn.mono_set hM.norm hsub) (ae_of_all _ fun _ ↦ norm_nonneg _)
    ((IntegrableOn.mono_set hM.norm hsub).mul_continuousOn (hx.mono hsub).norm isCompact_Icc)
    (fun s hs ↦ ?_) t ⟨le_rfl, hle⟩
  have hs' := hsub hs
  rw [h s hs', ODE.picard_apply, integral_symm s t₀]
  have hFmono : ∫ r in s..t₀, ‖F r‖ ≤ ∫ r in t..t₀, ‖F r‖ :=
    integral_mono_interval hs.1 hs.2 le_rfl (ae_of_all _ fun _ ↦ norm_nonneg _)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).2 (IntegrableOn.mono_set hF.norm hsub))
  linarith [norm_add_le x₀ (-∫ r in s..t₀, (M r (x r) + F r)),
    norm_neg (∫ r in s..t₀, (M r (x r) + F r)), norm_integral_le_integral hM hF hx hs' ht₀ hs.2]

end CaratheodoryLinear

open CaratheodoryLinear

/-- **Carathéodory's existence theorem for linear equations with integrable coefficients.** Let
`M : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on `[a, b]` and let `t₀ ∈ [a, b]`. Then the
linear equation `x' = M(t) x + F(t)` with `x(t₀) = x₀` has a solution in Carathéodory's sense: a
curve `x` continuous on `[a, b]` with `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` for every
`t ∈ [a, b]`. -/
theorem exists_continuousOn_forall_mem_Icc_eq_picard [CompleteSpace E]
    (ht₀ : t₀ ∈ Icc a b) (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b))
    (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧
      ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t := by
  have hab := ht₀.1.trans ht₀.2
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) ht₀ hM hF
  obtain ⟨y, hy⟩ : ∃ y, IsFixedPt (next ht₀ hM hF x₀) y :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  refine ⟨IccExtend hab y, y.continuous.Icc_extend'.continuousOn, fun t ht ↦ ?_⟩
  rw [IccExtend_of_mem hab _ ht]
  conv_lhs => rw [← hy]
  rw [next_apply]

/-- **Uniqueness for linear equations with integrable coefficients.** Let `M : ℝ → E →L[ℝ] E` and
`F : ℝ → E` be integrable on `[a, b]` and let `t₀ ∈ [a, b]`. Two curves continuous on `[a, b]`
that solve `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on `[a, b]` agree on `[a, b]`. -/
theorem eqOn_of_forall_mem_Icc_eq_picard (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x₁ x₂ : ℝ → E}
    (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x₁ t)
    (h₂ : ∀ t ∈ Icc a b, x₂ t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x₂ t) :
    EqOn x₁ x₂ (Icc a b) := by
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) ht₀ hM hF
  have := hC.fixedPoint_unique' ((isFixedPt_next ht₀ hM hF hx₁ h₁).iterate n)
    ((isFixedPt_next ht₀ hM hF hx₂ h₂).iterate n)
  exact fun t ht ↦ congr($this ⟨t, ht⟩)

/-- A solution of the linear integral equation `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on
`[a, b]`, with `M` and `F` integrable on `[a, b]`, is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) :
    AbsolutelyContinuousOnInterval x a b := by
  have hab := ht₀.1.trans ht₀.2
  have hI := intervalIntegrable_clm_apply_add hab hM hF hx
  refine ((LipschitzWith.const x₀).lipschitzOnWith.absolutelyContinuousOnInterval.add
    (hI.absolutelyContinuousOnInterval_intervalIntegral' (by rwa [uIcc_of_le hab]))).congr
    fun t ht ↦ ?_
  rw [uIcc_of_le hab] at ht
  rw [Pi.add_apply, h t ht, ODE.picard_apply]

/-- A solution of the linear integral equation `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on
`[a, b]`, with `M` and `F` integrable on `[a, b]`, has derivative `M t (x t) + F t` at almost
every `t ∈ (a, b)`. -/
theorem ae_hasDerivAt_of_forall_mem_Icc_eq_picard [CompleteSpace E] (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt x (M t (x t) + F t) t := by
  have hab := ht₀.1.trans ht₀.2
  have hI := intervalIntegrable_clm_apply_add hab hM hF hx
  filter_upwards [hI.ae_hasDerivAt_integral] with t hd ht
  rw [uIcc_of_le hab] at hd
  refine ((hd (Ioo_subset_Icc_self ht) t₀ ht₀).const_add x₀).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [h s (Ioo_subset_Icc_self hs), ODE.picard_apply]

/-- **Absolutely continuous solutions.** Let `M : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on
`[a, b]` and let `t₀ ∈ [a, b]`. A curve `x` absolutely continuous on `[a, b]` with `x t₀ = x₀` and
derivative `M t (x t) + F t` at almost every `t ∈ (a, b)` solves the integral equation
`x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on `[a, b]`. -/
theorem forall_mem_Icc_eq_picard_of_absolutelyContinuousOnInterval [CompleteSpace E]
    (ht₀ : t₀ ∈ Icc a b) (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b))
    {x : ℝ → E} (hx : AbsolutelyContinuousOnInterval x a b) (hx₀ : x t₀ = x₀)
    (hd : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt x (M t (x t) + F t) t) :
    ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t := by
  have hab := ht₀.1.trans ht₀.2
  have hxc : ContinuousOn x (Icc a b) := by simpa [uIcc_of_le hab] using hx.continuousOn
  have hI := intervalIntegrable_clm_apply_add hab hM hF hxc
  have ht₀' : t₀ ∈ uIcc a b := by rwa [uIcc_of_le hab]
  -- `x` minus the primitive of its derivative is constant on `[a, b]`.
  obtain ⟨C, hC⟩ := (hx.sub (hI.absolutelyContinuousOnInterval_intervalIntegral' ht₀')
    ).const_of_ae_hasDerivAt_zero (by
      filter_upwards [hd, hI.ae_hasDerivAt_integral, Measure.ae_ne volume a,
        Measure.ae_ne volume b] with t hdt hit hta htb htI
      have htI' : t ∈ Icc a b := by rwa [uIcc_of_le hab] at htI
      simpa only [sub_self] using
        (hdt ⟨htI'.1.lt_of_ne' hta, htI'.2.lt_of_ne htb⟩).sub (hit htI t₀ ht₀'))
  intro t ht
  have h₁ := hC t (by rwa [uIcc_of_le hab])
  have h₂ := hC t₀ ht₀'
  simp only [Pi.sub_apply, integral_same, sub_zero, hx₀] at h₁ h₂
  rw [ODE.picard_apply, h₂, ← h₁, sub_add_cancel]

/-- **A priori bound for linear equations with integrable coefficients.** Let
`M : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on `[a, b]` and let `t₀ ∈ [a, b]`. A solution
of `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on `[a, b]` satisfies
`‖x t‖ ≤ (‖x₀‖ + |∫ s in t₀..t, ‖F s‖|) exp |∫ s in t₀..t, ‖M s‖|` for every `t ∈ [a, b]`. -/
theorem norm_le_mul_exp_of_forall_mem_Icc_eq_picard (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) {t : ℝ}
    (ht : t ∈ Icc a b) :
    ‖x t‖ ≤ (‖x₀‖ + |∫ s in t₀..t, ‖F s‖|) * exp |∫ s in t₀..t, ‖M s‖| := by
  rcases le_total t₀ t with hle | hle
  · simpa only [abs_of_nonneg (integral_nonneg hle fun _ _ ↦ norm_nonneg _)] using
      norm_le_of_le ht₀ hM hF hx h ht hle
  · simpa only [integral_symm t t₀, abs_neg,
      abs_of_nonneg (integral_nonneg hle fun _ _ ↦ norm_nonneg _)] using
      norm_le_of_ge ht₀ hM hF hx h ht hle

end TauCeti

/-- **Uniqueness for time-dependent linear equations.** Two solutions of `v' = B(t) v` on the line,
for a continuous family `B` of bounded operators, that agree at one time agree everywhere. On a
bounded interval `B` is bounded, so the equation is uniformly Lipschitz there. -/
theorem Continuous.eq_of_hasDerivAt_clm_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {B : ℝ → X →L[ℝ] X} (hB : Continuous B) {v w : ℝ → X}
    (hv : ∀ t, HasDerivAt v (B t (v t)) t) (hw : ∀ t, HasDerivAt w (B t (w t)) t) {t₀ : ℝ}
    (h : v t₀ = w t₀) : v = w := by
  funext t
  set a := min t t₀ - 1
  set b := max t t₀ + 1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.continuousOn (s := Icc a b))
  have hLip (s : ℝ) (hs : s ∈ Ioo a b) : LipschitzOnWith (Real.toNNReal C) (B s) univ :=
    ((B s).lipschitzWith.weaken (NNReal.le_toNNReal_of_coe_le (by
      simpa using hC s (Ioo_subset_Icc_self hs)))).lipschitzOnWith
  exact ODE_solution_unique_of_mem_Ioo (v := fun s ↦ B s) (s := fun _ ↦ univ) hLip
    (t₀ := t₀) ⟨by grind, by grind⟩ (fun s _ ↦ ⟨hv s, mem_univ _⟩)
    (fun s _ ↦ ⟨hw s, mem_univ _⟩) h ⟨by grind, by grind⟩

/-- **Forward uniqueness for time-dependent linear equations.** Two solutions of `v' = B(t) v` on
the half-line `[a, ∞)`, for a continuous family `B` of bounded operators, that agree at time `a`
agree on `[a, ∞)`. The equation is only required at times `t ≥ a` (with a two-sided derivative at
`a`), so the two solutions may come from equations that only agree on `[a, ∞)`. -/
theorem Continuous.eqOn_Ici_of_hasDerivAt_clm_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {B : ℝ → X →L[ℝ] X} (hB : Continuous B) {v w : ℝ → X} {a : ℝ}
    (hv : ∀ t, a ≤ t → HasDerivAt v (B t (v t)) t) (hw : ∀ t, a ≤ t → HasDerivAt w (B t (w t)) t)
    (h : v a = w a) : EqOn v w (Ici a) := by
  intro t (ht : a ≤ t)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.continuousOn (s := Icc a t))
  have hLip (s : ℝ) (hs : s ∈ Ico a t) : LipschitzOnWith (Real.toNNReal C) (B s) univ :=
    ((B s).lipschitzWith.weaken (NNReal.le_toNNReal_of_coe_le (by
      simpa using hC s (Ico_subset_Icc_self hs)))).lipschitzOnWith
  exact ODE_solution_unique_of_mem_Icc_right (v := fun s ↦ B s) (s := fun _ ↦ univ) hLip
    (HasDerivAt.continuousOn fun s hs ↦ hv s hs.1) (fun s hs ↦ (hv s hs.1).hasDerivWithinAt)
    (fun _ _ ↦ mem_univ _) (HasDerivAt.continuousOn fun s hs ↦ hw s hs.1)
    (fun s hs ↦ (hw s hs.1).hasDerivWithinAt) (fun _ _ ↦ mem_univ _) h ⟨ht, le_rfl⟩

/-- **A linear equation preserves the invariant subspaces of its coefficients.** Let `V` be a
closed complemented subspace invariant under every operator of a continuous family `B`. A solution
of `w' = B(t) w` on the line that lies in `V` at one time lies in `V` at all times: for a continuous
projection `P` onto `V`, the component `w - P w` solves a linear equation and vanishes at that
time. -/
theorem Continuous.mem_of_hasDerivAt_clm_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {B : ℝ → X →L[ℝ] X} (hB : Continuous B) {V : Submodule ℝ X}
    (hVc : V.ClosedComplemented) (hV : ∀ t, ∀ x ∈ V, B t x ∈ V) {w : ℝ → X}
    (hw : ∀ t, HasDerivAt w (B t (w t)) t) {t₀ : ℝ} (h : w t₀ ∈ V) (t : ℝ) : w t ∈ V := by
  obtain ⟨P, hP⟩ := hVc
  set Q := ContinuousLinearMap.id ℝ X - V.subtypeL ∘L P
  have hQV {x : X} (hx : x ∈ V) : Q x = 0 := by
    simp [Q, hP ⟨x, hx⟩]
  -- `Q w` solves `u' = Q B(t) u`, since `Q B(t)` kills `V`.
  have hQ (t : ℝ) (x : X) : Q (B t x) = (Q ∘L B t) (Q x) := by
    have hx : Q x = x - P x := by simp [Q]
    simp [hx, hQV (hV t _ (P x).property)]
  have hQw : (fun t ↦ Q (w t)) = fun _ ↦ 0 :=
    (continuous_const.clm_comp hB).eq_of_hasDerivAt_clm_apply (B := fun t ↦ Q ∘L B t)
      (fun t ↦ (Q.hasFDerivAt.comp_hasDerivAt t (hw t)).congr_deriv (hQ t (w t)))
      (fun t ↦ by simpa using hasDerivAt_const t (0 : X)) (hQV h)
  have h0 : w t - P (w t) = 0 := congrFun hQw t
  rw [sub_eq_zero] at h0
  rw [h0]
  exact (P (w t)).property
