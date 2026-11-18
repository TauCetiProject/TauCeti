/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Linear differential equations with integrable coefficients

Let `E` be a real normed space, `[a, b]` a compact interval and `t₀ ∈ [a, b]`. For a coefficient
`P : ℝ → E →L[ℝ] E` integrable on `[a, b]` (so `‖P‖` is integrable, but `P` need not be essentially
bounded) and a forcing term `F : ℝ → E` integrable on `[a, b]`, consider the linear equation
`Y' = P(t) Y + F(t)` with `Y(t₀) = y₀` in Carathéodory's sense, as the integral equation

`Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)`,

for `Y` continuous on `[a, b]`. This file proves that the equation has a solution
(`TauCeti.exists_continuousOn_forall_mem_Icc_eq_add_integral`) and that any two solutions agree on
`[a, b]` (`TauCeti.eqOn_of_forall_mem_Icc_eq_add_integral`); `TauCeti.linear_caratheodory` states
both together. Every solution is absolutely continuous on `[a, b]`
(`TauCeti.absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_add_integral`), and for complete `E`
it has derivative `P t (Y t) + F t` at almost every `t ∈ (a, b)`
(`TauCeti.ae_hasDerivAt_of_forall_mem_Icc_eq_add_integral`). A complex Banach space with a
complex-linear coefficient is the case obtained by restriction of scalars.

The essentially bounded case, `TauCeti.exists_continuousOn_eq_forall_mem_Icc_eq_picard` and
`TauCeti.eqOn_of_forall_mem_Icc_eq_picard` in `TauCeti.Analysis.ODE.Caratheodory`, is derived from
these results. The proof shows, as in Mathlib's Picard–Lindelöf theorem, that some iterate of the
Picard map is a contraction, measuring time by `Φ t = ∫ s in t₀..t, ‖P s‖`: the `n`-th iterate
moves two curves at time `t` by at most `|Φ t| ^ n / n!` times their distance. The induction step
is the identity `∫ s in Ι c t, g s * |G s| ^ n = |G t| ^ (n + 1) / (n + 1)` for a nonnegative
integrable `g` with primitive `G` (`IntervalIntegrable.integral_uIoc_mul_abs_primitive_pow`).

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 2, §1.
* Mathlib's `Mathlib/Analysis/ODE/PicardLindelof.lean` (Yury Kudryashov, Winston Yin), whose
  argument that some iterate of the Picard map is a contraction the existence and uniqueness proofs
  follow.
-/

public section

open Function MeasureTheory Set intervalIntegral
open scoped Nat NNReal Interval

namespace MeasureTheory.IntegrableOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P : ℝ → E →L[ℝ] E} {F : ℝ → E}
  {a b : ℝ}

/-- The right-hand side `s ↦ P s (x s) + F s` of a linear equation with coefficient `P` and forcing
term `F` integrable on `[a, b]` is integrable on `[a, b]` along every curve `x` continuous on
`[a, b]`. -/
theorem clm_apply_add (hP : IntegrableOn P (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b)) : IntegrableOn (fun s ↦ P s (x s) + F s) (Icc a b) :=
  ((hP.locallyIntegrableOn.clm_apply_continuousOn isClosed_Icc.isLocallyClosed hx)
    |>.integrableOn_isCompact isCompact_Icc).add hF

end MeasureTheory.IntegrableOn

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P : ℝ → E →L[ℝ] E} {F : ℝ → E}
  {a b t₀ : ℝ} {y₀ : E}

namespace LinearCaratheodory

variable (ht₀ : t₀ ∈ Icc a b) (hP : IntegrableOn P (Icc a b)) (hF : IntegrableOn F (Icc a b))

include ht₀ hP hF in
/-- The integrand of the Picard map along `y : C([a, b], E)` is interval integrable between `t₀`
and any `t ∈ [a, b]`. -/
private theorem intervalIntegrable (y : C(Icc a b, E)) (t : Icc a b) :
    IntervalIntegrable (fun s ↦ P s (IccExtend (ht₀.1.trans ht₀.2) y s) + F s) volume t₀ t :=
  ((hP.clm_apply_add hF
    y.continuous.Icc_extend'.continuousOn).mono_set (uIcc_subset_Icc ht₀ t.2)).intervalIntegrable

/-- The Picard map `y ↦ y₀ + ∫ s in t₀..t, (P s (y s) + F s)` on `C([a, b], E)`. -/
private noncomputable def next (y₀ : E) (y : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := y₀ + ∫ s in t₀..(t : ℝ), (P s (IccExtend (ht₀.1.trans ht₀.2) y s) + F s)
  continuous_toFun := by
    have hI := hP.clm_apply_add hF
      (y.continuous.Icc_extend' (h := ht₀.1.trans ht₀.2)).continuousOn
    have h := continuousOn_primitive_interval'
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (ht₀.1.trans ht₀.2)).2 hI)
      (by rwa [uIcc_of_le (ht₀.1.trans ht₀.2)])
    rw [uIcc_of_le (ht₀.1.trans ht₀.2)] at h
    exact (continuousOn_const.add h).comp_continuous continuous_subtype_val Subtype.prop

private theorem next_apply (y : C(Icc a b, E)) (t : Icc a b) :
    next ht₀ hP hF y₀ y t =
      y₀ + ∫ s in t₀..(t : ℝ), (P s (IccExtend (ht₀.1.trans ht₀.2) y s) + F s) :=
  rfl

include ht₀ hP hF in
/-- The `n`-th iterate of the Picard map moves two curves at time `t` by at most
`|∫ s in t₀..t, ‖P s‖| ^ n / n!` times their distance. -/
private theorem dist_iterate_next_apply_le (n : ℕ) (y z : C(Icc a b, E)) (t : Icc a b) :
    dist ((next ht₀ hP hF y₀)^[n] y t) ((next ht₀ hP hF y₀)^[n] z t) ≤
      |∫ s in t₀..(t : ℝ), ‖P s‖| ^ n / n ! * dist y z := by
  have hab := ht₀.1.trans ht₀.2
  have hPn : IntervalIntegrable (fun s ↦ ‖P s‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hP.norm
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
  | succ n ih =>
    set Y := (next ht₀ hP hF y₀)^[n] y
    set Z := (next ht₀ hP hF y₀)^[n] z
    set Φ := fun u : ℝ ↦ ∫ s in t₀..u, ‖P s‖
    have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ t.2
    have hΦ : ContinuousOn Φ (Icc a b) := by
      simpa [uIcc_of_le hab] using
        continuousOn_primitive_interval' hPn (by rwa [uIcc_of_le hab])
    have hbound : IntervalIntegrable (fun s ↦ ‖P s‖ * |Φ s| ^ n * (dist y z / n !)) volume t₀ t :=
      (IntegrableOn.mono_set
        ((IntegrableOn.mul_continuousOn hP.norm (hΦ.abs.pow n) isCompact_Icc).mul_const _)
        hsub).intervalIntegrable
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (intervalIntegrable ht₀ hP hF Y t) (intervalIntegrable ht₀ hP hF Z t)]
    refine (norm_integral_le_abs_of_norm_le ?_ hbound).trans_eq ?_
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hs' : s ∈ Icc a b := hsub (uIoc_subset_uIcc hs)
      rw [add_sub_add_right_eq_sub, ← map_sub, IccExtend_of_mem hab _ hs',
        IccExtend_of_mem hab _ hs', mul_assoc]
      refine ((P s).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [← dist_eq_norm]
      refine (ih ⟨s, hs'⟩).trans_eq ?_
      simp only [Φ]
      ring
    · rw [intervalIntegral.integral_mul_const, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ dist y z / n !), abs_integral_eq_abs_integral_uIoc,
        abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun s _ ↦ by positivity),
        (hPn.mono_set (by rwa [uIcc_of_le hab])).integral_uIoc_mul_abs_primitive_pow
          (ae_of_all _ fun s ↦ norm_nonneg _),
        Nat.factorial_succ]
      push_cast
      field_simp

include ht₀ hP hF in
/-- Some iterate of the Picard map is a contraction. -/
private theorem exists_contractingWith_iterate_next :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next ht₀ hP hF y₀)^[n] := by
  set K := ∫ s in Icc a b, ‖P s‖
  have hK : ∀ t : Icc a b, |∫ s in t₀..(t : ℝ), ‖P s‖| ≤ K := fun t ↦ by
    rw [abs_integral_eq_abs_integral_uIoc,
      abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun s _ ↦ norm_nonneg _)]
    exact setIntegral_mono_set hP.norm (.of_forall fun s ↦ norm_nonneg _)
      (ae_of_all _ (uIoc_subset_uIcc.trans (uIcc_subset_Icc ht₀ t.2)))
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop K
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have h₀ : 0 ≤ K ^ n / n ! := by positivity
  refine ⟨n, (K ^ n / n !).toNNReal, Real.toNNReal_lt_one.2 hn,
    LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  rw [Real.coe_toNNReal _ h₀, ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_next_apply_le ht₀ hP hF n y z t).trans ?_
  gcongr
  exact hK t

include ht₀ hP hF in
/-- A curve continuous on `[a, b]` solving the integral equation there restricts to a fixed point
of the Picard map. -/
private theorem isFixedPt_next {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = y₀ + ∫ s in t₀..t, (P s (x s) + F s)) :
    IsFixedPt (next ht₀ hP hF y₀) ⟨(Icc a b).domRestrict x, hx.domRestrict⟩ := by
  ext t
  rw [next_apply, ContinuousMap.coe_mk, domRestrict_apply, h t t.2]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  simp [IccExtend_of_mem (ht₀.1.trans ht₀.2) _ (uIcc_subset_Icc ht₀ t.2 hs)]

end LinearCaratheodory

open LinearCaratheodory

/-- **Carathéodory's existence theorem for linear equations with integrable coefficients.** Let
`t₀ ∈ [a, b]`, and let `P : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on `[a, b]`. Then the
equation `Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)` has a solution continuous on `[a, b]`. -/
theorem exists_continuousOn_forall_mem_Icc_eq_add_integral (ht₀ : t₀ ∈ Icc a b) (y₀ : E)
    (hP : IntegrableOn P (Icc a b)) (hF : IntegrableOn F (Icc a b)) :
    ∃ Y : ℝ → E, ContinuousOn Y (Icc a b) ∧
      ∀ t ∈ Icc a b, Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s) := by
  by_cases hE : CompleteSpace E
  swap
  · exact ⟨fun _ ↦ y₀, continuousOn_const, fun t _ ↦ by
      simp [intervalIntegral, integral_of_not_completeSpace hE]⟩
  have hab := ht₀.1.trans ht₀.2
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (y₀ := y₀) ht₀ hP hF
  obtain ⟨y, hy⟩ : ∃ y, IsFixedPt (next ht₀ hP hF y₀) y :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  refine ⟨IccExtend hab y, y.continuous.Icc_extend'.continuousOn, fun t ht ↦ ?_⟩
  rw [IccExtend_of_mem hab _ ht]
  conv_lhs => rw [← hy]
  rw [next_apply]

/-- **Uniqueness for linear equations with integrable coefficients.** Let `t₀ ∈ [a, b]`, and let
`P : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on `[a, b]`. Two curves continuous on `[a, b]`
that solve `Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)` on `[a, b]` agree on `[a, b]`. -/
theorem eqOn_of_forall_mem_Icc_eq_add_integral (ht₀ : t₀ ∈ Icc a b)
    (hP : IntegrableOn P (Icc a b)) (hF : IntegrableOn F (Icc a b)) {Y₁ Y₂ : ℝ → E}
    (hY₁ : ContinuousOn Y₁ (Icc a b)) (hY₂ : ContinuousOn Y₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, Y₁ t = y₀ + ∫ s in t₀..t, (P s (Y₁ s) + F s))
    (h₂ : ∀ t ∈ Icc a b, Y₂ t = y₀ + ∫ s in t₀..t, (P s (Y₂ s) + F s)) :
    EqOn Y₁ Y₂ (Icc a b) := by
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (y₀ := y₀) ht₀ hP hF
  have := hC.fixedPoint_unique' ((isFixedPt_next ht₀ hP hF hY₁ h₁).iterate n)
    ((isFixedPt_next ht₀ hP hF hY₂ h₂).iterate n)
  exact fun t ht ↦ congr($this ⟨t, ht⟩)

/-- A solution of the linear equation `Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)` on `[a, b]`,
with `P` and `F` integrable on `[a, b]`, is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_add_integral (ht₀ : t₀ ∈ Icc a b)
    (hP : IntegrableOn P (Icc a b)) (hF : IntegrableOn F (Icc a b)) {Y : ℝ → E}
    (hY : ContinuousOn Y (Icc a b))
    (h : ∀ t ∈ Icc a b, Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)) :
    AbsolutelyContinuousOnInterval Y a b := by
  have hab := ht₀.1.trans ht₀.2
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    (hP.clm_apply_add hF hY)
  refine ((contDiffOn_const (c := y₀)).absolutelyContinuousOnInterval.add
    (hI.absolutelyContinuousOnInterval_intervalIntegral' (by rwa [uIcc_of_le hab]))).congr ?_
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact (h t ht).symm

/-- A solution of the linear equation `Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)` on `[a, b]`,
with `P` and `F` integrable on `[a, b]`, has derivative `P t (Y t) + F t` at almost every
`t ∈ (a, b)`. -/
theorem ae_hasDerivAt_of_forall_mem_Icc_eq_add_integral [CompleteSpace E] (ht₀ : t₀ ∈ Icc a b)
    (hP : IntegrableOn P (Icc a b)) (hF : IntegrableOn F (Icc a b)) {Y : ℝ → E}
    (hY : ContinuousOn Y (Icc a b))
    (h : ∀ t ∈ Icc a b, Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt Y (P t (Y t) + F t) t := by
  have hab := ht₀.1.trans ht₀.2
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    (hP.clm_apply_add hF hY)
  filter_upwards [hI.ae_hasDerivAt_integral] with t hd ht
  rw [uIcc_of_le hab] at hd
  refine ((hd (Ioo_subset_Icc_self ht) t₀ ht₀).const_add y₀).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact h s (Ioo_subset_Icc_self hs)

/-- **The linear Carathéodory theorem.** On a compact interval `[a, b]` with `t₀ ∈ [a, b]`, for a
coefficient `P : ℝ → E →L[ℝ] E` integrable on `[a, b]` (not necessarily essentially bounded) and a
forcing term `F : ℝ → E` integrable on `[a, b]`, the integral equation
`Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)` has a solution continuous on `[a, b]`, and any two
such solutions agree on `[a, b]`. -/
theorem linear_caratheodory {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (y₀ : E) (P : ℝ → E →L[ℝ] E)
    (hP : IntegrableOn P (Icc a b)) (F : ℝ → E) (hF : IntegrableOn F (Icc a b)) :
    (∃ Y : ℝ → E, ContinuousOn Y (Icc a b) ∧
      ∀ t ∈ Icc a b, Y t = y₀ + ∫ s in t₀..t, (P s (Y s) + F s)) ∧
    ∀ Y₁ Y₂ : ℝ → E, ContinuousOn Y₁ (Icc a b) → ContinuousOn Y₂ (Icc a b) →
      (∀ t ∈ Icc a b, Y₁ t = y₀ + ∫ s in t₀..t, (P s (Y₁ s) + F s)) →
      (∀ t ∈ Icc a b, Y₂ t = y₀ + ∫ s in t₀..t, (P s (Y₂ s) + F s)) →
      EqOn Y₁ Y₂ (Icc a b) :=
  ⟨exists_continuousOn_forall_mem_Icc_eq_add_integral ht₀ y₀ hP hF,
    fun _ _ hY₁ hY₂ h₁ h₂ ↦ eqOn_of_forall_mem_Icc_eq_add_integral ht₀ hP hF hY₁ hY₂ h₁ h₂⟩

end TauCeti
