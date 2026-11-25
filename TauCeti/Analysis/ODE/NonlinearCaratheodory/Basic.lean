/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.MeasureTheory.Function.L1Space.Caratheodory
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The nonlinear Carathéodory theorem

Let `E` be a Banach space and `F : ℝ → E → E` a time-dependent vector field on `[a, b]` such that
`t ↦ F t x` is integrable on `[a, b]` for every `x` and, for almost every `t ∈ [a, b]`, `F t` is
Lipschitz with constant `L t`, where `L : ℝ → ℝ≥0` is integrable on `[a, b]`. Neither `F` nor `L`
need be continuous or bounded in `t`, so Mathlib's Picard–Lindelöf theorem does not apply. For
`t₀ ∈ [a, b]` the initial value problem `x' = F(t, x)`, `x(t₀) = x₀` is understood in
Carathéodory's sense, as the integral equation

`x t = x₀ + ∫ s in t₀..t, F s (x s)`,

that is `x = ODE.picard F t₀ x₀ x` on `[a, b]`, for `x` continuous on `[a, b]`.

## Main results

* `TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`: the integral equation
  has a solution continuous on `[a, b]`.
* `TauCeti.eqOn_of_forall_mem_Icc_eq_picard_of_lipschitzWith`: two such solutions agree on
  `[a, b]`.
* `TauCeti.absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard_of_lipschitzWith` and
  `TauCeti.ae_hasDerivAt_of_forall_mem_Icc_eq_picard_of_lipschitzWith`: every solution is
  absolutely continuous on `[a, b]`, with derivative `F t (x t)` at almost every `t ∈ (a, b)`.
* `TauCeti.norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_lipschitzWith`: if
  `‖F t x₀‖ ≤ m t` almost everywhere, every solution satisfies
  `‖x t - x₀‖ ≤ |∫ s in t₀..t, m s| exp |∫ s in t₀..t, L s|`. The bound only uses the Lipschitz
  estimate at `x₀` (`TauCeti.norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_dist_le`).
* `TauCeti.dist_le_mul_exp_of_forall_mem_Icc_eq_picard_of_lipschitzWith`: solutions from two
  initial values stay within `‖x₀ - y₀‖ exp |∫ s in t₀..t, L s|` of each other.

The linear case `F t x = M t x + G t`, with `L = ‖M‖`, is
`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard` in `TauCeti/Analysis/ODE/Caratheodory.lean`,
which is derived from the results here.

## Implementation notes

Along every curve continuous on `[a, b]` the composite `s ↦ F s (x s)` is integrable on `[a, b]`
(`TauCeti.integrableOn_apply_of_lipschitzWith`, in
`TauCeti/MeasureTheory/Function/L1Space/Caratheodory.lean`, which also shows that integrability of
one section `t ↦ F t x₀` gives integrability of every section).

Some iterate of the Picard map on `C([a, b], E)` is a contraction: its `n`-th iterate moves two
curves at time `t` at most `|∫ s in t₀..t, L s| ^ n / n!` times their distance apart. The factorial
comes from `IntervalIntegrable.abs_integral_mul_abs_pow_integral`. The bounds follow from
Grönwall's inequality with an integrable kernel on either side of `t₀`
(`TauCeti.le_mul_exp_abs_integral_of_le_add_abs_integral_mul`).

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E → E} {L : ℝ → ℝ≥0}
  {a b t₀ : ℝ} {x₀ : E}

namespace CaratheodoryNonlinear

variable (ht₀ : t₀ ∈ Icc a b) (hF : ∀ x, IntegrableOn (fun t ↦ F t x) (Icc a b))
  (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc a b))
  (hLip : ∀ᵐ t ∂volume.restrict (Icc a b), LipschitzWith (L t) (F t))

/-- The Picard map `y ↦ x₀ + ∫_{t₀}^t F s (y s) ds` on `C([a, b], E)`. -/
private noncomputable def next (x₀ : E) (y : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ODE.picard F t₀ x₀ (IccExtend (ht₀.1.trans ht₀.2) y) t
  continuous_toFun := by
    have hab := ht₀.1.trans ht₀.2
    have h := continuousOn_primitive_interval'
      (intervalIntegrable_apply_of_lipschitzWith hab hF hL hLip (x := IccExtend hab y)
        y.continuous.Icc_extend'.continuousOn) (by rwa [uIcc_of_le hab])
    rw [uIcc_of_le hab] at h
    exact (continuousOn_const.add h).comp_continuous continuous_subtypeVal Subtype.prop

private theorem next_apply (y : C(Icc a b, E)) (t : Icc a b) :
    next ht₀ hF hL hLip x₀ y t = ODE.picard F t₀ x₀ (IccExtend (ht₀.1.trans ht₀.2) y) t :=
  rfl

/-- The `n`-th iterate of the Picard map moves two curves at time `t` at most
`|∫ s in t₀..t, L s| ^ n / n!` times their distance apart. -/
private theorem dist_iterate_next_apply_le (n : ℕ) (y z : C(Icc a b, E)) (t : Icc a b) :
    dist ((next ht₀ hF hL hLip x₀)^[n] y t) ((next ht₀ hF hL hLip x₀)^[n] z t) ≤
      |∫ s in t₀..t, (L s : ℝ)| ^ n / n ! * dist y z := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
  | succ n ih =>
    set Y := (next ht₀ hF hL hLip x₀)^[n] y
    set Z := (next ht₀ hF hL hLip x₀)^[n] z
    have hab := ht₀.1.trans ht₀.2
    have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ t.property
    have hint (W : C(Icc a b, E)) :
        IntervalIntegrable (fun s ↦ F s (IccExtend hab W s)) volume t₀ t :=
      ((integrableOn_apply_of_lipschitzWith hF hL hLip
        W.continuous.Icc_extend'.continuousOn).mono_set hsub).intervalIntegrable
    have hLt : IntervalIntegrable (fun s ↦ (L s : ℝ)) volume t₀ t :=
      (hL.mono_set hsub).intervalIntegrable
    have hΛ : ContinuousOn (fun s ↦ ∫ r in t₀..s, (L r : ℝ)) (uIcc t₀ t) :=
      continuousOn_primitive_interval (hL.mono_set hsub)
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      ODE.picard_apply, ODE.picard_apply, add_sub_add_left_eq_sub,
      ← integral_sub (hint Y) (hint Z)]
    calc _ ≤ |∫ s in t₀..t, (L s : ℝ) * (|∫ r in t₀..s, (L r : ℝ)| ^ n / n ! * dist y z)| := by
          refine norm_integral_le_abs_of_norm_le ?_
            (hLt.mul_continuousOn ((hΛ.abs.pow n).div_const _ |>.mul continuousOn_const))
          have hLip' := ae_restrict_of_ae_restrict_of_subset
            ((uIoc_subset_uIcc (a := t₀) (b := (t : ℝ))).trans hsub) hLip
          filter_upwards [hLip', ae_restrict_mem measurableSet_uIoc] with s hs hsI
          have hs' : s ∈ Icc a b := hsub (uIoc_subset_uIcc hsI)
          rw [← dist_eq_norm, IccExtend_of_mem hab _ hs', IccExtend_of_mem hab _ hs']
          exact (hs.dist_le_mul _ _).trans
            (mul_le_mul_of_nonneg_left (ih ⟨s, hs'⟩) (L s).coe_nonneg)
      _ = |∫ s in t₀..t, (L s : ℝ)| ^ (n + 1) / (n + 1)! * dist y z := by
          have : (fun s ↦ (L s : ℝ) * (|∫ r in t₀..s, (L r : ℝ)| ^ n / n ! * dist y z)) =
              fun s ↦ dist y z / n ! * ((L s : ℝ) * |∫ r in t₀..s, (L r : ℝ)| ^ n) := by
            ext s
            ring
          rw [this, intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity),
            hLt.abs_integral_mul_abs_pow_integral (ae_of_all _ fun s ↦ (L s).coe_nonneg),
            Nat.factorial_succ]
          push_cast
          field_simp

/-- Some iterate of the Picard map is a contraction. -/
private theorem exists_contractingWith_iterate_next :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next ht₀ hF hL hLip x₀)^[n] := by
  have hab := ht₀.1.trans ht₀.2
  set K := |∫ s in a..b, (L s : ℝ)|
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop K
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  refine ⟨n, (K ^ n / n !).toNNReal, Real.toNNReal_lt_one.2 hn,
    LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  rw [Real.coe_toNNReal _ (by positivity), ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_next_apply_le ht₀ hF hL hLip n y z t).trans ?_
  gcongr
  refine abs_integral_mono_interval ?_ (ae_of_all _ fun s ↦ (L s).coe_nonneg)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hL)
  exact uIoc_subset_uIoc_of_uIcc_subset_uIcc (by
    simpa [uIcc_of_le hab] using uIcc_subset_Icc ht₀ t.property)

/-- A curve continuous on `[a, b]` solving the integral equation there restricts to a fixed point of
the Picard map. -/
private theorem isFixedPt_next {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t) :
    IsFixedPt (next ht₀ hF hL hLip x₀) ⟨(Icc a b).domRestrict x, hx.domRestrict⟩ := by
  unfold Function.IsFixedPt
  ext t
  simp only [next_apply, ContinuousMap.coe_mk, domRestrict_apply]
  rw [h t t.property]
  simp only [ODE.picard_apply]
  congr 1
  refine integral_congr fun s hs ↦ ?_
  have hs' : s ∈ Icc a b := uIcc_subset_Icc ht₀ t.property hs
  simp [IccExtend_of_mem (ht₀.1.trans ht₀.2) _ hs']

end CaratheodoryNonlinear

open CaratheodoryNonlinear

variable (hF : ∀ x, IntegrableOn (fun t ↦ F t x) (Icc a b))
  (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc a b))
  (hLip : ∀ᵐ t ∂volume.restrict (Icc a b), LipschitzWith (L t) (F t))

include hF hL hLip

/-- **The nonlinear Carathéodory theorem: existence.** Let `F : ℝ → E → E` have every section
`t ↦ F t x` integrable on `[a, b]`, and let `F t` be Lipschitz with constant `L t` for almost
every `t ∈ [a, b]`, where `L` is integrable on `[a, b]`. For `t₀ ∈ [a, b]` and `x₀ : E` there is a
curve `x` continuous on `[a, b]` with `x t = x₀ + ∫ s in t₀..t, F s (x s)` for every
`t ∈ [a, b]`. -/
theorem exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith [CompleteSpace E]
    (ht₀ : t₀ ∈ Icc a b) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧ ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t := by
  have hab := ht₀.1.trans ht₀.2
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) ht₀ hF hL hLip
  obtain ⟨y, hy⟩ : ∃ y, IsFixedPt (next ht₀ hF hL hLip x₀) y :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  refine ⟨IccExtend hab y, y.continuous.Icc_extend'.continuousOn, fun t ht ↦ ?_⟩
  rw [IccExtend_of_mem hab _ ht, ← next_apply ht₀ hF hL hLip y ⟨t, ht⟩, hy.eq]

/-- **The nonlinear Carathéodory theorem: uniqueness.** Under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`, two curves continuous on
`[a, b]` that solve `x t = x₀ + ∫ s in t₀..t, F s (x s)` on `[a, b]` agree on `[a, b]`. -/
theorem eqOn_of_forall_mem_Icc_eq_picard_of_lipschitzWith (ht₀ : t₀ ∈ Icc a b)
    {x₁ x₂ : ℝ → E} (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = ODE.picard F t₀ x₀ x₁ t)
    (h₂ : ∀ t ∈ Icc a b, x₂ t = ODE.picard F t₀ x₀ x₂ t) :
    EqOn x₁ x₂ (Icc a b) := by
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) ht₀ hF hL hLip
  have := hC.fixedPoint_unique' ((isFixedPt_next ht₀ hF hL hLip hx₁ h₁).iterate n)
    ((isFixedPt_next ht₀ hF hL hLip hx₂ h₂).iterate n)
  exact fun t ht ↦ congr($this ⟨t, ht⟩)

/-- A solution of the nonlinear integral equation `x t = x₀ + ∫ s in t₀..t, F s (x s)` on
`[a, b]`, under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`, is absolutely continuous
on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard_of_lipschitzWith
    (ht₀ : t₀ ∈ Icc a b) {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t) :
    AbsolutelyContinuousOnInterval x a b := by
  have hab := ht₀.1.trans ht₀.2
  have hI := intervalIntegrable_apply_of_lipschitzWith hab hF hL hLip hx
  refine ((LipschitzWith.const x₀).lipschitzOnWith.absolutelyContinuousOnInterval.add
    (hI.absolutelyContinuousOnInterval_intervalIntegral' (by rwa [uIcc_of_le hab]))).congr
    fun t ht ↦ ?_
  rw [uIcc_of_le hab] at ht
  rw [Pi.add_apply, h t ht, ODE.picard_apply]

/-- A solution of the nonlinear integral equation `x t = x₀ + ∫ s in t₀..t, F s (x s)` on
`[a, b]`, under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`, has derivative
`F t (x t)` at almost every `t ∈ (a, b)`. -/
theorem ae_hasDerivAt_of_forall_mem_Icc_eq_picard_of_lipschitzWith [CompleteSpace E]
    (ht₀ : t₀ ∈ Icc a b) {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt x (F t (x t)) t := by
  have hab := ht₀.1.trans ht₀.2
  have hI := intervalIntegrable_apply_of_lipschitzWith hab hF hL hLip hx
  filter_upwards [hI.ae_hasDerivAt_integral] with t hd ht
  rw [uIcc_of_le hab] at hd
  refine ((hd (Ioo_subset_Icc_self ht) t₀ ht₀).const_add x₀).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [h s (Ioo_subset_Icc_self hs), ODE.picard_apply]

omit hF hLip in
/-- **A priori bound for the nonlinear Carathéodory theorem, at the initial value.** Let
`‖F t y - F t x₀‖ ≤ L t ‖y - x₀‖` for every `y` and almost every `t ∈ [a, b]`, where `L` is
integrable on `[a, b]`, and let `‖F t x₀‖ ≤ m t` for almost every `t ∈ [a, b]`, where `m` is
integrable on `[a, b]`. A curve continuous on `[a, b]` with `x t = x₀ + ∫ s in t₀..t, F s (x s)`
there satisfies `‖x t - x₀‖ ≤ |∫ s in t₀..t, m s| exp |∫ s in t₀..t, L s|` for every
`t ∈ [a, b]`. Only the Lipschitz bound at `x₀` is used; the composite `s ↦ F s (x s)` need not be
known to be integrable. -/
theorem norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_dist_le (ht₀ : t₀ ∈ Icc a b)
    {m : ℝ → ℝ}
    (hm : IntegrableOn m (Icc a b)) (hFm : ∀ᵐ t ∂volume.restrict (Icc a b), ‖F t x₀‖ ≤ m t)
    (hLx₀ : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ y, dist (F t y) (F t x₀) ≤ L t * dist y x₀)
    {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖x t - x₀‖ ≤ |∫ s in t₀..t, m s| * exp |∫ s in t₀..t, (L s : ℝ)| := by
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
  refine le_mul_exp_abs_integral_of_le_add_abs_integral_mul (u := fun s ↦ ‖x s - x₀‖)
    (hL.mono_set hsub) (ae_of_all _ fun s ↦ (L s).coe_nonneg)
    ((hL.mono_set hsub).mul_continuousOn ((hx.mono hsub).sub continuousOn_const).norm
      isCompact_uIcc) (fun _ _ ↦ norm_nonneg _) fun s hs ↦ ?_
  have hs' : s ∈ Icc a b := hsub hs
  have hsub' : uIcc t₀ s ⊆ Icc a b := uIcc_subset_Icc ht₀ hs'
  have hmi : IntervalIntegrable m volume t₀ s := (hm.mono_set hsub').intervalIntegrable
  have hLu : IntervalIntegrable (fun r ↦ (L r : ℝ) * ‖x r - x₀‖) volume t₀ s :=
    ((hL.mono_set hsub').mul_continuousOn ((hx.mono hsub').sub continuousOn_const).norm
      isCompact_uIcc).intervalIntegrable
  -- The integral of `m` grows with the interval, since `m ≥ ‖F · x₀‖ ≥ 0`.
  have hm_mono : |∫ r in t₀..s, m r| ≤ |∫ r in t₀..t, m r| := by
    have hm₀ : ∀ᵐ r ∂volume.restrict (uIoc t₀ t), 0 ≤ m r :=
      (ae_restrict_of_ae_restrict_of_subset (uIoc_subset_uIcc.trans hsub) hFm).mono
        fun _ hr ↦ (norm_nonneg _).trans hr
    exact abs_integral_mono_interval
      (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc_left hs)) hm₀
      (hm.mono_set hsub).intervalIntegrable
  rw [h s hs', ODE.picard_apply, add_sub_cancel_left]
  calc ‖∫ r in t₀..s, F r (x r)‖ ≤ |∫ r in t₀..s, (m r + (L r : ℝ) * ‖x r - x₀‖)| := by
        refine norm_integral_le_abs_of_norm_le ?_ (hmi.add hLu)
        filter_upwards [ae_restrict_of_ae_restrict_of_subset (uIoc_subset_uIcc.trans hsub')
          (hFm.and hLx₀)] with r ⟨hr, hrL⟩
        rw [← dist_eq_norm]
        exact (norm_le_norm_add_const_of_dist_le (hrL (x r))).trans
          (add_le_add hr le_rfl)
    _ ≤ |∫ r in t₀..s, m r| + |∫ r in t₀..s, (L r : ℝ) * ‖x r - x₀‖| := by
        rw [integral_add hmi hLu]
        exact abs_add_le _ _
    _ ≤ _ := add_le_add hm_mono le_rfl

omit hF in
/-- **A priori bound for the nonlinear Carathéodory theorem.** Let `F t` be Lipschitz with
constant `L t` for almost every `t ∈ [a, b]`, where `L` is integrable on `[a, b]`, and let
`‖F t x₀‖ ≤ m t` for almost every `t ∈ [a, b]`, where `m` is integrable on `[a, b]`. A solution of
`x t = x₀ + ∫ s in t₀..t, F s (x s)` on `[a, b]` satisfies
`‖x t - x₀‖ ≤ |∫ s in t₀..t, m s| exp |∫ s in t₀..t, L s|` for every `t ∈ [a, b]`. -/
theorem norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_lipschitzWith (ht₀ : t₀ ∈ Icc a b)
    {m : ℝ → ℝ}
    (hm : IntegrableOn m (Icc a b)) (hFm : ∀ᵐ t ∂volume.restrict (Icc a b), ‖F t x₀‖ ≤ m t)
    {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖x t - x₀‖ ≤ |∫ s in t₀..t, m s| * exp |∫ s in t₀..t, (L s : ℝ)| :=
  norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_dist_le hL ht₀ hm hFm
    (hLip.mono fun _ hr y ↦ hr.dist_le_mul y x₀) hx h ht

/-- **Continuous dependence on the initial value.** Under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`, solutions `x` and `y` on
`[a, b]` of the integral equation with initial values `x₀` and `y₀` at `t₀` satisfy
`‖x t - y t‖ ≤ ‖x₀ - y₀‖ exp |∫ s in t₀..t, L s|` for every `t ∈ [a, b]`. -/
theorem dist_le_mul_exp_of_forall_mem_Icc_eq_picard_of_lipschitzWith (ht₀ : t₀ ∈ Icc a b)
    {y₀ : E}
    {x y : ℝ → E} (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxe : ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t)
    (hye : ∀ t ∈ Icc a b, y t = ODE.picard F t₀ y₀ y t) {t : ℝ} (ht : t ∈ Icc a b) :
    dist (x t) (y t) ≤ dist x₀ y₀ * exp |∫ s in t₀..t, (L s : ℝ)| := by
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
  rw [dist_eq_norm, dist_eq_norm]
  refine le_mul_exp_abs_integral_of_le_add_abs_integral_mul (u := fun s ↦ ‖x s - y s‖)
    (hL.mono_set hsub) (ae_of_all _ fun s ↦ (L s).coe_nonneg)
    ((hL.mono_set hsub).mul_continuousOn ((hx.mono hsub).sub (hy.mono hsub)).norm
      isCompact_uIcc) (fun _ _ ↦ norm_nonneg _) fun s hs ↦ ?_
  have hs' : s ∈ Icc a b := hsub hs
  have hsub' : uIcc t₀ s ⊆ Icc a b := uIcc_subset_Icc ht₀ hs'
  have hint {z : ℝ → E} (hz : ContinuousOn z (Icc a b)) :
      IntervalIntegrable (fun r ↦ F r (z r)) volume t₀ s :=
    ((integrableOn_apply_of_lipschitzWith hF hL hLip hz).mono_set hsub').intervalIntegrable
  have hLu : IntervalIntegrable (fun r ↦ (L r : ℝ) * ‖x r - y r‖) volume t₀ s :=
    ((hL.mono_set hsub').mul_continuousOn ((hx.mono hsub').sub (hy.mono hsub')).norm
      isCompact_uIcc).intervalIntegrable
  rw [hxe s hs', hye s hs', ODE.picard_apply, ODE.picard_apply, add_sub_add_comm,
    ← integral_sub (hint hx) (hint hy)]
  refine (norm_add_le _ _).trans (add_le_add le_rfl (norm_integral_le_abs_of_norm_le ?_ hLu))
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (uIoc_subset_uIcc.trans hsub') hLip]
    with r hr
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact hr.dist_le_mul _ _

end TauCeti
