/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Linear differential equations with measurable coefficients

Let `E` be a Banach space and consider the linear initial value problem

`x' = M(t) x + F(t)`, `x(a) = x₀`

on `[a, b]`, where `M : ℝ → E →L[ℝ] E` is almost everywhere strongly measurable and essentially
bounded by `K` on `(a, b)`, and `F : ℝ → E` is integrable there. Neither `M` nor `F` need be
continuous in `t`, so Mathlib's Picard–Lindelöf theorem does not apply; the equation is understood
in Carathéodory's sense, as the integral equation

`x t = x₀ + ∫ s in a..t, (M s (x s) + F s)`,

that is `x = ODE.picard (fun s y ↦ M s y + F s) a x₀ x` on `[a, b]`, for `x` continuous on
`[a, b]`. This file proves that this equation has a solution
(`TauCeti.exists_continuousOn_eq_forall_mem_Icc_eq_picard`) and that the solution is unique
(`TauCeti.eqOn_of_forall_mem_Icc_eq_picard`).

Linear equations with merely measurable, bounded coefficients arise as the Galerkin
approximations of linear parabolic equations, whose coefficients are only measurable in time.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 2.
* Mathlib's `Mathlib/Analysis/ODE/PicardLindelof.lean` (Yury Kudryashov, Winston Yin). The
  existence and uniqueness proofs here follow its argument that some iterate of the Picard map is
  a contraction.
-/

public section

open Function MeasureTheory Set intervalIntegral
open scoped Nat NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : ℝ → E →L[ℝ] E} {F : ℝ → E}
  {a b K : ℝ} {x₀ : E}

/-- The right-hand side `s ↦ M s (x s) + F s` of a linear equation with essentially bounded
measurable `M` and integrable `F` on `(a, b)` is integrable on `(a, b)` along every curve `x`
continuous on `[a, b]`. -/
theorem integrableOn_clm_apply_add (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))
    {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntegrableOn (fun s ↦ M s (x s) + F s) (Ioo a b) := by
  refine IntegrableOn.add ?_ hF
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  refine (integrable_const (max K 0 * max C 0)).mono'
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).aestronglyMeasurable_comp₂ hM
      ((hx.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)) ?_
  filter_upwards [hK, ae_restrict_mem measurableSet_Ioo] with s hs hs'
  exact ((M s).le_opNorm _).trans (mul_le_mul (hs.trans (le_max_left _ _))
    ((hC s (Ioo_subset_Icc_self hs')).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))

namespace CaratheodoryLinear

/-- The integrand `s ↦ M s (y s) + F s` of the Picard map is integrable on `[a, b]`. -/
private theorem integrableOn_Icc (hab : a ≤ b)
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))
    (y : C(Icc a b, E)) :
    IntegrableOn (fun s ↦ M s (IccExtend hab y s) + F s) (Icc a b) :=
  (integrableOn_Icc_iff_integrableOn_Ioo (f := fun s ↦ M s (IccExtend hab y s) + F s)).2
    (integrableOn_clm_apply_add hM hK hF y.continuous.Icc_extend'.continuousOn)

/-- The Picard map `y ↦ x₀ + ∫ₐᵗ (M s (y s) + F s) ds` on `C([a, b], E)`. -/
private noncomputable def next (hab : a ≤ b)
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))
    (x₀ : E) (y : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ODE.picard (fun s z ↦ M s z + F s) a x₀ (IccExtend hab y) t
  continuous_toFun := by
    have hI : IntegrableOn (fun s ↦ M s (IccExtend hab y s) + F s) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact integrableOn_Icc hab hM hK hF y
    have h := continuousOn_primitive_interval hI
    rw [uIcc_of_le hab] at h
    exact (continuousOn_const.add h).comp_continuous continuous_subtype_val Subtype.prop

private theorem next_apply (hab : a ≤ b)
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))
    (y : C(Icc a b, E)) (t : Icc a b) :
    next hab hM hK hF x₀ y t = ODE.picard (fun s z ↦ M s z + F s) a x₀ (IccExtend hab y) t :=
  rfl

variable (hab : a ≤ b) (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
  (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))

include hab hM hK hF in
/-- If `‖M t‖ ≤ L` almost everywhere, the `n`-th iterate of the Picard map moves two curves at
time `t` at most `(L (t - a))ⁿ / n!` times their distance apart. -/
private theorem dist_iterate_next_apply_le {L : ℝ} (hL : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ L)
    (hL₀ : 0 ≤ L) (n : ℕ) (y z : C(Icc a b, E)) (t : Icc a b) :
    dist ((next hab hM hK hF x₀)^[n] y t) ((next hab hM hK hF x₀)^[n] z t) ≤
      (L * (t - a)) ^ n / n ! * dist y z := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
  | succ n ih =>
    set Y := (next hab hM hK hF x₀)^[n] y
    set Z := (next hab hM hK hF x₀)^[n] z
    have hint : ∀ W : C(Icc a b, E), IntervalIntegrable
        (fun s ↦ M s (IccExtend hab W s) + F s) volume a t := fun W ↦
      (intervalIntegrable_iff_integrableOn_Icc_of_le t.2.1).2
        ((integrableOn_Icc hab hM hK hF W).mono_set (Icc_subset_Icc_right t.2.2))
    have hLae : ∀ᵐ s, s ∈ Ioc a b → ‖M s‖ ≤ L := by
      rwa [← ae_restrict_iff' measurableSet_Ioc, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      ODE.picard_apply, ODE.picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hint Y) (hint Z)]
    calc _ ≤ ∫ s in a..t, L * ((L * (s - a)) ^ n / n ! * dist y z) := by
          refine norm_integral_le_of_norm_le t.2.1 ?_
            (Continuous.intervalIntegrable (by fun_prop) _ _)
          filter_upwards [hLae] with s hs hst
          have hs' : s ∈ Icc a b := ⟨hst.1.le, hst.2.trans t.2.2⟩
          rw [add_sub_add_right_eq_sub, ← map_sub, IccExtend_of_mem hab _ hs',
            IccExtend_of_mem hab _ hs']
          refine ((M s).le_opNorm _).trans (mul_le_mul (hs ⟨hst.1, hst.2.trans t.2.2⟩) ?_
            (norm_nonneg _) hL₀)
          simpa [dist_eq_norm] using ih ⟨s, hs'⟩
      _ = (L * (t - a)) ^ (n + 1) / (n + 1)! * dist y z := by
          have : ∫ s in a..t, L * ((L * (s - a)) ^ n / n ! * dist y z) =
              L ^ (n + 1) * dist y z / n ! * ∫ s in a..t, (s - a) ^ n := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1
            ext s
            rw [mul_pow, pow_succ]
            ring
          rw [this, intervalIntegral.integral_comp_sub_right (fun s ↦ s ^ n), integral_pow,
            sub_self, zero_pow n.succ_ne_zero, sub_zero, Nat.factorial_succ, mul_pow]
          push_cast
          field_simp

include hab hM hK hF in
/-- Some iterate of the Picard map is a contraction. -/
private theorem exists_contractingWith_iterate_next :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next hab hM hK hF x₀)^[n] := by
  set K' := max K 0
  have hK' : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K' := hK.mono fun t ht ↦ ht.trans
    (le_max_left _ _)
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K' * (b - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have h₀ : 0 ≤ (K' * (b - a)) ^ n / n ! := by
    have : 0 ≤ K' := le_max_right _ _
    have : 0 ≤ b - a := sub_nonneg.2 hab
    positivity
  refine ⟨n, ((K' * (b - a)) ^ n / n !).toNNReal, Real.toNNReal_lt_one.2 hn,
    LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  rw [Real.coe_toNNReal _ h₀, ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_next_apply_le hab hM hK hF hK' (le_max_right _ _) n y z t).trans ?_
  have h₁ : 0 ≤ K' * (t - a) := mul_nonneg (le_max_right _ _) (sub_nonneg.2 t.2.1)
  have h₂ : K' * (t - a) ≤ K' * (b - a) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right t.2.2 a) (le_max_right _ _)
  gcongr

include hab hM hK hF in
/-- A curve continuous on `[a, b]` solving the integral equation there restricts to a fixed point of
the Picard map. -/
private theorem isFixedPt_next {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x t) :
    IsFixedPt (next hab hM hK hF x₀) ⟨(Icc a b).domRestrict x, hx.domRestrict⟩ := by
  ext t
  rw [next_apply, ContinuousMap.coe_mk, domRestrict_apply, h t t.2, ODE.picard_apply,
    ODE.picard_apply]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  have hs' : s ∈ Icc a b := uIcc_subset_Icc ⟨le_rfl, hab⟩ t.2 hs
  simp [IccExtend_of_mem hab _ hs']

end CaratheodoryLinear

open CaratheodoryLinear

/-- **Carathéodory's existence theorem for linear equations.** Let `M : ℝ → E →L[ℝ] E` be almost
everywhere strongly measurable and essentially bounded on `(a, b)`, and let `F : ℝ → E` be
integrable on `(a, b)`. Then the linear equation `x' = M(t) x + F(t)` with `x(a) = x₀` has a
solution in Carathéodory's sense: a curve `x` continuous on `[a, b]` with `x a = x₀` and
`x t = x₀ + ∫ s in a..t, (M s (x s) + F s)` for every `t ∈ [a, b]`. -/
theorem exists_continuousOn_eq_forall_mem_Icc_eq_picard [CompleteSpace E]
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b)) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧ x a = x₀ ∧
      ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x t := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨fun _ ↦ x₀, continuousOn_const, rfl, by simp [Icc_eq_empty_of_lt hba]⟩
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) hab hM hK hF
  obtain ⟨y, hy⟩ : ∃ y, IsFixedPt (next hab hM hK hF x₀) y :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  have hsol : ∀ t ∈ Icc a b,
      IccExtend hab y t = ODE.picard (fun s y ↦ M s y + F s) a x₀ (IccExtend hab y) t := by
    intro t ht
    rw [IccExtend_of_mem hab _ ht]
    conv_lhs => rw [← hy]
    rw [next_apply]
  exact ⟨IccExtend hab y, y.continuous.Icc_extend'.continuousOn,
    by simpa using hsol a (left_mem_Icc.2 hab), hsol⟩

/-- **Uniqueness for linear equations with measurable coefficients.** Let `M : ℝ → E →L[ℝ] E` be
almost everywhere strongly measurable and essentially bounded on `(a, b)`, and let `F : ℝ → E` be
integrable on `(a, b)`. Two curves continuous on `[a, b]` that solve
`x t = x₀ + ∫ s in a..t, (M s (x s) + F s)` on `[a, b]` agree on `[a, b]`. -/
theorem eqOn_of_forall_mem_Icc_eq_picard
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))
    {x₁ x₂ : ℝ → E} (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x₁ t)
    (h₂ : ∀ t ∈ Icc a b, x₂ t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x₂ t) :
    EqOn x₁ x₂ (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · simp [Icc_eq_empty_of_lt hba]
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) hab hM hK hF
  have := hC.fixedPoint_unique' ((isFixedPt_next hab hM hK hF hx₁ h₁).iterate n)
    ((isFixedPt_next hab hM hK hF hx₂ h₂).iterate n)
  exact fun t ht ↦ congr($this ⟨t, ht⟩)

end TauCeti
