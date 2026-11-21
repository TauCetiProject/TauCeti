/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.MeasureTheory.Function.LocallyIntegrable

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
(`TauCeti.eqOn_of_forall_mem_Icc_eq_picard`). For continuous coefficients and classical
solutions on the whole line, `Continuous.eq_of_hasDerivAt_clm_apply` deduces uniqueness for
`v' = B(t) v` from Mathlib's `ODE_solution_unique_of_mem_Ioo`, and
`Continuous.eqOn_Ici_of_hasDerivAt_clm_apply` does the same in forward time on a half-line
`[a, ∞)` from `ODE_solution_unique_of_mem_Icc_right`.

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

/-- The right-hand side `s ↦ M s (x s) + F s` of a linear equation with `M` and `F` integrable on
`(a, b)` is integrable on `(a, b)` along every curve `x` continuous on `[a, b]`. -/
theorem integrableOn_clm_apply_add (hM : IntegrableOn M (Ioo a b)) (hF : IntegrableOn F (Ioo a b))
    {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntegrableOn (fun s ↦ M s (x s) + F s) (Ioo a b) := by
  -- `M` is integrable on the compact interval `[a, b]`, on which `x` is continuous.
  have hM' := ((integrableOn_Icc_iff_integrableOn_Ioo (f := M)).2 hM).locallyIntegrableOn
  exact (((hM'.clm_apply_continuousOn isClosed_Icc.isLocallyClosed hx).integrableOn_isCompact
    isCompact_Icc).mono_set Ioo_subset_Icc_self).add hF

namespace CaratheodoryLinear

/-- The integrand `s ↦ M s (y s) + F s` of the Picard map is integrable on `[a, b]`. -/
private theorem integrableOn_Icc (hab : a ≤ b) (hM : IntegrableOn M (Ioo a b))
    (hF : IntegrableOn F (Ioo a b)) (y : C(Icc a b, E)) :
    IntegrableOn (fun s ↦ M s (IccExtend hab y s) + F s) (Icc a b) :=
  (integrableOn_Icc_iff_integrableOn_Ioo (f := fun s ↦ M s (IccExtend hab y s) + F s)).2
    (integrableOn_clm_apply_add hM hF y.continuous.Icc_extend'.continuousOn)

/-- The Picard map `y ↦ x₀ + ∫ₐᵗ (M s (y s) + F s) ds` on `C([a, b], E)`. -/
private noncomputable def next (hab : a ≤ b) (hM : IntegrableOn M (Ioo a b))
    (hF : IntegrableOn F (Ioo a b)) (x₀ : E) (y : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ODE.picard (fun s z ↦ M s z + F s) a x₀ (IccExtend hab y) t
  continuous_toFun := by
    have h := continuousOn_primitive_interval (a := a) (b := b)
      (by rw [uIcc_of_le hab]; exact integrableOn_Icc hab hM hF y)
    rw [uIcc_of_le hab] at h
    exact (continuousOn_const.add h).comp_continuous continuous_subtypeVal Subtype.prop

private theorem next_apply (hab : a ≤ b) (hM : IntegrableOn M (Ioo a b))
    (hF : IntegrableOn F (Ioo a b)) (y : C(Icc a b, E)) (t : Icc a b) :
    next hab hM hF x₀ y t = ODE.picard (fun s z ↦ M s z + F s) a x₀ (IccExtend hab y) t :=
  rfl

variable (hab : a ≤ b) (hM : IntegrableOn M (Ioo a b)) (hF : IntegrableOn F (Ioo a b))

include hab hM hF in
/-- If `‖M t‖ ≤ L` almost everywhere, the `n`-th iterate of the Picard map moves two curves at
time `t` at most `(L (t - a))ⁿ / n!` times their distance apart. -/
private theorem dist_iterate_next_apply_le {L : ℝ} (hL : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ L)
    (hL₀ : 0 ≤ L) (n : ℕ) (y z : C(Icc a b, E)) (t : Icc a b) :
    dist ((next hab hM hF x₀)^[n] y t) ((next hab hM hF x₀)^[n] z t) ≤
      (L * (t - a)) ^ n / n ! * dist y z := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
  | succ n ih =>
    set Y := (next hab hM hF x₀)^[n] y
    set Z := (next hab hM hF x₀)^[n] z
    have hint : ∀ W : C(Icc a b, E), IntervalIntegrable
        (fun s ↦ M s (IccExtend hab W s) + F s) volume a t := fun W ↦
      (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).2
        ((integrableOn_Icc hab hM hF W).mono_set (Icc_subset_Icc_right t.property.2))
    have hLae : ∀ᵐ s, s ∈ Ioc a b → ‖M s‖ ≤ L := by
      rwa [← ae_restrict_iff' measurableSet_Ioc, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      ODE.picard_apply, ODE.picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hint Y) (hint Z)]
    calc _ ≤ ∫ s in a..t, L * ((L * (s - a)) ^ n / n ! * dist y z) := by
          refine norm_integral_le_of_norm_le t.property.1 ?_
            (Continuous.intervalIntegrable (by fun_prop) _ _)
          filter_upwards [hLae] with s hs hst
          have hs' : s ∈ Icc a b := ⟨hst.1.le, hst.2.trans t.property.2⟩
          rw [add_sub_add_right_eq_sub, ← map_sub, IccExtend_of_mem hab _ hs',
            IccExtend_of_mem hab _ hs']
          refine ((M s).le_opNorm _).trans (mul_le_mul (hs ⟨hst.1, hst.2.trans t.property.2⟩) ?_
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

include hab hM hF in
/-- If `‖M t‖ ≤ K` almost everywhere, some iterate of the Picard map is a contraction. -/
private theorem exists_contractingWith_iterate_next
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next hab hM hF x₀)^[n] := by
  set K' := max K 0
  have hK' : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K' := hK.mono fun t ht ↦ ht.trans
    (le_max_left _ _)
  have hK'₀ : 0 ≤ K' := le_max_right _ _
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K' * (b - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have h₀ : 0 ≤ (K' * (b - a)) ^ n / n ! := by
    have : 0 ≤ b - a := sub_nonneg.2 hab
    positivity
  refine ⟨n, ((K' * (b - a)) ^ n / n !).toNNReal, Real.toNNReal_lt_one.2 hn,
    LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  rw [Real.coe_toNNReal _ h₀, ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_next_apply_le hab hM hF hK' hK'₀ n y z t).trans ?_
  have : 0 ≤ (t : ℝ) - a := sub_nonneg.2 t.property.1
  have : (t : ℝ) ≤ b := t.property.2
  gcongr

include hab hM hF in
/-- A curve continuous on `[a, b]` solving the integral equation there restricts to a fixed point of
the Picard map. -/
private theorem isFixedPt_next {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x t) :
    IsFixedPt (next hab hM hF x₀) ⟨(Icc a b).domRestrict x, hx.domRestrict⟩ := by
  ext t
  rw [next_apply, ContinuousMap.coe_mk, domRestrict_apply, h t t.property, ODE.picard_apply,
    ODE.picard_apply]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  have hs' : s ∈ Icc a b := uIcc_subset_Icc ⟨le_rfl, hab⟩ t.property hs
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
  have hMi : IntegrableOn M (Ioo a b) := Integrable.of_bound hM K hK
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) hab hMi hF hK
  obtain ⟨y, hy⟩ : ∃ y, IsFixedPt (next hab hMi hF x₀) y :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  have hsol : ∀ t ∈ Icc a b,
      IccExtend hab y t = ODE.picard (fun s y ↦ M s y + F s) a x₀ (IccExtend hab y) t :=
    fun t ht ↦ by rw [IccExtend_of_mem hab _ ht, ← next_apply hab hMi hF y ⟨t, ht⟩, hy]
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
  have hMi : IntegrableOn M (Ioo a b) := Integrable.of_bound hM K hK
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) hab hMi hF hK
  have := hC.fixedPoint_unique' ((isFixedPt_next hab hMi hF hx₁ h₁).iterate n)
    ((isFixedPt_next hab hMi hF hx₂ h₂).iterate n)
  exact fun t ht ↦ congr($this ⟨t, ht⟩)

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
