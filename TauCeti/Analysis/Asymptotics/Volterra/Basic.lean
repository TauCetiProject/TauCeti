/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.MeasureTheory.Integral.Bochner.Tail

/-!
# Volterra integral equations with separable kernel bounds

Let `s ⊆ ℝ` be a measurable set (such as `(a, ∞)`, `(a, b)`, `(-∞, b)`, or `[α, b)`), let
`K : ℝ → ℝ → 𝕜` be continuous on `{p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2}` with a separable bound
`‖K x v‖ ≤ P x * Q v` for `x < v` in `s`, and let `P : ℝ → ℝ`, `J : ℝ → E`, and `ψ : ℝ → 𝕜` be
continuous on `s` such that the tail integrals

* `Φ x = ∫ v in s ∩ Ioi x, Q v * ‖J v‖`,
* `Ψ x = ∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖`

are integrable on `s ∩ Ioi x` for every `x ∈ s`. Then the Volterra integral equation

  `h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v)`

has a solution continuous on `s` satisfying `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for all `x ∈ s`, and
any two continuous solutions on `s` that are `O(P)` on `s ∩ Ioi x` for every `x ∈ s` agree on `s`.
Neither `ContinuousOn Q s` nor sign hypotheses `0 ≤ P`, `0 ≤ Q` are required. When `P` is a
constant `P₀` and `‖J v‖ ≤ ‖ψ v‖` on `s` (for example `J = ψ`), every continuous solution bounded
on tails satisfies the sharper estimate `‖h x‖ ≤ exp (P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖) - 1`.

Differentiation, `C¹` regularity, and derivative bounds for Volterra solutions are developed in
`TauCeti.Analysis.Asymptotics.Volterra.Deriv`. Together with its discrete counterpart
`TauCeti.exists_discrete_volterra_solution`, this theory (Olver, Chapter 6, §10; NIST DLMF §2.7)
underpins the existence and error-bound theorems for rank-one irregular singularities, the
Liouville–Green approximation, and differential equations with a large parameter.

## Main statements

* `TauCeti.exists_volterra_solution_on`, `TauCeti.exists_volterra_solution`, and
  `TauCeti.exists_volterra_solution_Ioo`: existence and `P Φ exp Ψ` bound on a measurable set `s`,
  on `(a, ∞)`, and on `(a, b)`.
* `TauCeti.eqOn_volterra_solution` and `TauCeti.eqOn_volterra_solution_Ioi`: uniqueness among
  continuous solutions with `h = O(P)` on tails.
* `TauCeti.norm_volterra_solution_le_on` and `TauCeti.norm_volterra_solution_le`: every continuous
  `O(P)` solution satisfies the `P Φ exp Ψ` bound.
* `TauCeti.norm_volterra_solution_le_exp_sub_one_on` and
  `TauCeti.norm_volterra_solution_le_exp_sub_one`: sharper `exp (P₀ Φ) - 1` bound when `P = P₀` is
  constant and `‖J‖ ≤ ‖ψ‖`.
* `TauCeti.volterra_bound_abs_eq`, `TauCeti.volterra_bound_nonneg_on`, and
  `TauCeti.continuousOn_volterra_integral`: sign invariance of the Volterra bound and parametric
  continuity of linear Volterra integral operators.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted A K Peters,
  1997. Chapter 6, §10.
* NIST Digital Library of Mathematical Functions, §§2.7–2.8, <https://dlmf.nist.gov/2.7>.
-/

public section

open MeasureTheory Filter Set Asymptotics Function
open scoped Topology Nat

namespace TauCeti

section SignHelpers

/-- If `0 ≤ c * Q v` throughout a measurable set `t`, then `|c| * ∫_t |Q| g = c * ∫_t Q g`. -/
private lemma abs_mul_setIntegral_abs_eq {t : Set ℝ} (ht : MeasurableSet t) {c : ℝ}
    {Q g : ℝ → ℝ} (hcQ : ∀ v ∈ t, 0 ≤ c * Q v) :
    |c| * ∫ v in t, |Q v| * g v = c * ∫ v in t, Q v * g v := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hEq : EqOn (fun v ↦ |Q v| * g v) (fun v ↦ -(Q v * g v)) t := fun v hv ↦ by
      dsimp only; rw [abs_of_nonpos (nonpos_of_mul_nonneg_right (hcQ v hv) hc), neg_mul]
    rw [abs_of_neg hc, setIntegral_congr_fun ht hEq, integral_neg, neg_mul_neg]
  · simp
  · have hEq : EqOn (fun v ↦ |Q v| * g v) (fun v ↦ Q v * g v) t := fun v hv ↦ by
      dsimp only; rw [abs_of_nonneg (nonneg_of_mul_nonneg_right (hcQ v hv) hc)]
    rw [abs_of_pos hc, setIntegral_congr_fun ht hEq]

/-- If `0 ≤ P x * Q v` for all `x < v` in `s`, then `{v ∈ s | P v * Q v < 0}` has at most two
elements and is therefore finite. -/
private lemma finite_mul_neg_of_mul_nonneg {s : Set ℝ} {P Q : ℝ → ℝ}
    (hPQ : ∀ x ∈ s, ∀ v ∈ s, x < v → 0 ≤ P x * Q v) :
    {v ∈ s | P v * Q v < 0}.Finite := by
  set B := {v ∈ s | P v * Q v < 0}
  have hno3 : ∀ {u v w}, u ∈ B → v ∈ B → w ∈ B → u < v → v < w → False :=
    fun {u v w} hu hv hw huv hvw ↦ by
      have hu' : P u * Q u < 0 := hu.2; have hv' : P v * Q v < 0 := hv.2
      have hw' : P w * Q w < 0 := hw.2
      have hpos : ∀ {x y}, x ∈ s → y ∈ s → x < y → P x * Q x < 0 → P y * Q y < 0 → 0 < P x * Q y :=
        fun {x y} hx hy hxy hxx hyy ↦ lt_of_le_of_ne (hPQ x hx y hy hxy)
          (mul_ne_zero (fun h ↦ by simp [h] at hxx) (fun h ↦ by simp [h] at hyy)).symm
      have hprod_pos := mul_pos (mul_pos (hpos hu.1 hv.1 huv hu' hv') (hpos hv.1 hw.1 hvw hv' hw'))
        (hpos hu.1 hw.1 (huv.trans hvw) hu' hw')
      have hprod_eq : (P u * Q v) * (P v * Q w) * (P u * Q w) =
          (P v * Q v) * (P u * Q w) ^ 2 := by ring
      rw [hprod_eq] at hprod_pos; nlinarith [sq_nonneg (P u * Q w)]
  rcases B.eq_empty_or_nonempty with hB | ⟨v₀, hv₀⟩
  · exact hB ▸ finite_empty
  have hlt : (B ∩ Iio v₀).Subsingleton := fun a ha b hb ↦
    (lt_trichotomy a b).elim (fun h ↦ (hno3 ha.1 hb.1 hv₀ h hb.2).elim)
      (·.elim id fun h ↦ (hno3 hb.1 ha.1 hv₀ h ha.2).elim)
  have hgt : (B ∩ Ioi v₀).Subsingleton := fun a ha b hb ↦
    (lt_trichotomy a b).elim (fun h ↦ (hno3 hv₀ ha.1 hb.1 ha.2 h).elim)
      (·.elim id fun h ↦ (hno3 hv₀ hb.1 ha.1 hb.2 h).elim)
  refine ((finite_singleton v₀).union (hlt.finite.union hgt.finite)).subset fun x hx ↦ ?_
  rcases lt_trichotomy x v₀ with h | rfl | h
  · simp [hx, h]
  · simp
  · simp [hx, h]

/-- Under `0 ≤ P x * Q v` for `x < v` in `s`, replacing `P` and `Q` by `|P|` and `|Q|` leaves any
Lebesgue integral of `P * Q * g` over a measurable subset `t ⊆ s` unchanged. -/
private lemma setIntegral_abs_mul_abs_eq {s t : Set ℝ} (ht : MeasurableSet t) (hts : t ⊆ s)
    {P Q g : ℝ → ℝ} (hPQ : ∀ x ∈ s, ∀ v ∈ s, x < v → 0 ≤ P x * Q v) :
    ∫ v in t, |P v| * |Q v| * g v = ∫ v in t, P v * Q v * g v := by
  have hnull : ∀ᵐ v ∂volume, v ∉ {v ∈ s | P v * Q v < 0} :=
    compl_mem_ae_iff.2 ((finite_mul_neg_of_mul_nonneg hPQ).measure_zero volume)
  refine setIntegral_congr_ae ht (hnull.mono fun v hv hvt ↦ ?_)
  simp only [← abs_mul, abs_of_nonneg (not_lt.1 fun hneg ↦ hv ⟨hts hvt, hneg⟩)]

/-- Sign invariance of the Volterra error bound: whenever `0 ≤ P y * Q v` for `y < v` in `s` and
`0 ≤ P₁ x * Q v` on `s ∩ Ioi x`, replacing `P₁`, `P`, and `Q` by `|P₁|`, `|P|`, and `|Q|` leaves
`P₁ x * Φ x * exp (Ψ x)` unchanged. -/
theorem volterra_bound_abs_eq {𝕜 E : Type*} [SeminormedAddCommGroup E] [NormedField 𝕜]
    {s : Set ℝ} (hs : MeasurableSet s) {J : ℝ → E} {ψ : ℝ → 𝕜} {P P₁ Q : ℝ → ℝ}
    (hPQ : ∀ y ∈ s, ∀ v ∈ s, y < v → 0 ≤ P y * Q v)
    {x : ℝ} (hP₁Q : ∀ v ∈ s ∩ Ioi x, 0 ≤ P₁ x * Q v) :
    |P₁ x| * (∫ v in s ∩ Ioi x, |Q v| * ‖J v‖) *
        Real.exp (∫ v in s ∩ Ioi x, |P v| * |Q v| * ‖ψ v‖) =
      P₁ x * (∫ v in s ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  have ht : MeasurableSet (s ∩ Ioi x) := hs.inter measurableSet_Ioi
  rw [abs_mul_setIntegral_abs_eq ht hP₁Q, setIntegral_abs_mul_abs_eq ht inter_subset_left hPQ]

/-- When `0 ≤ P x * Q v` for all `x < v` in `s`, the Volterra bound `P x * Φ x * exp (Ψ x)` is
nonnegative at every `x ∈ s`, even if `P` and `Q` take negative values. -/
theorem volterra_bound_nonneg_on {𝕜 E : Type*} [SeminormedAddCommGroup E] [NormedField 𝕜]
    {s : Set ℝ} (hs : MeasurableSet s) {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}
    (hPQ : ∀ x ∈ s, ∀ v ∈ s, x < v → 0 ≤ P x * Q v) {x : ℝ} (hx : x ∈ s) :
    0 ≤ P x * (∫ v in s ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  rw [← volterra_bound_abs_eq hs hPQ fun v hv ↦ hPQ x hx v hv.1 hv.2]
  exact mul_nonneg (mul_nonneg (abs_nonneg _)
    (integral_nonneg fun _ ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))) (Real.exp_nonneg _)

end SignHelpers

section ParametricOperator

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {s : Set ℝ} {K : ℝ → ℝ → 𝕜} {P : ℝ → ℝ}

omit [NormedSpace ℝ E] in
/-- Strong measurability of `v ↦ K x v • g v` on `s ∩ Ioi x` when `K` is continuous on the strict
upper triangle and `g` is continuous on `s`. -/
theorem aestronglyMeasurable_volterra_smul (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    {g : ℝ → E} (hg : ContinuousOn g s) {x : ℝ} (hx : x ∈ s) :
    AEStronglyMeasurable (fun v ↦ K x v • g v) (volume.restrict (s ∩ Ioi x)) := by
  have hcont : ContinuousOn (fun v ↦ K x v • g v) (s ∩ Ioi x) :=
    (ContinuousOn.comp (s := s ∩ Ioi x) hK (continuousOn_const.prodMk continuousOn_id)
      fun _ hv ↦ ⟨hx, hv.1, hv.2⟩).smul (hg.mono inter_subset_left)
  exact hcont.aestronglyMeasurable (hs.inter measurableSet_Ioi)

omit [NormedSpace ℝ E] in
/-- Almost-everywhere convergence along `𝓝[s] x₀` of the indicator Volterra integrand
`x ↦ (Ioi x).indicator (fun v ↦ K x v • g v) v` on `t ⊆ s`. -/
private lemma tendsto_indicator_kernel_smul {t : Set ℝ} (ht : MeasurableSet t) (hts : t ⊆ s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    {g : ℝ → E} {x₀ : ℝ} (hx₀ : x₀ ∈ s) :
    ∀ᵐ v ∂volume.restrict t,
      Tendsto (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • g u) v) (𝓝[s] x₀)
        (𝓝 ((Ioi x₀).indicator (fun u ↦ K x₀ u • g u) v)) := by
  refine ((ae_restrict_of_ae (Measure.ae_ne volume x₀)).and (ae_restrict_mem ht)).mono
    fun v ⟨hne, hvt⟩ ↦ ?_
  rcases lt_or_gt_of_ne hne with hvx₀ | hx₀v
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hvx₀)] with x hx
    simp [not_lt.2 (mem_Ioi.1 hx).le, not_lt.2 hvx₀.le]
  · have hmap : MapsTo (fun x ↦ (x, v)) (s ∩ Iio v) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2} :=
      fun _ hx ↦ ⟨hx.1, hts hvt, hx.2⟩
    have hcont : ContinuousWithinAt (fun x ↦ K x v • g v) s x₀ :=
      (((ContinuousOn.comp hK (continuousOn_id.prodMk continuousOn_const) hmap).continuousWithinAt
        ⟨hx₀, hx₀v⟩).mono_of_mem_nhdsWithin
        (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hx₀v)))).smul
        continuousWithinAt_const
    simp only [mem_Ioi.2 hx₀v, indicator_of_mem]
    refine hcont.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx₀v)] with x hx
    simp [mem_Ioi.2 (mem_Iio.1 hx)]

/-- Continuity within `s` at `x₀` of `x ↦ ∫ v in s ∩ Ioi x, K x v • g v` given a lower bound
`u ∈ s` along `𝓝[s] x₀` and an integrable majorant `B` on `s ∩ Ioi u`. -/
private lemma continuousWithinAt_volterra_integral (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    {g : ℝ → E} (hg : ContinuousOn g s) (hP : ContinuousOn P s)
    {x₀ u : ℝ} (hx₀ : x₀ ∈ s) (hge : ∀ᶠ x in 𝓝[s] x₀, u ≤ x) {B : ℝ → ℝ}
    (hB_int : IntegrableOn B (s ∩ Ioi u))
    (hKle : ∀ x ∈ s, u ≤ x → ∀ v ∈ s ∩ Ioi x, ‖K x v • g v‖ ≤ |P x| * B v) :
    ContinuousWithinAt (fun x ↦ ∫ v in s ∩ Ioi x, K x v • g v) s x₀ := by
  set t := s ∩ Ioi u
  have ht : MeasurableSet t := hs.inter measurableSet_Ioi
  have hinter : ∀ {x}, u ≤ x → Ioi x ∩ t = s ∩ Ioi x := fun {x} hux ↦ by
    ext v; simp only [t, mem_inter_iff, mem_Ioi]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, hux.trans_lt h.2⟩⟩
  set F : ℝ → ℝ → E := fun x v ↦ (Ioi x).indicator (fun v ↦ K x v • g v) v
  have hEq : (fun x ↦ ∫ v in s ∩ Ioi x, K x v • g v) =ᶠ[𝓝[s] x₀] fun x ↦ ∫ v in t, F x v := by
    filter_upwards [hge] with x hx
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      hinter hx]
  have hEq₀ : ∫ v in s ∩ Ioi x₀, K x₀ v • g v = ∫ v in t, F x₀ v := hEq.self_of_nhdsWithin hx₀
  rw [ContinuousWithinAt, hEq₀]
  refine (tendsto_congr' hEq).2 (tendsto_integral_filter_of_dominated_convergence
    (fun v ↦ (|P x₀| + 1) * ‖B v‖) ?_ ?_ (hB_int.norm.const_mul _)
    (tendsto_indicator_kernel_smul ht inter_subset_left hK hx₀))
  · filter_upwards [self_mem_nhdsWithin, hge] with x hx hxge
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, hinter hxge]
    exact aestronglyMeasurable_volterra_smul hs hK hg hx
  · have hP_lt : ∀ᶠ x in 𝓝[s] x₀, |P x| < |P x₀| + 1 :=
      ((continuous_abs.comp_continuousOn hP) x₀ hx₀).eventually (Iio_mem_nhds (lt_add_one |P x₀|))
    filter_upwards [self_mem_nhdsWithin, hge, hP_lt] with x hx hxge hPx
    refine ae_restrict_of_forall_mem ht fun v hv ↦ ?_
    simp only [F, indicator, mem_Ioi]
    split_ifs with hxv
    · exact (hKle x hx hxge v ⟨hv.1, hxv⟩).trans
        ((mul_le_mul_of_nonneg_left (Real.le_norm_self _) (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hPx.le (norm_nonneg _)))
    · rw [norm_zero]; positivity

/-- Parametric continuity on `s` of the linear Volterra integral operator
`x ↦ ∫ v in s ∩ Ioi x, K x v • g v` whenever each tail `s ∩ Ioi u` has an integrable majorant
`B u` with `‖K x v • g v‖ ≤ |P x| * B u v` for `u ≤ x < v` in `s`. -/
theorem continuousOn_volterra_integral (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    {g : ℝ → E} (hg : ContinuousOn g s) (hP : ContinuousOn P s)
    (B : ℝ → ℝ → ℝ) (hB_int : ∀ u ∈ s, IntegrableOn (B u) (s ∩ Ioi u))
    (hKle : ∀ u ∈ s, ∀ x ∈ s, u ≤ x → ∀ v ∈ s ∩ Ioi x, ‖K x v • g v‖ ≤ |P x| * B u v) :
    ContinuousOn (fun x ↦ ∫ v in s ∩ Ioi x, K x v • g v) s := by
  intro x₀ hx₀
  by_cases hleft : ∃ x₁ ∈ s, x₁ < x₀
  · obtain ⟨x₁, hx₁, hx₁₀⟩ := hleft
    exact continuousWithinAt_volterra_integral hs hK hg hP hx₀
      (eventually_of_mem (nhdsWithin_le_nhds (Ioi_mem_nhds hx₁₀)) fun _ hx ↦ le_of_lt hx)
      (hB_int x₁ hx₁) (hKle x₁ hx₁)
  · push Not at hleft
    exact continuousWithinAt_volterra_integral hs hK hg hP hx₀
      (eventually_of_mem self_mem_nhdsWithin hleft) (hB_int x₀ hx₀) (hKle x₀ hx₀)

end ParametricOperator

section PicardIteration

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {s : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

/-- Antitonicity on `s` of a tail integral `x ↦ ∫ v in s ∩ Ioi x, f v` of a nonnegative function. -/
private lemma setIntegral_Ioi_anti_of_nonneg (hs : MeasurableSet s) {f : ℝ → ℝ}
    (hf0 : ∀ v ∈ s, 0 ≤ f v) (hf_int : ∀ x ∈ s, IntegrableOn f (s ∩ Ioi x))
    {x y : ℝ} (hx : x ∈ s) (hxy : x ≤ y) :
    ∫ v in s ∩ Ioi y, f v ≤ ∫ v in s ∩ Ioi x, f v :=
  setIntegral_mono_set (hf_int x hx)
    (ae_restrict_of_forall_mem (hs.inter measurableSet_Ioi) fun v hv ↦ hf0 v hv.1)
    (Eventually.of_forall (inter_subset_inter_right s (Ioi_subset_Ioi hxy)))

/-- Increments of the Picard iteration for the Volterra integral equation on `s`: the `0`-th term is
`∫ v in s ∩ Ioi x, K x v • J v`, and each subsequent term applies
`f ↦ ∫ v in s ∩ Ioi x, K x v • ψ v • f v`. -/
private noncomputable def volterraPicardTerm (s : Set ℝ) (K : ℝ → ℝ → 𝕜) (J : ℝ → E)
    (ψ : ℝ → 𝕜) : ℕ → ℝ → E
  | 0, x => ∫ v in s ∩ Ioi x, K x v • J v
  | k + 1, x => ∫ v in s ∩ Ioi x, K x v • ψ v • volterraPicardTerm s K J ψ k v

omit [NormedSpace ℝ E] in
/-- One step of the Volterra Picard estimate: if `‖f v‖ ≤ c * P v * Ψ(v)^k / k!` on `s ∩ Ioi x`,
then `∫ v in s ∩ Ioi x, ‖K x v • ψ v • f v‖ ≤ c * P x * Ψ(x)^(k + 1) / (k + 1)!`. -/
private lemma setIntegral_norm_smul_smul_le (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hψ : ContinuousOn ψ s) (hP0 : ∀ x ∈ s, 0 ≤ P x) (hQ0 : ∀ v ∈ s, 0 ≤ Q v)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    {x : ℝ} (hx : x ∈ s) (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {f : ℝ → E} (hf_cont : ContinuousOn f s) {c : ℝ} (k : ℕ)
    (hf_le : ∀ v ∈ s ∩ Ioi x,
      ‖f v‖ ≤ c * P v * (∫ t in s ∩ Ioi v, P t * Q t * ‖ψ t‖) ^ k / k !) :
    IntegrableOn (fun v ↦ K x v • ψ v • f v) (s ∩ Ioi x) ∧
      ∫ v in s ∩ Ioi x, ‖K x v • ψ v • f v‖ ≤
        c * P x * (∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ (k + 1) / (k + 1)! := by
  set a : ℝ → ℝ := fun v ↦ P v * Q v * ‖ψ v‖
  set t := s ∩ Ioi x
  have ht : MeasurableSet t := hs.inter measurableSet_Ioi
  have hEq : EqOn (fun v ↦ a v * (∫ u in t ∩ Ioi v, a u) ^ k)
      (fun v ↦ a v * (∫ u in s ∩ Ioi v, a u) ^ k) t := fun v hv ↦ by
    dsimp only [t]; rw [inter_assoc, Ioi_inter_Ioi, max_eq_right hv.2.le]
  have ha_pow : IntegrableOn (fun v ↦ a v * (∫ u in s ∩ Ioi v, a u) ^ k) t :=
    (hΨ.mul_pow_setIntegral_Ioi k).congr_fun hEq ht
  have hpt : ∀ v ∈ t, ‖K x v • ψ v • f v‖ ≤
      (c * P x / k !) * (a v * (∫ u in s ∩ Ioi v, a u) ^ k) := fun v hv ↦ by
    rw [norm_smul, norm_smul]
    calc ‖K x v‖ * (‖ψ v‖ * ‖f v‖)
        ≤ (P x * Q v) * (‖ψ v‖ * (c * P v * (∫ u in s ∩ Ioi v, a u) ^ k / k !)) :=
          mul_le_mul (hKle x hx v hv.1 hv.2)
            (mul_le_mul_of_nonneg_left (hf_le v hv) (norm_nonneg _))
            (by positivity) (mul_nonneg (hP0 x hx) (hQ0 v hv.1))
      _ = (c * P x / k !) * (a v * (∫ u in s ∩ Ioi v, a u) ^ k) := by dsimp only [a]; ring
  have hint : IntegrableOn (fun v ↦ K x v • ψ v • f v) t :=
    (ha_pow.const_mul (c * P x / k !)).mono'
      (aestronglyMeasurable_volterra_smul hs hK (hψ.smul hf_cont) hx)
      (ae_restrict_of_forall_mem ht hpt)
  refine ⟨hint, ?_⟩
  calc ∫ v in t, ‖K x v • ψ v • f v‖
      ≤ ∫ v in t, (c * P x / k !) * (a v * (∫ u in s ∩ Ioi v, a u) ^ k) :=
        setIntegral_mono_on hint.norm (ha_pow.const_mul _) ht hpt
    _ = (c * P x / k !) * ∫ v in t, a v * (∫ u in t ∩ Ioi v, a u) ^ k := by
        rw [integral_const_mul, setIntegral_congr_fun ht hEq.symm]
    _ = c * P x * (∫ v in t, a v) ^ (k + 1) / (k + 1)! := by
        rw [hΨ.setIntegral_mul_pow_setIntegral_Ioi k, Nat.factorial_succ]; push_cast; field_simp

omit [NormedSpace ℝ E] in
private lemma integrableOn_volterra_smul_J (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2}) (hJ : ContinuousOn J s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v) {x : ℝ} (hx : x ∈ s)
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x)) :
    IntegrableOn (fun v ↦ K x v • J v) (s ∩ Ioi x) :=
  (hΦ.const_mul (P x)).mono' (aestronglyMeasurable_volterra_smul hs hK hJ hx)
    (ae_restrict_of_forall_mem (hs.inter measurableSet_Ioi) fun v hv ↦ by
      rw [norm_smul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hKle x hx v hv.1 hv.2) (norm_nonneg _))

/-- Inductive step for `continuousOn_and_norm_volterraPicardTerm_le`. -/
private lemma volterraPicardTerm_succ_step (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hψ : ContinuousOn ψ s) (hP : ContinuousOn P s)
    (hP0 : ∀ x ∈ s, 0 ≤ P x) (hQ0 : ∀ v ∈ s, 0 ≤ Q v)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x)) {k : ℕ}
    (ih_cont : ContinuousOn (volterraPicardTerm s K J ψ k) s)
    (ih_le : ∀ x ∈ s, ‖volterraPicardTerm s K J ψ k x‖ ≤
      (∫ v in s ∩ Ioi x, Q v * ‖J v‖) * P x *
        ((∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !)) :
    ContinuousOn (volterraPicardTerm s K J ψ (k + 1)) s ∧
      ∀ x ∈ s, ‖volterraPicardTerm s K J ψ (k + 1) x‖ ≤
        (∫ v in s ∩ Ioi x, Q v * ‖J v‖) * P x *
          ((∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ (k + 1) / (k + 1)!) := by
  set Φ : ℝ → ℝ := fun x ↦ ∫ v in s ∩ Ioi x, Q v * ‖J v‖
  set Ψ : ℝ → ℝ := fun x ↦ ∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖
  have hΦ0 : ∀ x ∈ s, 0 ≤ Φ x := fun _ _ ↦ setIntegral_nonneg (hs.inter measurableSet_Ioi)
    fun v hv ↦ mul_nonneg (hQ0 v hv.1) (norm_nonneg _)
  have hΨ0 : ∀ x ∈ s, 0 ≤ Ψ x := fun _ _ ↦ setIntegral_nonneg (hs.inter measurableSet_Ioi)
    fun v hv ↦ mul_nonneg (mul_nonneg (hP0 v hv.1) (hQ0 v hv.1)) (norm_nonneg _)
  have hcont := continuousOn_volterra_integral hs hK (hψ.smul ih_cont) hP
    (fun u v ↦ Φ u * (Ψ u ^ k / k !) * (P v * Q v * ‖ψ v‖))
    (fun u hu ↦ (hΨ u hu).const_mul _) fun u hu x hx hxge v hv ↦ by
      rw [norm_smul, Pi.smul_apply', norm_smul, abs_of_nonneg (hP0 x hx)]
      calc ‖K x v‖ * (‖ψ v‖ * ‖volterraPicardTerm s K J ψ k v‖)
          ≤ (P x * Q v) * (‖ψ v‖ * (Φ v * P v * (Ψ v ^ k / k !))) :=
            mul_le_mul (hKle x hx v hv.1 hv.2)
              (mul_le_mul_of_nonneg_left (ih_le v hv.1) (norm_nonneg _))
              (by positivity) (mul_nonneg (hP0 x hx) (hQ0 v hv.1))
        _ ≤ (P x * Q v) * (‖ψ v‖ * (Φ u * P v * (Ψ u ^ k / k !))) := by
            have := hP0 x hx; have := hQ0 v hv.1; have := hP0 v hv.1
            have := hΦ0 v hv.1; have := hΦ0 u hu; have := hΨ0 v hv.1
            gcongr
            · exact setIntegral_Ioi_anti_of_nonneg hs
                (fun w hw ↦ mul_nonneg (hQ0 w hw) (norm_nonneg _)) hΦ hu (hxge.trans hv.2.le)
            · exact setIntegral_Ioi_anti_of_nonneg hs
                (fun w hw ↦ mul_nonneg (mul_nonneg (hP0 w hw) (hQ0 w hw)) (norm_nonneg _))
                hΨ hu (hxge.trans hv.2.le)
        _ = P x * (Φ u * (Ψ u ^ k / k !) * (P v * Q v * ‖ψ v‖)) := by ring
  refine ⟨hcont, fun x hx ↦ ?_⟩
  rw [volterraPicardTerm, mul_div_assoc']
  refine (norm_integral_le_integral_norm _).trans
    (setIntegral_norm_smul_smul_le hs hK hψ hP0 hQ0 hKle hx (hΨ x hx) ih_cont
      k fun v hv ↦ ?_).2
  have := hP0 v hv.1; have := hΨ0 v hv.1
  calc ‖volterraPicardTerm s K J ψ k v‖
      ≤ Φ v * (P v * (Ψ v ^ k / k !)) := by rw [← mul_assoc]; exact ih_le v hv.1
    _ ≤ Φ x * (P v * (Ψ v ^ k / k !)) := mul_le_mul_of_nonneg_right
        (setIntegral_Ioi_anti_of_nonneg hs
          (fun w hw ↦ mul_nonneg (hQ0 w hw) (norm_nonneg _)) hΦ hx hv.2.le) (by positivity)
    _ = Φ x * P v * Ψ v ^ k / k ! := by ring

/-- Each Picard increment `volterraPicardTerm s K J ψ k` is continuous on `s` and bounded by
`Φ x * P x * (Ψ x ^ k / k !)`. -/
private lemma continuousOn_and_norm_volterraPicardTerm_le (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP : ContinuousOn P s)
    (hP0 : ∀ x ∈ s, 0 ≤ P x) (hQ0 : ∀ v ∈ s, 0 ≤ Q v)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x)) (k : ℕ) :
    ContinuousOn (volterraPicardTerm s K J ψ k) s ∧
      ∀ x ∈ s, ‖volterraPicardTerm s K J ψ k x‖ ≤
        (∫ v in s ∩ Ioi x, Q v * ‖J v‖) * P x *
          ((∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !) := by
  induction k with
  | zero =>
    refine ⟨continuousOn_volterra_integral hs hK hJ hP (fun _ v ↦ Q v * ‖J v‖) hΦ
      fun _ _ x hx _ v hv ↦ by
        rw [norm_smul, abs_of_nonneg (hP0 x hx), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hKle x hx v hv.1 hv.2) (norm_nonneg _), fun x hx ↦ ?_⟩
    have hpt : ∀ v ∈ s ∩ Ioi x, ‖K x v • J v‖ ≤ P x * (Q v * ‖J v‖) := fun v hv ↦ by
      rw [norm_smul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hKle x hx v hv.1 hv.2) (norm_nonneg _)
    simpa [volterraPicardTerm, mul_comm] using (norm_integral_le_integral_norm _).trans
      ((setIntegral_mono_on (integrableOn_volterra_smul_J hs hK hJ hKle hx (hΦ x hx)).norm
        ((hΦ x hx).const_mul _) (hs.inter measurableSet_Ioi) hpt).trans_eq (integral_const_mul _ _))
  | succ k ih => exact volterraPicardTerm_succ_step hs hK hψ hP hP0 hQ0 hKle hΦ hΨ ih.1 ih.2

/-- Continuity on `s` of the Picard series `∑' k, volterraPicardTerm s K J ψ k x`. -/
private lemma continuousOn_tsum_volterraPicardTerm [CompleteSpace E] {Φ Ψ : ℝ → ℝ}
    (hP : ContinuousOn P s) (hP0 : ∀ x ∈ s, 0 ≤ P x)
    (hΦ0 : ∀ x ∈ s, 0 ≤ Φ x) (hΨ0 : ∀ x ∈ s, 0 ≤ Ψ x)
    (hΦ_anti : ∀ ⦃x y⦄, x ∈ s → x ≤ y → Φ y ≤ Φ x)
    (hΨ_anti : ∀ ⦃x y⦄, x ∈ s → x ≤ y → Ψ y ≤ Ψ x)
    (hT_cont : ∀ k, ContinuousOn (volterraPicardTerm s K J ψ k) s)
    (hT_le : ∀ k, ∀ x ∈ s, ‖volterraPicardTerm s K J ψ k x‖ ≤ Φ x * P x * (Ψ x ^ k / k !)) :
    ContinuousOn (fun x ↦ ∑' k, volterraPicardTerm s K J ψ k x) s := by
  have hwithin : ∀ {x₀ u}, x₀ ∈ s → u ∈ s → (∀ᶠ x in 𝓝[s] x₀, u ≤ x) →
      ContinuousWithinAt (fun x ↦ ∑' k, volterraPicardTerm s K J ψ k x) s x₀ :=
    fun {x₀ u} hx₀ hu hge ↦ by
      set U := {x ∈ s | u ≤ x ∧ P x ≤ P x₀ + 1}
      have hU_mem : U ∈ 𝓝[s] x₀ := by
        filter_upwards [self_mem_nhdsWithin, hge,
          (hP x₀ hx₀).eventually (Iio_mem_nhds (lt_add_one (P x₀)))] with x hx hxge hPx
        exact ⟨hx, hxge, hPx.le⟩
      have hU_cont : ContinuousOn (fun x ↦ ∑' k, volterraPicardTerm s K J ψ k x) U := by
        refine continuousOn_tsum (fun k ↦ (hT_cont k).mono fun _ hx ↦ hx.1)
          ((Real.summable_pow_div_factorial (Ψ u)).mul_left (Φ u * (P x₀ + 1)))
          fun k x hx ↦ (hT_le k x hx.1).trans ?_
        have := hΦ0 x hx.1; have := hΦ0 u hu; have := hP0 x hx.1
        have := hΨ0 x hx.1; have := hP0 x₀ hx₀
        gcongr
        · exact hΦ_anti hu hx.2.1
        · exact hx.2.2
        · exact hΨ_anti hu hx.2.1
      exact (hU_cont x₀ (mem_of_mem_nhdsWithin hx₀ hU_mem)).mono_of_mem_nhdsWithin hU_mem
  intro x₀ hx₀
  by_cases hleft : ∃ x₁ ∈ s, x₁ < x₀
  · obtain ⟨x₁, hx₁, hx₁₀⟩ := hleft
    exact hwithin hx₀ hx₁
      (eventually_of_mem (nhdsWithin_le_nhds (Ioi_mem_nhds hx₁₀)) fun _ hx ↦ le_of_lt hx)
  · push Not at hleft
    exact hwithin hx₀ hx₀ (eventually_of_mem self_mem_nhdsWithin hleft)

/-- The sum of Picard increments satisfies the Volterra integral equation whenever the increments
are dominated on `s ∩ Ioi x` by `c * P * Ψ^k / k!`. -/
private lemma volterraPicardSum_eq (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hψ : ContinuousOn ψ s) (hP0 : ∀ x ∈ s, 0 ≤ P x) (hQ0 : ∀ v ∈ s, 0 ≤ Q v)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v) {x : ℝ} (hx : x ∈ s)
    (hKJ : IntegrableOn (fun v ↦ K x v • J v) (s ∩ Ioi x))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    (hT_cont : ∀ k, ContinuousOn (volterraPicardTerm s K J ψ k) s)
    (hh_cont : ContinuousOn (fun y ↦ ∑' k, volterraPicardTerm s K J ψ k y) s)
    {c M : ℝ}
    (hT_tail : ∀ k, ∀ v ∈ s ∩ Ioi x,
      ‖volterraPicardTerm s K J ψ k v‖ ≤
        c * P v * (∫ t in s ∩ Ioi v, P t * Q t * ‖ψ t‖) ^ k / k !)
    (hh_tail : ∀ v ∈ s ∩ Ioi x, ‖∑' k, volterraPicardTerm s K J ψ k v‖ ≤ M * P v)
    (hT_sum : Summable fun k ↦ volterraPicardTerm s K J ψ k x) :
    (∑' k, volterraPicardTerm s K J ψ k x) =
      ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • ∑' k, volterraPicardTerm s K J ψ k v) := by
  set T := volterraPicardTerm s K J ψ
  set h : ℝ → E := fun y ↦ ∑' k, T k y
  set Ψx := ∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖
  have hF := fun k ↦
    setIntegral_norm_smul_smul_le hs hK hψ hP0 hQ0 hKle hx hΨ (hT_cont k) k (hT_tail k)
  have hF_sum : Summable fun k ↦ ∫ v in s ∩ Ioi x, ‖K x v • ψ v • T k v‖ :=
    ((summable_nat_add_iff 1).2
      ((Real.summable_pow_div_factorial Ψx).mul_left (c * P x))).of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      fun k ↦ (hF k).2.trans_eq (mul_div_assoc _ _ _)
  have hKh_int : IntegrableOn (fun v ↦ K x v • ψ v • h v) (s ∩ Ioi x) :=
    (hΨ.const_mul (P x * max M 0)).mono'
      (aestronglyMeasurable_volterra_smul hs hK (hψ.smul hh_cont) hx)
      (ae_restrict_of_forall_mem (hs.inter measurableSet_Ioi) fun v hv ↦ by
        rw [norm_smul, norm_smul]
        calc ‖K x v‖ * (‖ψ v‖ * ‖h v‖)
            ≤ (P x * Q v) * (‖ψ v‖ * (max M 0 * P v)) :=
              mul_le_mul (hKle x hx v hv.1 hv.2)
                (mul_le_mul_of_nonneg_left ((hh_tail v hv).trans
                  (mul_le_mul_of_nonneg_right (le_max_left _ _) (hP0 v hv.1))) (norm_nonneg _))
                (by positivity) (mul_nonneg (hP0 x hx) (hQ0 v hv.1))
          _ = (P x * max M 0) * (P v * Q v * ‖ψ v‖) := by ring)
  have hsmul : ∀ v, K x v • ψ v • h v = ∑' k, K x v • ψ v • T k v := fun _ ↦ by
    simp only [h, ← tsum_const_smul'']
  simp_rw [smul_add]; rw [integral_add hKJ hKh_int]; simp_rw [hsmul]
  rw [← integral_tsum_of_summable_integral_norm (fun k ↦ (hF k).1) hF_sum]
  exact hT_sum.tsum_eq_zero_add

/-- Core Picard existence theorem in a complete space `E` for nonnegative weights `P, Q ≥ 0`. -/
private lemma exists_volterra_solution_on_nonneg [CompleteSpace E] (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP : ContinuousOn P s)
    (hP0 : ∀ x ∈ s, 0 ≤ P x) (hQ0 : ∀ v ∈ s, 0 ≤ Q v)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x)) :
    ∃ h : ℝ → E, ContinuousOn h s ∧
      (∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ s, ‖h x‖ ≤ P x * (∫ v in s ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  set T := volterraPicardTerm s K J ψ
  set h : ℝ → E := fun x ↦ ∑' k, T k x
  set Φ : ℝ → ℝ := fun x ↦ ∫ v in s ∩ Ioi x, Q v * ‖J v‖
  set Ψ : ℝ → ℝ := fun x ↦ ∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖
  have hT := continuousOn_and_norm_volterraPicardTerm_le hs hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ
  have hΦ0 : ∀ x ∈ s, 0 ≤ Φ x := fun _ _ ↦ setIntegral_nonneg (hs.inter measurableSet_Ioi)
    fun v hv ↦ mul_nonneg (hQ0 v hv.1) (norm_nonneg _)
  have hΨ0 : ∀ x ∈ s, 0 ≤ Ψ x := fun _ _ ↦ setIntegral_nonneg (hs.inter measurableSet_Ioi)
    fun v hv ↦ mul_nonneg (mul_nonneg (hP0 v hv.1) (hQ0 v hv.1)) (norm_nonneg _)
  have hΦ_anti : ∀ ⦃x y⦄, x ∈ s → x ≤ y → Φ y ≤ Φ x := fun _ _ hx hxy ↦
    setIntegral_Ioi_anti_of_nonneg hs (fun w hw ↦ mul_nonneg (hQ0 w hw) (norm_nonneg _)) hΦ hx hxy
  have hΨ_anti : ∀ ⦃x y⦄, x ∈ s → x ≤ y → Ψ y ≤ Ψ x := fun _ _ hx hxy ↦
    setIntegral_Ioi_anti_of_nonneg hs
      (fun w hw ↦ mul_nonneg (mul_nonneg (hP0 w hw) (hQ0 w hw)) (norm_nonneg _)) hΨ hx hxy
  have hexp : ∀ x, HasSum (fun k ↦ Φ x * P x * (Ψ x ^ k / k !))
      (Φ x * P x * Real.exp (Ψ x)) := fun x ↦ by
    rw [Real.exp_eq_exp_ℝ]; exact (NormedSpace.expSeries_div_hasSum_exp (Ψ x)).mul_left _
  have hh_cont : ContinuousOn h s := continuousOn_tsum_volterraPicardTerm hP hP0 hΦ0 hΨ0
    hΦ_anti hΨ_anti (fun k ↦ (hT k).1) (fun k x hx ↦ (hT k).2 x hx)
  have hh_le : ∀ x ∈ s, ‖h x‖ ≤ P x * Φ x * Real.exp (Ψ x) := fun x hx ↦ by
    rw [mul_comm (P x)]; exact tsum_of_norm_bounded (hexp x) fun k ↦ (hT k).2 x hx
  refine ⟨h, hh_cont, fun x hx ↦ volterraPicardSum_eq hs hK hψ hP0 hQ0 hKle hx
    (integrableOn_volterra_smul_J hs hK hJ hKle hx (hΦ x hx)) (hΨ x hx)
    (fun k ↦ (hT k).1) hh_cont
    (fun k v hv ↦ by
      have := hP0 v hv.1; have := hΨ0 v hv.1
      calc ‖T k v‖ ≤ Φ v * (P v * (Ψ v ^ k / k !)) := by rw [← mul_assoc]; exact (hT k).2 v hv.1
        _ ≤ Φ x * (P v * (Ψ v ^ k / k !)) :=
            mul_le_mul_of_nonneg_right (hΦ_anti hx hv.2.le) (by positivity)
        _ = Φ x * P v * Ψ v ^ k / k ! := by ring)
    (fun v hv ↦ (hh_le v hv.1).trans (by
      rw [mul_assoc, mul_comm (P v)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hΦ_anti hx hv.2.le)
        (Real.exp_le_exp.2 (hΨ_anti hx hv.2.le)) (Real.exp_nonneg _) (hΦ0 x hx)) (hP0 v hv.1)))
    ((hexp x).summable.of_norm_bounded fun k ↦ (hT k).2 x hx), hh_le⟩

end PicardIteration

section GeneralSet

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {s : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

omit [NormedSpace ℝ E] [NormedSpace 𝕜 E] in
/-- A function satisfying the Volterra bound `‖h y‖ ≤ P y * Φ y * exp (Ψ y)` on `s` is `O(P)` along
`𝓟 (s ∩ Ici x)` for every `x ∈ s`. -/
theorem isBigO_of_norm_le_volterra_bound_on (hs : MeasurableSet s)
    (hPQ : ∀ x ∈ s, ∀ v ∈ s, x < v → 0 ≤ P x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh : ∀ y ∈ s, ‖h y‖ ≤ P y * (∫ v in s ∩ Ioi y, Q v * ‖J v‖) *
      Real.exp (∫ v in s ∩ Ioi y, P v * Q v * ‖ψ v‖)) {x : ℝ} (hx : x ∈ s) :
    h =O[𝓟 (s ∩ Ici x)] P := by
  have hΦ' : IntegrableOn (fun v ↦ |Q v| * ‖J v‖) (s ∩ Ioi x) := by
    rw [IntegrableOn]; simpa [abs_mul] using (hΦ x hx).norm
  have hΨ' : IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi x) := by
    rw [IntegrableOn]; simpa [abs_mul] using (hΨ x hx).norm
  set C := (∫ v in s ∩ Ioi x, |Q v| * ‖J v‖) * Real.exp (∫ v in s ∩ Ioi x, |P v| * |Q v| * ‖ψ v‖)
  refine IsBigO.of_bound C (eventually_principal.2 fun y hy ↦ ?_)
  have hΦ_le : ∫ v in s ∩ Ioi y, |Q v| * ‖J v‖ ≤ ∫ v in s ∩ Ioi x, |Q v| * ‖J v‖ :=
    setIntegral_mono_set hΦ' (ae_of_all _ fun _ ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (Eventually.of_forall (inter_subset_inter_right s (Ioi_subset_Ioi hy.2)))
  have hΨ_le : ∫ v in s ∩ Ioi y, |P v| * |Q v| * ‖ψ v‖ ≤ ∫ v in s ∩ Ioi x, |P v| * |Q v| * ‖ψ v‖ :=
    setIntegral_mono_set hΨ'
      (ae_of_all _ fun _ ↦ mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _))
      (Eventually.of_forall (inter_subset_inter_right s (Ioi_subset_Ioi hy.2)))
  calc ‖h y‖
      ≤ |P y| * (∫ v in s ∩ Ioi y, |Q v| * ‖J v‖) *
          Real.exp (∫ v in s ∩ Ioi y, |P v| * |Q v| * ‖ψ v‖) := by
        rw [volterra_bound_abs_eq hs hPQ fun v hv ↦ hPQ y hy.1 v hv.1 hv.2]; exact hh y hy.1
    _ ≤ |P y| * C := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul hΦ_le (Real.exp_le_exp.2 hΨ_le)
          (Real.exp_nonneg _) (integral_nonneg fun _ ↦ by positivity)) (abs_nonneg _)
    _ = C * ‖P y‖ := by rw [Real.norm_eq_abs, mul_comm]

omit [NormedSpace ℝ E] in
/-- For a continuous function `h` on `s` satisfying `h =O[𝓟 (s ∩ Ioi x)] P`, the Volterra integrand
`v ↦ K x v • (J v + ψ v • h v)` is integrable on `s ∩ Ioi x`. -/
theorem integrableOn_volterra_of_isBigO_on (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s) {x : ℝ} (hx : x ∈ s)
    (hh_O : h =O[𝓟 (s ∩ Ioi x)] P) :
    IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (s ∩ Ioi x) := by
  obtain ⟨C, hC⟩ := hh_O.bound; rw [eventually_principal] at hC; set C' := max C 0
  have hΦ' : IntegrableOn (fun v ↦ |Q v| * ‖J v‖) (s ∩ Ioi x) := by
    rw [IntegrableOn]; simpa [abs_mul] using (hΦ x hx).norm
  have hΨ' : IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi x) := by
    rw [IntegrableOn]; simpa [abs_mul] using (hΨ x hx).norm
  refine ((hΦ'.add (hΨ'.const_mul C')).const_mul |P x|).mono'
    (aestronglyMeasurable_volterra_smul hs hK (hJ.add (hψ.smul hh_cont)) hx)
    (ae_restrict_of_forall_mem (hs.inter measurableSet_Ioi) fun v hv ↦ ?_)
  have hhv : ‖h v‖ ≤ C' * |P v| := by
    simpa [C', Real.norm_eq_abs] using (hC v hv).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_smul]
  calc ‖K x v‖ * ‖J v + ψ v • h v‖
      ≤ (|P x| * |Q v|) * (‖J v‖ + ‖ψ v‖ * (C' * |P v|)) := by
        refine mul_le_mul ((hKle x hx v hv.1 hv.2).trans ((le_abs_self _).trans_eq (abs_mul _ _)))
          ((norm_add_le _ _).trans ?_) (norm_nonneg _) (by positivity)
        rw [norm_smul]; gcongr
    _ = |P x| * (|Q v| * ‖J v‖ + C' * (|P v| * |Q v| * ‖ψ v‖)) := by ring

/-- **Volterra integral equations, existence on a measurable set.** If `K` is continuous on the
strict upper triangle `{p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2}` with `‖K x v‖ ≤ P x * Q v`, `J`, `ψ`,
and `P` are continuous on `s`, and `Q * ‖J‖` and `P * Q * ‖ψ‖` are integrable on `s ∩ Ioi x` for
every `x ∈ s`, then `h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v)` has a solution continuous on
`s` satisfying `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` on `s`. -/
theorem exists_volterra_solution_on (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP : ContinuousOn P s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x)) :
    ∃ h : ℝ → E, ContinuousOn h s ∧
      (∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ s, ‖h x‖ ≤ P x * (∫ v in s ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  have hPQ : ∀ x ∈ s, ∀ v ∈ s, x < v → 0 ≤ P x * Q v :=
    fun x hx v hv hxv ↦ (norm_nonneg _).trans (hKle x hx v hv hxv)
  by_cases hE : CompleteSpace E
  · obtain ⟨h, hh_cont, hh_eq, hh_le⟩ := exists_volterra_solution_on_nonneg hs hK hJ hψ
      (continuous_abs.comp_continuousOn hP) (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ abs_nonneg _)
      (fun x hx v hv hxv ↦ (hKle x hx v hv hxv).trans ((le_abs_self _).trans_eq (abs_mul _ _)))
      (fun x hx ↦ by rw [IntegrableOn]; simpa [abs_mul] using (hΦ x hx).norm)
      (fun x hx ↦ by rw [IntegrableOn]; simpa [abs_mul] using (hΨ x hx).norm)
    refine ⟨h, hh_cont, hh_eq, fun x hx ↦ (hh_le x hx).trans_eq ?_⟩
    exact volterra_bound_abs_eq hs hPQ fun v hv ↦ hPQ x hx v hv.1 hv.2
  · refine ⟨0, continuousOn_const, fun x _ ↦ by simp [integral_of_not_completeSpace hE],
      fun x hx ↦ by simpa using volterra_bound_nonneg_on hs hPQ hx⟩

/-- Pointwise homogeneous difference bound for two continuous `O(P)` Volterra solutions on `s`. -/
private lemma norm_sub_volterra_solution_le (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hψ : ContinuousOn ψ s) (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h₁ h₂ : ℝ → E} (h₁_cont : ContinuousOn h₁ s) (h₂_cont : ContinuousOn h₂ s)
    (h₁_eq : ∀ x ∈ s, h₁ x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ s, h₂ x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_O : ∀ x ∈ s, h₁ =O[𝓟 (s ∩ Ioi x)] P) (h₂_O : ∀ x ∈ s, h₂ =O[𝓟 (s ∩ Ioi x)] P)
    {x : ℝ} (hx : x ∈ s) :
    ‖(h₁ - h₂) x‖ ≤ ∫ v in s ∩ Ioi x, ‖K x v • ψ v • (h₁ - h₂) v‖ := by
  set d : ℝ → E := h₁ - h₂
  obtain ⟨C, hC⟩ := ((h₁_O x hx).sub (h₂_O x hx)).bound; rw [eventually_principal] at hC
  have hΨ' : IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi x) := by
    rw [IntegrableOn]; simpa [abs_mul] using (hΨ x hx).norm
  have hd_int : IntegrableOn (fun v ↦ K x v • ψ v • d v) (s ∩ Ioi x) :=
    (setIntegral_norm_smul_smul_le hs hK hψ (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ abs_nonneg _)
      (fun y hy v hv hyv ↦ (hKle y hy v hv hyv).trans ((le_abs_self _).trans_eq (abs_mul _ _)))
      hx hΨ' (h₁_cont.sub h₂_cont) (c := C) 0 fun v hv ↦ by
        simpa [d, Real.norm_eq_abs] using hC v hv).1
  have ht := hs.inter (measurableSet_Ioi (a := x))
  by_cases hF₂ : IntegrableOn (fun v ↦ K x v • (J v + ψ v • h₂ v)) (s ∩ Ioi x)
  · have hF₁ : IntegrableOn (fun v ↦ K x v • (J v + ψ v • h₁ v)) (s ∩ Ioi x) :=
      (hF₂.add hd_int).congr_fun
        (fun v _ ↦ by simp only [d, Pi.add_apply, Pi.sub_apply, smul_add, smul_sub]; abel) ht
    have hsub : d x = ∫ v in s ∩ Ioi x, K x v • ψ v • d v := by
      simp only [d, Pi.sub_apply, h₁_eq x hx, h₂_eq x hx, ← integral_sub hF₁ hF₂]
      exact setIntegral_congr_fun ht fun _ _ ↦ by simp [smul_add, smul_sub]
    rw [hsub]; exact norm_integral_le_integral_norm _
  · have hF₁ : ¬ IntegrableOn (fun v ↦ K x v • (J v + ψ v • h₁ v)) (s ∩ Ioi x) := fun hF₁ ↦
      hF₂ ((hF₁.sub hd_int).congr_fun
        (fun v _ ↦ by simp only [d, Pi.sub_apply, smul_add, smul_sub]; abel) ht)
    simp only [d, Pi.sub_apply, h₁_eq x hx, h₂_eq x hx, integral_undef hF₁, integral_undef hF₂,
      sub_zero, norm_zero]
    exact integral_nonneg fun _ ↦ norm_nonneg _

/-- **Volterra integral equations, uniqueness on a measurable set.** Any two solutions continuous on
`s` that satisfy `hᵢ =O[𝓟 (s ∩ Ioi x)] P` for every `x ∈ s` agree on `s`. -/
theorem eqOn_volterra_solution (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hψ : ContinuousOn ψ s) (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h₁ h₂ : ℝ → E} (h₁_cont : ContinuousOn h₁ s) (h₂_cont : ContinuousOn h₂ s)
    (h₁_eq : ∀ x ∈ s, h₁ x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ s, h₂ x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_O : ∀ x ∈ s, h₁ =O[𝓟 (s ∩ Ioi x)] P) (h₂_O : ∀ x ∈ s, h₂ =O[𝓟 (s ∩ Ioi x)] P) :
    EqOn h₁ h₂ s := by
  intro x₀ hx₀; set d : ℝ → E := h₁ - h₂
  have hd_cont : ContinuousOn d s := h₁_cont.sub h₂_cont
  have hKle' : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ |P x| * |Q v| :=
    fun x hx v hv hxv ↦ (hKle x hx v hv hxv).trans ((le_abs_self _).trans_eq (abs_mul _ _))
  have hΨ' : ∀ x ∈ s, IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi x) := fun x hx ↦ by
    rw [IntegrableOn]; simpa [abs_mul] using (hΨ x hx).norm
  obtain ⟨C, hC⟩ := ((h₁_O x₀ hx₀).sub (h₂_O x₀ hx₀)).bound; rw [eventually_principal] at hC
  set C' := max C 0
  set Ψ' : ℝ → ℝ := fun x ↦ ∫ v in s ∩ Ioi x, |P v| * |Q v| * ‖ψ v‖
  have hstep : ∀ {y}, y ∈ s → ∀ {k}, (∀ v ∈ s ∩ Ioi y, ‖d v‖ ≤ C' * |P v| * Ψ' v ^ k / k !) →
      ‖d y‖ ≤ C' * |P y| * Ψ' y ^ (k + 1) / (k + 1)! := fun {y} hy {k} hk ↦
    (norm_sub_volterra_solution_le hs hK hψ hKle hΨ h₁_cont h₂_cont h₁_eq h₂_eq h₁_O h₂_O
      hy).trans (setIntegral_norm_smul_smul_le hs hK hψ (fun _ _ ↦ abs_nonneg _)
      (fun _ _ ↦ abs_nonneg _) hKle' hy (hΨ' y hy) hd_cont k hk).2
  have hiter : ∀ k : ℕ, ∀ v ∈ s ∩ Ioi x₀, ‖d v‖ ≤ C' * |P v| * Ψ' v ^ k / k ! := by
    intro k; induction k with
    | zero =>
      intro v hv
      simpa [d, C', Real.norm_eq_abs] using (hC v hv).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    | succ k ih =>
      intro v hv; exact hstep hv.1 fun u hu ↦ ih u ⟨hu.1, hv.2.trans hu.2⟩
  have hlim : Tendsto (fun k ↦ C' * |P x₀| * (Ψ' x₀ ^ (k + 1) / (k + 1)!)) atTop (𝓝 0) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).2
      (FloorSemiring.tendsto_pow_div_factorial_atTop (Ψ' x₀))).const_mul (C' * |P x₀|)
  exact sub_eq_zero.1 (norm_le_zero_iff.1
    (ge_of_tendsto' hlim fun k ↦ (hstep hx₀ (hiter k)).trans_eq (mul_div_assoc _ _ _)))

/-- **Volterra integral equations, solution bound on a measurable set.** Every continuous solution
on `s` satisfying `h =O[𝓟 (s ∩ Ioi x)] P` for all `x ∈ s` obeys `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`. -/
theorem norm_volterra_solution_le_on (hs : MeasurableSet s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP : ContinuousOn P s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ s, h =O[𝓟 (s ∩ Ioi x)] P) {x : ℝ} (hx : x ∈ s) :
    ‖h x‖ ≤ P x * (∫ v in s ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨h₀, h₀_cont, h₀_eq, h₀_le⟩ := exists_volterra_solution_on hs hK hJ hψ hP hKle hΦ hΨ
  have hPQ : ∀ y ∈ s, ∀ v ∈ s, y < v → 0 ≤ P y * Q v :=
    fun y hy v hv hyv ↦ (norm_nonneg _).trans (hKle y hy v hv hyv)
  have h₀_O : ∀ y ∈ s, h₀ =O[𝓟 (s ∩ Ioi y)] P := fun y hy ↦
    (isBigO_of_norm_le_volterra_bound_on hs hPQ hΦ hΨ h₀_le hy).mono
      (principal_mono.2 (inter_subset_inter_right s Ioi_subset_Ici_self))
  rw [eqOn_volterra_solution hs hK hψ hKle hΨ hh_cont h₀_cont hh_eq h₀_eq hh_O h₀_O hx]
  exact h₀_le x hx

/-- One step of the exponential-tail bound for constant `P₀` and `‖J‖ ≤ ‖ψ‖`: if
`‖h v‖ ≤ (exp (Ψ v) - 1) + M * (Ψ v ^ k / k !)` on `s ∩ Ioi y`, then
`‖h y‖ ≤ (exp (Ψ y) - 1) + M * (Ψ y ^ (k + 1) / (k + 1)!)`. -/
private lemma norm_volterra_exp_step (hs : MeasurableSet s) {P₀ : ℝ}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P₀ * Q v) (hJψ : ∀ v ∈ s, ‖J v‖ ≤ ‖ψ v‖)
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    {y M : ℝ} (hy : y ∈ s)
    (ha_int : IntegrableOn (fun v ↦ |P₀| * |Q v| * ‖ψ v‖) (s ∩ Ioi y)) (k : ℕ)
    (hbound : ∀ v ∈ s ∩ Ioi y,
      ‖h v‖ ≤ (Real.exp (∫ u in s ∩ Ioi v, |P₀| * |Q u| * ‖ψ u‖) - 1) +
        M * ((∫ u in s ∩ Ioi v, |P₀| * |Q u| * ‖ψ u‖) ^ k / k !)) :
    ‖h y‖ ≤ (Real.exp (∫ v in s ∩ Ioi y, |P₀| * |Q v| * ‖ψ v‖) - 1) +
      M * ((∫ v in s ∩ Ioi y, |P₀| * |Q v| * ‖ψ v‖) ^ (k + 1) / (k + 1)!) := by
  set a : ℝ → ℝ := fun v ↦ |P₀| * |Q v| * ‖ψ v‖
  set Ψ : ℝ → ℝ := fun z ↦ ∫ u in s ∩ Ioi z, a u; set t := s ∩ Ioi y
  have ht : MeasurableSet t := hs.inter measurableSet_Ioi
  have hinter : ∀ {v}, v ∈ t → t ∩ Ioi v = s ∩ Ioi v := fun hv ↦ by
    dsimp only [t]; rw [inter_assoc, Ioi_inter_Ioi, max_eq_right hv.2.le]
  have hEq_exp : EqOn (fun v ↦ a v * Real.exp (∫ u in t ∩ Ioi v, a u))
      (fun v ↦ a v * Real.exp (Ψ v)) t := fun v hv ↦ by dsimp only; rw [hinter hv]
  have hEq_pow : EqOn (fun v ↦ a v * (∫ u in t ∩ Ioi v, a u) ^ k)
      (fun v ↦ a v * Ψ v ^ k) t := fun v hv ↦ by dsimp only; rw [hinter hv]
  have ha_exp := ha_int.mul_exp_setIntegral_Ioi.congr_fun hEq_exp ht
  have ha_pow := (ha_int.mul_pow_setIntegral_Ioi k).congr_fun hEq_pow ht
  have hpt : ∀ v ∈ t, ‖K y v • (J v + ψ v • h v)‖ ≤
      a v * Real.exp (Ψ v) + (M / k !) * (a v * Ψ v ^ k) := fun v hv ↦ by
    rw [norm_smul]
    calc ‖K y v‖ * ‖J v + ψ v • h v‖
        ≤ (|P₀| * |Q v|) * (‖ψ v‖ + ‖ψ v‖ * ((Real.exp (Ψ v) - 1) + M * (Ψ v ^ k / k !))) := by
          refine mul_le_mul ((hKle y hy v hv.1 hv.2).trans ((le_abs_self _).trans_eq (abs_mul _ _)))
            ((norm_add_le _ _).trans (add_le_add (hJψ v hv.1) ?_)) (norm_nonneg _) (by positivity)
          rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hbound v hv) (norm_nonneg _)
      _ = a v * Real.exp (Ψ v) + (M / k !) * (a v * Ψ v ^ k) := by dsimp only [a]; ring
  have hint : IntegrableOn (fun v ↦ K y v • (J v + ψ v • h v)) t :=
    (ha_exp.add (ha_pow.const_mul (M / k !))).mono'
      (aestronglyMeasurable_volterra_smul hs hK (hJ.add (hψ.smul hh_cont)) hy)
      (ae_restrict_of_forall_mem ht hpt)
  rw [hh_eq y hy]
  calc ‖∫ v in t, K y v • (J v + ψ v • h v)‖
      ≤ ∫ v in t, (a v * Real.exp (Ψ v) + (M / k !) * (a v * Ψ v ^ k)) :=
        (norm_integral_le_integral_norm _).trans
          (setIntegral_mono_on hint.norm (ha_exp.add (ha_pow.const_mul _)) ht hpt)
    _ = (Real.exp (Ψ y) - 1) + M * (Ψ y ^ (k + 1) / (k + 1)!) := by
        rw [integral_add ha_exp (ha_pow.const_mul _), integral_const_mul,
          setIntegral_congr_fun ht hEq_exp.symm, ha_int.setIntegral_mul_exp_setIntegral_Ioi,
          setIntegral_congr_fun ht hEq_pow.symm, ha_int.setIntegral_mul_pow_setIntegral_Ioi k,
          Nat.factorial_succ]
        dsimp only [Ψ, t]; push_cast; field_simp

/-- **Sharper Volterra bound for constant `P₀` and `‖J‖ ≤ ‖ψ‖`.** When `‖K x v‖ ≤ P₀ * Q v` and
`‖J v‖ ≤ ‖ψ v‖` on `s`, every continuous solution bounded on each tail `s ∩ Ioi x` satisfies
`‖h x‖ ≤ exp (P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖) - 1`. -/
theorem norm_volterra_solution_le_exp_sub_one_on (hs : MeasurableSet s) {P₀ : ℝ}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P₀ * Q v) (hJψ : ∀ v ∈ s, ‖J v‖ ≤ ‖ψ v‖)
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ s, h =O[𝓟 (s ∩ Ioi x)] (1 : ℝ → ℝ)) {x : ℝ} (hx : x ∈ s) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖) - 1 := by
  set a : ℝ → ℝ := fun v ↦ |P₀| * |Q v| * ‖ψ v‖
  set Ψ : ℝ → ℝ := fun y ↦ ∫ v in s ∩ Ioi y, a v
  have ha_int : ∀ y ∈ s, IntegrableOn a (s ∩ Ioi y) := fun y hy ↦ by
    have hq : IntegrableOn (fun v ↦ |Q v| * ‖ψ v‖) (s ∩ Ioi y) := by
      rw [IntegrableOn]; simpa [abs_mul] using (hΨ y hy).norm
    simpa only [IntegrableOn, a, mul_assoc] using hq.const_mul |P₀|
  obtain ⟨C, hC⟩ := (hh_O x hx).bound; rw [eventually_principal] at hC
  set M := max C 0
  have hiter : ∀ k : ℕ, ∀ v ∈ s ∩ Ioi x, ‖h v‖ ≤ (Real.exp (Ψ v) - 1) + M * (Ψ v ^ k / k !) := by
    intro k; induction k with
    | zero =>
      intro v hv
      have hhv : ‖h v‖ ≤ M := ((hC v hv).trans_eq (by simp)).trans (le_max_left _ _)
      have hΨ0 : 0 ≤ Real.exp (Ψ v) - 1 :=
        sub_nonneg.2 (Real.one_le_exp (integral_nonneg fun _ ↦ by dsimp only [a]; positivity))
      simpa using add_le_add hΨ0 hhv
    | succ k ih =>
      intro v hv; exact norm_volterra_exp_step hs hK hJ hψ hKle hJψ hh_cont hh_eq
        hv.1 (ha_int v hv.1) k fun u hu ↦ ih u ⟨hu.1, hv.2.trans hu.2⟩
  have hx_le : ∀ k, ‖h x‖ ≤ (Real.exp (Ψ x) - 1) + M * (Ψ x ^ (k + 1) / (k + 1)!) := fun k ↦
    norm_volterra_exp_step hs hK hJ hψ hKle hJψ hh_cont hh_eq hx (ha_int x hx) k (hiter k)
  have hlim : Tendsto (fun k ↦ (Real.exp (Ψ x) - 1) + M * (Ψ x ^ (k + 1) / (k + 1)!))
      atTop (𝓝 (Real.exp (Ψ x) - 1)) := by
    simpa using tendsto_const_nhds.add (((tendsto_add_atTop_iff_nat 1).2
      (FloorSemiring.tendsto_pow_div_factorial_atTop (Ψ x))).const_mul M)
  have hΨ_eq : Ψ x = P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖ := by
    dsimp only [Ψ, a]; simp_rw [mul_assoc, integral_const_mul]
    exact abs_mul_setIntegral_abs_eq (hs.inter measurableSet_Ioi)
      fun v hv ↦ (norm_nonneg _).trans (hKle x hx v hv.1 hv.2)
  rw [← hΨ_eq]; exact ge_of_tendsto' hlim hx_le

end GeneralSet

section Intervals

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {a b : ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

private lemma Ioi_inter_of_gt {y : ℝ} (hy : y ∈ Ioi a) : Ioi a ∩ Ioi y = Ioi y :=
  inter_eq_right.2 (Ioi_subset_Ioi hy.le)

omit [NormedSpace ℝ E] [NormedSpace 𝕜 E] in
/-- A function satisfying the Volterra bound on `Ioi a` is `O(P)` on `Ici x` for every `x > a`. -/
theorem isBigO_of_norm_le_volterra_bound (hPQ : ∀ x v, a < x → x < v → 0 ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : ∀ y ∈ Ioi a, ‖h y‖ ≤ P y * (∫ v in Ioi y, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi y, P v * Q v * ‖ψ v‖)) {x : ℝ} (hx : x ∈ Ioi a) :
    h =O[𝓟 (Ici x)] P := by
  simpa only [inter_eq_right.2 (Ici_subset_Ioi.2 hx)] using isBigO_of_norm_le_volterra_bound_on
    (s := Ioi a) measurableSet_Ioi (fun y hy v _ hyv ↦ hPQ y v hy hyv)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΦ y hy)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΨ y hy)
    (fun y hy ↦ by simpa only [Ioi_inter_of_gt hy] using hh y hy) hx

omit [NormedSpace ℝ E] [NormedSpace 𝕜 E] in
/-- A function satisfying the Volterra bound on `Ioi a` is `O(P)` along `atTop`. -/
theorem isBigO_atTop_of_norm_le_volterra_bound (hPQ : ∀ x v, a < x → x < v → 0 ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : ∀ y ∈ Ioi a, ‖h y‖ ≤ P y * (∫ v in Ioi y, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi y, P v * Q v * ‖ψ v‖)) :
    h =O[atTop] P :=
  (isBigO_of_norm_le_volterra_bound hPQ hΦ hΨ hh (lt_add_one a)).mono
    (le_principal_iff.2 (Ici_mem_atTop (a + 1)))

/-- **Volterra integral equations on `(a, ∞)`, existence.** -/
theorem exists_volterra_solution (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 < p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hP : ContinuousOn P (Ioi a))
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) :
    ∃ h : ℝ → E, ContinuousOn h (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ := exists_volterra_solution_on (s := Ioi a) measurableSet_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ hP (fun y hy v _ hyv ↦ hKle y v hy hyv)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΦ y hy)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΨ y hy)
  exact ⟨h, hh_cont, fun x hx ↦ by simpa only [Ioi_inter_of_gt hx] using hh_eq x hx,
    fun x hx ↦ by simpa only [Ioi_inter_of_gt hx] using hh_le x hx⟩

/-- **Volterra integral equations on `(a, b)`, existence.** -/
theorem exists_volterra_solution_Ioo
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b})
    (hJ : ContinuousOn J (Ioo a b)) (hψ : ContinuousOn ψ (Ioo a b)) (hP : ContinuousOn P (Ioo a b))
    (hKle : ∀ x v, a < x → x < v → v < b → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioo x b))
    (hΨ : ∀ x ∈ Ioo a b, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioo x b)) :
    ∃ h : ℝ → E, ContinuousOn h (Ioo a b) ∧
      (∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioo a b, ‖h x‖ ≤ P x * (∫ v in Ioo x b, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioo x b, P v * Q v * ‖ψ v‖) := by
  have hinter : ∀ {x}, a ≤ x → Ioo a b ∩ Ioi x = Ioo x b := fun {x} hax ↦ by
    rw [← Ioi_inter_Iio, inter_right_comm, Ioi_inter_Ioi, max_eq_right hax, Ioi_inter_Iio]
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ := exists_volterra_solution_on (s := Ioo a b) measurableSet_Ioo
    (hK.mono fun _ hp ↦ ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hJ hψ hP
    (fun y hy v hv hyv ↦ hKle y v hy.1 hyv hv.2) (fun y hy ↦ (hinter hy.1.le).symm ▸ hΦ y hy)
    (fun y hy ↦ (hinter hy.1.le).symm ▸ hΨ y hy)
  exact ⟨h, hh_cont, fun x hx ↦ by simpa only [hinter hx.1.le] using hh_eq x hx,
    fun x hx ↦ by simpa only [hinter hx.1.le] using hh_le x hx⟩

/-- **Volterra integral equations on `(a, ∞)`, uniqueness.** -/
theorem eqOn_volterra_solution_Ioi (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 < p.2})
    (hψ : ContinuousOn ψ (Ioi a)) (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h₁ h₂ : ℝ → E} (h₁_cont : ContinuousOn h₁ (Ioi a)) (h₂_cont : ContinuousOn h₂ (Ioi a))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_O : ∀ x ∈ Ioi a, h₁ =O[𝓟 (Ioi x)] P) (h₂_O : ∀ x ∈ Ioi a, h₂ =O[𝓟 (Ioi x)] P) :
    EqOn h₁ h₂ (Ioi a) :=
  eqOn_volterra_solution (s := Ioi a) measurableSet_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hψ
    (fun y hy v _ hyv ↦ hKle y v hy hyv) (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΨ y hy)
    h₁_cont h₂_cont (fun x hx ↦ (Ioi_inter_of_gt hx).symm ▸ h₁_eq x hx)
    (fun x hx ↦ (Ioi_inter_of_gt hx).symm ▸ h₂_eq x hx)
    (fun x hx ↦ (Ioi_inter_of_gt hx).symm ▸ h₁_O x hx)
    (fun x hx ↦ (Ioi_inter_of_gt hx).symm ▸ h₂_O x hx)

/-- **Volterra integral equations on `(a, ∞)`, solution bound.** -/
theorem norm_volterra_solution_le (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 < p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hP : ContinuousOn P (Ioi a))
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h (Ioi a))
    (hh_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ Ioi a, h =O[𝓟 (Ioi x)] P) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  simpa only [Ioi_inter_of_gt hx] using norm_volterra_solution_le_on (s := Ioi a) measurableSet_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ hP (fun y hy v _ hyv ↦ hKle y v hy hyv)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΦ y hy)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΨ y hy) hh_cont
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hh_eq y hy)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hh_O y hy) hx

/-- **Sharper Volterra bound on `(a, ∞)` for constant `P₀` and `‖J‖ ≤ ‖ψ‖`.** -/
theorem norm_volterra_solution_le_exp_sub_one {P₀ : ℝ}
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 < p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P₀ * Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h (Ioi a))
    (hh_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ Ioi a, h =O[𝓟 (Ioi x)] (1 : ℝ → ℝ)) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  simpa only [Ioi_inter_of_gt hx] using norm_volterra_solution_le_exp_sub_one_on (s := Ioi a)
    measurableSet_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ
    (fun y hy v _ hyv ↦ hKle y v hy hyv) hJψ (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hΨ y hy)
    hh_cont (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hh_eq y hy)
    (fun y hy ↦ (Ioi_inter_of_gt hy).symm ▸ hh_O y hy) hx

/-- Sanity check for `K = 0`: `exists_volterra_solution` and `eqOn_volterra_solution_Ioi` specialize
to the unique `O(P)` solution `h = 0` with `0 ≤ P x * Φ x * exp (Ψ x)`. -/
example (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hP : ContinuousOn P (Ioi a))
    (hPQ : ∀ x v, a < x → x < v → 0 ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) :
    ∃ h : ℝ → E, EqOn h 0 (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, (0 : 𝕜) • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioi a, 0 ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ := exists_volterra_solution (K := fun _ _ ↦ (0 : 𝕜))
    continuousOn_const hJ hψ hP (fun x v hx hxv ↦ by simpa using hPQ x v hx hxv) hΦ hΨ
  have hh_O : ∀ x ∈ Ioi a, h =O[𝓟 (Ioi x)] P := fun x hx ↦ (isBigO_of_norm_le_volterra_bound hPQ
    hΦ hΨ hh_le hx).mono (principal_mono.2 Ioi_subset_Ici_self)
  have heq0 : EqOn h 0 (Ioi a) := eqOn_volterra_solution_Ioi (K := fun _ _ ↦ (0 : 𝕜))
    continuousOn_const hψ (fun x v hx hxv ↦ by simpa using hPQ x v hx hxv) hΨ
    hh_cont continuousOn_const hh_eq (fun _ _ ↦ by simp) hh_O (fun _ _ ↦ isBigO_zero _ _)
  exact ⟨h, heq0, hh_eq, fun x hx ↦ by simpa [heq0 hx] using hh_le x hx⟩

end Intervals

end TauCeti
