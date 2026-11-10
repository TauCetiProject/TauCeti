/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Topology.Order.Interval
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weak derivatives on an interval

Let `F` be a Banach space and `u, u' : ℝ → F` locally integrable on the open interval `(a, b)`.
This file proves that `u'` is the weak derivative of `u` on `(a, b)` exactly when `u` is, almost
everywhere, a constant plus the primitive of `u'`:

`u t = c + ∫ s in t₀..t, u' s` for almost every `t ∈ (a, b)`,

for any base point `t₀ ∈ (a, b)`. When `u'` is integrable on the whole interval, `u` therefore has
a representative `v` continuous on `[a, b]`, every such representative satisfies the fundamental
theorem of calculus `v t - v s = ∫ r in s..t, u' r` on `[a, b]`, and, when `a < b`, it is bounded
by

`‖v t‖ ≤ ⨍ s in (a, b), ‖u s‖ + ∫ s in (a, b), ‖u' s‖`.

This is the theory of the vector-valued Sobolev space `W^{1,1}(a, b; F)`. It is the analytic
input for evolution equations, whose solutions are functions of time `t ∈ (0, T)` with values in a
function space `F`, and whose time derivatives are weak derivatives in this sense. The weak
derivative is `TauCeti.HasWeakLineDerivOn` for Lebesgue measure on `ℝ`, the open set `(a, b)` and
the direction `1`, so the test functions are the real smooth functions with compact support in
`(a, b)`.

## Proof

The primitive `w t = ∫ s in t₀..t, u' s` has weak derivative `u'`: against a test function `φ`
supported in `[α, β] ⊆ (a, b)`, the integration by parts
`TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le`, proved with Fubini's
theorem, turns `∫ φ' t • ∫ s in α..t, u' s` into `-∫ φ s • u' s`. Then
`u - w` has weak derivative `0`, so it is almost everywhere constant by the du Bois-Reymond lemma
`MeasureTheory.LocallyIntegrableOn.exists_ae_eq_const_Ioo_of_integral_deriv_smul_eq_zero`.

## Main declarations

* `TauCeti.hasWeakLineDerivOn_intervalIntegral`: the primitive of a locally integrable function
  is weakly differentiable, with weak derivative the function.
* `TauCeti.hasWeakLineDerivOn_intervalIntegral_left`: the same for the primitive from the left
  endpoint of the interval, when the function is integrable on the whole interval.
* `TauCeti.HasWeakLineDerivOn.exists_ae_eq_const`: a function with weak derivative `0` on an
  interval is almost everywhere constant there.
* `TauCeti.HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral` and
  `TauCeti.hasWeakLineDerivOn_Ioo_iff_exists_ae_eq_add_intervalIntegral`: a function is weakly
  differentiable on an interval exactly when it is almost everywhere a constant plus the primitive
  of its weak derivative.
* `TauCeti.HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral_left`: the same with the primitive
  taken from the left endpoint, when the weak derivative is integrable.
* `TauCeti.HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral_top`: the same on the whole line.
* `TauCeti.HasWeakLineDerivOn.exists_continuousOn_ae_eq`: if the weak derivative is integrable,
  the function has a representative continuous on the closed interval.
* `TauCeti.HasWeakLineDerivOn.integral_eq_sub`: the fundamental theorem of calculus for such a
  continuous representative.
* `TauCeti.HasWeakLineDerivOn.absolutelyContinuousOnInterval` and
  `TauCeti.HasWeakLineDerivOn.ae_hasDerivAt`: absolute continuity and identification of the
  classical derivative of a continuous representative.
* `TauCeti.HasWeakLineDerivOn.integral_eq_zero_iff_exists_absolutelyContinuousOnInterval`:
  zero integral of the weak derivative characterizes matching endpoint traces.
* `TauCeti.HasWeakLineDerivOn.integral_deriv_smul_eq_sub`: integration by parts against a `C¹`
  function for such a continuous representative.
* `TauCeti.HasWeakLineDerivOn.norm_le_setAverage_add_integral`: for `a < b`, the pointwise bound
  `‖v t‖ ≤ ⨍ s in (a, b), ‖u s‖ + ∫ s in (a, b), ‖u' s‖` of a continuous representative `v`.
* `MeasureTheory.LocallyIntegrableOn.exists_ae_monotoneOn_of_integral_deriv_mul_nonpos`: a real
  function locally integrable on `Ioo a b` whose distributional derivative is nonnegative is
  monotone on `Ioo a b` outside a null set.
* `MeasureTheory.LocallyIntegrableOn.exists_ae_antitoneOn_sub_integral_of_integral_nonneg`:
  if `f' ≤ g` in the sense of distributions on `Ioo a b`, with `g` integrable, then
  `f - ∫ t in a..·, g t` is antitone on `Ioo a b` outside a null set.

## Functions with a nonnegative distributional derivative

The sign version of the du Bois-Reymond lemma says that a locally integrable real function `f`
with `∫ ψ' f ≤ 0` for every nonnegative test function `ψ` on `(a, b)` is monotone off a null set.
For continuous `f` this is `ContinuousOn.monotoneOn_of_integral_deriv_mul_nonpos`. In general, let
`G` be a primitive of `f`. For `δ > 0` the increment `G (· + δ) - G` is continuous, and its
distributional derivative is again nonnegative: pairing it with `ψ'` gives `∫ χ' f`, where
`χ x = ∫ s in x - δ..x, ψ s` is a nonnegative test function. So the increment is monotone, and
dividing by `δ` and letting `δ → 0` at the Lebesgue points of `f` gives the claim.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.2,
  Theorem 8.2 and Lemmas 8.1 and 8.2 (the scalar case).
-/

public section

open MeasureTheory Set Filter TopologicalSpace intervalIntegral
open scoped Interval Distributions Pointwise Topology ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b t₀ : ℝ} {u u' v : ℝ → F}

/-! ### The primitive is weakly differentiable -/

section Primitive

variable [CompleteSpace F]

/-- **The primitive is weakly differentiable.** If `u'` is locally integrable on `Ioo a b` and
`t₀ ∈ Ioo a b`, then `u'` is the weak derivative of its primitive `t ↦ ∫ s in t₀..t, u' s` on
`Ioo a b`. -/
theorem hasWeakLineDerivOn_intervalIntegral (hu' : LocallyIntegrableOn u' (Ioo a b))
    (ht₀ : t₀ ∈ Ioo a b) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ∫ s in t₀..t, u' s) u' 1 := by
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨‹_›,
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_locallyIntegrableOn hu'
      ht₀).locallyIntegrableOn
      measurableSet_Ioo, hu', fun φ ↦ ?_⟩
  -- Choose `[α, β] ⊆ Ioo a b` whose interior contains `t₀` and the support of `φ`.
  obtain ⟨α, β, hsub, hαβ⟩ := IsCompact.exists_Icc_between (φ.hasCompactSupport.insert t₀)
    (insert_nonempty _ _) (insert_subset ht₀ φ.tsupport_subset)
  have ht₀αβ : t₀ ∈ Ioo α β := hsub (mem_insert _ _)
  have hle : α ≤ β := (ht₀αβ.1.trans ht₀αβ.2).le
  have hint : IntervalIntegrable u' volume α β :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).2
      (hu'.integrableOn_compact_subset hαβ isCompact_Icc)
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  have hφd : Continuous (deriv (φ : ℝ → ℝ)) := hφ.continuous_deriv le_rfl
  have hφ0 : ∀ t ∉ Ioo α β, (φ : ℝ → ℝ) t = 0 := fun t ht ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ ht (hsub (mem_insert_of_mem _ h))
  have hφ'0 : ∀ t ∉ Ioo α β, deriv (φ : ℝ → ℝ) t = 0 := fun t ht ↦
    Function.notMem_support.1 fun h ↦ ht (hsub (mem_insert_of_mem _ (support_deriv_subset h)))
  -- Both pairings only see `[α, β]`.
  have hαβ0 : ∀ g : ℝ → F, (∀ t ∉ Ioo α β, g t = 0) → ∫ t in α..β, g t = ∫ t, g t :=
    fun g hg ↦ integral_eq_integral_of_support_subset fun t ht ↦
      Ioo_subset_Ioc_self (not_not.1 fun h ↦ ht (hg t h))
  have hL : ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • ∫ s in t₀..t, u' s =
      ∫ t in α..β, deriv (φ : ℝ → ℝ) t • ∫ s in t₀..t, u' s := by
    rw [hαβ0 _ (fun t ht ↦ by rw [hφ'0 t ht, zero_smul])]
    simp
  have hR : ∫ t, (φ : ℝ → ℝ) t • u' t = ∫ t in α..β, (φ : ℝ → ℝ) t • u' t :=
    (hαβ0 _ fun t ht ↦ by rw [hφ0 t ht, zero_smul]).symm
  -- Rebase the primitive at `α`; the constant `∫ s in α..t₀, u' s` pairs to zero with `φ'`.
  have hsplit : EqOn (fun t ↦ deriv (φ : ℝ → ℝ) t • ∫ s in t₀..t, u' s)
      (fun t ↦ deriv (φ : ℝ → ℝ) t • (∫ s in α..t, u' s) -
        deriv (φ : ℝ → ℝ) t • ∫ s in α..t₀, u' s) (uIcc α β) := fun t ht ↦ by
    dsimp only
    rw [← smul_sub, integral_interval_sub_left (hint.mono_set (uIcc_subset_uIcc_left ht))
      (hint.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc (Ioo_subset_Icc_self ht₀αβ))))]
  -- The constant part pairs to zero with `φ'`, since `φ` vanishes at `α` and `β`.
  have hconst : ∫ t in α..β, deriv (φ : ℝ → ℝ) t • ∫ s in α..t₀, u' s = 0 := by
    rw [intervalIntegral.integral_smul_const,
      integral_deriv_eq_sub (fun x _ ↦ (hφ.differentiable one_ne_zero) x)
        (hφd.intervalIntegrable _ _)]
    simp [hφ0 α (by simp), hφ0 β (by simp)]
  calc ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • ∫ s in t₀..t, u' s
      = ∫ t in α..β, deriv (φ : ℝ → ℝ) t • ∫ s in t₀..t, u' s := hL
    _ = (∫ t in α..β, deriv (φ : ℝ → ℝ) t • ∫ s in α..t, u' s) -
          ∫ t in α..β, deriv (φ : ℝ → ℝ) t • ∫ s in α..t₀, u' s := by
        rw [integral_congr hsplit, intervalIntegral.integral_sub ?_ ?_]
        · exact (hφd.continuousOn.smul (continuousOn_primitive_interval' hint
            left_mem_uIcc)).intervalIntegrable
        · exact (hφd.smul continuous_const).intervalIntegrable _ _
    _ = (φ : ℝ → ℝ) β • (∫ s in α..β, u' s) - ∫ t in α..β, (φ : ℝ → ℝ) t • u' t := by
        rw [hconst, sub_zero,
          TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hle hφ hint]
    _ = -∫ t, (φ : ℝ → ℝ) t • u' t := by simp [hφ0 β (by simp), hR]

/-- **The primitive from an endpoint is weakly differentiable.** If `u'` is integrable on
`Ioo a b`, then `u'` is the weak derivative of its primitive `t ↦ ∫ s in a..t, u' s` on
`Ioo a b`. -/
theorem hasWeakLineDerivOn_intervalIntegral_left (hu' : IntegrableOn u' (Ioo a b)) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ∫ s in a..t, u' s) u' 1 := by
  rcases le_or_gt b a with hba | hab
  · -- On an empty interval every pair of functions is a weak derivative pair.
    have h0 : volume.restrict (Ioo a b) = 0 := by simp [Ioo_eq_empty_of_le hba]
    exact (hasWeakLineDerivOn_zero.congr_ae (by simp [h0, EventuallyEq])).congr_ae_deriv
      (by simp [h0, EventuallyEq])
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hint : IntervalIntegrable u' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hu'
  have hsub : Ioo a b ⊆ uIcc a b := Ioo_subset_Icc_self.trans Icc_subset_uIcc
  -- Rebase the primitive at the midpoint, where `TauCeti.hasWeakLineDerivOn_intervalIntegral`
  -- applies.
  refine (((hasWeakLineDerivOn_const (∫ s in a..(a + b) / 2, u' s)).add
    (hasWeakLineDerivOn_intervalIntegral hu'.locallyIntegrableOn ht₀)).congr_ae
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht ↦ ?_))).congr_ae_deriv
    (EventuallyEq.of_eq (zero_add u'))
  exact integral_add_adjacent_intervals (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc
    (hsub ht₀))) (hint.mono_set (uIcc_subset_uIcc (hsub ht₀) (hsub ht)))

end Primitive

/-! ### The fundamental theorem of calculus -/

/-- **The du Bois-Reymond lemma for weak derivatives.** A function whose weak derivative on
`Ioo a b` is `0` is almost everywhere equal to a constant on `Ioo a b`. -/
theorem HasWeakLineDerivOn.exists_ae_eq_const
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u 0 1) :
    ∃ c, u =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ c := by
  have := h.completeSpace
  refine h.locallyIntegrableOn.exists_ae_eq_const_Ioo_of_integral_deriv_smul_eq_zero
    fun ψ hψ hψs ↦ ?_
  have hψc : HasCompactSupport ψ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) (hψs.trans Ioo_subset_Icc_self)
  simpa using h.integral_lineDeriv_smul_eq_neg_integral_smul ⟨ψ, hψ, hψc, hψs⟩

/-- **The fundamental theorem of calculus for weak derivatives.** If `u'` is the weak derivative
of `u` on `Ioo a b` and `t₀ ∈ Ioo a b`, then `u` is almost everywhere on `Ioo a b` equal to a
constant plus the primitive `t ↦ ∫ s in t₀..t, u' s`. -/
theorem HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ c, u =ᵐ[volume.restrict (Ioo a b)] fun t ↦ c + ∫ s in t₀..t, u' s := by
  have := h.completeSpace
  have hd := (h.sub (hasWeakLineDerivOn_intervalIntegral h.locallyIntegrableOn_deriv
    ht₀)).congr_ae_deriv (EventuallyEq.of_eq (sub_self u'))
  obtain ⟨c, hc⟩ := hd.exists_ae_eq_const
  refine ⟨c, ?_⟩
  filter_upwards [hc] with t ht
  rw [← ht, Pi.sub_apply, sub_add_cancel]

/-- **The fundamental theorem of calculus for weak derivatives, from the left endpoint.** If `u'`
is the weak derivative of `u` on `Ioo a b` and `u'` is integrable on `Ioo a b`, then `u` is almost
everywhere on `Ioo a b` equal to a constant plus the primitive `t ↦ ∫ s in a..t, u' s`. -/
theorem HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral_left
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1) (hu' : IntegrableOn u' (Ioo a b)) :
    ∃ c, u =ᵐ[volume.restrict (Ioo a b)] fun t ↦ c + ∫ s in a..t, u' s := by
  have := h.completeSpace
  obtain ⟨c, hc⟩ := ((h.sub (hasWeakLineDerivOn_intervalIntegral_left hu')).congr_ae_deriv
    (EventuallyEq.of_eq (sub_self u'))).exists_ae_eq_const
  refine ⟨c, ?_⟩
  filter_upwards [hc] with t ht
  rw [← ht, Pi.sub_apply, sub_add_cancel]

/-- **Weak derivatives on an interval.** For `u'` locally integrable on `Ioo a b` and
`t₀ ∈ Ioo a b`, `u'` is the weak derivative of `u` on `Ioo a b` exactly when `u` is almost
everywhere on `Ioo a b` a constant plus the primitive `t ↦ ∫ s in t₀..t, u' s`. -/
theorem hasWeakLineDerivOn_Ioo_iff_exists_ae_eq_add_intervalIntegral [CompleteSpace F]
    (hu' : LocallyIntegrableOn u' (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1 ↔
      ∃ c, u =ᵐ[volume.restrict (Ioo a b)] fun t ↦ c + ∫ s in t₀..t, u' s := by
  refine ⟨fun h ↦ h.exists_ae_eq_add_intervalIntegral ht₀, fun ⟨c, hc⟩ ↦ ?_⟩
  have h := (hasWeakLineDerivOn_const (μ := volume) (Ω := ⟨Ioo a b, isOpen_Ioo⟩) (v := 1) c).add
    (hasWeakLineDerivOn_intervalIntegral hu' ht₀)
  exact (h.congr_ae hc.symm).congr_ae_deriv (EventuallyEq.of_eq (zero_add u'))

/-- **The fundamental theorem of calculus for weak derivatives on the line.** If `u'` is the weak
derivative of `u` on all of `ℝ`, then `u` is almost everywhere equal to a constant plus the
primitive `t ↦ ∫ s in t₀..t, u' s`, for any base point `t₀`. -/
theorem HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral_top
    (h : HasWeakLineDerivOn volume ⊤ u u' 1) (t₀ : ℝ) :
    ∃ c, u =ᵐ[volume] fun t ↦ c + ∫ s in t₀..t, u' s := by
  let I (n : ℕ) : Set ℝ := Ioo (t₀ - (n + 1)) (t₀ + (n + 1))
  have hI (n : ℕ) := (h.mono (Ω' := ⟨I n, isOpen_Ioo⟩) le_top).exists_ae_eq_add_intervalIntegral
    (t₀ := t₀) ⟨by linarith [n.cast_nonneg (α := ℝ)], by linarith [n.cast_nonneg (α := ℝ)]⟩
  choose c hc using hI
  refine ⟨c 0, ?_⟩
  -- The constants agree, since every interval contains `I 0`, which has positive measure.
  have hc0 (n : ℕ) : c n = c 0 := by
    have hsub : I 0 ⊆ I n := Ioo_subset_Ioo (by push_cast; linarith [n.cast_nonneg (α := ℝ)])
      (by push_cast; linarith [n.cast_nonneg (α := ℝ)])
    have : (ae (volume.restrict (I 0))).NeBot := ae_restrict_neBot.2 (by simp [I])
    obtain ⟨t, htn, ht0⟩ := ((ae_restrict_of_ae_restrict_of_subset hsub (hc n)).and (hc 0)).exists
    exact add_right_cancel (htn.symm.trans ht0)
  have hU : (⋃ n, I n) = univ := eq_univ_of_forall fun t ↦ mem_iUnion.2 <| by
    obtain ⟨n, hn⟩ := exists_nat_gt |t - t₀|
    have := abs_lt.1 (hn.trans (lt_add_one _))
    exact ⟨n, by simp only [I, mem_Ioo]; constructor <;> linarith⟩
  have hae := (ae_restrict_iUnion_iff I fun t ↦ u t = c 0 + ∫ s in t₀..t, u' s).2 fun n ↦ by
    have h := hc n
    rw [hc0 n] at h
    exact h
  rwa [hU, Measure.restrict_univ] at hae

/-- **A continuous representative.** If `u'` is the weak derivative of `u` on `Ioo a b` and `u'`
is integrable on `Ioo a b`, then `u` agrees almost everywhere on `Ioo a b` with a function
continuous on `Icc a b`. -/
theorem HasWeakLineDerivOn.exists_continuousOn_ae_eq
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo a b)) :
    ∃ v, ContinuousOn v (Icc a b) ∧ u =ᵐ[volume.restrict (Ioo a b)] v := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨u, (subsingleton_Icc_of_ge hba).continuousOn _, EventuallyEq.rfl⟩
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc⟩ := h.exists_ae_eq_add_intervalIntegral ht₀
  exact ⟨_, continuousOn_const.add
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hu'
      (Ioo_subset_Icc_self ht₀)), hc⟩

/-- **The fundamental theorem of calculus for a continuous representative.** Let `u'` be the weak
derivative of `u` on `Ioo a b`, integrable on `Ioo a b`, and let `v` be continuous on `Icc a b`
and equal to `u` almost everywhere on `Ioo a b`. Then `∫ r in s..t, u' r = v t - v s` for all
`s, t ∈ Icc a b`. -/
theorem HasWeakLineDerivOn.integral_eq_sub
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo a b)) (hv : ContinuousOn v (Icc a b))
    (hae : u =ᵐ[volume.restrict (Ioo a b)] v) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∫ r in s..t, u' r = v t - v s := by
  rcases le_or_gt b a with hba | hab
  · rw [subsingleton_Icc_of_ge hba hs ht, integral_same, sub_self]
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc⟩ := h.exists_ae_eq_add_intervalIntegral ht₀
  have hint : IntervalIntegrable u' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hu'
  set w : ℝ → _ := fun t ↦ c + ∫ r in (a + b) / 2..t, u' r with hw_def
  have hw : ContinuousOn w (Icc a b) := continuousOn_const.add
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hu'
      (Ioo_subset_Icc_self ht₀))
  -- Two functions continuous on `Icc a b` and almost everywhere equal on `Ioo a b` agree on
  -- `Icc a b`.
  have heq : EqOn v w (Icc a b) :=
    (Measure.eqOn_open_of_ae_eq (hae.symm.trans hc) isOpen_Ioo (hv.mono Ioo_subset_Icc_self)
      (hw.mono Ioo_subset_Icc_self)).of_subset_closure hv hw Ioo_subset_Icc_self
      (closure_Ioo hab.ne).ge
  have hsub : ∀ r ∈ Icc a b, IntervalIntegrable u' volume ((a + b) / 2) r := fun r hr ↦
    hint.mono_set (uIcc_subset_uIcc (uIcc_of_le hab.le ▸ Ioo_subset_Icc_self ht₀)
      (uIcc_of_le hab.le ▸ hr))
  rw [heq ht, heq hs, hw_def, add_sub_add_left_eq_sub,
    integral_interval_sub_left (hsub t ht) (hsub s hs)]

/-- A continuous representative of a function with integrable weak derivative on an interval
is absolutely continuous on the closed interval. -/
theorem HasWeakLineDerivOn.absolutelyContinuousOnInterval
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo a b)) (hv : ContinuousOn v (Icc a b))
    (hae : u =ᵐ[volume.restrict (Ioo a b)] v) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval v a b := by
  have hint := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hu'
  have hconst := (LipschitzWith.const (v a)).lipschitzOnWith.absolutelyContinuousOnInterval
    (a := a) (b := b)
  refine (hconst.add (hint.absolutelyContinuousOnInterval_intervalIntegral'
    left_mem_uIcc)).congr fun t ht ↦ ?_
  simp only [Pi.add_apply]
  rw [h.integral_eq_sub hu' hv hae (left_mem_Icc.2 hab) (uIcc_of_le hab ▸ ht)]
  exact add_sub_cancel _ _

/-- The classical derivative of a continuous Sobolev representative agrees almost everywhere
in the interval with its weak derivative. -/
theorem HasWeakLineDerivOn.ae_hasDerivAt
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo a b)) (hv : ContinuousOn v (Icc a b))
    (hae : u =ᵐ[volume.restrict (Ioo a b)] v) (hab : a ≤ b) :
    ∀ᵐ t, t ∈ uIoc a b → HasDerivAt v (u' t) t := by
  have := h.completeSpace
  have hint := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hu'
  filter_upwards [hint.ae_hasDerivAt_integral, volume.ae_ne b] with t ht htb hmem
  have htIoc : t ∈ Ioc a b := uIoc_of_le hab ▸ hmem
  have htI : t ∈ Ioo a b := ⟨htIoc.1, lt_of_le_of_ne htIoc.2 htb⟩
  refine ((ht (uIoc_subset_uIcc hmem) a left_mem_uIcc).const_add (v a)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds htI.1 htI.2] with s hs
  rw [h.integral_eq_sub hu' hv hae (left_mem_Icc.2 hab) (Ioo_subset_Icc_self hs)]
  exact (add_sub_cancel _ _).symm

/-- The integral of an integrable weak derivative is zero exactly when the Sobolev function
has an absolutely continuous representative whose endpoint values agree. -/
theorem HasWeakLineDerivOn.integral_eq_zero_iff_exists_absolutelyContinuousOnInterval
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo a b)) (hab : a ≤ b) :
    (∫ t in a..b, u' t) = 0 ↔ ∃ v, AbsolutelyContinuousOnInterval v a b ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧ v a = v b := by
  constructor
  · intro hz
    obtain ⟨v, hv, hae⟩ := h.exists_continuousOn_ae_eq hu'
    refine ⟨v, h.absolutelyContinuousOnInterval hu' hv hae hab, hae, ?_⟩
    have hftc := h.integral_eq_sub hu' hv hae (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
    exact (sub_eq_zero.mp (hftc.symm.trans hz)).symm
  · rintro ⟨v, hv, hae, hvab⟩
    rw [h.integral_eq_sub hu' (uIcc_of_le hab ▸ hv.continuousOn) hae
      (left_mem_Icc.2 hab) (right_mem_Icc.2 hab), hvab, sub_self]

/-- **Integration by parts for a continuous representative.** Let `u'` be the weak derivative of
`u` on `Ioo a b`, `a ≤ b`, integrable on `Ioo a b`, and let `v` be continuous on `Icc a b` and
equal to `u` almost everywhere on `Ioo a b`. Then for every `C¹` function `φ : ℝ → ℝ`,
`∫ t in a..b, φ' t • v t = φ b • v b - φ a • v a - ∫ t in a..b, φ t • u' t`. -/
theorem HasWeakLineDerivOn.integral_deriv_smul_eq_sub
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo a b)) (hv : ContinuousOn v (Icc a b))
    (hae : u =ᵐ[volume.restrict (Ioo a b)] v) (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ t in a..b, deriv φ t • v t = φ b • v b - φ a • v a - ∫ t in a..b, φ t • u' t := by
  have := h.completeSpace
  have hφd : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hint : IntervalIntegrable u' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hu'
  -- On `[a, b]`, `v` is `v a` plus the primitive of `u'` from `a`.
  have hftc : ∀ t ∈ uIcc a b, v t = v a + ∫ r in a..t, u' r := fun t ht ↦ by
    rw [h.integral_eq_sub hu' hv hae (left_mem_Icc.2 hab) (uIcc_of_le hab ▸ ht),
      add_sub_cancel]
  have hP : ContinuousOn (fun t ↦ ∫ r in a..t, u' r) (uIcc a b) :=
    continuousOn_primitive_interval' hint left_mem_uIcc
  rw [integral_congr (g := fun t ↦ deriv φ t • v a + deriv φ t • ∫ r in a..t, u' r)
      fun t ht ↦ by simp only [hftc t ht, smul_add],
    integral_add (f := fun t ↦ deriv φ t • v a) (g := fun t ↦ deriv φ t • ∫ r in a..t, u' r)
      ((hφd.smul continuous_const).intervalIntegrable _ _)
      ((hφd.continuousOn.smul hP).intervalIntegrable),
    intervalIntegral.integral_smul_const,
    TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hab hφ
      hint, integral_deriv_eq_sub (fun x _ ↦ (hφ.differentiable one_ne_zero) x)
      (hφd.intervalIntegrable _ _), hftc b right_mem_uIcc]
  simp only [sub_smul, smul_add]
  abel

/-- **The `W^{1,1}` bound.** Let the weak derivative `u'` of `u` on `Ioo a b`, `a < b`, be
integrable on `Ioo a b`, and let `v` be continuous on `Icc a b` and equal to `u` almost everywhere
on `Ioo a b`. Then at every `t ∈ Icc a b`,
`‖v t‖ ≤ ⨍ s in Ioo a b, ‖u s‖ + ∫ s in Ioo a b, ‖u' s‖`. -/
theorem HasWeakLineDerivOn.norm_le_setAverage_add_integral
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1) (hab : a < b)
    (hu' : IntegrableOn u' (Ioo a b)) (hv : ContinuousOn v (Icc a b))
    (hae : u =ᵐ[volume.restrict (Ioo a b)] v) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖v t‖ ≤ (⨍ s in Ioo a b, ‖u s‖) + ∫ s in Ioo a b, ‖u' s‖ := by
  set M := ∫ s in Ioo a b, ‖u' s‖
  -- `‖v t‖ ≤ ‖v s‖ + M` for every `s ∈ Icc a b`, by the fundamental theorem of calculus.
  have hpt : ∀ s ∈ Icc a b, ‖v t‖ ≤ ‖v s‖ + M := fun s hs ↦ by
    have hM : ‖v t - v s‖ ≤ M := by
      have hMIcc : M = ∫ s in Icc a b, ‖u' s‖ := integral_Icc_eq_integral_Ioo.symm
      rw [← h.integral_eq_sub hu' hv hae hs ht, hMIcc]
      refine norm_integral_le_integral_norm_uIoc.trans (setIntegral_mono_set
        ((integrableOn_Icc_iff_integrableOn_Ioo (f := u') (a := a) (b := b)).2 hu').norm
        (Eventually.of_forall fun _ ↦ norm_nonneg _) (Eventually.of_forall ?_))
      exact uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)
    calc ‖v t‖ = ‖v s + (v t - v s)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v s‖ + ‖v t - v s‖ := norm_add_le _ _
      _ ≤ ‖v s‖ + M := by gcongr
  -- Averaging over `s ∈ Ioo a b` gives the bound.
  have hlen : volume.real (Ioo a b) = b - a := by simp [Measure.real, hab.le]
  have hpos : 0 < b - a := sub_pos.2 hab
  have hnorm : (fun s ↦ ‖u s‖) =ᵐ[volume.restrict (Ioo a b)] fun s ↦ ‖v s‖ :=
    hae.fun_comp norm
  have hvi : IntegrableOn (fun s ↦ ‖v s‖) (Ioo a b) :=
    (hv.norm.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have key : (b - a) * ‖v t‖ ≤ (∫ s in Ioo a b, ‖u s‖) + (b - a) * M := by
    calc (b - a) * ‖v t‖ = ∫ _ in Ioo a b, ‖v t‖ := by
          rw [setIntegral_const, hlen, smul_eq_mul]
      _ ≤ ∫ s in Ioo a b, (‖v s‖ + M) :=
          setIntegral_mono_on (integrableOn_const measure_Ioo_lt_top.ne)
            (hvi.add (integrableOn_const measure_Ioo_lt_top.ne)) measurableSet_Ioo
            fun s hs ↦ hpt s (Ioo_subset_Icc_self hs)
      _ = (∫ s in Ioo a b, ‖u s‖) + (b - a) * M := by
          rw [integral_add hvi (integrableOn_const measure_Ioo_lt_top.ne), setIntegral_const, hlen,
            smul_eq_mul,
            integral_congr_ae hnorm]
  rw [setAverage_eq, hlen, smul_eq_mul]
  have : (b - a) * ((b - a)⁻¹ * (∫ s in Ioo a b, ‖u s‖) + M) =
      (∫ s in Ioo a b, ‖u s‖) + (b - a) * M := by
    field_simp
  exact le_of_mul_le_mul_left (by rw [this]; exact key) hpos

/-! ### Functions with a nonnegative distributional derivative -/

section Monotone

/-- Let `ψ` be a nonnegative test function supported in `Ioo a (b - δ)`, `δ > 0`. Its moving
integral `χ x = ∫ s in x - δ..x, ψ s` over windows of length `δ` is a nonnegative test function
supported in `Ioo a b`, with derivative `ψ - ψ (· - δ)`. -/
private lemma exists_windowIntegral {ψ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo a (b - δ)) (hψc : HasCompactSupport ψ) (hψnn : ∀ x, 0 ≤ ψ x) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Ioo a b ∧ (∀ x, 0 ≤ χ x) ∧
      deriv χ = fun x ↦ ψ x - ψ (x - δ) := by
  set Ψ : ℝ → ℝ := fun t ↦ ∫ s in 0..t, ψ s with hΨ_def
  have hΨd : ∀ t, HasDerivAt Ψ (ψ t) t := fun t ↦
    integral_hasDerivAt_right (hψ.continuous.intervalIntegrable _ _)
      (hψ.continuous.stronglyMeasurableAtFilter _ _) hψ.continuous.continuousAt
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_infty_iff_deriv.mpr
    ⟨fun t ↦ (hΨd t).differentiableAt, (funext fun t ↦ (hΨd t).deriv) ▸ hψ⟩
  have hχ : ∀ x, Ψ x - Ψ (x - δ) = ∫ s in x - δ..x, ψ s := fun x ↦
    integral_interval_sub_left (hψ.continuous.intervalIntegrable _ _)
      (hψ.continuous.intervalIntegrable _ _)
  refine ⟨fun x ↦ Ψ x - Ψ (x - δ), hΨ.sub (hΨ.comp (contDiff_id.sub contDiff_const)), ?_,
    fun x ↦ by
      dsimp only
      rw [hχ x]
      exact integral_nonneg (by linarith) fun s _ ↦ hψnn s,
    funext fun x ↦ ((hΨd x).sub ((hΨd (x - δ)).comp_sub_const x δ)).deriv⟩
  -- `χ x` vanishes unless `x = s + e` with `s ∈ tsupport ψ` and `0 ≤ e ≤ δ`.
  have hK : IsCompact (tsupport ψ + Icc 0 δ) := hψc.isCompact.add isCompact_Icc
  refine (closure_minimal (fun x hx ↦ ?_) hK.isClosed).trans fun x hx ↦ ?_
  · by_contra hxK
    refine hx ?_
    dsimp only
    rw [hχ x, ← integral_zero (a := x - δ) (b := x) (μ := volume) (E := ℝ)]
    refine integral_congr fun s hs ↦ image_eq_zero_of_notMem_tsupport fun hsK ↦ hxK ?_
    rw [uIcc_of_le (by linarith)] at hs
    exact Set.mem_add.2 ⟨s, hsK, x - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by ring⟩
  · obtain ⟨s, hs, e, he, rfl⟩ := Set.mem_add.1 hx
    have := hψs hs
    exact ⟨by linarith [this.1, he.1], by linarith [this.2, he.2]⟩

/-- Let `f` be locally integrable on `Ioo a b` with nonnegative distributional derivative, and let
`G` be its primitive based at `t₀ ∈ Ioo a b`. For `δ > 0`, the increment `G (· + δ) - G` again has
nonnegative distributional derivative on `Ioo a (b - δ)`. -/
private lemma integral_deriv_mul_primitive_add_sub_nonpos {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      ∫ x, deriv ψ x * f x ≤ 0) {δ : ℝ} (hδ : 0 < δ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo a (b - δ)) (hψnn : ∀ x, 0 ≤ ψ x) :
    ∫ x, deriv ψ x * ((∫ s in t₀..x + δ, f s) - ∫ s in t₀..x, f s) ≤ 0 := by
  set G : ℝ → ℝ := fun t ↦ ∫ s in t₀..t, f s with hG_def
  have hψc : HasCompactSupport ψ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) (hψs.trans Ioo_subset_Icc_self)
  have hGc : ContinuousOn G (Ioo a b) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_locallyIntegrableOn hf ht₀
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hψ's : tsupport (deriv ψ) ⊆ Ioo a (b - δ) := tsupport_deriv_subset.trans hψs
  -- The pairings of `ψ'` with `G (· + δ)` and with `G` are integrals of continuous functions with
  -- compact support.
  have hI₁ : Integrable fun x ↦ deriv ψ x * G (x + δ) :=
    (ContinuousOn.continuous_of_tsupport_subset (hψ'c.continuousOn.mul (hGc.comp
      (by fun_prop : Continuous fun x : ℝ ↦ x + δ).continuousOn fun x hx ↦
        ⟨by linarith [hx.1], by linarith [hx.2]⟩)) isOpen_Ioo
      (tsupport_mul_subset_left.trans hψ's)).integrable_of_hasCompactSupport hψc.deriv.mul_right
  have hI₂ : Integrable fun x ↦ deriv ψ x * G x :=
    (ContinuousOn.continuous_of_tsupport_subset (hψ'c.continuousOn.mul hGc) isOpen_Ioo
      (tsupport_mul_subset_left.trans (hψ's.trans (Ioo_subset_Ioo_right (by linarith))))
      ).integrable_of_hasCompactSupport hψc.deriv.mul_right
  have hI₁' : Integrable fun x ↦ deriv ψ (x - δ) * G x := by
    simpa only [sub_add_cancel] using hI₁.comp_sub_right δ
  -- The test function `φ = χ'` is `ψ - ψ (· - δ)`, so `φ' = ψ' - ψ' (· - δ)`.
  obtain ⟨χ, hχ, hχs, hχnn, hχd⟩ := exists_windowIntegral hδ hψ hψs hψc hψnn
  have hφ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.1 hχ).2
  have hφs : tsupport (deriv χ) ⊆ Ioo a b := tsupport_deriv_subset.trans hχs
  have hφc : HasCompactSupport (deriv χ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hφs.trans Ioo_subset_Icc_self)
  have hdφ : ∀ x, deriv (deriv χ) x = deriv ψ x - deriv ψ (x - δ) := fun x ↦ by
    have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
    rw [hχd]
    exact ((hd x).hasDerivAt.sub ((hd (x - δ)).hasDerivAt.comp_sub_const x δ)).deriv
  -- Pair `φ` with the weak derivative `f` of `G`.
  have hw : ∫ x, deriv (deriv χ) x * G x = -∫ x, deriv χ x * f x := by
    simpa using (hasWeakLineDerivOn_intervalIntegral hf ht₀
      ).integral_lineDeriv_smul_eq_neg_integral_smul ⟨deriv χ, hφ, hφc, hφs⟩
  calc ∫ x, deriv ψ x * (G (x + δ) - G x)
      = (∫ x, deriv ψ x * G (x + δ)) - ∫ x, deriv ψ x * G x := by
        rw [← integral_sub hI₁ hI₂]
        simp_rw [mul_sub]
    _ = (∫ x, deriv ψ (x - δ) * G x) - ∫ x, deriv ψ x * G x := by
        rw [← integral_sub_right_eq_self (fun x ↦ deriv ψ x * G (x + δ)) δ]
        simp only [sub_add_cancel]
    _ = -∫ x, deriv (deriv χ) x * G x := by
        rw [← integral_sub hI₁' hI₂, ← MeasureTheory.integral_neg]
        congr 1 with x
        rw [hdφ]
        ring
    _ = ∫ x, deriv χ x * f x := by rw [hw, neg_neg]
    _ ≤ 0 := h χ hχ hχs hχnn

end Monotone

end TauCeti

namespace MeasureTheory.LocallyIntegrableOn

open TauCeti

variable {a b : ℝ}

/-- **The monotone du Bois-Reymond lemma, almost everywhere.** A real function locally integrable
on an open interval whose distributional derivative is nonnegative, in the sense that
`∫ x, deriv ψ x * f x ≤ 0` for every nonnegative test function `ψ` on the interval, is monotone on
the interval outside a null set. -/
theorem exists_ae_monotoneOn_of_integral_deriv_mul_nonpos
    {f : ℝ → ℝ} (hf : LocallyIntegrableOn f (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      ∫ x, deriv ψ x * f x ≤ 0) :
    ∃ s : Set ℝ, (∀ᵐ x, x ∈ s) ∧ MonotoneOn f (Ioo a b ∩ s) := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨univ, Eventually.of_forall fun _ ↦ trivial, by
    simpa [Ioo_eq_empty (not_lt.2 hba)] using (Set.subsingleton_empty (α := ℝ)).monotoneOn f⟩
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  set G : ℝ → ℝ := fun t ↦ ∫ s in (a + b) / 2..t, f s with hG_def
  have hGc : ContinuousOn G (Ioo a b) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_locallyIntegrableOn hf ht₀
  -- For `δ > 0` the increment `G (· + δ) - G` is continuous with nonnegative distributional
  -- derivative on `Ioo a (b - δ)`, hence monotone there.
  have hmono : ∀ δ > 0, MonotoneOn (fun x ↦ G (x + δ) - G x) (Ioo a (b - δ)) := fun δ hδ ↦
    ContinuousOn.monotoneOn_of_integral_deriv_mul_nonpos
      ((hGc.comp (by fun_prop : Continuous fun x : ℝ ↦ x + δ).continuousOn fun x hx ↦
        ⟨by linarith [hx.1], by linarith [hx.2]⟩).sub
        (hGc.mono (Ioo_subset_Ioo_right (by linarith))))
      fun ψ hψ hψs hψnn ↦
        TauCeti.integral_deriv_mul_primitive_add_sub_nonpos hf ht₀ h hδ hψ hψs hψnn
  -- At almost every point of the interval the difference quotients of `G` tend to `f`.
  set s : Set ℝ := {x | x ∈ Ioo a b → HasDerivAt G (f x) x}
  have hlim : ∀ z ∈ Ioo a b ∩ s,
      Tendsto (fun δ ↦ δ⁻¹ * (G (z + δ) - G z)) (𝓝[>] 0) (𝓝 (f z)) := fun z hz ↦ by
    simpa only [smul_eq_mul] using (hasDerivAt_iff_tendsto_slope_zero.1 (hz.2 hz.1)).mono_left
      (nhdsWithin_mono _ fun δ hδ ↦ ne_of_gt hδ)
  refine ⟨s, ?_, fun x hx y hy hxy ↦ le_of_tendsto_of_tendsto (hlim x hx) (hlim y hy) ?_⟩
  · filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxI using hx hxI _ ht₀
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hy.1.2)] with δ hδ
  exact mul_le_mul_of_nonneg_left (hmono δ hδ.1 ⟨hx.1.1, by linarith [hδ.2]⟩
    ⟨hy.1.1, by linarith [hδ.2]⟩ hxy) (inv_nonneg.2 hδ.1.le)

/-- **Functions whose distributional derivative is bounded above.** Let `f` be locally integrable
and `g` integrable on `Ioo a b`, and suppose that `f' ≤ g` in the sense of distributions:
`0 ≤ ∫ x, (f x * deriv ψ x + g x * ψ x)` for every nonnegative test function `ψ` on `Ioo a b`.
Then `f - ∫ t in a..·, g t` is antitone on `Ioo a b` outside a null set. -/
theorem exists_ae_antitoneOn_sub_integral_of_integral_nonneg
    {f g : ℝ → ℝ} (hf : LocallyIntegrableOn f (Ioo a b)) (hg : IntegrableOn g (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, (f x * deriv ψ x + g x * ψ x)) :
    ∃ s : Set ℝ, (∀ᵐ x, x ∈ s) ∧ AntitoneOn (fun x ↦ f x - ∫ t in a..x, g t) (Ioo a b ∩ s) := by
  set P : ℝ → ℝ := fun x ↦ ∫ t in a..x, g t with hP_def
  have hP : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ P g 1 :=
    hasWeakLineDerivOn_intervalIntegral_left hg
  -- The distributional derivative of `-(f - P)` is `g - f' ≥ 0`.
  have hneg : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      ∫ x, deriv ψ x * -(f x - P x) ≤ 0 := by
    intro ψ hψ hψs hψnn
    have hψc : HasCompactSupport ψ :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) (hψs.trans Ioo_subset_Icc_self)
    have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2
    have hIf : Integrable fun x ↦ deriv ψ x * f x :=
      TestFunction.integrable_smul (Ω := ⟨Ioo a b, isOpen_Ioo⟩)
        ⟨deriv ψ, hψ', hψc.deriv, tsupport_deriv_subset.trans hψs⟩ hf
    have hIP : Integrable fun x ↦ deriv ψ x * P x :=
      TestFunction.integrable_smul (Ω := ⟨Ioo a b, isOpen_Ioo⟩)
        ⟨deriv ψ, hψ', hψc.deriv, tsupport_deriv_subset.trans hψs⟩ hP.locallyIntegrableOn
    have hIg : Integrable fun x ↦ ψ x * g x :=
      TestFunction.integrable_smul (Ω := ⟨Ioo a b, isOpen_Ioo⟩) ⟨ψ, hψ, hψc, hψs⟩
        hg.locallyIntegrableOn
    have hw : ∫ x, deriv ψ x * P x = -∫ x, ψ x * g x := by
      simpa using hP.integral_lineDeriv_smul_eq_neg_integral_smul ⟨ψ, hψ, hψc, hψs⟩
    have e₁ : ∫ x, deriv ψ x * -(f x - P x) = (∫ x, deriv ψ x * P x) - ∫ x, deriv ψ x * f x := by
      rw [← integral_sub hIP hIf]
      congr 1 with x
      ring
    have e₂ : ∫ x, (f x * deriv ψ x + g x * ψ x) = (∫ x, deriv ψ x * f x) + ∫ x, ψ x * g x := by
      rw [← integral_add hIf hIg]
      congr 1 with x
      ring
    have h₀ := h ψ hψ hψs hψnn
    rw [e₁, hw]
    linarith
  obtain ⟨s, hs, hmono⟩ :=
    ((hf.sub hP.locallyIntegrableOn).neg).exists_ae_monotoneOn_of_integral_deriv_mul_nonpos hneg
  exact ⟨s, hs, fun x hx y hy hxy ↦ neg_le_neg_iff.1 (hmono hx hy hxy)⟩

end MeasureTheory.LocallyIntegrableOn
