/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
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
* `TauCeti.HasWeakLineDerivOn.exists_ae_eq_const`: a function with weak derivative `0` on an
  interval is almost everywhere constant there.
* `TauCeti.HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral` and
  `TauCeti.hasWeakLineDerivOn_Ioo_iff_exists_ae_eq_add_intervalIntegral`: a function is weakly
  differentiable on an interval exactly when it is almost everywhere a constant plus the primitive
  of its weak derivative.
* `TauCeti.HasWeakLineDerivOn.exists_continuousOn_ae_eq`: if the weak derivative is integrable,
  the function has a representative continuous on the closed interval.
* `TauCeti.HasWeakLineDerivOn.integral_eq_sub`: the fundamental theorem of calculus for such a
  continuous representative.
* `TauCeti.HasWeakLineDerivOn.norm_le_setAverage_add_integral`: for `a < b`, the pointwise bound
  `‖v t‖ ≤ ⨍ s in (a, b), ‖u s‖ + ∫ s in (a, b), ‖u' s‖` of a continuous representative `v`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.2,
  Theorem 8.2 and Lemmas 8.1 and 8.2 (the scalar case).
-/

public section

open MeasureTheory Set Filter TopologicalSpace intervalIntegral
open scoped Interval Distributions

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

end Primitive

/-! ### The fundamental theorem of calculus -/

/-- The primitive of a function integrable on `Ioo a b`, based at a point of `Icc a b`, is
continuous on `Icc a b`. -/
private theorem continuousOn_primitive_Icc_of_integrableOn_Ioo (hu' : IntegrableOn u' (Ioo a b))
    (ht₀ : t₀ ∈ Icc a b) : ContinuousOn (fun t ↦ ∫ s in t₀..t, u' s) (Icc a b) := by
  have hab : a ≤ b := ht₀.1.trans ht₀.2
  simpa [uIcc_of_le hab] using continuousOn_primitive_interval'
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hu') (uIcc_of_le hab ▸ ht₀)

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
    (continuousOn_primitive_Icc_of_integrableOn_Ioo hu' (Ioo_subset_Icc_self ht₀)), hc⟩

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
    (continuousOn_primitive_Icc_of_integrableOn_Ioo hu' (Ioo_subset_Icc_self ht₀))
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

/-- **The `W^{1,1}` bound.** Let `u` and its weak derivative `u'` on `Ioo a b`, `a < b`, be
integrable on `Ioo a b`, and let `v` be continuous on `Icc a b` and equal to `u` almost everywhere
on `Ioo a b`. Then at every `t ∈ Icc a b`,
`‖v t‖ ≤ ⨍ s in Ioo a b, ‖u s‖ + ∫ s in Ioo a b, ‖u' s‖`. -/
theorem HasWeakLineDerivOn.norm_le_setAverage_add_integral
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1) (hab : a < b)
    (hu : IntegrableOn u (Ioo a b)) (hu' : IntegrableOn u' (Ioo a b))
    (hv : ContinuousOn v (Icc a b)) (hae : u =ᵐ[volume.restrict (Ioo a b)] v) {t : ℝ}
    (ht : t ∈ Icc a b) :
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
  have hvi : IntegrableOn (fun s ↦ ‖v s‖) (Ioo a b) := hu.norm.congr hnorm
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

end TauCeti
