/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.Analysis.Sobolev.WeakDeriv.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Integral.L2NormSq
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The absolutely continuous characterization of interval Sobolev classes

An absolutely continuous real function on `[a,b]` whose classical derivative belongs to `Lᵖ`
defines an element of `W1p volume (Ioo a b) p`, for every `1 ≤ p ≤ ∞`. Its value and gradient
agree almost everywhere with the function and its derivative. This is the converse to the
existing construction of absolutely continuous representatives of interval Sobolev classes.
For `p < ∞`, if the function also vanishes at both endpoints, the class lies in `W^{1,p}_0(a,b)`.

The range of `W1p.intervalRepresentativeL` is exactly the continuous functions whose extension
by endpoint projection is absolutely continuous and has derivative in `Lᵖ(a,b)`. In
particular the characterization retains derivative integrability at `p = 2`; absolute
continuity alone does not characterize `H¹`. A constant plus the primitive of an `Lᵖ` function is
such a representative, with weak gradient that function
(`TauCeti.W1p.exists_intervalRepresentativeL_eq_and_gradient_ae_eq`). The class of an absolutely
continuous function with `Lᵖ` derivative has that function as representative and value, and its
derivative as weak gradient
(`TauCeti.W1p.exists_intervalRepresentativeL_eq_and_value_gradient_ae_eq`); every `C¹` function
and every function Lipschitz on `[a, b]` is a special case
(`TauCeti.W1p.exists_intervalRepresentativeL_eq_of_contDiff`,
`TauCeti.W1p.exists_intervalRepresentativeL_eq_of_lipschitzOnWith`). Integrating by
parts against the flux `F(x) = c - ∫_a^x f` of an integrable `f` gives
`∫_a^b F v' = F(b) v(b) - F(a) v(a) + ∫_a^b f v` for every Sobolev class `v`
(`TauCeti.W1p.setIntegral_sub_intervalIntegral_mul_gradient_eq`), so the class with
representative `C + ∫_a^x F` satisfies this identity with `u'` in place of `F`
(`TauCeti.W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq`).

For `p = 2` the squared `L²` norms of the value and of the gradient are the interval integrals of
the squares of the representative and of its derivative
(`TauCeti.W1p.norm_value_sq_eq_integral_intervalRepresentativeL`,
`TauCeti.W1p.norm_gradient_sq_eq_integral_deriv_intervalRepresentativeL`).

A class whose value agrees almost everywhere with a function continuous on `[a,b]` has that
function as its continuous representative
(`TauCeti.W1p.intervalRepresentativeL_apply_of_value_ae_eq`), and its trace is the pair of endpoint
values (`TauCeti.W1p.intervalTraceL_eq_of_value_ae_eq`).

## References

* G. Leoni, *A First Course in Sobolev Spaces*, Theorem 7.13.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal

namespace AbsolutelyContinuousOnInterval

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℝ → ℝ}

/-- An absolutely continuous function with classical derivative in `Lᵖ(a,b)` represents a
Sobolev class, including at `p = ∞`; the recorded weak gradient is its classical derivative
almost everywhere. -/
theorem exists_w1p_value_gradient_ae_eq (hf : AbsolutelyContinuousOnInterval f a b)
    (hdf : MemLp (deriv f) p (volume.restrict (Ioo a b))) :
    ∃ u : TauCeti.W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      TauCeti.W1p.value u =ᵐ[volume.restrict (Ioo a b)] f ∧
      TauCeti.W1p.gradient u =ᵐ[volume.restrict (Ioo a b)] deriv f := by
  have hv : MemLp f p (volume.restrict (Ioo a b)) :=
    hf.continuousOn.memLp_restrict_of_subset_isCompact
      isCompact_uIcc measurableSet_Ioo (Ioo_subset_Icc_self.trans Icc_subset_uIcc) p
  have hw : TauCeti.HasWeakFDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ f
      (fun t ↦ innerSL ℝ (deriv f t)) := by
    apply TauCeti.hasWeakFDerivOn_iff.2
    intro v
    simpa [Pi.smul_def, smul_eq_mul, real_inner_comm, mul_comm] using
      hf.hasWeakLineDerivOn.smul_direction v
  refine ⟨TauCeti.W1p.mk (hv.toLp f) (hdf.toLp (deriv f))
    ((hw.congr_ae hv.coeFn_toLp.symm).congr_ae_deriv ?_), ?_, ?_⟩
  · filter_upwards [hdf.coeFn_toLp] with t ht
    rw [ht]
  · simpa only [TauCeti.W1p.value_mk] using hv.coeFn_toLp
  · simpa only [TauCeti.W1p.gradient_mk] using hdf.coeFn_toLp

/-- For `p < ∞`, an absolutely continuous function vanishing at both endpoints, with classical
derivative in `Lᵖ(a,b)`, represents a class in `W^{1,p}_0(a,b)`; the recorded weak gradient is
its classical derivative almost everywhere. -/
theorem exists_mem_w1p0Submodule_value_gradient_ae_eq (hf : AbsolutelyContinuousOnInterval f a b)
    (hdf : MemLp (deriv f) p (volume.restrict (Ioo a b))) (hp : p ≠ ∞)
    (ha : f a = 0) (hb : f b = 0) :
    ∃ u ∈ TauCeti.w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      TauCeti.W1p.value u =ᵐ[volume.restrict (Ioo a b)] f ∧
      TauCeti.W1p.gradient u =ᵐ[volume.restrict (Ioo a b)] deriv f := by
  obtain ⟨u, hv, hg⟩ := hf.exists_w1p_value_gradient_ae_eq hdf
  refine ⟨u, TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure hp
    (by simpa using Metric.isBounded_Ioo a b) ?_ ?_ hv, hv, hg⟩ <;>
    rcases le_or_gt b a with hab | hab
  -- On an empty interval the closure and the frontier are empty.
  · simp [Ioo_eq_empty_of_le hab]
  · simpa [closure_Ioo hab.ne, uIcc_of_le hab.le] using hf.continuousOn
  · simp [Ioo_eq_empty_of_le hab]
  · intro t ht
    simp only [Opens.coe_mk, frontier_Ioo hab, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    exacts [ha, hb]

end AbsolutelyContinuousOnInterval

namespace TauCeti.W1p

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If the value of a class agrees almost everywhere on `(a,b)` with a function `f` continuous on
`[a,b]`, then `f` is its continuous representative, including at both endpoints. -/
theorem intervalRepresentativeL_apply_of_value_ae_eq (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : value u =ᵐ[volume.restrict (Ioo a b)] f) (t : Icc a b) :
    intervalRepresentativeL hab u t = f t := by
  have heq : intervalRepresentativeL hab u = ⟨(Icc a b).domRestrict f, hf.domRestrict⟩ := by
    apply (intervalRepresentativeL_eq_iff hab u _).2
    filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ContinuousMap.coe_mk, projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem), domRestrict_apply]
    exact ht
  rw [heq, ContinuousMap.coe_mk, domRestrict_apply]

/-- If the value of a class agrees almost everywhere on `(a,b)` with a function `f` continuous on
`[a,b]`, then its trace is the pair of endpoint values `(f a, f b)`. -/
theorem intervalTraceL_eq_of_value_ae_eq (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : value u =ᵐ[volume.restrict (Ioo a b)] f) : intervalTraceL hab u = (f a, f b) := by
  rw [intervalTraceL_apply, intervalRepresentativeL_apply_of_value_ae_eq hab hf hu,
    intervalRepresentativeL_apply_of_value_ae_eq hab hf hu]

/-- An absolutely continuous real function with `Lᵖ` derivative is the continuous representative
of an interval Sobolev class, including at both endpoints, whose value and weak gradient agree
almost everywhere with the function and its classical derivative. -/
theorem exists_intervalRepresentativeL_eq_and_value_gradient_ae_eq (hab : a < b) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hdf : MemLp (deriv f) p (volume.restrict (Ioo a b))) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      (∀ t : Icc a b, intervalRepresentativeL hab u t = f t) ∧
      value u =ᵐ[volume.restrict (Ioo a b)] f ∧
      gradient u =ᵐ[volume.restrict (Ioo a b)] deriv f := by
  obtain ⟨u, hv, hg⟩ := hf.exists_w1p_value_gradient_ae_eq hdf
  exact ⟨u, intervalRepresentativeL_apply_of_value_ae_eq hab
    (uIcc_of_le hab.le ▸ hf.continuousOn) hv, hv, hg⟩

/-- Every absolutely continuous real function with `Lᵖ` derivative is the representative of
exactly one interval Sobolev class. The equality includes both endpoint values. -/
theorem existsUnique_intervalRepresentativeL_eq (hab : a < b) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hdf : MemLp (deriv f) p (volume.restrict (Ioo a b))) :
    ∃! u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      ∀ t : Icc a b, intervalRepresentativeL hab u t = f t := by
  obtain ⟨u, hu, -⟩ := exists_intervalRepresentativeL_eq_and_value_gradient_ae_eq hab hf hdf
  refine ⟨u, hu, fun v hv ↦ intervalRepresentativeL_injective hab ?_⟩
  ext t
  exact (hv t).trans (hu t).symm

/-- In the open interval the derivative of the representative, extended to `ℝ` by projection
onto `[a,b]`, agrees almost everywhere with the weak gradient. -/
theorem deriv_intervalRepresentativeL_ae_eq_gradient (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t))
      =ᵐ[volume.restrict (Ioo a b)] gradient u := by
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_hasDerivAt_intervalRepresentativeL hab u] with t ht hmem
  exact (ht (uIoc_of_le hab.le ▸ Ioo_subset_Ioc_self hmem)).deriv

/-- Characterization of the range of the continuous-representative map. The projection
extends a function on `[a,b]` by constants outside the interval and imposes no extra endpoint
differentiability requirement. -/
-- Rewrite before simplification of range membership and the open-set coercion in the carrier.
@[simp↓]
theorem mem_range_intervalRepresentativeL_iff (hab : a < b) (w : C(Icc a b, ℝ)) :
    w ∈ Set.range (intervalRepresentativeL (p := p) hab) ↔
      AbsolutelyContinuousOnInterval (fun t ↦ w (projIcc a b hab.le t)) a b ∧
      MemLp (deriv (fun t ↦ w (projIcc a b hab.le t))) p
        (volume.restrict (Ioo a b)) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨absolutelyContinuousOnInterval_intervalRepresentativeL hab u,
      (Lp.memLp (gradient u)).ae_eq (deriv_intervalRepresentativeL_ae_eq_gradient hab u).symm⟩
  · rintro ⟨hw, hdw⟩
    obtain ⟨u, hu, -⟩ := existsUnique_intervalRepresentativeL_eq hab hw hdw
    refine ⟨u, ?_⟩
    ext t
    simpa only [projIcc_of_mem hab.le t.property] using hu t

/-- A constant plus the primitive of a function `g ∈ Lᵖ(a, b)`, based at a point `t₀ ∈ [a, b]`, is
the continuous representative of a Sobolev class, whose weak gradient is `g`. -/
theorem exists_intervalRepresentativeL_eq_and_gradient_ae_eq (hab : a < b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (c : ℝ) {g : ℝ → ℝ} (hg : MemLp g p (volume.restrict (Ioo a b))) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      (∀ t : Icc a b, intervalRepresentativeL hab u t = c + ∫ s in t₀..t, g s) ∧
      gradient u =ᵐ[volume.restrict (Ioo a b)] g := by
  have hint : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hg.integrable Fact.out)
  set f : ℝ → ℝ := fun t ↦ c + ∫ s in t₀..t, g s
  have hAC : AbsolutelyContinuousOnInterval f a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval.add
      (hint.absolutelyContinuousOnInterval_intervalIntegral (Icc_subset_uIcc ht₀))
  -- By Lebesgue's differentiation theorem `f` has derivative `g` at almost every point.
  have hfd : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt f (g t) t := by
    filter_upwards [hint.ae_hasDerivAt_integral] with t ht htI
    exact (ht (Icc_subset_uIcc (Ioo_subset_Icc_self htI)) t₀ (Icc_subset_uIcc ht₀)).const_add c
  have hderiv : deriv f =ᵐ[volume.restrict (Ioo a b)] g :=
    (ae_restrict_iff' measurableSet_Ioo).2 (hfd.mono fun t ht htI ↦ (ht htI).deriv)
  obtain ⟨u, hu, -⟩ := existsUnique_intervalRepresentativeL_eq hab hAC (hg.ae_eq hderiv.symm)
  refine ⟨u, hu, (ae_restrict_iff' measurableSet_Ioo).2 ?_⟩
  -- Near a point of `(a, b)` the representative of `u` is `f`, so their derivatives agree.
  filter_upwards [ae_hasDerivAt_intervalRepresentativeL hab u, hfd] with t hut hft htI
  refine (hut (uIoc_of_le hab.le ▸ Ioo_subset_Ioc_self htI)).unique
    ((hft htI).congr_of_eventuallyEq ?_)
  filter_upwards [Ioo_mem_nhds htI.1 htI.2] with s hs
  rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hs)]
  exact hu ⟨s, Ioo_subset_Icc_self hs⟩

/-- **Integration by parts against a flux.** For `f ∈ L¹(a, b)`, a constant `c` and
`v ∈ W^{1,p}(a, b)`, the flux `F(x) = c - ∫_a^x f` satisfies
`∫_a^b F v' = F(b) v(b) - F(a) v(a) + ∫_a^b f v`. -/
theorem setIntegral_sub_intervalIntegral_mul_gradient_eq (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a b)) (c : ℝ) (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ∫ t in Ioo a b, (c - ∫ s in a..t, f s) * gradient v t =
      (c - ∫ t in Ioo a b, f t) * (intervalTraceL hab v).2 -
        c * (intervalTraceL hab v).1 + ∫ t in Ioo a b, f t * value v t := by
  -- The flux is the representative of a `W^{1,1}` class with weak gradient `-f`.
  obtain ⟨w, hw, hgw⟩ := exists_intervalRepresentativeL_eq_and_gradient_ae_eq (p := 1) hab
    (left_mem_Icc.2 hab.le) c (memLp_one_iff_integrable.2 hf).neg
  have hrep (t : Icc a b) : intervalRepresentativeL hab w t = c - ∫ s in a..(t : ℝ), f s := by
    rw [hw]
    simp only [Pi.neg_apply, intervalIntegral.integral_neg, sub_eq_add_neg]
  have h := integral_intervalRepresentativeL_mul_gradient_eq_sub hab w v
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
  have h1 : ∫ t in Ioo a b, intervalRepresentativeL hab w (projIcc a b hab.le t) *
      gradient v t = ∫ t in Ioo a b, (c - ∫ s in a..t, f s) * gradient v t := by
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self ht), hrep]
  have h2 : ∫ t in Ioo a b, gradient w t *
      intervalRepresentativeL hab v (projIcc a b hab.le t) =
        -∫ t in Ioo a b, f t * value v t := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hgw, value_ae_eq_intervalRepresentativeL hab v] with t hgt hvt
    rw [hgt, ← hvt, Pi.neg_apply, neg_mul]
  have hb : ∫ s in a..b, f s = ∫ t in Ioo a b, f t := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  rw [h1, h2, intervalTraceL_apply, intervalTraceL_apply, hrep, hrep] at h
  simp only [intervalIntegral.integral_same, sub_zero, hb] at h
  rw [h, intervalTraceL_apply]
  ring

/-- **The class with a prescribed flux.** For `f ∈ L¹(a, b)` and constants `C` and `c`, the
function `C + ∫_a^x (c - ∫_a^s f) ds` is the representative of a class `u ∈ W^{1,p}(a, b)` with
flux `u' = c - ∫_a^x f`, so that `∫_a^b u' v' = (c - ∫_a^b f) v(b) - c v(a) + ∫_a^b f v` for every
`v ∈ W^{1,q}(a, b)`. -/
theorem exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hab : a < b) {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b))
    (C c : ℝ) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      (∀ t : Icc a b, intervalRepresentativeL hab u t =
        C + ∫ s in a..(t : ℝ), (c - ∫ r in a..s, f r)) ∧
      ∀ v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ q,
        ∫ t in Ioo a b, gradient u t * gradient v t =
          (c - ∫ t in Ioo a b, f t) * (intervalTraceL hab v).2 -
            c * (intervalTraceL hab v).1 + ∫ t in Ioo a b, f t * value v t := by
  have hg : MemLp (fun t => c - ∫ s in a..t, f s) p (volume.restrict (Ioo a b)) :=
    (memLp_const c).sub (TauCeti.intervalIntegral.memLp_primitive hf (left_mem_Icc.2 hab.le))
  obtain ⟨u, hu, hgu⟩ :=
    exists_intervalRepresentativeL_eq_and_gradient_ae_eq hab (left_mem_Icc.2 hab.le) C hg
  refine ⟨u, hu, fun v => ?_⟩
  rw [← setIntegral_sub_intervalIntegral_mul_gradient_eq hab hf c v]
  refine integral_congr_ae ?_
  filter_upwards [hgu] with t ht
  rw [ht]

/-- A `C¹` function on `ℝ` is the continuous representative of a Sobolev class on `(a, b)`, whose
value and weak gradient agree almost everywhere with the function and its derivative. -/
theorem exists_intervalRepresentativeL_eq_of_contDiff (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      (∀ t : Icc a b, intervalRepresentativeL hab u t = f t) ∧
      value u =ᵐ[volume.restrict (Ioo a b)] f ∧
      gradient u =ᵐ[volume.restrict (Ioo a b)] deriv f :=
  exists_intervalRepresentativeL_eq_and_value_gradient_ae_eq hab
    hf.contDiffOn.absolutelyContinuousOnInterval
    ((hf.continuous_deriv le_rfl).continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc
      measurableSet_Ioo Ioo_subset_Icc_self p)

/-- A function Lipschitz on `[a, b]` is the continuous representative of a Sobolev class on
`(a, b)`, whose value and weak gradient agree almost everywhere with the function and its
derivative. -/
theorem exists_intervalRepresentativeL_eq_of_lipschitzOnWith (hab : a < b) {f : ℝ → ℝ}
    {K : NNReal} (hf : LipschitzOnWith K f (Icc a b)) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      (∀ t : Icc a b, intervalRepresentativeL hab u t = f t) ∧
      value u =ᵐ[volume.restrict (Ioo a b)] f ∧
      gradient u =ᵐ[volume.restrict (Ioo a b)] deriv f :=
  exists_intervalRepresentativeL_eq_and_value_gradient_ae_eq hab
    (uIcc_of_le hab.le ▸ hf).absolutelyContinuousOnInterval
    (MemLp.of_bound (measurable_deriv f).aestronglyMeasurable K
      (ae_restrict_of_forall_mem measurableSet_Ioo fun _ ht ↦
        norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hf))

/-! ### Squared `L²` norms as interval integrals -/

/-- If the value of `u ∈ H¹(a, b)` agrees almost everywhere on `(a, b)` with `g`, then its squared
`L²` norm is the integral of `g²` over `(a, b)`. -/
theorem norm_value_sq_eq_intervalIntegral_of_ae_eq (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} {g : ℝ → ℝ}
    (hg : value u =ᵐ[volume.restrict (Ioo a b)] g) :
    ‖value u‖ ^ 2 = ∫ t in a..b, g t ^ 2 :=
  L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hab.le hg

/-- If the gradient of `u ∈ H¹(a, b)` agrees almost everywhere on `(a, b)` with `g`, then its
squared `L²` norm is the integral of `g²` over `(a, b)`. -/
theorem norm_gradient_sq_eq_intervalIntegral_of_ae_eq (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} {g : ℝ → ℝ}
    (hg : gradient u =ᵐ[volume.restrict (Ioo a b)] g) :
    ‖gradient u‖ ^ 2 = ∫ t in a..b, g t ^ 2 :=
  L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hab.le hg

/-- The squared `L²` norm of the value of `u ∈ H¹(a, b)` is the integral of the square of its
continuous representative. -/
theorem norm_value_sq_eq_integral_intervalRepresentativeL (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    ‖value u‖ ^ 2 = ∫ t in a..b, intervalRepresentativeL hab u (projIcc a b hab.le t) ^ 2 :=
  norm_value_sq_eq_intervalIntegral_of_ae_eq hab (value_ae_eq_intervalRepresentativeL hab u)

/-- The squared `L²` norm of the gradient of `u ∈ H¹(a, b)` is the integral of the square of the
derivative of its continuous representative. -/
theorem norm_gradient_sq_eq_integral_deriv_intervalRepresentativeL (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    ‖gradient u‖ ^ 2 =
      ∫ t in a..b, deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) t ^ 2 :=
  norm_gradient_sq_eq_intervalIntegral_of_ae_eq hab
    (deriv_intervalRepresentativeL_ae_eq_gradient hab u).symm

/-- The square of the derivative of the continuous representative of `u ∈ H¹(a, b)` is
integrable over `(a, b)`. -/
theorem intervalIntegrable_deriv_intervalRepresentativeL_sq (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    IntervalIntegrable
      (fun t ↦ deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) t ^ 2)
      volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 ?_
  refine (Lp.memLp (gradient u)).norm.integrable_sq.congr ?_
  filter_upwards [deriv_intervalRepresentativeL_ae_eq_gradient hab u] with t ht
  rw [ht, Real.norm_eq_abs, sq_abs]

end TauCeti.W1p
