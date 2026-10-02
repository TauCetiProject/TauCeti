/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Topology.FilledHull
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Contour.Curve.Approximation
import TauCeti.Analysis.Contour.Curve.Concat
import TauCeti.Analysis.Contour.Curve.Integrability
import TauCeti.Analysis.Contour.HomologyCauchy
import TauCeti.Analysis.Contour.Winding.UnboundedComponent

/-!
# Primitives from vanishing contour integrals, and logarithms on sets without holes

A continuous function `f` on an open set `U ⊆ ℂ` whose contour integral
`∫ t in a..b, deriv γ t • f (γ t)` vanishes along every closed piecewise-`C¹` curve `γ` in `U` has
a primitive on `U` (`Complex.IsExactOn f U`): fix a base point in each path component of `U`, and
integrate `f` from it along any piecewise-`C¹` curve in `U`. The vanishing of closed integrals
makes the value independent of the curve, and near each point the primitive differs from the
integral along a segment by a constant, whose derivative Mathlib computes
(`HasFDerivAt.curveIntegral_segment_source'`).

By the homology form of Cauchy's theorem, the hypothesis holds for every holomorphic `f` as soon as
every closed curve in `U` is null-homologous in `U`, and that is the case when `U` has no holes:
when every connected component of `ℂ \ U` is unbounded (`filledHull U ⊆ U`), the condition that
the complement of `U` in the Riemann sphere is connected. On such a set every holomorphic function
has a primitive, so every nowhere-zero holomorphic function `g` has a holomorphic logarithm — a
primitive of `g' / g`, corrected by a locally constant function — and holomorphic `n`-th roots.
These are the implications (d) ⇒ (c) ⇒ (f) ⇒ (g) ⇒ (h) ⇒ (i) of Rudin's characterisation of
simply connected plane domains, the step (c) ⇒ (f) being the homology form of Cauchy's theorem: a
set without holes has holomorphic square roots.

## Main results

* `TauCeti.Contour.intervalIntegral_deriv_smul_eq_of_forall_closed_integral_eq_zero` — if the
  contour integrals of `f` along closed curves in `U` vanish, its contour integral along a curve in
  `U` depends only on the endpoints.
* `TauCeti.Contour.intervalIntegral_deriv_smul_segment_eq_curveIntegral` — the contour integral
  along an affinely parametrized segment is Mathlib's curve integral along `Path.segment`.
* `TauCeti.Contour.isExactOn_of_forall_closed_integral_eq_zero` — the converse of Cauchy's theorem:
  such an `f` has a primitive on `U`.
* `TauCeti.Contour.isExactOn_of_forall_isNullHomologous` — a holomorphic function has a primitive
  on an open set in which every closed curve is null-homologous.
* `TauCeti.Contour.isExactOn_of_filledHull_subset` — a holomorphic function has a primitive on an
  open set without holes.
* `TauCeti.Contour.exists_differentiableOn_eqOn_exp_comp_of_isExactOn` — a nowhere-zero
  holomorphic function whose logarithmic derivative has a primitive has a holomorphic logarithm.
* `TauCeti.Contour.exists_differentiableOn_eqOn_exp_comp_of_filledHull_subset`,
  `TauCeti.Contour.exists_differentiableOn_pow_eq_of_filledHull_subset` — holomorphic logarithms and
  `n`-th roots on an open set without holes.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.11 ((d) ⇒ (c) ⇒ (f) ⇒ (g) ⇒ (h) ⇒
  (i)).
* L. Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, Section 1.3, Theorem 1.
-/

public section

namespace TauCeti.Contour

open Set Filter Topology MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set ℂ} {f : ℂ → E}

/-- **Path independence.** If the contour integral of a continuous `f` vanishes along every closed
piecewise-`C¹` curve in `U`, then its contour integrals along two piecewise-`C¹` curves in `U` with
the same endpoints agree. -/
theorem intervalIntegral_deriv_smul_eq_of_forall_closed_integral_eq_zero (hf : ContinuousOn f U)
    (h : ∀ (γ : ℝ → ℂ) (a b : ℝ), IsPiecewiseC1On γ a b → MapsTo γ (uIcc a b) U → γ a = γ b →
      ∫ t in a..b, deriv γ t • f (γ t) = 0)
    {γ δ : ℝ → ℂ} {a b c d : ℝ} (hγ : IsPiecewiseC1On γ a b) (hδ : IsPiecewiseC1On δ c d)
    (hab : a ≤ b) (hcd : c ≤ d) (hγU : MapsTo γ (uIcc a b) U) (hδU : MapsTo δ (uIcc c d) U)
    (hstart : γ a = δ c) (hend : γ b = δ d) :
    ∫ t in a..b, deriv γ t • f (γ t) = ∫ t in c..d, deriv δ t • f (δ t) := by
  -- The closed curve: `γ` on `[a, b]`, then `δ` backwards on `[b, b + d - c]`.
  have hbe : b ≤ b + d - c := by linarith
  have hρ : IsPiecewiseC1On (fun t => δ (b + d - t)) b (b + d - c) := by
    simpa using (hδ.comp_const_sub (b + d)).symm
  have hρU : MapsTo (fun t => δ (b + d - t)) (uIcc b (b + d - c)) U := fun t ht => hδU <| by
    rw [uIcc_of_le hbe] at ht
    rw [uIcc_of_le hcd]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  set σ : ℝ → ℂ := fun t => if t ≤ b then γ t else δ (b + d - t)
  have hσγ : EqOn σ γ (Icc a b) := fun t ht => ite_eq_left ht.2
  have hσρ : EqOn σ (fun t => δ (b + d - t)) (Icc b (b + d - c)) := fun t ht => by
    rcases ht.1.eq_or_lt with rfl | hlt
    · simp [σ, hend]
    · exact ite_eq_right (not_le.2 hlt)
  have hσpc : IsPiecewiseC1On σ a (b + d - c) := hγ.if_le hρ hab hbe (by simpa using hend)
  have hσU : MapsTo σ (uIcc a (b + d - c)) U := by
    intro t ht
    rw [uIcc_of_le (hab.trans hbe)] at ht
    rcases le_total t b with htb | hbt
    · rw [hσγ ⟨ht.1, htb⟩]
      exact hγU (by rw [uIcc_of_le hab]; exact ⟨ht.1, htb⟩)
    · rw [hσρ ⟨hbt, ht.2⟩]
      exact hρU (by rw [uIcc_of_le hbe]; exact ⟨hbt, ht.2⟩)
  have hσclosed : σ a = σ (b + d - c) := by
    rw [hσγ ⟨le_rfl, hab⟩, hσρ ⟨hbe, le_rfl⟩]
    simpa using hstart
  have hzero := h σ a (b + d - c) hσpc hσU hσclosed
  rw [intervalIntegral_deriv_smul_eq_add_of_eqOn (b := b) (δ := fun t => δ (b + d - t))
      (fun t ht => hσγ (Ioo_subset_Icc_self (by rwa [uIoo_of_le hab] at ht)))
      (fun t ht => hσρ (Ioo_subset_Icc_self (by rwa [uIoo_of_le hbe] at ht)))
      (hγ.intervalIntegrable_deriv_smul_comp_of_mapsTo hf hγU)
      (hρ.intervalIntegrable_deriv_smul_comp_of_mapsTo hf hρU),
    intervalIntegral_deriv_smul_comp_const_sub, add_sub_cancel_left, sub_sub_cancel,
    intervalIntegral.integral_symm c d, ← sub_eq_add_neg, sub_eq_zero] at hzero
  exact hzero

/-- **Segments as contour integrals.** The contour integral along the segment from `z` to `w`,
parametrized affinely on `[s, s + 1]`, is Mathlib's curve integral of the `1`-form `v ↦ v • f x`
along `Path.segment z w`. -/
theorem intervalIntegral_deriv_smul_segment_eq_curveIntegral (f : ℂ → E) (z w : ℂ) (s : ℝ) :
    ∫ t in s..s + 1, deriv (fun t : ℝ => (t - s) • (w - z) + z) t •
        f ((t - s) • (w - z) + z) =
      ∫ᶜ x in Path.segment z w, ContinuousLinearMap.toSpanSingleton ℂ (f x) := by
  have hderiv : ∀ t : ℝ, deriv (fun t : ℝ => (t - s) • (w - z) + z) t = w - z := fun t => by
    simpa using ((((hasDerivAt_id t).sub_const s).smul_const (w - z)).add_const z).deriv
  simp only [hderiv, curveIntegral_segment, ContinuousLinearMap.toSpanSingleton_apply,
    AffineMap.lineMap_apply_module']
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => (w - z) • f (t • (w - z) + z))]
  norm_num

/-- Following a curve `γ` on `[0, 1]` in `U` that ends at `z` by the segment from `z` to `w`, when
that segment lies in `U`, gives a curve on `[0, 2]` in `U` from `γ 0` to `w`, along which the
contour integral of `f` is that along `γ` plus the curve integral along the segment. -/
private theorem exists_intervalIntegral_deriv_smul_eq_add_curveIntegral_segment
    (hf : ContinuousOn f U) {γ : ℝ → ℂ} (hγ : IsPiecewiseC1On γ 0 1)
    (hγU : MapsTo γ (uIcc 0 1) U) {z w : ℂ} (hz : γ 1 = z) (hseg : segment ℝ z w ⊆ U) :
    ∃ η : ℝ → ℂ, IsPiecewiseC1On η 0 2 ∧ MapsTo η (uIcc 0 2) U ∧ η 0 = γ 0 ∧ η 2 = w ∧
      ∫ t in (0 : ℝ)..2, deriv η t • f (η t) = (∫ t in (0 : ℝ)..1, deriv γ t • f (γ t)) +
        ∫ᶜ x in Path.segment z w, ContinuousLinearMap.toSpanSingleton ℂ (f x) := by
  set σ : ℝ → ℂ := fun t => (t - 1) • (w - z) + z with hσ
  have hσU : MapsTo σ (uIcc 1 2) U := fun t ht => hseg <| by
    rw [uIcc_of_le one_le_two] at ht
    rw [segment_eq_image_lineMap]
    exact ⟨t - 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, AffineMap.lineMap_apply_module' _ _ _⟩
  set η : ℝ → ℂ := fun t => if t ≤ 1 then γ t else σ t
  have hηγ : EqOn η γ (Icc 0 1) := fun t ht => ite_eq_left ht.2
  have hησ : EqOn η σ (Icc 1 2) := fun t ht => by
    rcases ht.1.eq_or_lt with rfl | hlt
    · simp [η, σ, hz]
    · exact ite_eq_right (not_le.2 hlt)
  have hσpc : IsPiecewiseC1On σ 1 2 := .of_contDiffOn (by fun_prop)
  have hηpc : IsPiecewiseC1On η 0 2 := hγ.if_le hσpc zero_le_one one_le_two (by simp [σ, hz])
  have hηU : MapsTo η (uIcc 0 2) U := by
    intro t ht
    rw [uIcc_of_le zero_le_two] at ht
    rcases le_total t 1 with ht1 | ht1
    · rw [hηγ ⟨ht.1, ht1⟩]
      exact hγU (by rw [uIcc_of_le zero_le_one]; exact ⟨ht.1, ht1⟩)
    · rw [hησ ⟨ht1, ht.2⟩]
      exact hσU (by rw [uIcc_of_le one_le_two]; exact ⟨ht1, ht.2⟩)
  refine ⟨η, hηpc, hηU, hηγ ⟨le_rfl, zero_le_one⟩, by rw [hησ ⟨one_le_two, le_rfl⟩]; norm_num [σ],
    ?_⟩
  have hseg' := intervalIntegral_deriv_smul_segment_eq_curveIntegral f z w 1
  rw [one_add_one_eq_two] at hseg'
  rw [intervalIntegral_deriv_smul_eq_add_of_eqOn (b := 1) (δ := σ)
      (fun t ht => hηγ (Ioo_subset_Icc_self (by rwa [uIoo_of_le zero_le_one] at ht)))
      (fun t ht => hησ (Ioo_subset_Icc_self (by rwa [uIoo_of_le one_le_two] at ht)))
      (hγ.intervalIntegrable_deriv_smul_comp_of_mapsTo hf hγU)
      (hσpc.intervalIntegrable_deriv_smul_comp_of_mapsTo hf hσU),
    hσ, hseg']

/-- **The converse of Cauchy's theorem.** A continuous function on an open set `U` whose contour
integral vanishes along every closed piecewise-`C¹` curve in `U` has a primitive on `U`. -/
theorem isExactOn_of_forall_closed_integral_eq_zero [CompleteSpace E] (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (h : ∀ (γ : ℝ → ℂ) (a b : ℝ), IsPiecewiseC1On γ a b → MapsTo γ (uIcc a b) U → γ a = γ b →
      ∫ t in a..b, deriv γ t • f (γ t) = 0) :
    Complex.IsExactOn f U := by
  -- A base point for each path component of `U`, and a curve in `U` from it to each `z ∈ U`.
  let base : ℂ → ℂ := fun z => Classical.epsilon fun x => JoinedIn U x z
  have hbase : ∀ z ∈ U, JoinedIn U (base z) z := fun z hz =>
    Classical.epsilon_spec (p := fun x => JoinedIn U x z) ⟨z, JoinedIn.refl hz⟩
  have hbase_eq : ∀ {z w : ℂ}, JoinedIn U z w → base w = base z := fun hzw => by
    simp only [base]
    congr 1
    ext x
    exact ⟨fun hx => hx.trans hzw.symm, fun hx => hx.trans hzw⟩
  let IsCurveTo : ℂ → (ℝ → ℂ) → Prop := fun z γ =>
    IsPiecewiseC1On γ 0 1 ∧ MapsTo γ (uIcc 0 1) U ∧ γ 0 = base z ∧ γ 1 = z
  let curve : ℂ → ℝ → ℂ := fun z => Classical.epsilon (IsCurveTo z)
  have hcurve : ∀ z ∈ U, IsCurveTo z (curve z) := fun z hz => by
    obtain ⟨γ, hγ, hγ0, hγ1, hγU⟩ := (hbase z hz).exists_contDiff_mapsTo hU
    refine Classical.epsilon_spec (p := IsCurveTo z) ⟨γ, ?_, ?_, hγ0, hγ1⟩
    · exact .of_contDiffOn (hγ.of_le le_top).contDiffOn
    · rwa [uIcc_of_le zero_le_one]
  refine ⟨fun z => ∫ t in (0 : ℝ)..1, deriv (curve z) t • f (curve z t), fun z hz => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  -- Near `z`, the primitive is its value at `z` plus the integral along the segment from `z`.
  have hloc : ∀ w ∈ Metric.ball z r,
      ∫ t in (0 : ℝ)..1, deriv (curve w) t • f (curve w t) =
        (∫ t in (0 : ℝ)..1, deriv (curve z) t • f (curve z t)) +
          ∫ᶜ x in Path.segment z w, ContinuousLinearMap.toSpanSingleton ℂ (f x) := by
    intro w hw
    obtain ⟨hzpc, hzU, hz0, hz1⟩ := hcurve z hz
    obtain ⟨hwpc, hwU, hw0, hw1⟩ := hcurve w (hball hw)
    have hzw : JoinedIn U z w :=
      (((convex_ball z r).isPathConnected ⟨z, Metric.mem_ball_self hr⟩).joinedIn z
        (Metric.mem_ball_self hr) w hw).mono hball
    obtain ⟨η, hηpc, hηU, hη0, hη2, hηint⟩ :=
      exists_intervalIntegral_deriv_smul_eq_add_curveIntegral_segment hf hzpc hzU hz1
        (((convex_ball z r).segment_subset (Metric.mem_ball_self hr) hw).trans hball)
    rw [← hηint]
    exact intervalIntegral_deriv_smul_eq_of_forall_closed_integral_eq_zero hf h hwpc hηpc
      zero_le_one zero_le_two hwU hηU (by rw [hw0, hη0, hz0, hbase_eq hzw]) (by rw [hw1, hη2])
  -- The integral along the segment from `z` has derivative `f z` at `z`.
  have hbz : Metric.ball z r ∈ 𝓝 z := Metric.ball_mem_nhds z hr
  have hω : ∀ᶠ x in 𝓝 z, ContinuousAt (fun x => ContinuousLinearMap.toSpanSingleton ℂ (f x)) x :=
    eventually_of_mem hbz fun x hx =>
      (ContinuousLinearMap.toSpanSingletonLIE ℂ E).continuous.continuousAt.comp
        (hf.continuousAt (hU.mem_nhds (hball hx)))
  have hder := (HasFDerivAt.curveIntegral_segment_source' hω).hasDerivAt
  rw [ContinuousLinearMap.toSpanSingleton_apply_one] at hder
  exact (hder.const_add _).congr_of_eventuallyEq (eventually_of_mem hbz hloc)

/-- **Holomorphic functions have primitives where closed curves are null-homologous.** If every
closed piecewise-`C¹` curve in the open set `U` is null-homologous in `U`, then every function
holomorphic on `U` has a primitive on `U`. -/
theorem isExactOn_of_forall_isNullHomologous {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ (γ : ℝ → ℂ) (a b : ℝ), IsPiecewiseC1On γ a b → MapsTo γ (uIcc a b) U → γ a = γ b →
      IsNullHomologous γ a b U) :
    Complex.IsExactOn f U :=
  isExactOn_of_forall_closed_integral_eq_zero hU hf.continuousOn fun γ a b hγ hγU hclosed =>
    homologyCauchyTheorem hU γ a b hγ (fun _ ht => hγU ht) hclosed hf (h γ a b hγ hγU hclosed)

/-- **Holomorphic functions have primitives on a set without holes.** If `U` is open and every
connected component of `ℂ \ U` is unbounded (`filledHull U ⊆ U`), then every function holomorphic
on `U` has a primitive on `U`. -/
theorem isExactOn_of_filledHull_subset {f : ℂ → ℂ} (hU : IsOpen U) (hUf : filledHull U ⊆ U)
    (hf : DifferentiableOn ℂ f U) : Complex.IsExactOn f U :=
  isExactOn_of_forall_isNullHomologous hU hf fun _ _ _ hγ hγU hclosed =>
    hγ.isNullHomologous_of_filledHull_subset hclosed hγU hUf

/-- **A holomorphic logarithm from a primitive of the logarithmic derivative.** If `g` is
holomorphic and nowhere zero on an open set `U` and `g' / g` has a primitive `h` on `U`, then `g`
has a holomorphic logarithm on `U`. -/
theorem exists_differentiableOn_eqOn_exp_comp_of_isExactOn {g : ℂ → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hg₀ : 0 ∉ g '' U) (hex : Complex.IsExactOn (logDeriv g) U) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ EqOn (Complex.exp ∘ L) g U := by
  obtain ⟨h, hh⟩ := hex
  have hgne : ∀ z ∈ U, g z ≠ 0 := fun z hz hz0 => hg₀ ⟨z, hz, hz0⟩
  let k : ℂ → ℂ := fun z => g z * Complex.exp (-h z)
  have hkd : ∀ z ∈ U, HasDerivAt k 0 z := fun z hz => by
    have hgz := ((hg z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    convert hgz.mul (hh z hz).neg.cexp using 1
    rw [logDeriv_apply]
    field_simp [hgne z hz]
    ring
  have hkconst : ∀ z ∈ U, ∀ᶠ w in 𝓝 z, k w = k z := fun z hz => by
    have hopen := hU.isOpen_inter_preimage_of_deriv_eq_zero
      (fun w hw => (hkd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hkd w hw).deriv) {k z}
    exact eventually_of_mem (hopen.mem_nhds ⟨hz, rfl⟩) fun w hw => hw.2
  refine ⟨fun z => h z + Complex.log (k z), fun z hz => ?_, fun z hz => ?_⟩
  · refine (((hh z hz).differentiableAt.add_const (Complex.log (k z))).congr_of_eventuallyEq
      ?_).differentiableWithinAt
    filter_upwards [hkconst z hz] with w hw
    rw [hw]
  · have hk0 : k z ≠ 0 := mul_ne_zero (hgne z hz) (Complex.exp_ne_zero _)
    have hkz : k z = g z * Complex.exp (-h z) := rfl
    rw [Function.comp_apply, Complex.exp_add, Complex.exp_log hk0, hkz, Complex.exp_neg]
    field_simp

/-- **Holomorphic logarithms on a set without holes.** If `U` is open and every connected component
of `ℂ \ U` is unbounded (`filledHull U ⊆ U`), then every function holomorphic and nowhere zero on
`U` has a holomorphic logarithm on `U`. -/
theorem exists_differentiableOn_eqOn_exp_comp_of_filledHull_subset {g : ℂ → ℂ} (hU : IsOpen U)
    (hUf : filledHull U ⊆ U) (hg : DifferentiableOn ℂ g U) (hg₀ : 0 ∉ g '' U) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ EqOn (Complex.exp ∘ L) g U := by
  refine exists_differentiableOn_eqOn_exp_comp_of_isExactOn hU hg hg₀
    (isExactOn_of_filledHull_subset hU hUf fun z hz => ?_)
  have hgz : g z ≠ 0 := fun h0 => hg₀ ⟨z, hz, h0⟩
  have hd : DifferentiableAt ℂ (deriv g) z := (hg.deriv hU z hz).differentiableAt (hU.mem_nhds hz)
  exact (hd.div ((hg z hz).differentiableAt (hU.mem_nhds hz)) hgz).differentiableWithinAt.congr
    (fun w _ => logDeriv_apply g w) (logDeriv_apply g z)

/-- **Holomorphic `n`-th roots on a set without holes.** If `U` is open and every connected
component of `ℂ \ U` is unbounded (`filledHull U ⊆ U`), then every function holomorphic and nowhere
zero on `U` has a holomorphic `n`-th root on `U`, namely `exp (L / n)` for a holomorphic logarithm
`L`. -/
theorem exists_differentiableOn_pow_eq_of_filledHull_subset {g : ℂ → ℂ} (hU : IsOpen U)
    (hUf : filledHull U ⊆ U) (hg : DifferentiableOn ℂ g U) (hg₀ : 0 ∉ g '' U) {n : ℕ}
    (hn : n ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ EqOn (fun z => f z ^ n) g U := by
  obtain ⟨L, hLd, hLeq⟩ := exists_differentiableOn_eqOn_exp_comp_of_filledHull_subset hU hUf hg hg₀
  refine ⟨fun z => Complex.exp (L z / n), fun z hz => ((hLd z hz).div_const _).cexp,
    fun z hz => ?_⟩
  dsimp only
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn)]
  exact hLeq hz

end TauCeti.Contour
