/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Asymptotic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Logarithmic
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Power growth of Schwarz--Christoffel primitives at infinity

When the total turning exponent `S` is greater than `-1`, the Schwarz--Christoffel primitive
has the leading asymptotic

`F(z) / z ^ (S + 1) → 1 / (S + 1)`

as `z` tends to infinity through the whole upper half-plane. In particular, the primitive
escapes every bounded subset of the plane, uniformly even for approaches tangential to the
real axis. Together with the logarithmic endpoint `S = -1`, this supplies the growth estimate
used in properness arguments for maps onto unbounded polygonal domains.

The proof integrates the uniform integrand asymptotic along radial segments. Their inner
endpoints lie on a fixed upper semicircle, where the primitive is bounded; no integrability
condition at the finite prevertices is needed.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

private abbrev schwarzChristoffelPowerRemainder (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (z : ℂ) : ℂ :=
  schwarzChristoffelPrimitive a e z₀ z -
    z ^ (((∑ i, e i) + 1 : ℝ) : ℂ) / ((∑ i, e i) + 1)

private theorem hasDerivAt_schwarzChristoffelPowerRemainder (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {z : ℂ} (hz : z ∈ upperHalfPlaneSet)
    (hsum : -1 < ∑ i, e i) :
    HasDerivAt (schwarzChristoffelPowerRemainder a e z₀)
      (schwarzChristoffelIntegrand a e z - z ^ ((∑ i, e i : ℝ) : ℂ)) z := by
  -- Expose the pointwise subtraction hidden by the private abbreviation so the derivative
  -- combinators see the primitive and the comparison power separately.
  change HasDerivAt (fun w ↦ schwarzChristoffelPrimitive a e z₀ w -
    w ^ (((∑ i, e i) + 1 : ℝ) : ℂ) / ((∑ i, e i) + 1))
      (schwarzChristoffelIntegrand a e z - z ^ ((∑ i, e i : ℝ) : ℂ)) z
  let S : ℝ := ∑ i, e i
  have hS1 : (S : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by dsimp [S]; linarith : S + 1 ≠ 0)
  have hzslit : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz))
  have hpow : HasDerivAt (fun w : ℂ ↦ w ^ ((S : ℂ) + 1))
      (((S : ℂ) + 1) * z ^ ((S : ℂ) + 1 - 1)) z :=
    (Complex.hasStrictDerivAt_cpow_const hzslit).hasDerivAt
  have hpow' : HasDerivAt (fun z : ℂ ↦ z ^ ((S : ℂ) + 1) / ((S : ℂ) + 1))
      (z ^ (S : ℂ)) z := by
    convert hpow.const_mul (((S : ℂ) + 1)⁻¹) using 1
    · funext w
      rw [div_eq_mul_inv, mul_comm]
    · have hexp : (S : ℂ) + 1 - 1 = S := by ring
      rw [hexp]
      field_simp
  convert (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).sub hpow' using 1
  · funext w
    simp only [Pi.sub_apply]
    have hcast : (((∑ i, e i) + 1 : ℝ) : ℂ) = (S : ℂ) + 1 := by simp [S]
    rw [hcast]

/-- On the part of the circle of radius `R` in the closed upper half-plane, the primitive extends
continuously, provided every finite prevertex lies strictly inside the circle (`|a i| < R`). -/
private theorem continuousOn_extendFrom_schwarzChristoffelPrimitive_sphere
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {R : ℝ} (haR : ∀ i, |a i| < R) :
    ContinuousOn (extendFrom upperHalfPlaneSet (schwarzChristoffelPrimitive a e z₀))
      (sphere 0 R ∩ closure upperHalfPlaneSet) := by
  classical
  apply continuousOn_extendFrom
  · intro z hz
    exact hz.2
  · intro z hz
    by_cases hzH : z ∈ upperHalfPlaneSet
    · exact ⟨schwarzChristoffelPrimitive a e z₀ z,
        ((differentiableOn_schwarzChristoffelPrimitive a e z₀ z hzH).differentiableAt
          (isOpen_upperHalfPlaneSet.mem_nhds hzH)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds⟩
    · have hzcl : 0 ≤ z.im := by
        simpa [Complex.closure_setOfPred_lt_im] using hz.2
      have hzim : z.im = 0 := le_antisymm (not_lt.mp hzH) hzcl
      have hzreal : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hzim])
      have hzabs : |z.re| = R := by
        have hznorm : ‖z‖ = R := by simpa using hz.1
        rw [← hzreal, norm_real, Real.norm_eq_abs] at hznorm
        exact hznorm
      have hne (i : ι) : a i ≠ z.re := by
        intro hi
        have := haR i
        rw [hi, hzabs] at this
        exact this.false
      have hlocal : ∑ i with a i = z.re, e i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact (hne i (Finset.mem_filter.mp hi).2).elim
      rw [← hzreal]
      exact ⟨schwarzChristoffelBoundary a e z₀ z.re,
        tendsto_schwarzChristoffelPrimitive_boundary a e z₀ z.re (by rw [hlocal]; norm_num)⟩

private theorem exists_bound_schwarzChristoffelPowerRemainder_on_semicircle
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : -1 < ∑ i, e i)
    {R : ℝ} (_hR : 0 < R) (haR : ∀ i, |a i| < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ upperHalfPlaneSet, ‖z‖ = R →
      ‖schwarzChristoffelPowerRemainder a e z₀ z‖ ≤ M := by
  classical
  let K : Set ℂ := sphere 0 R ∩ closure upperHalfPlaneSet
  let F : ℂ → ℂ := schwarzChristoffelPrimitive a e z₀
  have hcont : ContinuousOn (extendFrom upperHalfPlaneSet F) K :=
    continuousOn_extendFrom_schwarzChristoffelPrimitive_sphere a e z₀ haR
  have hK : IsCompact K :=
    (isCompact_sphere (0 : ℂ) R).inter_right isClosed_closure
  have hbdd := (hK.image_of_continuousOn hcont).isBounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdd
  let M : ℝ := max 0 (C + R ^ ((∑ i, e i) + 1) / ((∑ i, e i) + 1))
  refine ⟨M, le_max_left _ _, ?_⟩
  intro z hzH hzR
  have hzK : z ∈ K := ⟨by simpa [mem_sphere] using hzR, subset_closure hzH⟩
  have hF : ‖F z‖ ≤ C := by
    have himg : extendFrom upperHalfPlaneSet F z ∈ extendFrom upperHalfPlaneSet F '' K :=
      ⟨z, hzK, rfl⟩
    have := hC _ himg
    rwa [extendFrom_extends
      (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hzH] at this
  apply (norm_sub_le _ _).trans
  calc
    ‖F z‖ + ‖z ^ (((∑ i, e i) + 1 : ℝ) : ℂ) / ((∑ i, e i) + 1)‖
        ≤ C + R ^ ((∑ i, e i) + 1) / ((∑ i, e i) + 1) := by
          gcongr
          have hden : ‖((∑ i, e i : ℝ) : ℂ) + 1‖ = (∑ i, e i) + 1 := by
            rw [← ofReal_one, ← ofReal_add, norm_real, Real.norm_eq_abs,
              abs_of_pos (by linarith : 0 < (∑ i, e i) + 1)]
          rw [norm_div, Complex.norm_cpow_real, hzR, hden]
    _ ≤ M := le_max_right _ _

/-- The pointwise bound on the radial derivative of the power remainder. -/
private theorem norm_mul_schwarzChristoffelIntegrand_sub_cpow_le (a e : ι → ℝ) {R η t : ℝ}
    {z : ℂ}
    (herror : ∀ y ∈ upperHalfPlaneSet, R ≤ ‖y‖ →
      ‖schwarzChristoffelIntegrand a e y - y ^ ((∑ i, e i : ℝ) : ℂ)‖ ≤
        η * ‖y‖ ^ (∑ i, e i))
    (hz0 : 0 < ‖z‖) (ht0 : 0 < t) (hy : (t : ℂ) * z ∈ upperHalfPlaneSet)
    (hyR : R ≤ ‖(t : ℂ) * z‖) :
    ‖z * (schwarzChristoffelIntegrand a e ((t : ℂ) * z) -
        ((t : ℂ) * z) ^ ((∑ i, e i : ℝ) : ℂ))‖ ≤
      η * ‖z‖ ^ ((∑ i, e i) + 1) * t ^ (∑ i, e i) := by
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_left (herror _ hy hyR) (norm_nonneg z)).trans_eq ?_
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0,
    Real.mul_rpow ht0.le (norm_nonneg z), Real.rpow_add hz0, Real.rpow_one]
  ring

private theorem norm_schwarzChristoffelPowerRemainder_sub_le (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 < ∑ i, e i) {R η : ℝ} (hR : 0 < R)
    (hη : 0 ≤ η)
    (herror : ∀ y ∈ upperHalfPlaneSet, R ≤ ‖y‖ →
      ‖schwarzChristoffelIntegrand a e y - y ^ ((∑ i, e i : ℝ) : ℂ)‖ ≤
        η * ‖y‖ ^ (∑ i, e i))
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (hzR : R ≤ ‖z‖) :
    ‖schwarzChristoffelPowerRemainder a e z₀ z -
        schwarzChristoffelPowerRemainder a e z₀ (((R / ‖z‖ : ℝ) : ℂ) * z)‖ ≤
      η / ((∑ i, e i) + 1) * ‖z‖ ^ ((∑ i, e i) + 1) := by
  let S : ℝ := ∑ i, e i
  let δ : ℝ := R / ‖z‖
  let Q : ℂ → ℂ := schwarzChristoffelPowerRemainder a e z₀
  let B : ℝ → ℝ := fun t ↦ η * ‖z‖ ^ (S + 1) * t ^ S
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hz
  have hδ0 : 0 < δ := div_pos hR hz0
  have hδ1 : δ ≤ 1 := (div_le_one hz0).mpr hzR
  have htmem : ∀ t ∈ Icc δ 1, ((t : ℂ) * z) ∈ upperHalfPlaneSet := by
    intro t ht
    simpa using mul_pos (hδ0.trans_le ht.1) hz
  have hderiv : ∀ t ∈ Icc δ 1, HasDerivAt (fun t : ℝ ↦ Q ((t : ℂ) * z))
      (z * (schwarzChristoffelIntegrand a e ((t : ℂ) * z) -
        ((t : ℂ) * z) ^ (S : ℂ))) t := by
    intro t ht
    have hinner : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * z) z t := by
      simpa using Complex.ofRealCLM.hasDerivAt.mul_const z
    simpa [Q, S, Function.comp_def, smul_eq_mul] using
      (hasDerivAt_schwarzChristoffelPowerRemainder a e z₀ (htmem t ht) hsum).scomp t hinner
  have hbound : ∀ t ∈ Icc δ 1,
      ‖z * (schwarzChristoffelIntegrand a e ((t : ℂ) * z) -
        ((t : ℂ) * z) ^ (S : ℂ))‖ ≤ B t := by
    intro t ht
    have ht0 : 0 < t := hδ0.trans_le ht.1
    have hyR : R ≤ ‖(t : ℂ) * z‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      calc R = δ * ‖z‖ := by simp [δ, hz0.ne']
        _ ≤ t * ‖z‖ := mul_le_mul_of_nonneg_right ht.1 (norm_nonneg z)
    exact norm_mul_schwarzChristoffelIntegrand_sub_cpow_le a e herror hz0 ht0 (htmem t ht) hyR
  have hcont : ContinuousOn (fun t : ℝ ↦ Q ((t : ℂ) * z)) (Icc δ 1) :=
    fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t : ℝ ↦ Q ((t : ℂ) * z)) (Ioo δ 1) :=
    fun t ht ↦ (hderiv t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  have hBi : IntervalIntegrable B volume δ 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδ1]
    exact (continuousOn_const.mul continuousOn_const).mul
      (continuousOn_id.rpow_const fun t ht ↦ Or.inl (ne_of_gt (hδ0.trans_le ht.1)))
  have hfB : ∀ᵐ t : ℝ, t ∈ Ioo δ 1 →
      ‖deriv (fun t : ℝ ↦ Q ((t : ℂ) * z)) t‖ ≤ B t :=
    .of_forall fun t ht ↦ by
      rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv]
      exact hbound t (Ioo_subset_Icc_self ht)
  have hmain :=
    norm_sub_le_integral_of_norm_deriv_le_of_le hδ1 hcont hdiff hfB hBi
  have hint : (∫ t in δ..1, B t) ≤ η / (S + 1) * ‖z‖ ^ (S + 1) :=
    integral_const_mul_rpow_le hsum hδ0 hη (Real.rpow_nonneg (norm_nonneg z) _)
  simpa [Q, δ, S] using hmain.trans hint

/-- Outside a large semicircle enclosing every finite prevertex, the integrand is uniformly
close to `y ^ S` relative to `‖y‖ ^ S`, where `S` is the total turning exponent. -/
private theorem exists_radius_norm_schwarzChristoffelIntegrand_sub_le (a e : ι → ℝ) {η : ℝ}
    (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ (∀ i, |a i| < R) ∧ ∀ y ∈ upperHalfPlaneSet, R ≤ ‖y‖ →
      ‖schwarzChristoffelIntegrand a e y - y ^ ((∑ i, e i : ℝ) : ℂ)‖ ≤
        η * ‖y‖ ^ (∑ i, e i) := by
  classical
  have hnormalized := tendsto_schwarzChristoffelIntegrand_div_cpow_atInfinity a e
  have hev : ∀ᶠ y : ℂ in cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet,
      ‖schwarzChristoffelIntegrand a e y / y ^ ((∑ i, e i : ℝ) : ℂ) - 1‖ < η := by
    have := Metric.tendsto_nhds.mp hnormalized η hη
    simpa [dist_eq_norm] using this
  rw [eventually_inf_principal, Filter.hasBasis_cobounded_norm.eventually_iff] at hev
  obtain ⟨R₀, -, hR₀⟩ := hev
  let A : ℝ := 2 + ∑ i, |a i|
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨max R₀ A, hA.trans_le (le_max_right _ _), fun i ↦ ?_, fun y hy hyR ↦ ?_⟩
  · have hi : |a i| ≤ ∑ j, |a j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (a j)) (Finset.mem_univ i)
    dsimp [A] at hA ⊢
    exact lt_of_lt_of_le (by linarith) (le_max_right R₀ A)
  · have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hy
    have hp0 : y ^ ((∑ i, e i : ℝ) : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hy0)
    have heq : schwarzChristoffelIntegrand a e y - y ^ ((∑ i, e i : ℝ) : ℂ) =
        (schwarzChristoffelIntegrand a e y / y ^ ((∑ i, e i : ℝ) : ℂ) - 1) *
          y ^ ((∑ i, e i : ℝ) : ℂ) := by
      field_simp
    rw [heq, norm_mul, Complex.norm_cpow_real]
    exact mul_le_mul_of_nonneg_right
      (hR₀ (le_max_left R₀ A |>.trans hyR) hy).le (Real.rpow_nonneg (norm_nonneg y) _)

/-- For `z` in the upper half-plane with `R ≤ ‖z‖`, the power remainder `Q` satisfies
`‖Q z‖ / ‖z‖ ^ (S + 1) ≤ M / ‖z‖ ^ (S + 1) + η / (S + 1)`, where `S = ∑ i, e i`, `M` bounds `Q`
on the semicircle of radius `R`, and `η` is the constant of the radial error estimate. -/
private theorem norm_schwarzChristoffelPowerRemainder_div_le (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 < ∑ i, e i) {R η M : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    (herror : ∀ y ∈ upperHalfPlaneSet, R ≤ ‖y‖ →
      ‖schwarzChristoffelIntegrand a e y - y ^ ((∑ i, e i : ℝ) : ℂ)‖ ≤
        η * ‖y‖ ^ (∑ i, e i))
    (hM : ∀ z ∈ upperHalfPlaneSet, ‖z‖ = R →
      ‖schwarzChristoffelPowerRemainder a e z₀ z‖ ≤ M)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (hzR : R ≤ ‖z‖) :
    ‖schwarzChristoffelPowerRemainder a e z₀ z‖ / ‖z‖ ^ ((∑ i, e i) + 1) ≤
      M / ‖z‖ ^ ((∑ i, e i) + 1) + η / ((∑ i, e i) + 1) := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hz
  have hzpow : 0 < ‖z‖ ^ ((∑ i, e i) + 1) := Real.rpow_pos_of_pos hz0 _
  have hα : 0 < (∑ i, e i) + 1 := by linarith
  have hyH : ((R / ‖z‖ : ℝ) : ℂ) * z ∈ upperHalfPlaneSet := by
    simpa using mul_pos (div_pos hR hz0) hz
  have hynorm : ‖((R / ‖z‖ : ℝ) : ℂ) * z‖ = R := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hR hz0)]
    exact div_mul_cancel₀ R hz0.ne'
  have hradial := norm_schwarzChristoffelPowerRemainder_sub_le a e z₀ hsum hR hη herror hz hzR
  have hQz : ‖schwarzChristoffelPowerRemainder a e z₀ z‖ ≤
      M + η / ((∑ i, e i) + 1) * ‖z‖ ^ ((∑ i, e i) + 1) := by
    calc
      _ ≤ _ := norm_le_norm_sub_add _ _
      _ ≤ η / ((∑ i, e i) + 1) * ‖z‖ ^ ((∑ i, e i) + 1) + M :=
        add_le_add hradial (hM _ hyH hynorm)
      _ = _ := add_comm _ _
  calc
    _ ≤ (M + η / ((∑ i, e i) + 1) * ‖z‖ ^ ((∑ i, e i) + 1)) / ‖z‖ ^ ((∑ i, e i) + 1) :=
      div_le_div_of_nonneg_right hQz hzpow.le
    _ = _ := by field_simp

/-- The primitive divided by `z ^ (S + 1)` is the remainder divided by `z ^ (S + 1)` plus
`(S + 1)⁻¹`. -/
private theorem schwarzChristoffelPowerRemainder_div_cpow_add_inv (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 < ∑ i, e i) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPowerRemainder a e z₀ z / z ^ (((∑ i, e i) + 1 : ℝ) : ℂ) +
        (((∑ i, e i) + 1 : ℝ) : ℂ)⁻¹ =
      schwarzChristoffelPrimitive a e z₀ z / z ^ (((∑ i, e i) + 1 : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  have hpow0 : z ^ (((∑ i, e i) + 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hden : (((∑ i, e i) + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  dsimp only [schwarzChristoffelPowerRemainder]
  rw [← ofReal_one, ← ofReal_add]
  field_simp [hpow0, hden]
  ring

/-- **Power asymptotic at infinity.** If the total turning exponent is greater than `-1`,
the Schwarz--Christoffel primitive is asymptotic to
`z ^ ((∑ i, e i) + 1) / ((∑ i, e i) + 1)` throughout the upper half-plane. No ordering,
distinctness, or sign assumptions on the finite data are needed. -/
theorem tendsto_schwarzChristoffelPrimitive_div_cpow_atInfinity_of_neg_one_lt_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : -1 < ∑ i, e i) :
    Tendsto (fun z ↦ schwarzChristoffelPrimitive a e z₀ z /
      z ^ (((∑ i, e i) + 1 : ℝ) : ℂ))
      (cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet)
      (nhds (((∑ i, e i) + 1 : ℝ) : ℂ)⁻¹) := by
  classical
  let S : ℝ := ∑ i, e i
  let α : ℝ := S + 1
  let Q : ℂ → ℂ := schwarzChristoffelPowerRemainder a e z₀
  have hα : 0 < α := by dsimp [α, S]; linarith
  have hQ : Tendsto (fun z : ℂ => Q z / z ^ (α : ℂ))
      (cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let η : ℝ := ε * α / 4
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨R, hR, haR, herror⟩ := exists_radius_norm_schwarzChristoffelIntegrand_sub_le a e hη
    obtain ⟨M, _, hM⟩ :=
      exists_bound_schwarzChristoffelPowerRemainder_on_semicircle a e z₀ hsum hR haR
    have hsmall : Tendsto (fun r : ℝ => M / r ^ α) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hα)
    have hevsmall : ∀ᶠ r : ℝ in atTop, M / r ^ α < ε / 2 := by
      exact (tendsto_order.mp hsmall).2 (ε / 2) (half_pos hε)
    obtain ⟨T, hT⟩ := eventually_atTop.mp hevsmall
    filter_upwards [mem_inf_of_left (Filter.hasBasis_cobounded_norm.mem_iff.mpr
      ⟨max R T, trivial, fun _ hz ↦ hz⟩),
      mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hzRT hzH
    have hzR : R ≤ ‖z‖ := (le_max_left R T).trans hzRT
    have hzT : T ≤ ‖z‖ := (le_max_right R T).trans hzRT
    have hbound := norm_schwarzChristoffelPowerRemainder_div_le a e z₀ hsum hR hη.le herror hM
      hzH hzR
    rw [dist_zero_right, norm_div, Complex.norm_cpow_real]
    calc
      ‖Q z‖ / ‖z‖ ^ α ≤ M / ‖z‖ ^ α + η / α := hbound
      _ = M / ‖z‖ ^ α + ε / 4 := by
        congr 1
        dsimp [η]
        field_simp [hα.ne']
      _ < ε / 2 + ε / 4 := by linarith [hT _ hzT]
      _ < ε := by linarith
  have hlim := hQ.add
    (tendsto_const_nhds : Tendsto (fun _ : ℂ => ((α : ℂ)⁻¹))
      (cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet) (nhds ((α : ℂ)⁻¹)))
  have heq : (fun z : ℂ => Q z / z ^ (α : ℂ) + (α : ℂ)⁻¹) =ᶠ[
      cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet]
      (fun z => schwarzChristoffelPrimitive a e z₀ z / z ^ (α : ℂ)) := by
    filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
    have hcast : (α : ℂ) = (((∑ i, e i) + 1 : ℝ) : ℂ) := by simp [α, S]
    rw [hcast]
    exact schwarzChristoffelPowerRemainder_div_cpow_add_inv a e z₀ hsum hz
  have := hlim.congr' heq
  simpa [α, S] using this


/-- **Uniform escape in the power-growth case.** If the total turning exponent is greater
than `-1`, the Schwarz--Christoffel primitive tends to infinity through the entire upper
half-plane. -/
theorem tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_neg_one_lt_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : -1 < ∑ i, e i) :
    Tendsto (schwarzChristoffelPrimitive a e z₀)
      (cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet) (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hratio :=
    tendsto_schwarzChristoffelPrimitive_div_cpow_atInfinity_of_neg_one_lt_sum a e z₀ hsum
  have hconst : 0 < ‖(((∑ i, e i) + 1 : ℝ) : ℂ)⁻¹‖ := norm_pos_iff.mpr <| inv_ne_zero <|
    ofReal_ne_zero.mpr (by linarith)
  have hratioNorm : Tendsto (fun z ↦ ‖schwarzChristoffelPrimitive a e z₀ z /
      z ^ (((∑ i, e i) + 1 : ℝ) : ℂ)‖)
      (cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet)
      (nhds ‖(((∑ i, e i) + 1 : ℝ) : ℂ)⁻¹‖) := hratio.norm
  have hpow : Tendsto (fun z : ℂ => ‖z ^ (((∑ i, e i) + 1 : ℝ) : ℂ)‖)
      (cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet) atTop := by
    simp only [Complex.norm_cpow_real]
    exact (tendsto_rpow_atTop (by linarith)).comp
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
  have hprod := Filter.Tendsto.pos_mul_atTop hconst hratioNorm hpow
  refine hprod.congr' ?_
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)))]

/-- **Uniform escape in the complete nonintegrable range.** If the total turning exponent is
at least `-1`, the Schwarz--Christoffel primitive tends to infinity through the entire upper
half-plane. The endpoint is logarithmic and the strict range has power growth. -/
theorem tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_neg_one_le_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (schwarzChristoffelPrimitive a e z₀)
      (cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet) (cobounded ℂ) := by
  rcases hsum.eq_or_lt with hsum | hsum
  · exact tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_sum_eq_neg_one
      a e z₀ hsum.symm
  · exact tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_neg_one_lt_sum
      a e z₀ hsum

end TauCeti
