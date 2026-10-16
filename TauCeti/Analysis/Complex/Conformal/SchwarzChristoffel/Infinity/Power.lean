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

private theorem exists_bound_schwarzChristoffelPowerRemainder_on_semicircle
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : -1 < ∑ i, e i)
    {R : ℝ} (_hR : 0 < R) (haR : ∀ i, |a i| < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ upperHalfPlaneSet, ‖z‖ = R →
      ‖schwarzChristoffelPowerRemainder a e z₀ z‖ ≤ M := by
  classical
  let K : Set ℂ := sphere 0 R ∩ closure upperHalfPlaneSet
  let F : ℂ → ℂ := schwarzChristoffelPrimitive a e z₀
  have hcont : ContinuousOn (extendFrom upperHalfPlaneSet F) K := by
    apply continuousOn_extendFrom
    · intro z hz
      exact hz.2
    · intro z hz
      by_cases hzH : z ∈ upperHalfPlaneSet
      · exact ⟨F z, ((differentiableOn_schwarzChristoffelPrimitive a e z₀ z hzH).differentiableAt
          (isOpen_upperHalfPlaneSet.mem_nhds hzH)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds⟩
      · have hzcl : 0 ≤ z.im := by
          simpa [Complex.closure_setOfPred_lt_im] using hz.2
        have hzim : z.im = 0 := le_antisymm (not_lt.mp hzH) hzcl
        have hzreal : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hzim])
        have hzabs : |z.re| = R := by
          have hznorm : ‖z‖ = R := by simpa [K] using hz.1
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
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left (herror _ (htmem t ht) hyR) (norm_nonneg z)).trans_eq ?_
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0,
      Real.mul_rpow ht0.le (norm_nonneg z)]
    simp only [B]
    rw [Real.rpow_add hz0]
    simp only [Real.rpow_one]
    ring
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
  have hint : (∫ t in δ..1, B t) ≤ η / (S + 1) * ‖z‖ ^ (S + 1) := by
    simp only [B]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by simpa [S] using hsum)),
      Real.one_rpow]
    have hS1 : 0 < S + 1 := by dsimp [S]; linarith
    have hδpow : 0 ≤ δ ^ (S + 1) := Real.rpow_nonneg hδ0.le _
    calc
      η * ‖z‖ ^ (S + 1) * ((1 - δ ^ (S + 1)) / (S + 1))
          ≤ η * ‖z‖ ^ (S + 1) * (1 / (S + 1)) := by
            gcongr
            linarith
      _ = η / (S + 1) * ‖z‖ ^ (S + 1) := by ring
  simpa [Q, δ, S] using hmain.trans hint

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
    -- Convert the normalized integrand limit into a uniform derivative-error estimate outside
    -- a sufficiently large semicircle that also encloses every finite prevertex.
    have hnormalized := tendsto_schwarzChristoffelIntegrand_div_cpow_atInfinity a e
    have hev : ∀ᶠ y : ℂ in cobounded ℂ ⊓ Filter.principal upperHalfPlaneSet,
        ‖schwarzChristoffelIntegrand a e y / y ^ (S : ℂ) - 1‖ < η := by
      have := Metric.tendsto_nhds.mp hnormalized η hη
      simpa [S, dist_eq_norm] using this
    rw [eventually_inf_principal, Filter.hasBasis_cobounded_norm.eventually_iff] at hev
    obtain ⟨R₀, -, hR₀⟩ := hev
    let A : ℝ := 2 + ∑ i, |a i|
    let R : ℝ := max R₀ A
    have hA : 0 < A := by dsimp [A]; positivity
    have hR : 0 < R := hA.trans_le (le_max_right _ _)
    have haR (i : ι) : |a i| < R := by
      have hi : |a i| ≤ ∑ j, |a j| :=
        Finset.single_le_sum (fun j _ ↦ abs_nonneg (a j)) (Finset.mem_univ i)
      dsimp [A] at hA ⊢
      exact lt_of_lt_of_le (by linarith) (le_max_right R₀ A)
    have herror : ∀ y ∈ upperHalfPlaneSet, R ≤ ‖y‖ →
        ‖schwarzChristoffelIntegrand a e y - y ^ (S : ℂ)‖ ≤ η * ‖y‖ ^ S := by
      intro y hy hyR
      have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hy
      have hp0 : y ^ (S : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hy0)
      have heq : schwarzChristoffelIntegrand a e y - y ^ (S : ℂ) =
          (schwarzChristoffelIntegrand a e y / y ^ (S : ℂ) - 1) * y ^ (S : ℂ) := by
        field_simp
      rw [heq, norm_mul, Complex.norm_cpow_real]
      exact mul_le_mul_of_nonneg_right
        (hR₀ (le_max_left R₀ A |>.trans hyR) hy).le (Real.rpow_nonneg (norm_nonneg y) _)
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
    let y : ℂ := ((R / ‖z‖ : ℝ) : ℂ) * z
    have hyH : y ∈ upperHalfPlaneSet := by
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hzH
      simpa [y] using mul_pos (div_pos hR hz0) hzH
    have hynorm : ‖y‖ = R := by
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hzH
      calc
        ‖y‖ = (R / ‖z‖) * ‖z‖ := by
          rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hR hz0)]
        _ = R := div_mul_cancel₀ R hz0.ne'
    have hradial := norm_schwarzChristoffelPowerRemainder_sub_le a e z₀ hsum hR hη.le
      (by simpa [S] using herror) hzH hzR
    -- The radial estimate controls the varying endpoint; compactness of the fixed inner
    -- semicircle controls the other endpoint independently of the approach direction.
    have hQz : ‖Q z‖ ≤ M + η / α * ‖z‖ ^ α := by
      calc
        ‖Q z‖ ≤ ‖Q z - Q y‖ + ‖Q y‖ := norm_le_norm_sub_add _ _
        _ ≤ η / α * ‖z‖ ^ α + M :=
          add_le_add (by simpa [Q, y, S, α] using hradial) (hM y hyH hynorm)
        _ = M + η / α * ‖z‖ ^ α := add_comm _ _
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hzH
    have hzpow : 0 < ‖z‖ ^ α := Real.rpow_pos_of_pos hz0 α
    rw [dist_zero_right, norm_div, Complex.norm_cpow_real]
    calc
      ‖Q z‖ / ‖z‖ ^ α ≤ (M + η / α * ‖z‖ ^ α) / ‖z‖ ^ α :=
        div_le_div_of_nonneg_right hQz hzpow.le
      _ = M / ‖z‖ ^ α + η / α := by field_simp
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
    have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
    dsimp [Q, schwarzChristoffelPowerRemainder]
    have hcast : (α : ℂ) = (((∑ i, e i) + 1 : ℝ) : ℂ) := by simp [α, S]
    rw [hcast]
    have hpow0 : z ^ (((∑ i, e i) + 1 : ℝ) : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hden : (((∑ i, e i) + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
    rw [← ofReal_one, ← ofReal_add]
    field_simp [hpow0, hden]
    ring
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
