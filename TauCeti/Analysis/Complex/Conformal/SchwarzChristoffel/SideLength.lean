/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
public import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Side lengths in the Schwarz--Christoffel formula

The bounded side between two consecutive prevertices has length equal to the integral of the
absolute value of the Schwarz--Christoffel integrand over the interval between them.  This file
packages that integral as `TauCeti.schwarzChristoffelSideIntegral` and identifies it with the
distance between the corresponding vertices.

This is the real equation in the Schwarz--Christoffel parameter problem: after the turning
exponents have fixed the directions of the sides, the prevertices must be chosen so that these
integrals have the prescribed side-length ratios.  The proof also records interval integrability
of the density.  The only singularities on a bounded side occur at its endpoints; separating
those two factors reduces integrability to Euler's beta integral.

## Main results

* `TauCeti.intervalIntegrable_schwarzChristoffelDensity` -- the density is integrable between
  consecutive prevertices.
* `TauCeti.schwarzChristoffelSideIntegral_pos` -- every such side integral is positive.
* `TauCeti.dist_schwarzChristoffelVertex_succ_eq_sideIntegral` -- the integral is the geometric
  length of the corresponding polygon side.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

noncomputable section

open Complex Finset MeasureTheory Set

namespace TauCeti

variable {n : ℕ}

/-- The oriented candidate side-length integral between consecutive prevertices `a i` and
`a (i + 1)`.  For strictly ordered prevertices and integrable endpoint singularities it is
positive and equals the geometric side length, as proved below. -/
noncomputable def schwarzChristoffelSideIntegral (a e : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  ∫ x in a i.castSucc..a i.succ, schwarzChristoffelDensity a e x

/-- The Schwarz--Christoffel density is interval integrable between two distinct endpoints when
there is no nonzero-exponent prevertex in the open interval and the total exponent at each
endpoint is greater than `-1`. -/
theorem intervalIntegrable_schwarzChristoffelDensity {ι : Type*} [Fintype ι]
    (a e : ι → ℝ) {p q : ℝ} (hpq : p < q)
    (ha : ∀ k, e k ≠ 0 → a k ∉ Ioo p q)
    (hleft : -1 < ∑ k with a k = p, e k)
    (hright : -1 < ∑ k with a k = q, e k) :
    IntervalIntegrable (schwarzChristoffelDensity a e) volume p q := by
  classical
  let L := q - p
  have hL : 0 < L := sub_pos.mpr hpq
  let g : ℝ → ℝ := fun x ↦
    ∏ k ∈ Finset.univ.filter (fun k ↦ a k ≠ p ∧ a k ≠ q), |x - a k| ^ e k
  have hg : ContinuousOn g (Icc p q) := by
    refine continuousOn_finsetProd _ fun k hk x hx ↦ ?_
    rcases eq_or_ne (e k) 0 with hek | hek
    · simpa [hek] using continuousWithinAt_const
    · have hk' := (Finset.mem_filter.mp hk).2
      have hxne : x ≠ a k := by
        intro hxk
        subst x
        apply ha k hek
        exact ⟨lt_of_le_of_ne hx.1 hk'.1.symm, lt_of_le_of_ne hx.2 hk'.2⟩
      exact (((continuous_id.sub continuous_const).abs.continuousAt).rpow_const
        (Or.inl (abs_ne_zero.mpr (sub_ne_zero_of_ne hxne)))).continuousWithinAt
  have hbeta : IntervalIntegrable
      (fun t : ℝ ↦ t ^ (∑ k with a k = p, e k) *
        (1 - t) ^ (∑ k with a k = q, e k)) volume 0 1 := by
    simpa only [add_sub_cancel_right] using
      intervalIntegrable_rpow_mul_one_sub_rpow
        (a := (∑ k with a k = p, e k) + 1)
        (b := (∑ k with a k = q, e k) + 1) (by linarith) (by linarith)
        (u := 0) (v := 1) (by simp) (by simp)
  have hscaled : IntervalIntegrable
      (fun x : ℝ ↦ (x / L) ^ (∑ k with a k = p, e k) *
        (1 - x / L) ^ (∑ k with a k = q, e k))
      volume 0 L := by
    have h := hbeta.comp_mul_right (c := L⁻¹)
    simpa [div_eq_mul_inv, hL.ne'] using h
  have hshifted : IntervalIntegrable
      (fun x : ℝ ↦ ((x - p) / L) ^ (∑ k with a k = p, e k) *
        (1 - (x - p) / L) ^ (∑ k with a k = q, e k)) volume p q := by
    have h := hscaled.comp_sub_right p
    simpa [L] using h
  have hkernel : IntervalIntegrable
      (fun x : ℝ ↦ |x - p| ^ (∑ k with a k = p, e k) *
        |x - q| ^ (∑ k with a k = q, e k)) volume p q := by
    refine (hshifted.const_mul
      (L ^ ((∑ k with a k = p, e k) + ∑ k with a k = q, e k))).congr fun x hx ↦ ?_
    rw [uIoc_of_le hpq.le] at hx
    have hxp : 0 < x - p := sub_pos.mpr hx.1
    have hqx : 0 ≤ q - x := sub_nonneg.mpr hx.2
    have hone : 1 - (x - p) / L = (q - x) / L := by
      field_simp [hL.ne']
      ring
    rw [abs_of_pos hxp, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub, hone,
      Real.div_rpow hxp.le hL.le, Real.div_rpow hqx hL.le, div_eq_mul_inv]
    rw [Real.rpow_add hL]
    field_simp [(Real.rpow_pos_of_pos hL _).ne']
  have hg' : ContinuousOn g (uIcc p q) := by simpa [uIcc_of_le hpq.le] using hg
  refine (hkernel.mul_continuousOn hg').congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_of_ae (volume.ae_ne p),
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne q)] with x hxp hxq
  rw [schwarzChristoffelDensity_def]
  have hxp' : 0 < |x - p| := abs_pos.mpr (sub_ne_zero.mpr hxp)
  have hxq' : 0 < |x - q| := abs_pos.mpr (sub_ne_zero.mpr hxq)
  have hp_prod : |x - p| ^ (∑ k with a k = p, e k) =
      ∏ k ∈ Finset.univ.filter (fun k ↦ a k = p), |x - a k| ^ e k := by
    rw [Real.rpow_sum_of_pos hxp']
    apply Finset.prod_congr rfl
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  have hq_prod : |x - q| ^ (∑ k with a k = q, e k) =
      ∏ k ∈ Finset.univ.filter (fun k ↦ a k = q), |x - a k| ^ e k := by
    rw [Real.rpow_sum_of_pos hxq']
    apply Finset.prod_congr rfl
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  rw [hp_prod, hq_prod]
  simp only [g, Finset.prod_filter]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hkp : a k = p
  · simp [hkp, hpq.ne]
  by_cases hkq : a k = q
  · simp [hkq, hpq.ne']
  · simp [hkp, hkq]

private lemma not_mem_Ioo_prevertices_succ (a : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (i : Fin n) (k : Fin (n + 1)) : a k ∉ Ioo (a i.castSucc) (a i.succ) := by
  intro hk
  have hik : i.castSucc < k := (ha.lt_iff_lt).mp hk.1
  have hki : k < i.succ := (ha.lt_iff_lt).mp hk.2
  exact (Fin.le_of_castSucc_lt_of_succ_lt hik hki).false

/-- For strictly ordered prevertices, the density is integrable between consecutive prevertices
when the two endpoint exponents are greater than `-1`. -/
theorem intervalIntegrable_schwarzChristoffelDensity_succ (a e : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (i : Fin n) (hleft : -1 < e i.castSucc)
    (hright : -1 < e i.succ) :
    IntervalIntegrable (schwarzChristoffelDensity a e) volume
      (a i.castSucc) (a i.succ) := by
  apply intervalIntegrable_schwarzChristoffelDensity a e (ha i.castSucc_lt_succ)
    (fun k _ ↦ not_mem_Ioo_prevertices_succ a ha i k)
  · simpa [ha.injective.eq_iff, Finset.filter_eq'] using hleft
  · simpa [ha.injective.eq_iff, Finset.filter_eq'] using hright

/-- The vector of a bounded Schwarz--Christoffel side is its density integral times the unit
vector in the side's fixed direction. -/
theorem schwarzChristoffelVertex_succ_sub_eq_sideIntegral_mul (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (i : Fin n)
    (hleft : -1 < e i.castSucc) (hright : -1 < e i.succ) :
    schwarzChristoffelVertex a e z₀ i.succ -
        schwarzChristoffelVertex a e z₀ i.castSucc =
      (schwarzChristoffelSideIntegral a e i : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) := by
  classical
  let p := a i.castSucc
  let q := a i.succ
  let C : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  have hpq : p < q := ha i.castSucc_lt_succ
  have hfree : ∀ k, e k ≠ 0 → a k ∉ Ioo p q := by
    exact fun k _ ↦ not_mem_Ioo_prevertices_succ a ha i k
  have hsum (k : Fin (n + 1)) : ∑ l with a l = a k, e l = e k := by
    simp [ha.injective.eq_iff, Finset.filter_eq']
  have hleftsum : -1 < ∑ k with a k = p, e k := by
    simpa [p, hsum] using hleft
  have hrightsum : -1 < ∑ k with a k = q, e k := by
    simpa [q, hsum] using hright
  have hcont : ContinuousOn (schwarzChristoffelBoundary a e z₀) (Icc p q) :=
    continuousOn_schwarzChristoffelBoundary_Icc a e z₀ hfree
      hleftsum hrightsum
  have hdensity := intervalIntegrable_schwarzChristoffelDensity_succ a e ha i hleft hright
  have hcast : IntervalIntegrable (fun x : ℝ ↦ (schwarzChristoffelDensity a e x : ℂ))
      volume p q :=
    ⟨hdensity.1.ofReal, hdensity.2.ofReal⟩
  have hint : IntervalIntegrable
      (fun x : ℝ ↦ (schwarzChristoffelDensity a e x : ℂ) * C) volume p q :=
    hcast.mul_const C
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq.le hcont
    (fun x hx ↦ hasDerivAt_schwarzChristoffelBoundary a e z₀ hfree hx) hint
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ i.succ (by rw [hsum]; exact hright),
    schwarzChristoffelBoundary_apply_prevertex a e z₀ i.castSucc
      (by rw [hsum]; exact hleft)] at hFTC
  simpa only [schwarzChristoffelSideIntegral, p, q, C] using hFTC.symm

/-- Every bounded Schwarz--Christoffel side has positive integral length when its endpoint
singularities are integrable. -/
theorem schwarzChristoffelSideIntegral_pos (a e : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (i : Fin n) (hleft : -1 < e i.castSucc) (hright : -1 < e i.succ) :
    0 < schwarzChristoffelSideIntegral a e i := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_schwarzChristoffelDensity_succ a e ha i hleft hright) _
    (ha i.castSucc_lt_succ)
  intro x hx
  exact schwarzChristoffelDensity_pos a e fun k _ hxk ↦
    not_mem_Ioo_prevertices_succ a ha i k (hxk ▸ hx)

/-- The side-length integral is the Euclidean distance between the corresponding consecutive
Schwarz--Christoffel vertices. -/
theorem dist_schwarzChristoffelVertex_succ_eq_sideIntegral (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (i : Fin n)
    (hleft : -1 < e i.castSucc) (hright : -1 < e i.succ) :
    dist (schwarzChristoffelVertex a e z₀ i.succ)
        (schwarzChristoffelVertex a e z₀ i.castSucc) =
      schwarzChristoffelSideIntegral a e i := by
  rw [Complex.dist_eq, schwarzChristoffelVertex_succ_sub_eq_sideIntegral_mul a e z₀ ha i
    hleft hright, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (schwarzChristoffelSideIntegral_pos a e ha i hleft hright),
    Complex.norm_exp_ofReal_mul_I, mul_one]

end TauCeti
