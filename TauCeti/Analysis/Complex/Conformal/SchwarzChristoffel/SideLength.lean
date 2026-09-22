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
packages that integral as `TauCeti.schwarzChristoffelSideLength` and identifies it with the
distance between the corresponding vertices.

This is the real equation in the Schwarz--Christoffel parameter problem: after the turning
exponents have fixed the directions of the sides, the prevertices must be chosen so that these
integrals have the prescribed side-length ratios.  The proof also records interval integrability
of the density.  The only singularities on a bounded side occur at its endpoints; separating
those two factors reduces integrability to Euler's beta integral.

## Main results

* `TauCeti.intervalIntegrable_schwarzChristoffelDensity` -- the density is integrable between
  consecutive prevertices.
* `TauCeti.schwarzChristoffelSideLength_pos` -- every such side length is positive.
* `TauCeti.dist_schwarzChristoffelVertex_succ_eq_sideLength` -- the integral is the geometric
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

/-- The real Schwarz--Christoffel density on the boundary. -/
noncomputable def schwarzChristoffelDensity {ι : Type*} [Fintype ι]
    (a e : ι → ℝ) (x : ℝ) : ℝ :=
  ∏ k, |x - a k| ^ e k

/-- The boundary density is the norm of the Schwarz--Christoffel integrand at a real point. -/
theorem schwarzChristoffelDensity_eq_norm_integrand {ι : Type*} [Fintype ι]
    (a e : ι → ℝ) (x : ℝ) :
    schwarzChristoffelDensity a e x = ‖schwarzChristoffelIntegrand a e (x : ℂ)‖ := by
  rw [norm_schwarzChristoffelIntegrand, schwarzChristoffelDensity]
  apply Finset.prod_congr rfl
  intro k _
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The length assigned by the Schwarz--Christoffel formula to the bounded side between the
consecutive prevertices `a i` and `a (i + 1)`. -/
noncomputable def schwarzChristoffelSideLength (a e : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  ∫ x in a i.castSucc..a i.succ, schwarzChristoffelDensity a e x

/-- The Schwarz--Christoffel side length is the integral of the boundary density between its
consecutive prevertices. -/
theorem schwarzChristoffelSideLength_def (a e : Fin (n + 1) → ℝ) (i : Fin n) :
    schwarzChristoffelSideLength a e i =
      ∫ x in a i.castSucc..a i.succ, schwarzChristoffelDensity a e x :=
  (rfl)

private lemma density_eq_endpoint_mul (a e : Fin (n + 1) → ℝ) (i : Fin n)
    (x : ℝ) :
    schwarzChristoffelDensity a e x =
      |x - a i.castSucc| ^ e i.castSucc * |x - a i.succ| ^ e i.succ *
        (∏ k ∈ (Finset.univ.erase i.castSucc).erase i.succ, |x - a k| ^ e k) := by
  classical
  rw [schwarzChristoffelDensity]
  have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  let f : Fin (n + 1) → ℝ := fun k ↦ |x - a k| ^ e k
  calc
    ∏ k, |x - a k| ^ e k = f i.castSucc * ∏ k ∈ Finset.univ.erase i.castSucc, f k :=
      (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ _)).symm
    _ = f i.castSucc *
        (f i.succ * ∏ k ∈ (Finset.univ.erase i.castSucc).erase i.succ, f k) := by
      rw [Finset.mul_prod_erase (Finset.univ.erase i.castSucc) f
        (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)]
    _ = _ := by simp only [f]; ring

/-- The Schwarz--Christoffel density is interval integrable between consecutive, distinct
prevertices when the two endpoint exponents are greater than `-1`. -/
theorem intervalIntegrable_schwarzChristoffelDensity (a e : Fin (n + 1) → ℝ)
    (ha : StrictMono a) (i : Fin n) (hleft : -1 < e i.castSucc)
    (hright : -1 < e i.succ) :
    IntervalIntegrable (schwarzChristoffelDensity a e) volume
      (a i.castSucc) (a i.succ) := by
  classical
  let p := a i.castSucc
  let q := a i.succ
  let L := q - p
  have hpq : p < q := ha i.castSucc_lt_succ
  have hL : 0 < L := sub_pos.mpr hpq
  let g : ℝ → ℝ := fun x ↦
    ∏ k ∈ (Finset.univ.erase i.castSucc).erase i.succ, |x - a k| ^ e k
  have hg : ContinuousOn g (Icc p q) := by
    refine continuousOn_finsetProd _ fun k hk x hx ↦ ?_
    have hkleft : k ≠ i.castSucc := by
      exact fun h ↦ (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 h
    have hkright : k ≠ i.succ := (Finset.mem_erase.mp hk).1
    have hxne : x ≠ a k := by
      intro hxk
      have hlik : i.castSucc ≤ k := (ha.le_iff_le).mp (by simpa [p, hxk] using hx.1)
      have hkir : k ≤ i.succ := (ha.le_iff_le).mp (by simpa [q, hxk] using hx.2)
      have hk : k = i.castSucc ∨ k = i.succ := by
        have hlik' := Fin.mk_le_mk.mp hlik
        have hkir' := Fin.mk_le_mk.mp hkir
        have hkval : k.val = i.val ∨ k.val = i.val + 1 := by omega
        exact hkval.imp (fun h ↦ Fin.ext h) (fun h ↦ Fin.ext (by simpa using h))
      exact hk.elim hkleft hkright
    exact (((continuous_id.sub continuous_const).abs.continuousAt).rpow_const
      (Or.inl (abs_ne_zero.mpr (sub_ne_zero_of_ne hxne)))).continuousWithinAt
  have hbeta : IntervalIntegrable
      (fun t : ℝ ↦ t ^ e i.castSucc * (1 - t) ^ e i.succ) volume 0 1 := by
    simpa only [add_sub_cancel_right] using
      intervalIntegrable_rpow_mul_one_sub_rpow (a := e i.castSucc + 1)
        (b := e i.succ + 1) (by linarith) (by linarith)
        (u := 0) (v := 1) (by simp) (by simp)
  have hscaled : IntervalIntegrable
      (fun x : ℝ ↦ (x / L) ^ e i.castSucc * (1 - x / L) ^ e i.succ)
      volume 0 L := by
    have h := hbeta.comp_mul_right (c := L⁻¹)
    simpa [div_eq_mul_inv, hL.ne'] using h
  have hshifted : IntervalIntegrable
      (fun x : ℝ ↦ ((x - p) / L) ^ e i.castSucc *
        (1 - (x - p) / L) ^ e i.succ) volume p q := by
    have h := hscaled.comp_sub_right p
    simpa [q, L] using h
  have hkernel : IntervalIntegrable
      (fun x : ℝ ↦ |x - p| ^ e i.castSucc * |x - q| ^ e i.succ) volume p q := by
    refine (hshifted.const_mul (L ^ (e i.castSucc + e i.succ))).congr fun x hx ↦ ?_
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
  refine (hkernel.mul_continuousOn hg').congr fun x _ ↦ ?_
  rw [density_eq_endpoint_mul]

/-- On an open boundary interval containing no nonzero prevertex, the derivative of the
Schwarz--Christoffel boundary map is the positive density times the fixed edge direction. -/
theorem hasDerivAt_schwarzChristoffelBoundary {ι : Type*} [Fintype ι] (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q x : ℝ} (ha : ∀ k, e k ≠ 0 → a k ∉ Ioo p q)
    (hx : x ∈ Ioo p q) :
    HasDerivAt (schwarzChristoffelBoundary a e z₀)
      ((schwarzChristoffelDensity a e x : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) x := by
  let d : ℝ → ℝ := schwarzChristoffelDensity a e
  let C : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  have hdcontOn : ContinuousOn d (Ioo p q) := by
    refine continuousOn_finsetProd _ fun k _ y hy ↦ ?_
    rcases eq_or_ne (e k) 0 with hk | hk
    · simpa [d, schwarzChristoffelDensity, hk] using continuousWithinAt_const
    · have hyk : y ≠ a k := fun h ↦ ha k hk (h ▸ hy)
      exact (((continuous_id.sub continuous_const).abs.continuousAt).rpow_const
        (Or.inl (abs_ne_zero.mpr (sub_ne_zero_of_ne hyk)))).continuousWithinAt
  have hdcont : ContinuousAt d x :=
    (hdcontOn x hx).continuousAt (isOpen_Ioo.mem_nhds hx)
  have hInt : HasDerivAt (fun y : ℝ ↦ ∫ t in x..y, d t) (d x) x :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun y hy ↦ (hdcontOn y hy).continuousAt (isOpen_Ioo.mem_nhds hy)) x hx) hdcont
  have hcast : HasDerivAt (fun y : ℝ ↦ ((∫ t in x..y, d t : ℝ) : ℂ)) (d x : ℂ) x := by
    simpa [Function.comp_def] using Complex.ofRealCLM.hasDerivAt.scomp x hInt
  have hmodel : HasDerivAt
      (fun y : ℝ ↦ schwarzChristoffelBoundary a e z₀ x +
        ((∫ t in x..y, d t : ℝ) : ℂ) * C) ((d x : ℂ) * C) x :=
    (hcast.mul_const C).const_add _
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  have h := schwarzChristoffelBoundary_sub_eq a e z₀ ha hy hx
  simp only [d, C, schwarzChristoffelDensity] at h ⊢
  linear_combination h

/-- The vector of a bounded Schwarz--Christoffel side is its density integral times the unit
vector in the side's fixed direction. -/
theorem schwarzChristoffelVertex_succ_sub_eq_sideLength_mul (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (i : Fin n)
    (hleft : -1 < e i.castSucc) (hright : -1 < e i.succ) :
    schwarzChristoffelVertex a e z₀ i.succ -
        schwarzChristoffelVertex a e z₀ i.castSucc =
      (schwarzChristoffelSideLength a e i : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) := by
  classical
  let p := a i.castSucc
  let q := a i.succ
  let C : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  have hpq : p < q := ha i.castSucc_lt_succ
  have hfree : ∀ k, e k ≠ 0 → a k ∉ Ioo p q := by
    intro k _ hk
    have hik : i.castSucc < k := (ha.lt_iff_lt).mp hk.1
    have hki : k < i.succ := (ha.lt_iff_lt).mp hk.2
    have hik' := Fin.mk_lt_mk.mp hik
    have hki' := Fin.mk_lt_mk.mp hki
    omega
  have hsum (k : Fin (n + 1)) : ∑ l with a l = a k, e l = e k := by
    simp [ha.injective.eq_iff, Finset.filter_eq']
  have hleftsum : -1 < ∑ k with a k = p, e k := by
    rw [show p = a i.castSucc from rfl, hsum]
    exact hleft
  have hrightsum : -1 < ∑ k with a k = q, e k := by
    rw [show q = a i.succ from rfl, hsum]
    exact hright
  have hcont : ContinuousOn (schwarzChristoffelBoundary a e z₀) (Icc p q) :=
    continuousOn_schwarzChristoffelBoundary_Icc a e z₀ hfree
      hleftsum hrightsum
  have hdensity := intervalIntegrable_schwarzChristoffelDensity a e ha i hleft hright
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
  simpa only [schwarzChristoffelSideLength, p, q, C] using hFTC.symm

/-- Every bounded Schwarz--Christoffel side has positive integral length when its endpoint
singularities are integrable. -/
theorem schwarzChristoffelSideLength_pos (a e : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (i : Fin n) (hleft : -1 < e i.castSucc) (hright : -1 < e i.succ) :
    0 < schwarzChristoffelSideLength a e i := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_schwarzChristoffelDensity a e ha i hleft hright) _
    (ha i.castSucc_lt_succ)
  intro x hx
  exact Finset.prod_pos fun k _ ↦ Real.rpow_pos_of_pos
    (abs_pos.mpr (sub_ne_zero.mpr fun h ↦ by
      have hxk : a k ∈ Ioo (a i.castSucc) (a i.succ) := by simpa [h] using hx
      have hik : i.castSucc < k := (ha.lt_iff_lt).mp hxk.1
      have hki : k < i.succ := (ha.lt_iff_lt).mp hxk.2
      have hik' := Fin.mk_lt_mk.mp hik
      have hki' := Fin.mk_lt_mk.mp hki
      omega)) _

/-- The side-length integral is the Euclidean distance between the corresponding consecutive
Schwarz--Christoffel vertices. -/
theorem dist_schwarzChristoffelVertex_succ_eq_sideLength (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (i : Fin n)
    (hleft : -1 < e i.castSucc) (hright : -1 < e i.succ) :
    dist (schwarzChristoffelVertex a e z₀ i.succ)
        (schwarzChristoffelVertex a e z₀ i.castSucc) =
      schwarzChristoffelSideLength a e i := by
  rw [Complex.dist_eq, schwarzChristoffelVertex_succ_sub_eq_sideLength_mul a e z₀ ha i
    hleft hright, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (schwarzChristoffelSideLength_pos a e ha i hleft hright),
    Complex.norm_exp_ofReal_mul_I, mul_one]

end TauCeti
