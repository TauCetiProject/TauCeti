/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.NoncentralChi.Basic
public import TauCeti.Probability.Distributions.NoncentralChiSquared.PDF
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Densities and support of noncentral chi laws

Substituting `y = (x / s) ^ 2` in the continuous noncentral chi-squared density and multiplying
by the Jacobian `2 * x / s ^ 2` gives the continuous noncentral chi density on the positive
half-line. At positive degree this is the density of the noncentral chi law. At degree zero it
describes only the continuous component, and the atom `exp (-δ ^ 2 / 2)` at zero is kept
separate.

At positive noncentrality the modified Bessel representation of the noncentral chi-squared
density gives the classical closed form
`x / s ^ 2 * exp (-((x / s) ^ 2 + δ ^ 2) / 2) * (x / (s * δ)) ^ (k / 2 - 1) * I (δ * x / s)`,
where `I` is the modified Bessel function of the first kind of order `k / 2 - 1`.
At degree two this is the Rice density. The file also identifies the topological support.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {k s x : ℝ} {δ : ℝ≥0}

/-- The real density of the continuous component of a noncentral chi law. At degree zero the
atom is excluded; it vanishes at nonpositive arguments, nonpositive scale, and negative degree. -/
def noncentralChiPDFReal (k : ℝ) (δ : ℝ≥0) (s x : ℝ) : ℝ :=
  if 0 < s ∧ 0 < x then
    2 * x / s ^ 2 * noncentralChiSquaredPDFReal k (δ ^ 2) ((x / s) ^ 2)
  else 0

/-- The extended nonnegative density of the continuous component of a noncentral chi law. -/
def noncentralChiPDF (k : ℝ) (δ : ℝ≥0) (s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (noncentralChiPDFReal k δ s x)

/-- The extended density is obtained from its nonnegative real companion. -/
theorem noncentralChiPDF_eq_ofReal (k : ℝ) (δ : ℝ≥0) (s x : ℝ) :
    noncentralChiPDF k δ s x = ENNReal.ofReal (noncentralChiPDFReal k δ s x) := (rfl)

/-- On the positive half-line and at positive scale the density is the Jacobian-weighted
noncentral chi-squared density at the squared standardized coordinate. -/
theorem noncentralChiPDFReal_of_pos (hs : 0 < s) (hx : 0 < x) :
    noncentralChiPDFReal k δ s x =
      2 * x / s ^ 2 * noncentralChiSquaredPDFReal k (δ ^ 2) ((x / s) ^ 2) := by
  rw [noncentralChiPDFReal, ite_eq_left ⟨hs, hx⟩]

/-- The real density vanishes on the nonpositive half-line. -/
@[simp]
theorem noncentralChiPDFReal_of_nonpos (hx : x ≤ 0) : noncentralChiPDFReal k δ s x = 0 := by
  rw [noncentralChiPDFReal, ite_eq_right fun h ↦ (not_lt.mpr hx) h.2]

/-- The extended density vanishes on the nonpositive half-line. -/
@[simp]
theorem noncentralChiPDF_of_nonpos (hx : x ≤ 0) : noncentralChiPDF k δ s x = 0 := by
  simp [noncentralChiPDF_eq_ofReal, noncentralChiPDFReal_of_nonpos hx]

/-- The real density vanishes at nonpositive scale. -/
@[simp]
theorem noncentralChiPDFReal_of_scale_nonpos (hs : s ≤ 0) : noncentralChiPDFReal k δ s x = 0 := by
  rw [noncentralChiPDFReal, ite_eq_right fun h ↦ (not_lt.mpr hs) h.1]

/-- The extended density vanishes at nonpositive scale. -/
@[simp]
theorem noncentralChiPDF_of_scale_nonpos (hs : s ≤ 0) : noncentralChiPDF k δ s x = 0 := by
  simp [noncentralChiPDF_eq_ofReal, noncentralChiPDFReal_of_scale_nonpos hs]

/-- Invalid degrees have zero real density. -/
@[simp]
theorem noncentralChiPDFReal_of_neg (hk : k < 0) : noncentralChiPDFReal k δ s x = 0 := by
  rw [noncentralChiPDFReal]
  split_ifs
  · rw [noncentralChiSquaredPDFReal_of_neg hk, mul_zero]
  · rfl

/-- Invalid degrees have zero extended density. -/
@[simp]
theorem noncentralChiPDF_of_neg (hk : k < 0) : noncentralChiPDF k δ s x = 0 := by
  simp [noncentralChiPDF_eq_ofReal, noncentralChiPDFReal_of_neg hk]

/-- The real density is nonnegative for every parameter value. -/
theorem noncentralChiPDFReal_nonneg (k : ℝ) (δ : ℝ≥0) (s x : ℝ) :
    0 ≤ noncentralChiPDFReal k δ s x := by
  unfold noncentralChiPDFReal
  split_ifs with h
  · exact mul_nonneg (by have := h.2; positivity) (noncentralChiSquaredPDFReal_nonneg _ _ _)
  · rfl

/-- The extended density has the real density as its real value. -/
@[simp]
theorem toReal_noncentralChiPDF (k : ℝ) (δ : ℝ≥0) (s x : ℝ) :
    (noncentralChiPDF k δ s x).toReal = noncentralChiPDFReal k δ s x :=
  ENNReal.toReal_ofReal (noncentralChiPDFReal_nonneg k δ s x)

/-- At zero noncentrality the continuous density is the central chi density. -/
@[simp]
theorem noncentralChiPDFReal_zero_noncentrality (k s x : ℝ) :
    noncentralChiPDFReal k 0 s x = chiPDFReal k s x := by
  by_cases hsx : 0 < s ∧ 0 < x
  swap
  · rw [noncentralChiPDFReal, ite_eq_right hsx, chiPDFReal_of_not_pos fun h ↦ hsx h.2]
  obtain ⟨hs, hx⟩ := hsx
  rw [noncentralChiPDFReal_of_pos hs hx, zero_pow two_ne_zero,
    noncentralChiSquaredPDFReal_zero_noncentrality]
  by_cases hk : 0 < k
  swap
  · rw [chiPDFReal_of_not_pos fun h ↦ hk h.1]
    split_ifs with h
    · rw [le_antisymm (not_lt.mp hk) h.1, chiSquaredPDFReal_zero_degree, Pi.zero_apply,
        mul_zero]
    · rw [mul_zero]
  have hxs : 0 < x / s := div_pos hx hs
  have hpow : (x / s) ^ (k - 1) = ((x / s) ^ 2) ^ (k / 2 - 1) * (x / s) := by
    rw [← rpow_natCast, ← rpow_mul hxs.le, ← rpow_add_one hxs.ne']
    congr 1
    push_cast
    ring
  rw [ite_eq_left ⟨hk.le, by positivity⟩, chiSquaredPDFReal_of_nonneg (by positivity),
    chiPDFReal_of_pos hk hs hx, hpow, rpow_sub two_pos, rpow_one]
  field_simp

/-- At zero noncentrality the extended continuous density is the central chi density. -/
@[simp]
theorem noncentralChiPDF_zero_noncentrality (k s x : ℝ) :
    noncentralChiPDF k 0 s x = chiPDF k s x := by
  rw [noncentralChiPDF_eq_ofReal, chiPDF_eq_ofReal, noncentralChiPDFReal_zero_noncentrality]

/-- Every valid law other than the double-zero Dirac law has strictly positive continuous density
at positive arguments. -/
theorem noncentralChiPDFReal_pos (hk : 0 ≤ k) (hne : k ≠ 0 ∨ δ ≠ 0) (hs : 0 < s) (hx : 0 < x) :
    0 < noncentralChiPDFReal k δ s x := by
  rw [noncentralChiPDFReal_of_pos hs hx]
  exact mul_pos (by positivity) (noncentralChiSquaredPDFReal_pos hk
    (hne.imp_right (pow_ne_zero 2)) (by positivity))

/-- Every valid law other than the double-zero Dirac law has strictly positive extended
continuous density at positive arguments. -/
theorem noncentralChiPDF_pos (hk : 0 ≤ k) (hne : k ≠ 0 ∨ δ ≠ 0) (hs : 0 < s) (hx : 0 < x) :
    0 < noncentralChiPDF k δ s x := by
  rw [noncentralChiPDF_eq_ofReal, ENNReal.ofReal_pos]
  exact noncentralChiPDFReal_pos hk hne hs hx

/-- Away from the double-zero Dirac law, the function support of the continuous density is the
positive half-line. -/
@[simp]
theorem support_noncentralChiPDF (hk : 0 ≤ k) (hne : k ≠ 0 ∨ δ ≠ 0) (hs : 0 < s) :
    Function.support (noncentralChiPDF k δ s) = Ioi 0 := by
  ext y
  rw [Function.mem_support, mem_Ioi]
  exact ⟨fun hy ↦ not_le.mp fun h ↦ hy (noncentralChiPDF_of_nonpos h),
    fun hy ↦ (noncentralChiPDF_pos hk hne hs hy).ne'⟩

/-- The real density is measurable in its argument. -/
@[fun_prop]
theorem measurable_noncentralChiPDFReal (k : ℝ) (δ : ℝ≥0) (s : ℝ) :
    Measurable (noncentralChiPDFReal k δ s) := by
  unfold noncentralChiPDFReal
  refine Measurable.ite (by measurability) (Measurable.mul (by fun_prop) ?_) measurable_const
  exact measurable_uncurry_noncentralChiSquaredPDFReal.comp
    (by fun_prop : Measurable fun x : ℝ ↦ ((k, δ ^ 2), (x / s) ^ 2))

/-- The extended density is measurable in its argument. -/
@[fun_prop]
theorem measurable_noncentralChiPDF (k : ℝ) (δ : ℝ≥0) (s : ℝ) :
    Measurable (noncentralChiPDF k δ s) :=
  (measurable_noncentralChiPDFReal k δ s).ennreal_ofReal

/-- At positive noncentrality, scale, and argument the continuous density has its classical
modified-Bessel form. The formula also describes the continuous part at degree zero. -/
theorem noncentralChiPDFReal_eq_besselI (hk : 0 ≤ k) (hδ : 0 < δ) (hs : 0 < s) (hx : 0 < x) :
    noncentralChiPDFReal k δ s x =
      x / s ^ 2 * exp (-((x / s) ^ 2 + δ ^ 2) / 2) * (x / (s * δ)) ^ (k / 2 - 1) *
        besselI (k / 2 - 1) (δ * x / s) := by
  have hδ' : (0 : ℝ) < δ := hδ
  have hsqrt : √(((δ ^ 2 : ℝ≥0) : ℝ) * (x / s) ^ 2) = δ * x / s := by
    rw [NNReal.coe_pow, ← mul_pow, sqrt_sq (by positivity), mul_div_assoc]
  have hpow : ((x / s) ^ 2 / ((δ ^ 2 : ℝ≥0) : ℝ)) ^ (k / 4 - 1 / 2) =
      (x / (s * δ)) ^ (k / 2 - 1) := by
    rw [NNReal.coe_pow, ← div_pow, div_div, ← rpow_natCast, ← rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  rw [noncentralChiPDFReal_of_pos hs hx, noncentralChiSquaredPDFReal_eq_besselI hk
    (pow_pos hδ 2) (by positivity), hsqrt, hpow, NNReal.coe_pow]
  ring

/-- **Scaled square roots of the continuous noncentral chi-squared component.** The image of
the continuous noncentral chi-squared component under `s * √·` is the continuous noncentral chi
component; the substitution is `y = (x / s) ^ 2` on the positive half-line. -/
private theorem map_withDensity_noncentralChiSquaredPDF (hs : 0 < s) :
    (volume.withDensity (noncentralChiSquaredPDF k (δ ^ 2))).map (fun y ↦ s * √y) =
      volume.withDensity (noncentralChiPDF k δ s) := by
  set φ : ℝ → ℝ := fun t ↦ (t / s) ^ 2
  have himage : φ '' Ioi 0 = Ioi 0 := by
    ext y
    refine ⟨fun ⟨t, ht, hty⟩ ↦ hty ▸ mem_Ioi.mpr (pow_pos (div_pos ht hs) 2),
      fun hy ↦ ⟨s * √y, mul_pos hs (sqrt_pos.mpr hy), ?_⟩⟩
    simp [φ, hs.ne', sq_sqrt (mem_Ioi.mp hy).le]
  have hinj : InjOn φ (Ioi 0) := fun a ha b hb hab ↦
    (div_left_inj' hs.ne').1 ((sq_eq_sq₀ (div_pos ha hs).le (div_pos hb hs).le).1 hab)
  have hderiv (t : ℝ) : HasDerivAt φ (2 * t / s ^ 2) t := by
    refine (((hasDerivAt_id t).div_const s).fun_pow 2).congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
  -- The noncentral chi-squared density vanishes off the positive half-line.
  have hsource : volume.withDensity (noncentralChiSquaredPDF k (δ ^ 2)) =
      (volume.restrict (Ioi 0)).withDensity (noncentralChiSquaredPDF k (δ ^ 2)) := by
    rw [← withDensity_indicator measurableSet_Ioi]
    refine withDensity_congr_ae (.of_forall fun y ↦ ?_)
    by_cases hy : 0 < y
    · simp [hy]
    · simp [hy, noncentralChiSquaredPDF_eq_ofReal, noncentralChiSquaredPDFReal_of_nonpos
        (not_lt.mp hy)]
  have htarget : volume.withDensity (noncentralChiPDF k δ s) =
      (volume.restrict (Ioi 0)).withDensity fun t ↦
        ENNReal.ofReal |2 * t / s ^ 2| * noncentralChiSquaredPDF k (δ ^ 2) (φ t) := by
    rw [← withDensity_indicator measurableSet_Ioi]
    refine withDensity_congr_ae (.of_forall fun t ↦ ?_)
    by_cases ht : 0 < t
    · rw [indicator_of_mem (mem_Ioi.mpr ht), noncentralChiPDF_eq_ofReal,
        noncentralChiPDFReal_of_pos hs ht, abs_of_pos (by positivity),
        noncentralChiSquaredPDF_eq_ofReal, ENNReal.ofReal_mul (by positivity)]
    · simp [ht, noncentralChiPDF_of_nonpos (not_lt.mp ht)]
  have hchange := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
    (f := noncentralChiSquaredPDF k (δ ^ 2)) measurableSet_Ioi (by fun_prop)
    (fun t _ ↦ (hderiv t).hasDerivWithinAt) hinj
  rw [himage] at hchange
  rw [hsource, ← hchange, Measure.map_map (by fun_prop) (by fun_prop), htarget]
  -- The scaled square root inverts `φ` on the positive half-line.
  refine (Measure.map_congr ?_).trans Measure.map_id
  have hae : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), t ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hae] with t ht
  have ht' : 0 < t := ht
  simp only [Function.comp_apply, φ, id]
  rw [sqrt_sq (div_pos ht' hs).le]
  field_simp

/-- The noncentral chi law has this density at positive degree and scale. -/
theorem noncentralChiMeasure_eq_withDensity (hk : 0 < k) (hs : 0 < s) :
    noncentralChiMeasure k δ s = volume.withDensity (noncentralChiPDF k δ s) := by
  rw [noncentralChiMeasure_of_scale_pos hs, noncentralChiSquaredMeasure_eq_withDensity hk,
    map_withDensity_noncentralChiSquaredPDF hs]

/-- At degree zero and positive scale, the atom at zero has mass `exp (-δ ^ 2 / 2)` and the
density describes the remaining continuous component, including the pure-atom case `δ = 0`. -/
theorem noncentralChiMeasure_zero_degree_eq_atom_add_withDensity (δ : ℝ≥0) (hs : 0 < s) :
    noncentralChiMeasure 0 δ s =
      ENNReal.ofReal (exp (-(δ : ℝ) ^ 2 / 2)) • Measure.dirac 0 +
        volume.withDensity (noncentralChiPDF 0 δ s) := by
  rw [noncentralChiMeasure_of_scale_pos hs,
    noncentralChiSquaredMeasure_zero_degree_eq_atom_add_withDensity,
    Measure.map_add _ _ (by fun_prop), Measure.map_smul _ (by fun_prop),
    Measure.map_dirac' (by fun_prop), map_withDensity_noncentralChiSquaredPDF hs, NNReal.coe_pow,
    sqrt_zero, mul_zero]

/-- The Radon–Nikodym derivative is the density of the continuous component for every parameter
value. In particular, the atom at degree zero contributes zero to this derivative. -/
theorem rnDeriv_noncentralChiMeasure (k : ℝ) (δ : ℝ≥0) (s : ℝ) :
    (noncentralChiMeasure k δ s).rnDeriv volume =ᵐ[volume] noncentralChiPDF k δ s := by
  by_cases hs : s ≤ 0
  · have hzero : noncentralChiPDF k δ s = 0 := funext fun _ ↦ noncentralChiPDF_of_scale_nonpos hs
    rw [noncentralChiMeasure_of_scale_nonpos hs, hzero]
    simp
  replace hs : 0 < s := not_le.mp hs
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hzero : noncentralChiPDF k δ s = 0 := funext fun _ ↦ noncentralChiPDF_of_neg hk
    rw [noncentralChiMeasure_of_neg hk, hzero]
    simp
  · let := isProbabilityMeasure_noncentralChiMeasure (k := 0) (δ := δ) le_rfl hs
    have hc : volume.withDensity (noncentralChiPDF 0 δ s) ≤ noncentralChiMeasure 0 δ s := by
      rw [noncentralChiMeasure_zero_degree_eq_atom_add_withDensity δ hs]
      exact Measure.le_add_left le_rfl
    have ha : ENNReal.ofReal (exp (-(δ : ℝ) ^ 2 / 2)) • Measure.dirac 0 ≤
        noncentralChiMeasure 0 δ s := by
      rw [noncentralChiMeasure_zero_degree_eq_atom_add_withDensity δ hs]
      exact Measure.le_add_right le_rfl
    have := isFiniteMeasure_of_le _ hc
    have := isFiniteMeasure_of_le _ ha
    rw [noncentralChiMeasure_zero_degree_eq_atom_add_withDensity δ hs, add_comm]
    exact (Measure.rnDeriv_add_of_mutuallySingular _ _ _
      ((mutuallySingular_dirac 0 volume).smul _)).trans
        (Measure.rnDeriv_withDensity volume (measurable_noncentralChiPDF 0 δ s))
  · rw [noncentralChiMeasure_eq_withDensity hk hs]
    exact Measure.rnDeriv_withDensity _ (measurable_noncentralChiPDF k δ s)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a positive-degree noncentral chi law has a density. -/
theorem hasPDF_of_hasLaw_noncentralChiMeasure (hk : 0 < k) (hs : 0 < s)
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) : HasPDF X P := by
  rw [noncentralChiMeasure_eq_withDensity hk hs] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_noncentralChiPDF k δ s).aemeasurable hX

/-- The canonical density of a positive-degree noncentral chi variable agrees almost everywhere
with `noncentralChiPDF`. -/
theorem pdf_eq_noncentralChiPDF_of_hasLaw_noncentralChiMeasure (hk : 0 < k) (hs : 0 < s)
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) :
    pdf X P =ᵐ[volume] noncentralChiPDF k δ s := by
  rw [noncentralChiMeasure_eq_withDensity hk hs] at hX
  exact pdf_eq_of_hasLaw_withDensity (measurable_noncentralChiPDF k δ s).aemeasurable hX

/-- The support is empty for negative degree, the singleton zero at zero degree and
noncentrality, and `[0, ∞)` in every other case of positive scale. -/
@[simp]
theorem support_noncentralChiMeasure (k : ℝ) (δ : ℝ≥0) (hs : 0 < s) :
    (noncentralChiMeasure k δ s).support =
      if k < 0 then ∅ else if k = 0 ∧ δ = 0 then {0} else Ici 0 := by
  by_cases hkneg : k < 0
  · simp [hkneg]
  rw [ite_eq_right hkneg]
  by_cases hzero : k = 0 ∧ δ = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [chiMeasure_zero hs]
  rw [ite_eq_right hzero]
  have hk : 0 ≤ k := not_lt.mp hkneg
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici (ae_nonneg_noncentralChiMeasure k δ s)
  -- The continuous component is dominated by the law and has support `[0, ∞)`.
  have hle : volume.withDensity (noncentralChiPDF k δ s) ≤ noncentralChiMeasure k δ s := by
    rcases hk.eq_or_lt' with rfl | hk
    · rw [noncentralChiMeasure_zero_degree_eq_atom_add_withDensity δ hs]
      exact Measure.le_add_left le_rfl
    · rw [noncentralChiMeasure_eq_withDensity hk hs]
  rw [← closure_Ioi, ← Measure.support_withDensity_eq_closure (μ := volume)
    (measurable_noncentralChiPDF k δ s) isOpen_Ioi
    (support_noncentralChiPDF hk (not_and_or.mp hzero) hs)]
  exact hle.absolutelyContinuous.support_mono

end TauCeti.Probability
