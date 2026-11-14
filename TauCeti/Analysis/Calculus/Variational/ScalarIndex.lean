/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Algebra.QuadraticDiscriminant
public import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Stationarity and boundary rigidity of a scalar index form

The quadratic index form with coefficients `B` and `C` has density
`f'² + B f f' + C f²`. Polarization turns a sharp universal lower bound into stationarity.
Integration by parts and normalized power weights then determine its terminal boundary
coefficient. This supplies the scalar equality argument in reduced-length index comparison.

## Main results

* `TauCeti.scalarIndex_add_mul`: polarization of the quadratic integral.
* `TauCeti.scalarIndex_stationary`: stationarity at equality in the lower bound.
* `TauCeti.scalarIndex_boundary_rigidity`: the terminal coefficient is `1 / c + B c / 2`.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open scoped ContDiff Topology intervalIntegral

namespace TauCeti

/-- The scalar index density with mixed coefficient B and zero-order coefficient C, using the actual
derivative of the weight. -/
noncomputable def scalarIndexDensity (B C f : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv f s ^ 2 + B s * f s * deriv f s + C s * f s ^ 2

/-- The symmetric polarization of the scalar index density. -/
noncomputable def scalarMixedIndexDensity (B C f g : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv f s * deriv g s + B s / 2 * (deriv f s * g s + f s * deriv g s) +
    C s * f s * g s

/-- The scalar index quadratic form on the closed interval from zero to c. -/
noncomputable def scalarIndex (B C : ℝ → ℝ) (c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ s in 0..c, scalarIndexDensity B C f s

/-- The polarized scalar index form on the closed interval from zero to c. -/
noncomputable def scalarMixedIndex (B C : ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ s in 0..c, scalarMixedIndexDensity B C f g s

/-- The defining formula for the scalar index density. -/
theorem scalarIndexDensity_def (B C f : ℝ → ℝ) (s : ℝ) :
    scalarIndexDensity B C f s =
      deriv f s ^ 2 + B s * f s * deriv f s + C s * f s ^ 2 := by rfl

/-- The defining formula for the polarized scalar index density. -/
theorem scalarMixedIndexDensity_def (B C f g : ℝ → ℝ) (s : ℝ) :
    scalarMixedIndexDensity B C f g s =
      deriv f s * deriv g s + B s / 2 * (deriv f s * g s + f s * deriv g s) +
        C s * f s * g s := by rfl

/-- The scalar index is the integral of its density. -/
theorem scalarIndex_def (B C : ℝ → ℝ) (c : ℝ) (f : ℝ → ℝ) :
    scalarIndex B C c f = ∫ s in 0..c, scalarIndexDensity B C f s := by rfl

/-- The mixed scalar index is the integral of its density. -/
theorem scalarMixedIndex_def (B C : ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    scalarMixedIndex B C c f g = ∫ s in 0..c, scalarMixedIndexDensity B C f g s := by rfl

/-- The polarized density is symmetric in its weights. -/
theorem scalarMixedIndexDensity_comm (B C f g : ℝ → ℝ) (s : ℝ) :
    scalarMixedIndexDensity B C f g s = scalarMixedIndexDensity B C g f s := by
  unfold scalarMixedIndexDensity
  ring

/-- On the diagonal the polarized density equals the quadratic density. -/
@[simp] theorem scalarMixedIndexDensity_self (B C f : ℝ → ℝ) (s : ℝ) :
    scalarMixedIndexDensity B C f f s = scalarIndexDensity B C f s := by
  unfold scalarMixedIndexDensity scalarIndexDensity
  ring

/-- The zero weight has zero quadratic density. -/
@[simp] theorem scalarIndexDensity_zero (B C : ℝ → ℝ) (s : ℝ) :
    scalarIndexDensity B C 0 s = 0 := by
  simp [scalarIndexDensity]

/-- The polarized density vanishes when its first weight is zero. -/
@[simp] theorem scalarMixedIndexDensity_zero_left (B C g : ℝ → ℝ) (s : ℝ) :
    scalarMixedIndexDensity B C 0 g s = 0 := by
  simp [scalarMixedIndexDensity]

/-- The polarized density vanishes when its second weight is zero. -/
@[simp] theorem scalarMixedIndexDensity_zero_right (B C f : ℝ → ℝ) (s : ℝ) :
    scalarMixedIndexDensity B C f 0 s = 0 := by
  rw [scalarMixedIndexDensity_comm, scalarMixedIndexDensity_zero_left]

/-- The polarized integral is symmetric in its weights. -/
theorem scalarMixedIndex_comm (B C : ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    scalarMixedIndex B C c f g = scalarMixedIndex B C c g f := by
  unfold scalarMixedIndex
  simp_rw [scalarMixedIndexDensity_comm B C f g]

/-- On the diagonal the polarized integral equals the quadratic index. -/
@[simp] theorem scalarMixedIndex_self (B C : ℝ → ℝ) (c : ℝ) (f : ℝ → ℝ) :
    scalarMixedIndex B C c f f = scalarIndex B C c f := by
  simp [scalarMixedIndex, scalarIndex]

/-- The zero weight has zero scalar index. -/
@[simp] theorem scalarIndex_zero (B C : ℝ → ℝ) (c : ℝ) : scalarIndex B C c 0 = 0 := by
  simp [scalarIndex]

/-- The mixed index vanishes when its first weight is zero. -/
@[simp] theorem scalarMixedIndex_zero_left (B C : ℝ → ℝ) (c : ℝ) (g : ℝ → ℝ) :
    scalarMixedIndex B C c 0 g = 0 := by
  simp [scalarMixedIndex]

/-- The mixed index vanishes when its second weight is zero. -/
@[simp] theorem scalarMixedIndex_zero_right (B C : ℝ → ℝ) (c : ℝ) (f : ℝ → ℝ) :
    scalarMixedIndex B C c f 0 = 0 := by
  simp [scalarMixedIndex]

/-- The mixed density is additive in its first weight at differentiability points. -/
theorem scalarMixedIndexDensity_add_left (B C f g h : ℝ → ℝ) (s : ℝ)
    (hf : DifferentiableAt ℝ f s) (hg : DifferentiableAt ℝ g s) :
    scalarMixedIndexDensity B C (f + g) h s =
      scalarMixedIndexDensity B C f h s + scalarMixedIndexDensity B C g h s := by
  simp only [scalarMixedIndexDensity_def, Pi.add_apply, deriv_add hf hg]
  ring

/-- The mixed density is additive in its second weight at differentiability points. -/
theorem scalarMixedIndexDensity_add_right (B C f g h : ℝ → ℝ) (s : ℝ)
    (hg : DifferentiableAt ℝ g s) (hh : DifferentiableAt ℝ h s) :
    scalarMixedIndexDensity B C f (g + h) s =
      scalarMixedIndexDensity B C f g s + scalarMixedIndexDensity B C f h s := by
  rw [scalarMixedIndexDensity_comm B C f, scalarMixedIndexDensity_add_left B C g h f s hg hh,
    scalarMixedIndexDensity_comm B C g, scalarMixedIndexDensity_comm B C h]

/-- Scalar multiplication in the first weight factors out of the mixed density. -/
theorem scalarMixedIndexDensity_smul_left (B C f g : ℝ → ℝ) (s a : ℝ) :
    scalarMixedIndexDensity B C (a • f) g s = a * scalarMixedIndexDensity B C f g s := by
  simp only [scalarMixedIndexDensity_def, deriv_const_smul_field, Pi.smul_apply, smul_eq_mul]
  ring

/-- Scalar multiplication in the second weight factors out of the mixed density. -/
theorem scalarMixedIndexDensity_smul_right (B C f g : ℝ → ℝ) (s a : ℝ) :
    scalarMixedIndexDensity B C f (a • g) s = a * scalarMixedIndexDensity B C f g s := by
  rw [scalarMixedIndexDensity_comm B C f, scalarMixedIndexDensity_smul_left,
    scalarMixedIndexDensity_comm B C g]

/-- The mixed index is additive in its first weight when the summands are integrable. -/
theorem scalarMixedIndex_add_left (B C f g h : ℝ → ℝ) (c : ℝ)
    (hf : ∀ s ∈ Set.uIcc 0 c, DifferentiableAt ℝ f s)
    (hg : ∀ s ∈ Set.uIcc 0 c, DifferentiableAt ℝ g s)
    (hfi : IntervalIntegrable (scalarMixedIndexDensity B C f h) MeasureTheory.volume 0 c)
    (hgi : IntervalIntegrable (scalarMixedIndexDensity B C g h) MeasureTheory.volume 0 c) :
    scalarMixedIndex B C c (f + g) h =
      scalarMixedIndex B C c f h + scalarMixedIndex B C c g h := by
  simp only [scalarMixedIndex_def]
  rw [intervalIntegral.integral_congr (fun s hs ↦
    scalarMixedIndexDensity_add_left B C f g h s (hf s hs) (hg s hs)),
    intervalIntegral.integral_add hfi hgi]

/-- The mixed index is additive in its second weight when the summands are integrable. -/
theorem scalarMixedIndex_add_right (B C f g h : ℝ → ℝ) (c : ℝ)
    (hg : ∀ s ∈ Set.uIcc 0 c, DifferentiableAt ℝ g s)
    (hh : ∀ s ∈ Set.uIcc 0 c, DifferentiableAt ℝ h s)
    (hgi : IntervalIntegrable (scalarMixedIndexDensity B C f g) MeasureTheory.volume 0 c)
    (hhi : IntervalIntegrable (scalarMixedIndexDensity B C f h) MeasureTheory.volume 0 c) :
    scalarMixedIndex B C c f (g + h) =
      scalarMixedIndex B C c f g + scalarMixedIndex B C c f h := by
  rw [scalarMixedIndex_comm B C c f, scalarMixedIndex_add_left B C g h f c hg hh
    (by simpa only [funext (scalarMixedIndexDensity_comm B C g f)] using hgi)
    (by simpa only [funext (scalarMixedIndexDensity_comm B C h f)] using hhi),
    scalarMixedIndex_comm B C c g, scalarMixedIndex_comm B C c h]

/-- Scalar multiplication in the first weight factors out of the mixed index. -/
theorem scalarMixedIndex_smul_left (B C f g : ℝ → ℝ) (c a : ℝ) :
    scalarMixedIndex B C c (a • f) g = a * scalarMixedIndex B C c f g := by
  simp only [scalarMixedIndex_def, scalarMixedIndexDensity_smul_left,
    intervalIntegral.integral_const_mul]

/-- Scalar multiplication in the second weight factors out of the mixed index. -/
theorem scalarMixedIndex_smul_right (B C f g : ℝ → ℝ) (c a : ℝ) :
    scalarMixedIndex B C c f (a • g) = a * scalarMixedIndex B C c f g := by
  rw [scalarMixedIndex_comm B C c f, scalarMixedIndex_smul_left,
    scalarMixedIndex_comm B C c g]

/-- C¹ weights and continuous coefficients give a continuous scalar index density on an open
interval. -/
theorem continuousOn_scalarIndexDensity (B C f : ℝ → ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (scalarIndexDensity B C f) U := by
  have hd := (hf.deriv_of_isOpen hU (m := 0) (by simp)).continuousOn
  exact ((hd.pow 2).add ((hB.mul hf.continuousOn).mul hd)).add
    (hC.mul (hf.continuousOn.pow 2))

/-- The polarized index density is continuous for C¹ weights and continuous coefficients. -/
theorem continuousOn_scalarMixedIndexDensity (B C f g : ℝ → ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    ContinuousOn (scalarMixedIndexDensity B C f g) U := by
  have hdf := (hf.deriv_of_isOpen hU (m := 0) (by simp)).continuousOn
  have hdg := (hg.deriv_of_isOpen hU (m := 0) (by simp)).continuousOn
  exact ((hdf.mul hdg).add ((hB.div_const 2).mul
    ((hdf.mul hg.continuousOn).add (hf.continuousOn.mul hdg)))).add
      ((hC.mul hf.continuousOn).mul hg.continuousOn)

/-- Polarization expands the scalar index for differentiable weights with integrable
quadratic and mixed densities, with either orientation of the interval. -/
theorem scalarIndex_add_mul (B C f g : ℝ → ℝ) (c : ℝ)
    (hf : ∀ s ∈ Set.uIcc 0 c, DifferentiableAt ℝ f s)
    (hg : ∀ s ∈ Set.uIcc 0 c, DifferentiableAt ℝ g s)
    (hfi : IntervalIntegrable (scalarIndexDensity B C f) MeasureTheory.volume 0 c)
    (hgi : IntervalIntegrable (scalarIndexDensity B C g) MeasureTheory.volume 0 c)
    (hmi : IntervalIntegrable (scalarMixedIndexDensity B C f g) MeasureTheory.volume 0 c)
    (t : ℝ) :
    scalarIndex B C c (fun s ↦ f s + t * g s) = scalarIndex B C c f +
      (2 * t) * scalarMixedIndex B C c f g + t ^ 2 * scalarIndex B C c g := by
  unfold scalarIndex scalarMixedIndex
  calc
    (∫ s in 0..c, scalarIndexDensity B C (fun r ↦ f r + t * g r) s) =
        ∫ s in 0..c, scalarIndexDensity B C f s +
          (2 * t) * scalarMixedIndexDensity B C f g s + t ^ 2 * scalarIndexDensity B C g s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hfd := (hf s hs).hasDerivAt
      have hgd := (hg s hs).hasDerivAt
      have hd : deriv (fun r ↦ f r + t * g r) s = deriv f s + t * deriv g s := by
        simpa only [Pi.add_def] using (hfd.add (hgd.const_mul t)).deriv
      dsimp only [scalarIndexDensity, scalarMixedIndexDensity]
      rw [hd]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hfi.add (hmi.const_mul _)) (hgi.const_mul _),
        intervalIntegral.integral_add hfi (hmi.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- Continuous coefficients and `C¹` weights give the polarization identity. -/
theorem scalarIndex_add_mul_of_contDiffOn (B C f g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) (t : ℝ) :
    scalarIndex B C c (fun s ↦ f s + t * g s) = scalarIndex B C c f +
      (2 * t) * scalarMixedIndex B C c f g + t ^ 2 * scalarIndex B C c g := by
  have hfi : IntervalIntegrable (scalarIndexDensity B C f) MeasureTheory.volume 0 c :=
    ((continuousOn_scalarIndexDensity B C f U hU hB hC hf).mono hKU).intervalIntegrable_of_Icc hc
  have hgi : IntervalIntegrable (scalarIndexDensity B C g) MeasureTheory.volume 0 c :=
    ((continuousOn_scalarIndexDensity B C g U hU hB hC hg).mono hKU).intervalIntegrable_of_Icc hc
  have hmi : IntervalIntegrable (scalarMixedIndexDensity B C f g) MeasureTheory.volume 0 c :=
    ((continuousOn_scalarMixedIndexDensity B C f g U hU hB hC hf hg).mono hKU)
      |>.intervalIntegrable_of_Icc hc
  exact scalarIndex_add_mul B C f g c
    (fun s hs ↦ (hf.contDiffAt (hU.mem_nhds (hKU (by
      simpa only [Set.uIcc_of_le hc] using hs)))).differentiableAt (by simp))
    (fun s hs ↦ (hg.contDiffAt (hU.mem_nhds (hKU (by
      simpa only [Set.uIcc_of_le hc] using hs)))).differentiableAt (by simp))
    hfi hgi hmi t

/-- Equality in a universal scalar index lower bound makes the linear weight stationary against
every smooth weight vanishing at zero. -/
theorem scalarIndex_stationary (B C : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U) (d : ℝ)
    (hcompare : ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f U → f 0 = 0 →
      d * f c ^ 2 ≤ scalarIndex B C c f)
    (heq : scalarIndex B C c (fun s ↦ s / c) = d)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hw0 : w 0 = 0) :
    scalarMixedIndex B C c (fun s ↦ s / c) w = d * w c := by
  have hy : ContDiffOn ℝ ∞ (fun s : ℝ ↦ s / c) U := contDiffOn_id.div_const c
  have hq (t : ℝ) :
      0 ≤ (2 * (scalarMixedIndex B C c (fun s ↦ s / c) w - d * w c)) * t +
        (scalarIndex B C c w - d * w c ^ 2) * t ^ 2 := by
    have h := hcompare (fun s ↦ s / c + t * w s)
      (hy.add (contDiffOn_const.mul hw)) (by simp [hw0])
    rw [scalarIndex_add_mul_of_contDiffOn B C _ w c hc.le U hU hKU hB hC
      (hy.of_le (by simp)) (hw.of_le (by simp)) t, heq] at h
    have hcc : c / c = 1 := div_self hc.ne'
    rw [hcc] at h
    nlinarith
  have h := discrim_le_zero (a := scalarIndex B C c w - d * w c ^ 2)
    (b := 2 * (scalarMixedIndex B C c (fun s ↦ s / c) w - d * w c)) (c := 0)
    (fun t ↦ by simpa only [pow_two, add_zero, zero_add, add_comm] using hq t)
  unfold discrim at h
  nlinarith [sq_nonneg (scalarMixedIndex B C c (fun s ↦ s / c) w - d * w c)]

/-- Integration by parts separates the terminal coefficient of the linear weight from the interior
potential. -/
theorem scalarMixedIndex_linear_boundary (B C : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContDiffOn ℝ 1 B U) (hC : ContinuousOn C U)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w U) (hw0 : w 0 = 0) :
    scalarMixedIndex B C c (fun s ↦ s / c) w = (1 / c + B c / 2) * w c +
      ∫ s in 0..c, (C s - deriv B s / 2) * (s / c) * w s := by
  let Q : ℝ → ℝ := fun s ↦ (1 / c + B s / 2 * (s / c)) * w s
  have hQ : ContDiffOn ℝ 1 Q U :=
    (contDiffOn_const.add ((hB.div_const 2).mul (contDiffOn_id.div_const c))).mul
      hw
  have hQi : IntervalIntegrable (deriv Q) MeasureTheory.volume 0 c :=
    (((hQ.deriv_of_isOpen hU (m := 0) (by simp)).continuousOn).mono hKU)
      |>.intervalIntegrable_of_Icc hc.le
  have hRi : IntervalIntegrable (fun s ↦ (C s - deriv B s / 2) * (s / c) * w s)
      MeasureTheory.volume 0 c :=
    ((((hC.sub
      (((hB.deriv_of_isOpen hU (m := 0) (by simp)).continuousOn).div_const 2)).mul
      (continuousOn_id.div_const c)).mul hw.continuousOn).mono hKU)
      |>.intervalIntegrable_of_Icc hc.le
  have hder (s : ℝ) (hs : s ∈ Set.Icc 0 c) :
      scalarMixedIndexDensity B C (fun r ↦ r / c) w s =
        deriv Q s + (C s - deriv B s / 2) * (s / c) * w s := by
    have hBd := ((hB.contDiffAt (hU.mem_nhds (hKU hs))).differentiableAt (by simp)).hasDerivAt
    have hwd := ((hw.contDiffAt (hU.mem_nhds (hKU hs))).differentiableAt (by simp)).hasDerivAt
    have hyd : HasDerivAt (fun r : ℝ ↦ r / c) (1 / c) s :=
      (hasDerivAt_id s).div_const c
    have hQd := ((((hBd.div_const 2).mul hyd).const_add (1 / c)).mul hwd).deriv
    -- Q names exactly the pointwise product differentiated above.
    change deriv Q s = _ at hQd
    dsimp only [scalarMixedIndexDensity]
    rw [hQd, hyd.deriv]
    simp only [Pi.mul_apply]
    ring
  have hFTC : (∫ s in 0..c, deriv Q s) = Q c - Q 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hQi
    intro s hs
    have hs' : s ∈ Set.Icc 0 c := by simpa only [Set.uIcc_of_le hc.le] using hs
    exact ((hQ.contDiffAt (hU.mem_nhds (hKU hs'))).differentiableAt (by simp)).hasDerivAt
  unfold scalarMixedIndex
  calc
    (∫ s in 0..c, scalarMixedIndexDensity B C (fun r ↦ r / c) w s) =
        ∫ s in 0..c, deriv Q s + (C s - deriv B s / 2) * (s / c) * w s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hder s (by simpa only [Set.uIcc_of_le hc.le] using hs)
    _ = _ := by
      rw [intervalIntegral.integral_add hQi hRi, hFTC]
      simp only [Q, div_self hc.ne', mul_one, hw0, mul_zero, sub_zero]

/-- A sharp universal scalar index lower bound fixes the terminal coefficient; normalized powers
force the bounded interior error to zero. -/
theorem scalarIndex_boundary_rigidity (B C : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContDiffOn ℝ 1 B U) (hC : ContinuousOn C U) (d : ℝ)
    (hcompare : ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f U → f 0 = 0 →
      d * f c ^ 2 ≤ scalarIndex B C c f)
    (heq : scalarIndex B C c (fun s ↦ s / c) = d) :
    d = 1 / c + B c / 2 := by
  let R : ℝ → ℝ := fun s ↦ C s - deriv B s / 2
  have hR : ContinuousOn R (Set.Icc 0 c) :=
    (hC.sub
      (((hB.deriv_of_isOpen hU (m := 0) (by simp)).continuousOn).div_const 2)).mono hKU
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  have hK0 : 0 ≤ K := (norm_nonneg (R 0)).trans (hK 0 ⟨le_rfl, hc.le⟩)
  let a := d - (1 / c + B c / 2)
  have hbound (m : ℕ) : |a| ≤ K * c / ((m : ℝ) + 3) := by
    let w : ℝ → ℝ := fun s ↦ (s / c) ^ (m + 1)
    have hw : ContDiffOn ℝ ∞ w U := (contDiffOn_id.div_const c).pow (m + 1)
    have hw0 : w 0 = 0 := by simp [w]
    have hwc : w c = 1 := by simp [w, hc.ne']
    have hstat := scalarIndex_stationary B C c hc U hU hKU hB.continuousOn hC
      d hcompare heq w hw hw0
    rw [scalarMixedIndex_linear_boundary B C c hc U hU hKU hB hC w (hw.of_le (by simp)) hw0,
      hwc, mul_one, mul_one] at hstat
    have hpower : (fun s ↦ (C s - deriv B s / 2) * (s / c) * w s) =
        fun s ↦ R s * (s / c) ^ (m + 2) := by
      funext s
      dsimp only [R, w]
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring
    rw [hpower] at hstat
    have ha : a = ∫ s in 0..c, R s * (s / c) ^ (m + 2) := by
      dsimp only [a]
      linarith
    have hki : IntervalIntegrable (fun s : ℝ ↦ K * (s / c) ^ (m + 2))
        MeasureTheory.volume 0 c :=
      ((continuous_const.mul ((continuous_id.div_const c).pow (m + 2))).intervalIntegrable 0 c)
    have hi := intervalIntegral.norm_integral_le_of_norm_le hc.le
      (f := fun s ↦ R s * (s / c) ^ (m + 2))
      (Filter.Eventually.of_forall (fun s (hs : s ∈ Set.Ioc 0 c) ↦ by
        have hp : 0 ≤ (s / c) ^ (m + 2) := pow_nonneg (div_nonneg hs.1.le hc.le) _
        rw [norm_mul, Real.norm_of_nonneg hp]
        exact mul_le_mul_of_nonneg_right (hK s ⟨hs.1.le, hs.2⟩) hp)) hki
    rw [← ha, Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_div_pow c (m + 2)] at hi
    simpa only [Nat.cast_add, Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num,
      add_assoc, mul_div_assoc] using hi
  have ha0 : a = 0 := by
    by_contra hne
    have hapos : 0 < |a| := abs_pos.mpr hne
    obtain ⟨m, hm⟩ := exists_nat_gt (K * c / |a|)
    have hlt := (div_lt_iff₀ hapos).mp hm
    have hle := (le_div_iff₀ (by positivity : 0 < (m : ℝ) + 3)).mp (hbound m)
    nlinarith
  dsimp only [a] at ha0
  linarith

end TauCeti
