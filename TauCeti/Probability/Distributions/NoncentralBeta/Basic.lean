/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
import TauCeti.Probability.Distributions.Beta.Measurability
import TauCeti.Probability.Distributions.Gamma.Beta

/-!
# Noncentral Beta laws

For shapes `a ≥ 0` and `b > 0` and noncentrality `l ≥ 0`, the noncentral Beta law is the law of
`U / (U + V)` for independent `U` and `V`, where `U` is noncentral chi-squared with degree `2 * a`
and noncentrality `l` and `V` is central chi-squared with degree `2 * b`. Invalid shapes give the
zero measure. The numerator shape `a = 0` is allowed: the law then has an atom at zero.

Since the noncentral chi-squared law is a Poisson mixture of central chi-squared laws, and a
ratio `U / (U + V)` of independent central chi-squared variables is Beta, the noncentral Beta law
is the Poisson mixture, with weights of rate `l / 2`, of the laws
`noncentralBetaComponent (a + j) b`. Each component is `betaMeasure (a + j) b` for positive
first shape, and the point mass at zero when `a + j = 0`. This presentation is the route to the
density, distribution function, quantile and moments of the family.

## Main definitions

* `TauCeti.Probability.noncentralBetaComponent` — the Beta law extended by the point mass at zero
  at first shape zero.
* `TauCeti.Probability.noncentralBetaMeasure` — the noncentral Beta law.

## Main results

* `TauCeti.Probability.map_div_add_chiSquaredMeasure` — the ratio `U / (U + V)` of
  independent central chi-squared variables has law `noncentralBetaComponent`.
* `TauCeti.Probability.isProbabilityMeasure_noncentralBetaMeasure` — normalization.
* `TauCeti.Probability.noncentralBetaMeasure_eq_sum` and
  `TauCeti.Probability.noncentralBetaMeasure_eq_bind` — the Poisson mixture.
* `TauCeti.Probability.noncentralBetaMeasure_zero_noncentrality` — zero noncentrality gives the
  central component.
* `TauCeti.Probability.noncentralBetaMeasure_zero_shape` and
  `TauCeti.Probability.noncentralBetaMeasure_zero_shape_singleton` — at first shape zero, the
  atom `exp (-l / 2)` at zero plus a Poisson mixture of Beta laws.
* `TauCeti.Probability.absolutelyContinuous_noncentralBetaMeasure` — at positive first shape the
  law has a density with respect to Lebesgue measure.
* `TauCeti.Probability.support_noncentralBetaMeasure` — away from the Dirac case the topological
  support is `[0, 1]`.
* `TauCeti.Probability.measurable_noncentralBetaMeasure` — joint parameter measurability.
* `TauCeti.Probability.hasLaw_noncentralBeta_of_noncentralChiSquared` — the random-variable form
  of the defining ratio.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {a b : ℝ} {l : ℝ≥0}

/-! ### The mixture components -/

/-- The components of the noncentral Beta mixture: `betaMeasure a b` for positive first shape `a`,
the point mass at zero for `a = 0`, and the zero measure for negative `a`. -/
def noncentralBetaComponent (a b : ℝ) : Measure ℝ :=
  if a = 0 then Measure.dirac 0 else if 0 < a then betaMeasure a b else 0

/-- At positive first shape the component is the Beta law. -/
@[simp]
theorem noncentralBetaComponent_of_pos (ha : 0 < a) (b : ℝ) :
    noncentralBetaComponent a b = betaMeasure a b := by
  rw [noncentralBetaComponent, ite_eq_right ha.ne', ite_eq_left ha]

/-- At first shape zero the component is the point mass at zero. -/
@[simp]
theorem noncentralBetaComponent_zero (b : ℝ) : noncentralBetaComponent 0 b = Measure.dirac 0 := by
  rw [noncentralBetaComponent, ite_eq_left rfl]

/-- At negative first shape the component is the zero measure. -/
@[simp]
theorem noncentralBetaComponent_of_neg (ha : a < 0) (b : ℝ) : noncentralBetaComponent a b = 0 := by
  rw [noncentralBetaComponent, ite_eq_right ha.ne, ite_eq_right (not_lt.mpr ha.le)]

/-- The component is a probability measure for nonnegative first shape and positive second
shape. -/
theorem isProbabilityMeasure_noncentralBetaComponent (ha : 0 ≤ a) (hb : 0 < b) :
    IsProbabilityMeasure (noncentralBetaComponent a b) := by
  rcases ha.eq_or_lt' with rfl | ha
  · rw [noncentralBetaComponent_zero]
    infer_instance
  · rw [noncentralBetaComponent_of_pos ha]
    exact isProbabilityMeasureBeta ha hb

/-- Every component is carried by the closed unit interval. -/
theorem ae_mem_Icc_noncentralBetaComponent (a b : ℝ) :
    ∀ᵐ x ∂noncentralBetaComponent a b, x ∈ Icc (0 : ℝ) 1 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha]
  · simp
  · rw [noncentralBetaComponent_of_pos ha]
    exact ae_mem_Icc_betaMeasure a b

/-- The components are jointly measurable in the two shapes. -/
@[fun_prop]
theorem measurable_noncentralBetaComponent :
    Measurable fun p : ℝ × ℝ ↦ noncentralBetaComponent p.1 p.2 := by
  unfold noncentralBetaComponent
  exact Measurable.ite (measurable_fst (measurableSet_singleton 0)) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_betaMeasure
      measurable_const)

/-- The ratio `U / (U + V)` of independent central chi-squared variables with degrees `2 * a` and
`2 * b` has law `noncentralBetaComponent a b`. For `a > 0` this is the Beta law; for `a = 0` the
numerator vanishes almost surely; for `a < 0` both sides are zero. -/
theorem map_div_add_chiSquaredMeasure (a : ℝ) (hb : 0 < b) :
    ((chiSquaredMeasure (2 * a)).prod (chiSquaredMeasure (2 * b))).map
        (fun z ↦ z.1 / (z.1 + z.2)) = noncentralBetaComponent a b := by
  let _ := isProbabilityMeasure_chiSquaredMeasure (mul_pos two_pos hb).le
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha, chiSquaredMeasure_of_neg (by linarith : 2 * a < 0)]
  · rw [mul_zero, chiSquaredMeasure_zero, Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop)]
    simp [Function.comp_def, Measure.map_const]
  · rw [noncentralBetaComponent_of_pos ha, chiSquaredMeasure_eq_gammaMeasure (by positivity),
      chiSquaredMeasure_eq_gammaMeasure (by positivity), mul_div_cancel_left₀ _ two_ne_zero,
      mul_div_cancel_left₀ _ two_ne_zero]
    exact map_div_add_gammaMeasure ha hb one_half_pos

/-! ### The noncentral Beta law -/

/-- The noncentral Beta law with shapes `a` and `b` and noncentrality `l`: the law of
`U / (U + V)` for independent `U` with law `noncentralChiSquaredMeasure (2 * a) l` and `V` with law
`chiSquaredMeasure (2 * b)`. It is the zero measure unless `0 ≤ a` and `0 < b`. -/
def noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) : Measure ℝ :=
  if 0 ≤ a ∧ 0 < b then
    ((noncentralChiSquaredMeasure (2 * a) l).prod (chiSquaredMeasure (2 * b))).map
      (fun z ↦ z.1 / (z.1 + z.2))
  else 0

/-- For valid shapes, the noncentral Beta law is the defining ratio pushforward. -/
theorem noncentralBetaMeasure_eq_map (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    noncentralBetaMeasure a b l =
      ((noncentralChiSquaredMeasure (2 * a) l).prod (chiSquaredMeasure (2 * b))).map
        (fun z ↦ z.1 / (z.1 + z.2)) := by
  rw [noncentralBetaMeasure, ite_eq_left ⟨ha, hb⟩]

/-- For invalid shapes, the noncentral Beta measure is zero. -/
@[simp]
theorem noncentralBetaMeasure_of_not (h : ¬ (0 ≤ a ∧ 0 < b)) (l : ℝ≥0) :
    noncentralBetaMeasure a b l = 0 := by
  rw [noncentralBetaMeasure, ite_eq_right h]

/-- The noncentral Beta law is a probability measure for valid shapes, including `a = 0`. -/
theorem isProbabilityMeasure_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    IsProbabilityMeasure (noncentralBetaMeasure a b l) := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure (mul_nonneg zero_le_two ha) l
  let _ := isProbabilityMeasure_chiSquaredMeasure (mul_pos two_pos hb).le
  rw [noncentralBetaMeasure_eq_map ha hb]
  infer_instance

/-- The noncentral Beta measure is a probability measure exactly when its shapes are valid. -/
@[simp]
theorem isProbabilityMeasure_noncentralBetaMeasure_iff :
    IsProbabilityMeasure (noncentralBetaMeasure a b l) ↔ 0 ≤ a ∧ 0 < b := by
  refine ⟨fun h ↦ ?_, fun h ↦ isProbabilityMeasure_noncentralBetaMeasure h.1 h.2 l⟩
  by_contra hab
  rw [noncentralBetaMeasure_of_not hab] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl

/-- The noncentral Beta law is a finite measure for every choice of parameters. -/
instance isFiniteMeasure_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) :
    IsFiniteMeasure (noncentralBetaMeasure a b l) := by
  by_cases h : 0 ≤ a ∧ 0 < b
  · let _ := isProbabilityMeasure_noncentralBetaMeasure h.1 h.2 l
    infer_instance
  · rw [noncentralBetaMeasure_of_not h]
    infer_instance

/-! ### The Poisson mixture -/

/-- The noncentral Beta law is the Poisson-weighted sum, with weights of rate `l / 2`, of the
components `noncentralBetaComponent (a + j) b`. -/
theorem noncentralBetaMeasure_eq_sum (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    noncentralBetaMeasure a b l = Measure.sum fun j : ℕ ↦
      poissonMeasure (l / 2) {j} • noncentralBetaComponent (a + j) b := by
  let _ := isProbabilityMeasure_chiSquaredMeasure (mul_pos two_pos hb).le
  rw [noncentralBetaMeasure_eq_map ha hb,
    noncentralChiSquaredMeasure_eq_sum (mul_nonneg zero_le_two ha), Measure.prod_sum_left,
    Measure.map_sum (by fun_prop)]
  congr 1
  funext j
  rw [Measure.prod_smul_left, Measure.map_smul _ (by fun_prop), ← mul_add,
    map_div_add_chiSquaredMeasure _ hb]

/-- The noncentral Beta law as a `Measure.bind` mixture of its components over the Poisson law
of rate `l / 2`. -/
theorem noncentralBetaMeasure_eq_bind (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    noncentralBetaMeasure a b l =
      (poissonMeasure (l / 2)).bind fun j ↦ noncentralBetaComponent (a + j) b := by
  ext s hs
  rw [noncentralBetaMeasure_eq_sum ha hb, Measure.sum_apply _ hs,
    Measure.bind_apply hs (.of_discrete), lintegral_countable']
  simp only [Measure.smul_apply, smul_eq_mul, mul_comm]

/-- Set evaluation as an extended-real Poisson series; the formula holds for every set. -/
theorem noncentralBetaMeasure_apply (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (s : Set ℝ) :
    noncentralBetaMeasure a b l s =
      ∑' j : ℕ, poissonMeasure (l / 2) {j} * noncentralBetaComponent (a + j) b s := by
  rw [noncentralBetaMeasure_eq_sum ha hb, Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Nonnegative integration against the noncentral Beta law can be performed component by
component, without measurability, finiteness or integrability assumptions on the observable. -/
theorem lintegral_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂noncentralBetaMeasure a b l =
      ∑' j : ℕ, poissonMeasure (l / 2) {j} * ∫⁻ x, f x ∂noncentralBetaComponent (a + j) b := by
  rw [noncentralBetaMeasure_eq_sum ha hb, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

/-- At zero noncentrality the noncentral Beta law is its central component: `betaMeasure a b` for
`a > 0` and the point mass at zero for `a = 0`. -/
@[simp]
theorem noncentralBetaMeasure_zero_noncentrality (a : ℝ) (hb : 0 < b) :
    noncentralBetaMeasure a b 0 = noncentralBetaComponent a b := by
  rcases lt_or_ge a 0 with ha | ha
  · simp [ha]
  ext s hs
  rw [noncentralBetaMeasure_apply ha hb, tsum_eq_single 0]
  · simp [poissonMeasure_singleton]
  · intro j hj
    simp [poissonMeasure_singleton, hj]

/-- At first shape zero, the Poisson count zero contributes the atom at zero, of mass
`exp (-l / 2)`, and every positive count contributes a Beta law. -/
theorem noncentralBetaMeasure_zero_shape (hb : 0 < b) (l : ℝ≥0) :
    noncentralBetaMeasure 0 b l =
      ENNReal.ofReal (exp (-(l : ℝ) / 2)) • Measure.dirac 0 +
        Measure.sum (fun j : ℕ ↦ poissonMeasure (l / 2) {j + 1} • betaMeasure (j + 1) b) := by
  ext s hs
  rw [noncentralBetaMeasure_apply le_rfl hb, Measure.add_apply, Measure.sum_apply _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  simp only [Measure.smul_apply, smul_eq_mul, CharP.cast_eq_zero, add_zero,
    noncentralBetaComponent_zero, zero_add, Nat.cast_add, Nat.cast_one]
  congr 1
  · simp [poissonMeasure_singleton, NNReal.coe_div, neg_div]
  · exact tsum_congr fun j ↦ by rw [noncentralBetaComponent_of_pos (by positivity)]

/-- At first shape zero, the atom at zero has mass `exp (-l / 2)`, including mass one at
`l = 0`. -/
@[simp]
theorem noncentralBetaMeasure_zero_shape_singleton (hb : 0 < b) (l : ℝ≥0) :
    noncentralBetaMeasure 0 b l {0} = ENNReal.ofReal (exp (-(l : ℝ) / 2)) := by
  rw [noncentralBetaMeasure_zero_shape hb, Measure.add_apply,
    Measure.sum_apply _ (measurableSet_singleton 0)]
  have hzero (j : ℕ) : betaMeasure ((j : ℝ) + 1) b {0} = 0 :=
    (betaMeasure_eq_withDensity_ofReal _ b ▸ withDensity_absolutelyContinuous _ _)
      (measure_singleton 0)
  simp [Measure.smul_apply, hzero]

/-! ### Support and absolute continuity -/

/-- A noncentral Beta variable lies in the closed unit interval almost surely, for every choice
of parameters. -/
theorem ae_mem_Icc_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) :
    ∀ᵐ x ∂noncentralBetaMeasure a b l, x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : 0 ≤ a ∧ 0 < b
  · rw [noncentralBetaMeasure_eq_sum h.1 h.2]
    exact Measure.ae_sum_iff' measurableSet_Icc |>.2 fun j ↦
      Measure.ae_smul_measure (ae_mem_Icc_noncentralBetaComponent _ b) _
  · simp [noncentralBetaMeasure_of_not h]

/-- At positive first shape, a noncentral Beta variable lies in the open unit interval almost
surely. -/
theorem ae_mem_Ioo_noncentralBetaMeasure (ha : 0 < a) (b : ℝ) (l : ℝ≥0) :
    ∀ᵐ x ∂noncentralBetaMeasure a b l, x ∈ Ioo (0 : ℝ) 1 := by
  by_cases hb : 0 < b
  · rw [noncentralBetaMeasure_eq_sum ha.le hb]
    refine Measure.ae_sum_iff' measurableSet_Ioo |>.2 fun j ↦ Measure.ae_smul_measure ?_ _
    rw [noncentralBetaComponent_of_pos (by positivity)]
    exact ae_mem_Ioo_betaMeasure _ b
  · simp [noncentralBetaMeasure_of_not (fun h : 0 ≤ a ∧ 0 < b ↦ hb h.2)]

/-- At positive first shape, the noncentral Beta law is absolutely continuous with respect to
Lebesgue measure. -/
theorem absolutelyContinuous_noncentralBetaMeasure (ha : 0 < a) (b : ℝ) (l : ℝ≥0) :
    noncentralBetaMeasure a b l ≪ volume := by
  by_cases hb : 0 < b
  · rw [noncentralBetaMeasure_eq_sum ha.le hb]
    refine Measure.absolutelyContinuous_sum_left fun j ↦
      Measure.AbsolutelyContinuous.smul_left ?_ _
    rw [noncentralBetaComponent_of_pos (by positivity), betaMeasure_eq_withDensity_ofReal]
    exact withDensity_absolutelyContinuous _ _
  · simp [noncentralBetaMeasure_of_not (fun h : 0 ≤ a ∧ 0 < b ↦ hb h.2)]

/-- At positive first shape, the noncentral Beta law has no atoms. -/
theorem nullSingletonClass_noncentralBetaMeasure (ha : 0 < a) (b : ℝ) (l : ℝ≥0) :
    NullSingletonClass (noncentralBetaMeasure a b l) :=
  ⟨fun x ↦ absolutelyContinuous_noncentralBetaMeasure ha b l (measure_singleton x)⟩

/-- Every valid law other than the Dirac law at `a = l = 0` dominates a positive-weight Beta
component with positive first shape. -/
theorem exists_smul_betaMeasure_le_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b)
    (hne : a ≠ 0 ∨ l ≠ 0) :
    ∃ j : ℕ, 0 < a + j ∧ poissonMeasure (l / 2) {j} ≠ 0 ∧
      poissonMeasure (l / 2) {j} • betaMeasure (a + j) b ≤ noncentralBetaMeasure a b l := by
  have hle (j : ℕ) (hj : 0 < a + j) :
      poissonMeasure (l / 2) {j} • betaMeasure (a + j) b ≤ noncentralBetaMeasure a b l := by
    rw [noncentralBetaMeasure_eq_sum ha hb, ← noncentralBetaComponent_of_pos hj]
    exact Measure.le_sum (fun i : ℕ ↦
      poissonMeasure (l / 2) {i} • noncentralBetaComponent (a + i) b) j
  rcases hne with ha' | hl
  · have h0 : 0 < a + (0 : ℕ) := by simpa using lt_of_le_of_ne ha (Ne.symm ha')
    refine ⟨0, h0, ?_, hle 0 h0⟩
    simp [poissonMeasure_singleton, exp_pos]
  · have h1 : 0 < a + (1 : ℕ) := by positivity
    refine ⟨1, h1, ?_, hle 1 h1⟩
    rw [poissonMeasure_singleton, ENNReal.ofReal_ne_zero_iff]
    have : 0 < (l : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hl)
    positivity

/-- Away from the Dirac law at `a = l = 0`, the topological support of a valid noncentral Beta
law is the closed unit interval. -/
@[simp]
theorem support_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (hne : a ≠ 0 ∨ l ≠ 0) :
    (noncentralBetaMeasure a b l).support = Icc 0 1 := by
  apply Set.Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Icc (ae_mem_Icc_noncentralBetaMeasure a b l)
  · obtain ⟨j, hj, hw, hle⟩ := exists_smul_betaMeasure_le_noncentralBetaMeasure ha hb hne
    have hac := (Measure.absolutelyContinuous_smul hw).trans hle.absolutelyContinuous
    rw [← support_betaMeasure hj hb]
    exact hac.support_mono

/-! ### Parameter measurability -/

/-- The full totalized noncentral Beta family is jointly measurable in its two shapes and its
noncentrality. -/
@[fun_prop]
theorem measurable_noncentralBetaMeasure :
    Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ noncentralBetaMeasure p.1 p.2.1 p.2.2 := by
  have hseries : Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ Measure.sum fun j : ℕ ↦
      poissonMeasure (p.2.2 / 2) {j} • noncentralBetaComponent (p.1 + j) p.2.1 := by
    apply Measure.measurable_measure.2
    intro s hs
    simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    exact Measurable.tsum fun j ↦
      ((Measure.measurable_coe (measurableSet_singleton j)).comp
        (measurable_poissonMeasure.comp (measurable_snd.snd.div_const 2))).mul
        ((Measure.measurable_coe hs).comp (measurable_noncentralBetaComponent.comp
          ((measurable_fst.add_const (j : ℝ)).prodMk measurable_snd.fst)))
  have hvalid : MeasurableSet {p : ℝ × ℝ × ℝ≥0 | 0 ≤ p.1 ∧ 0 < p.2.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd.fst)
  have h : Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ if 0 ≤ p.1 ∧ 0 < p.2.1 then
      Measure.sum (fun j : ℕ ↦ poissonMeasure (p.2.2 / 2) {j} •
        noncentralBetaComponent (p.1 + j) p.2.1) else 0 :=
    Measurable.ite hvalid hseries measurable_const
  convert h using 1
  funext p
  by_cases hp : 0 ≤ p.1 ∧ 0 < p.2.1
  · simp [hp, noncentralBetaMeasure_eq_sum hp.1 hp.2]
  · simp [hp]

/-! ### Random-variable forms -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ}

/-- If `X` is noncentral chi-squared with degree `2 * a` and noncentrality `l`, and `Y` is an
independent central chi-squared variable with degree `2 * b`, then `X / (X + Y)` has the
noncentral Beta law. -/
theorem hasLaw_noncentralBeta_of_noncentralChiSquared (ha : 0 ≤ a) (hb : 0 < b)
    (hXY : IndepFun X Y P) (hX : HasLaw X (noncentralChiSquaredMeasure (2 * a) l) P)
    (hY : HasLaw Y (chiSquaredMeasure (2 * b)) P) :
    HasLaw (fun ω ↦ X ω / (X ω + Y ω)) (noncentralBetaMeasure a b l) P := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure (mul_nonneg zero_le_two ha) l
  let _ := isProbabilityMeasure_chiSquaredMeasure (mul_pos two_pos hb).le
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hratio : HasLaw (fun z : ℝ × ℝ ↦ z.1 / (z.1 + z.2)) (noncentralBetaMeasure a b l)
      ((noncentralChiSquaredMeasure (2 * a) l).prod (chiSquaredMeasure (2 * b))) :=
    ⟨by fun_prop, (noncentralBetaMeasure_eq_map ha hb l).symm⟩
  exact hratio.fun_comp (hXY.hasLaw_prod hX hY)

/-- A variable with a noncentral Beta law of positive first shape has a probability density
function with respect to Lebesgue measure. -/
theorem hasPDF_of_hasLaw_noncentralBetaMeasure (ha : 0 < a)
    (hX : HasLaw X (noncentralBetaMeasure a b l) P) : HasPDF X P :=
  ⟨hX.aemeasurable, by rw [hX.map_eq]; infer_instance,
    hX.map_eq ▸ absolutelyContinuous_noncentralBetaMeasure ha b l⟩

end TauCeti.Probability
