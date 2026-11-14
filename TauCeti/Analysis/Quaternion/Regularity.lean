/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.Analysis.Quaternion.Forms
public import TauCeti.Analysis.Quaternion.Kernel
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Basic
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Quaternion.Analytic
import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
import TauCeti.Analysis.Quaternion.Reflection

/-!
# Real analyticity, smoothness, and uniqueness of Fueter regular functions

Every function that is pointwise left or right Fueter regular on an open subset of `ℍ` is real
analytic on neighbourhoods there (`LeftFueterOn.analyticOnNhd`, `RightFueterOn.analyticOnNhd`),
hence smooth of class `C^ω` and `C^∞` (`LeftFueterOn.contDiffOn`, `RightFueterOn.contDiffOn`), even
though `LeftFueterOn` and `RightFueterOn` assume only pointwise real Fréchet differentiability and
the first-order Fueter equation.

For a coordinate box `dq '' Icc a b`, `boxBoundarySum` writes the left and right Cauchy–Fueter
boundary potentials as finite sums over the eight oriented three-dimensional faces `Fin 4 × Bool`
of compact-domain Bochner integrals against `cauchyFueterKernel`. Applying
`hasFPowerSeriesOnBall_sum_integral_cauchyFueterKernel_mul` and its right-hand counterpart gives a
quantitative `HasFPowerSeriesOnBall` expansion of both box boundary potentials on the ball of
radius `(√2 - 1) * δ` around any point `q₀` at Euclidean distance at least `δ > 0` from all eight
faces.

When `f` is continuous on the closed box and left Fueter regular in its open interior, and
`dq x₀` lies at coordinate distance at least `δ > 0` from every face, the ball of radius
`(√2 - 1) * δ` around `dq x₀` lies strictly inside the open box because `√2 - 1 < 1`. On that
ball `left_cauchyFueter_box` identifies `f` with `(2π²)⁻¹` times the left box boundary potential,
yielding a `HasFPowerSeriesOnBall` for `f` itself at `dq x₀` of radius `(√2 - 1) * δ`
(`LeftFueterOn.exists_hasFPowerSeriesOnBall_of_box`). Inscribing the cube of half-side `R / 2` in
a closed Euclidean ball `closedBall q₀ R` gives radius `(√2 - 1) * (R / 2)` for any function left
Fueter regular on `closedBall q₀ R` (`LeftFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall`).
All right-sided counterparts follow with the exact same radii through the reflection
`q ↦ star (f (star q))` (`RightFueterOn.star_star`), the reflected coordinate boxes
(`image_star_image_dq_Icc`, `image_star_image_dq_pi_Ioo`), and the real linear isometry
`starₗᵢ ℝ`.

Combining real analyticity with the analytic identity principle yields the uniqueness principle on
preconnected open sets: two left (or right) Fueter regular functions that agree on a nonempty open
subset, or share all iterated real Fréchet derivatives at one point, coincide throughout the
preconnected open domain. Unlike in one complex variable, agreement on a set with accumulation
points does not suffice in four real dimensions: `q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ)` is both left and
right Fueter regular on `ℍ` and vanishes on the two-dimensional subspace
`{q | q.re = 0 ∧ q.imI = 0}`, every point of which is an accumulation point, without vanishing
identically.

## Main declarations

* `TauCeti.exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul`,
  `TauCeti.exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel`: quantitative
  `HasFPowerSeriesOnBall` expansions on `eball q₀ ((√2 - 1) * δ)` for left and right Cauchy–Fueter
  box boundary potentials.
* `TauCeti.analyticAt_boxBoundarySum_cauchyFueterKernel_mul`,
  `TauCeti.analyticAt_boxBoundarySum_mul_cauchyFueterKernel`,
  `TauCeti.analyticOnNhd_boxBoundarySum_cauchyFueterKernel_mul`,
  `TauCeti.analyticOnNhd_boxBoundarySum_mul_cauchyFueterKernel`: real analyticity of left and right
  box boundary potentials away from the faces, and in particular on the open box.
* `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall_of_box`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall_of_box`,
  `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall`: quantitative power-series
  expansions of Fueter regular functions on boxes and closed balls.
* `TauCeti.LeftFueterOn.analyticAt`, `TauCeti.RightFueterOn.analyticAt`,
  `TauCeti.LeftFueterOn.analyticOnNhd`, `TauCeti.RightFueterOn.analyticOnNhd`: real analyticity of
  left and right Fueter regular functions.
* `TauCeti.LeftFueterOn.contDiffAt`, `TauCeti.RightFueterOn.contDiffAt`,
  `TauCeti.LeftFueterOn.contDiffOn`, `TauCeti.RightFueterOn.contDiffOn`: `C^n` (including `C^∞` and
  `C^ω`) smoothness of left and right Fueter regular functions.
* `TauCeti.LeftFueterOn.eqOn_of_isPreconnected_of_eqOn_open`,
  `TauCeti.RightFueterOn.eqOn_of_isPreconnected_of_eqOn_open`,
  `TauCeti.LeftFueterOn.eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.RightFueterOn.eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.LeftFueterOn.eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq`,
  `TauCeti.RightFueterOn.eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq`: uniqueness principles
  for left and right Fueter regular functions on preconnected open sets.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9 and the following remark.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set Topology
open scoped ContDiff ENNReal NNReal Pointwise

namespace TauCeti

open TauCeti.Quaternion

/-! ### Private face-chart helpers -/

/-- The compact parameter domain of the oriented face `(i, side)` of the coordinate box
`Icc a b`. -/
private abbrev BoxFaceDomain (a b : Fin 4 → ℝ) (p : Fin 4 × Bool) : Type :=
  ↥(Icc (a ∘ p.1.succAbove) (b ∘ p.1.succAbove))

/-- Continuous parametrization of the face `(p.1, p.2)` of `dq '' Icc a b` (`true` for the front
face at `b p.1`, `false` for the back face at `a p.1`). -/
private noncomputable def boxFaceChart (a b : Fin 4 → ℝ) (p : Fin 4 × Bool) :
    C(BoxFaceDomain a b p, ℍ) :=
  ⟨fun z ↦ dq (p.1.insertNth (cond p.2 (b p.1) (a p.1)) z.1),
    dq.continuous.comp (continuous_const.finInsertNth p.1 continuous_subtype_val)⟩

private theorem boxFaceChart_mem_image_Icc {a b : Fin 4 → ℝ} (hab : a ≤ b) (p : Fin 4 × Bool)
    (z : BoxFaceDomain a b p) : boxFaceChart a b p z ∈ dq '' Icc a b :=
  mem_image_of_mem dq (Fin.insertNth_mem_Icc.mpr ⟨by cases p.2 <;> simp [hab p.1], z.2⟩)

private theorem integrable_comp_boxFaceChart {a b : Fin 4 → ℝ} (hab : a ≤ b) {g : ℍ → ℍ}
    (hg : ContinuousOn g (dq '' Icc a b)) (p : Fin 4 × Bool) :
    Integrable (fun z : BoxFaceDomain a b p ↦ g (boxFaceChart a b p z))
      (Measure.comap Subtype.val volume) :=
  (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp <|
    (hg.comp (dq.continuous.comp (continuous_const.finInsertNth p.1 continuous_id)).continuousOn
      fun x hx ↦ boxFaceChart_mem_image_Icc hab p ⟨x, hx⟩).integrableOn_Icc

private theorem boxBoundarySum_comp_dq_eq_sum (a b : Fin 4 → ℝ) (G : Fin 4 → ℍ → ℍ) :
    boxBoundarySum a b (fun i x ↦ G i (dq x)) =
      ∑ p : Fin 4 × Bool,
        ∫ z : BoxFaceDomain a b p,
          (cond p.2 (1 : ℝ) (-1)) • G p.1 (boxFaceChart a b p z)
          ∂Measure.comap Subtype.val volume := by
  rw [Fintype.sum_prod_type, boxBoundarySum_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fintype.sum_bool]
  dsimp only [BoxFaceDomain, boxFaceChart, ContinuousMap.coe_mk]
  simp only [Bool.cond_true, Bool.cond_false, one_smul, neg_one_smul]
  rw [integral_subtype_comap measurableSet_Icc (fun x ↦ G i (dq (i.insertNth (b i) x))),
    integral_subtype_comap measurableSet_Icc (fun x ↦ -G i (dq (i.insertNth (a i) x))),
    integral_neg, ← sub_eq_add_neg]

private theorem boxBoundarySum_cauchyFueterKernel_mul_eq_sum (a b : Fin 4 → ℝ) (f : ℍ → ℍ)
    (q : ℍ) :
    boxBoundarySum a b (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)) =
      ∑ p : Fin 4 × Bool,
        ∫ z : BoxFaceDomain a b p,
          cauchyFueterKernel (boxFaceChart a b p z) q *
            ((cond p.2 (1 : ℝ) (-1)) • (dq (Pi.single p.1 1) * f (boxFaceChart a b p z)))
          ∂Measure.comap Subtype.val volume := by
  simpa only [mul_assoc, mul_smul_comm] using
    boxBoundarySum_comp_dq_eq_sum a b
      (fun i y ↦ cauchyFueterKernel y q * dq (Pi.single i 1) * f y)

private theorem boxBoundarySum_mul_cauchyFueterKernel_eq_sum (a b : Fin 4 → ℝ) (f : ℍ → ℍ)
    (q : ℍ) :
    boxBoundarySum a b (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q) =
      ∑ p : Fin 4 × Bool,
        ∫ z : BoxFaceDomain a b p,
          ((cond p.2 (1 : ℝ) (-1)) • (f (boxFaceChart a b p z) * dq (Pi.single p.1 1))) *
            cauchyFueterKernel (boxFaceChart a b p z) q
          ∂Measure.comap Subtype.val volume := by
  simpa only [smul_mul_assoc] using
    boxBoundarySum_comp_dq_eq_sum a b
      (fun i y ↦ f y * dq (Pi.single i 1) * cauchyFueterKernel y q)

private theorem le_norm_boxFaceChart_sub {a b : Fin 4 → ℝ} {q₀ : ℍ} {δ : ℝ}
    (hδ : ∀ i : Fin 4, ∀ z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      δ ≤ ‖dq (i.insertNth (a i) z) - q₀‖ ∧ δ ≤ ‖dq (i.insertNth (b i) z) - q₀‖)
    (p : Fin 4 × Bool) (z : BoxFaceDomain a b p) :
    δ ≤ ‖boxFaceChart a b p z - q₀‖ := by
  rcases p with ⟨i, (_ | _)⟩
  · exact (hδ i z.1 z.2).1
  · exact (hδ i z.1 z.2).2

private theorem boxFaceChart_ne_of_pos {a b : Fin 4 → ℝ} {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ i : Fin 4, ∀ z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      δ ≤ ‖dq (i.insertNth (a i) z) - q₀‖ ∧ δ ≤ ‖dq (i.insertNth (b i) z) - q₀‖)
    (p : Fin 4 × Bool) (z : BoxFaceDomain a b p) :
    boxFaceChart a b p z ≠ q₀ := by
  intro h
  have hd := le_norm_boxFaceChart_sub hδ p z
  simp only [h, sub_self, norm_zero] at hd
  linarith

private theorem notMem_iUnion_range_boxFaceChart {a b : Fin 4 → ℝ} {q₀ : ℍ}
    (hq₀ : ∀ i : Fin 4, ∀ z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      dq (i.insertNth (a i) z) ≠ q₀ ∧ dq (i.insertNth (b i) z) ≠ q₀) :
    q₀ ∉ ⋃ p ∈ (Finset.univ : Finset (Fin 4 × Bool)), range (boxFaceChart a b p) := by
  intro h
  simp only [mem_iUnion, Finset.mem_univ, mem_range, exists_prop, true_and] at h
  rcases h with ⟨⟨i, (_ | _)⟩, z, hzq⟩
  · exact (hq₀ i z.1 z.2).1 hzq
  · exact (hq₀ i z.1 z.2).2 hzq

private theorem dq_insertNth_ne_of_mem_pi_Ioo {a b x₀ : Fin 4 → ℝ}
    (hx₀ : x₀ ∈ pi univ (fun i ↦ Ioo (a i) (b i))) (i : Fin 4) (z : Fin 3 → ℝ) :
    dq (i.insertNth (a i) z) ≠ dq x₀ ∧ dq (i.insertNth (b i) z) ≠ dq x₀ :=
  ⟨fun h ↦ (hx₀ i (mem_univ i)).1.ne (by simpa using congrFun (dq_injective h) i),
   fun h ↦ (hx₀ i (mem_univ i)).2.ne (by simpa using (congrFun (dq_injective h) i).symm)⟩

/-! ### Power-series expansions and analyticity of box boundary potentials -/

/-- Quantitative `HasFPowerSeriesOnBall` expansion on `eball q₀ ((√2 - 1) * δ)` of the left
Cauchy–Fueter box boundary potential when every face of `dq '' Icc a b` lies at Euclidean distance
at least `δ > 0` from `q₀`. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' Icc a b))
    {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ i : Fin 4, ∀ z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      δ ≤ ‖dq (i.insertNth (a i) z) - q₀‖ ∧ δ ≤ ‖dq (i.insertNth (b i) z) - q₀‖) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)))
        P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hseries := hasFPowerSeriesOnBall_sum_integral_cauchyFueterKernel_mul
    (Finset.univ : Finset (Fin 4 × Bool)) (boxFaceChart a b)
    (fun _ ↦ Measure.comap Subtype.val volume)
    (fun p _ z ↦ boxFaceChart_ne_of_pos hδ₀ hδ p z) hδ₀
    (fun p _ z ↦ le_norm_boxFaceChart_sub hδ p z)
    (fun p _ ↦ (integrable_comp_boxFaceChart hab
      ((continuousOn_const (c := dq (Pi.single p.1 1))).mul hc) p).smul (cond p.2 (1 : ℝ) (-1)))
  exact ⟨_, hseries.congr fun q _ ↦ (boxBoundarySum_cauchyFueterKernel_mul_eq_sum a b f q).symm⟩

/-- Quantitative `HasFPowerSeriesOnBall` expansion on `eball q₀ ((√2 - 1) * δ)` of the right
Cauchy–Fueter box boundary potential when every face of `dq '' Icc a b` lies at Euclidean distance
at least `δ > 0` from `q₀`. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' Icc a b))
    {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ i : Fin 4, ∀ z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      δ ≤ ‖dq (i.insertNth (a i) z) - q₀‖ ∧ δ ≤ ‖dq (i.insertNth (b i) z) - q₀‖) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q))
        P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hseries := hasFPowerSeriesOnBall_sum_integral_mul_cauchyFueterKernel
    (Finset.univ : Finset (Fin 4 × Bool)) (boxFaceChart a b)
    (fun _ ↦ Measure.comap Subtype.val volume)
    (fun p _ z ↦ boxFaceChart_ne_of_pos hδ₀ hδ p z) hδ₀
    (fun p _ z ↦ le_norm_boxFaceChart_sub hδ p z)
    (fun p _ ↦ (integrable_comp_boxFaceChart hab
      (hc.mul (continuousOn_const (c := dq (Pi.single p.1 1)))) p).smul (cond p.2 (1 : ℝ) (-1)))
  exact ⟨_, hseries.congr fun q _ ↦ (boxBoundarySum_mul_cauchyFueterKernel_eq_sum a b f q).symm⟩

/-- The left Cauchy–Fueter box boundary potential is real analytic at every point not lying on any
of the eight closed faces of `dq '' Icc a b`. -/
theorem analyticAt_boxBoundarySum_cauchyFueterKernel_mul
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' Icc a b)) {q₀ : ℍ}
    (hq₀ : ∀ i : Fin 4, ∀ z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      dq (i.insertNth (a i) z) ≠ q₀ ∧ dq (i.insertNth (b i) z) ≠ q₀) :
    AnalyticAt ℝ
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x))) q₀ := by
  have han := analyticAt_sum_integral_cauchyFueterKernel_mul
    (Finset.univ : Finset (Fin 4 × Bool)) (boxFaceChart a b)
    (fun _ ↦ Measure.comap Subtype.val volume) (notMem_iUnion_range_boxFaceChart hq₀)
    (fun p _ ↦ (integrable_comp_boxFaceChart hab
      ((continuousOn_const (c := dq (Pi.single p.1 1))).mul hc) p).smul (cond p.2 (1 : ℝ) (-1)))
  exact han.congr (Eventually.of_forall fun q ↦
    (boxBoundarySum_cauchyFueterKernel_mul_eq_sum a b f q).symm)

/-- The right Cauchy–Fueter box boundary potential is real analytic at every point not lying on any
of the eight closed faces of `dq '' Icc a b`. -/
theorem analyticAt_boxBoundarySum_mul_cauchyFueterKernel
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' Icc a b)) {q₀ : ℍ}
    (hq₀ : ∀ i : Fin 4, ∀ z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      dq (i.insertNth (a i) z) ≠ q₀ ∧ dq (i.insertNth (b i) z) ≠ q₀) :
    AnalyticAt ℝ
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)) q₀ := by
  have han := analyticAt_sum_integral_mul_cauchyFueterKernel
    (Finset.univ : Finset (Fin 4 × Bool)) (boxFaceChart a b)
    (fun _ ↦ Measure.comap Subtype.val volume) (notMem_iUnion_range_boxFaceChart hq₀)
    (fun p _ ↦ (integrable_comp_boxFaceChart hab
      (hc.mul (continuousOn_const (c := dq (Pi.single p.1 1)))) p).smul (cond p.2 (1 : ℝ) (-1)))
  exact han.congr (Eventually.of_forall fun q ↦
    (boxBoundarySum_mul_cauchyFueterKernel_eq_sum a b f q).symm)

/-- The left Cauchy–Fueter box boundary potential is real analytic on neighbourhoods throughout the
open box `dq '' pi univ (fun i ↦ Ioo (a i) (b i))`. -/
theorem analyticOnNhd_boxBoundarySum_cauchyFueterKernel_mul
    {a b : Fin 4 → ℝ} {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' Icc a b)) :
    AnalyticOnNhd ℝ
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)))
      (dq '' pi univ (fun i ↦ Ioo (a i) (b i))) := by
  rintro _ ⟨x₀, hx₀, rfl⟩
  exact analyticAt_boxBoundarySum_cauchyFueterKernel_mul
    (fun i ↦ ((hx₀ i (mem_univ i)).1.trans (hx₀ i (mem_univ i)).2).le) hc
    fun i z _ ↦ dq_insertNth_ne_of_mem_pi_Ioo hx₀ i z

/-- The right Cauchy–Fueter box boundary potential is real analytic on neighbourhoods throughout the
open box `dq '' pi univ (fun i ↦ Ioo (a i) (b i))`. -/
theorem analyticOnNhd_boxBoundarySum_mul_cauchyFueterKernel
    {a b : Fin 4 → ℝ} {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' Icc a b)) :
    AnalyticOnNhd ℝ
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q))
      (dq '' pi univ (fun i ↦ Ioo (a i) (b i))) := by
  rintro _ ⟨x₀, hx₀, rfl⟩
  exact analyticAt_boxBoundarySum_mul_cauchyFueterKernel
    (fun i ↦ ((hx₀ i (mem_univ i)).1.trans (hx₀ i (mem_univ i)).2).le) hc
    fun i z _ ↦ dq_insertNth_ne_of_mem_pi_Ioo hx₀ i z

/-! ### Quantitative power-series expansions of Fueter regular functions -/

/-- If `f` is continuous on the closed box `dq '' Icc a b` and pointwise left Fueter regular on its
open interior, and `x₀` lies at coordinate distance at least `δ > 0` from every face, then `f` has a
convergent formal multilinear series on `eball (dq x₀) ((√2 - 1) * δ)`. -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall_of_box
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} {δ : ℝ}
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hc : ContinuousOn f (dq '' Icc a b)) (hδ₀ : 0 < δ)
    (hδ : ∀ i : Fin 4, a i + δ ≤ x₀ i ∧ x₀ i + δ ≤ b i) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hab : a ≤ b := fun i ↦ by linarith [(hδ i).1, (hδ i).2]
  have hface (i : Fin 4) (z : Fin 3 → ℝ) (_ : z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      δ ≤ ‖dq (i.insertNth (a i) z) - dq x₀‖ ∧ δ ≤ ‖dq (i.insertNth (b i) z) - dq x₀‖ := by
    refine ⟨?_, ?_⟩
    · have h1 : δ ≤ |a i - x₀ i| := by rw [abs_of_nonpos] <;> linarith [(hδ i).1]
      exact h1.trans (by simpa using abs_sub_apply_le_norm_dq_sub (i.insertNth (a i) z) x₀ i)
    · have h2 : δ ≤ |b i - x₀ i| := by rw [abs_of_nonneg] <;> linarith [(hδ i).2]
      exact h2.trans (by simpa using abs_sub_apply_le_norm_dq_sub (i.insertNth (b i) z) x₀ i)
  obtain ⟨P, hP⟩ :=
    exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul hab hc hδ₀ hface
  let cL : ℍ →L[ℝ] ℍ := (1 / (2 * Real.pi ^ 2)) • ContinuousLinearMap.id ℝ ℍ
  have hcP := cL.comp_hasFPowerSeriesOnBall hP
  refine ⟨_, hcP.congr fun q hq ↦ ?_⟩
  have hsqrt : Real.sqrt 2 - 1 < 1 := by
    have h2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by positivity)).2 (by norm_num)
    linarith
  have hrad_pos : 0 < (Real.sqrt 2 - 1) * δ :=
    mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀
  have hnorm : ‖q - dq x₀‖ < (Real.sqrt 2 - 1) * δ := by
    rw [Metric.mem_eball, edist_dist, dist_eq_norm] at hq
    exact (ENNReal.ofReal_lt_ofReal_iff hrad_pos).1 hq
  have hnorm_δ : ‖q - dq x₀‖ < δ :=
    hnorm.trans (by nlinarith)
  obtain ⟨x, rfl⟩ := dq_surjective q
  have hcoord (i : Fin 4) : |x i - x₀ i| < δ :=
    (abs_sub_apply_le_norm_dq_sub x x₀ i).trans_lt hnorm_δ
  have ha (i : Fin 4) : a i < x i := by linarith [(abs_lt.1 (hcoord i)).1, (hδ i).1]
  have hb (i : Fin 4) : x i < b i := by linarith [(abs_lt.1 (hcoord i)).2, (hδ i).2]
  simpa [cL] using (left_cauchyFueter_box hc (hf.mono sdiff_subset) ha hb).symm

/-- If `f` is continuous on the closed box `dq '' Icc a b` and pointwise right Fueter regular on its
open interior, and `x₀` lies at coordinate distance at least `δ > 0` from every face, then `f` has a
convergent formal multilinear series on `eball (dq x₀) ((√2 - 1) * δ)`. -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall_of_box
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} {δ : ℝ}
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hc : ContinuousOn f (dq '' Icc a b)) (hδ₀ : 0 < δ)
    (hδ : ∀ i : Fin 4, a i + δ ≤ x₀ i ∧ x₀ i + δ ≤ b i) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  let x₀' : Fin 4 → ℝ := fun i ↦ if i = 0 then x₀ 0 else -x₀ i
  let a' : Fin 4 → ℝ := fun i ↦ if i = 0 then a 0 else -b i
  let b' : Fin 4 → ℝ := fun i ↦ if i = 0 then b 0 else -a i
  have hf' : LeftFueterOn (fun q ↦ star (f (star q)))
      (dq '' pi univ (fun i ↦ Ioo (a' i) (b' i))) := by
    rw [← image_star_image_dq_pi_Ioo]
    exact hf.star_star
  have hc' : ContinuousOn (fun q ↦ star (f (star q))) (dq '' Icc a' b') := by
    refine continuous_star.comp_continuousOn (hc.comp continuous_star.continuousOn ?_)
    rw [← image_star_image_dq_Icc]
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hδ' (i : Fin 4) : a' i + δ ≤ x₀' i ∧ x₀' i + δ ≤ b' i := by
    rcases eq_or_ne i 0 with rfl | hi
    · simpa [x₀', a', b'] using hδ 0
    · simp only [x₀', a', b', hi, ↓reduceIte]
      exact ⟨by linarith [(hδ i).2], by linarith [(hδ i).1]⟩
  obtain ⟨P, hP⟩ := hf'.exists_hasFPowerSeriesOnBall_of_box hc' hδ₀ hδ'
  let u := (starₗᵢ ℝ : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearIsometry
  have hx₀' : dq x₀' = u (dq x₀) := (star_dq x₀).symm
  rw [hx₀'] at hP
  have hcomp := u.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hP.compLinearIsometry
  exact ⟨_, hcomp.congr fun x _ ↦ by simp [u]⟩

/-- A function pointwise left Fueter regular on `closedBall q₀ R` (`R > 0`) admits a convergent
formal multilinear series at `q₀` of radius at least `(√2 - 1) * (R / 2)`. -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall
    {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ} (hf : LeftFueterOn f (closedBall q₀ R)) (hR : 0 < R) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
  obtain ⟨x₀, rfl⟩ := dq_surjective q₀
  let a : Fin 4 → ℝ := fun i ↦ x₀ i - R / 2
  let b : Fin 4 → ℝ := fun i ↦ x₀ i + R / 2
  have hsub : dq '' Icc a b ⊆ closedBall (dq x₀) R := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have habs (i : Fin 4) : |x i - x₀ i| ≤ R / 2 := by
      have h1 : x₀ i - R / 2 ≤ x i := hx.1 i
      have h2 : x i ≤ x₀ i + R / 2 := hx.2 i
      exact abs_le.2 ⟨by linarith, by linarith⟩
    linarith [norm_dq_sub_le_two_mul_of_abs_sub_le habs]
  have hsub_open : dq '' pi univ (fun i ↦ Ioo (a i) (b i)) ⊆ closedBall (dq x₀) R :=
    (image_mono (t := Icc a b) fun _ hx ↦ ⟨fun i ↦ (hx i (mem_univ i)).1.le,
      fun i ↦ (hx i (mem_univ i)).2.le⟩).trans hsub
  exact (hf.mono hsub_open).exists_hasFPowerSeriesOnBall_of_box
    (hf.differentiableOn.continuousOn.mono hsub) (half_pos hR)
    (fun i ↦ ⟨by simp [a], by simp [b]⟩)

/-- A function pointwise right Fueter regular on `closedBall q₀ R` (`R > 0`) admits a convergent
formal multilinear series at `q₀` of radius at least `(√2 - 1) * (R / 2)`. -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall
    {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ} (hf : RightFueterOn f (closedBall q₀ R)) (hR : 0 < R) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
  let u := (starₗᵢ ℝ : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearIsometry
  have hf' : LeftFueterOn (fun x ↦ star (f (star x))) (closedBall (u q₀) R) := by
    simpa [u, Set.image_star] using hf.star_star
  obtain ⟨P, hP⟩ := hf'.exists_hasFPowerSeriesOnBall_of_closedBall hR
  have hcomp := u.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hP.compLinearIsometry
  exact ⟨_, hcomp.congr fun x _ ↦ by simp [u]⟩

/-! ### Real analyticity and smoothness -/

namespace LeftFueterOn

variable {f g : ℍ → ℍ} {s : Set ℍ} {q : ℍ}

/-- A function left Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem analyticAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) : AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hs
  obtain ⟨_, hP⟩ := (hf.mono hball).exists_hasFPowerSeriesOnBall_of_closedBall hR
  exact hP.analyticAt

/-- A function left Fueter regular on an open set is real analytic on neighbourhoods there. -/
theorem analyticOnNhd (hf : LeftFueterOn f s) (hs : IsOpen s) : AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A function left Fueter regular on a neighbourhood of `q` is `C^n` at `q` for every `n`,
including `n = ∞` and `n = ω`. -/
theorem contDiffAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) {n : ℕ∞ω} : ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A function left Fueter regular on an open set is `C^n` there for every `n`, including `n = ∞`
and `n = ω`. -/
theorem contDiffOn (hf : LeftFueterOn f s) (hs : IsOpen s) {n : ℕ∞ω} : ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-! ### Uniqueness principle for left Fueter regular functions -/

/-- **Uniqueness principle (open-subset form).** Two left Fueter regular functions on a preconnected
open set `s` that agree on a nonempty open subset `t ⊆ s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_eqOn_open
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {t : Set ℍ} (ht : IsOpen t) (hne : t.Nonempty) (hts : t ⊆ s) (hfg : EqOn f g t) :
    EqOn f g s := by
  obtain ⟨q₀, hq₀⟩ := hne
  exact (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc
    (hts hq₀) (hfg.eventuallyEq_of_mem (ht.mem_nhds hq₀))

/-- If a left Fueter regular function on a preconnected open set `s` has all iterated real Fréchet
derivatives equal to `0` at one point of `s`, then it vanishes throughout `s`. -/
theorem eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfq₀ : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ hfq₀

/-- Two left Fueter regular functions on a preconnected open set `s` whose iterated real Fréchet
derivatives all agree at one point of `s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfg : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ hfg

end LeftFueterOn

namespace RightFueterOn

variable {f g : ℍ → ℍ} {s : Set ℍ} {q : ℍ}

/-- A function right Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem analyticAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) : AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hs
  obtain ⟨_, hP⟩ := (hf.mono hball).exists_hasFPowerSeriesOnBall_of_closedBall hR
  exact hP.analyticAt

/-- A function right Fueter regular on an open set is real analytic on neighbourhoods there. -/
theorem analyticOnNhd (hf : RightFueterOn f s) (hs : IsOpen s) : AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A function right Fueter regular on a neighbourhood of `q` is `C^n` at `q` for every `n`,
including `n = ∞` and `n = ω`. -/
theorem contDiffAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) {n : ℕ∞ω} : ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A function right Fueter regular on an open set is `C^n` there for every `n`, including `n = ∞`
and `n = ω`. -/
theorem contDiffOn (hf : RightFueterOn f s) (hs : IsOpen s) {n : ℕ∞ω} : ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-! ### Uniqueness principle for right Fueter regular functions -/

/-- **Uniqueness principle (open-subset form).** Two right Fueter regular functions on a
preconnected open set `s` that agree on a nonempty open subset `t ⊆ s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_eqOn_open
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {t : Set ℍ} (ht : IsOpen t) (hne : t.Nonempty) (hts : t ⊆ s) (hfg : EqOn f g t) :
    EqOn f g s := by
  obtain ⟨q₀, hq₀⟩ := hne
  exact (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc
    (hts hq₀) (hfg.eventuallyEq_of_mem (ht.mem_nhds hq₀))

/-- If a right Fueter regular function on a preconnected open set `s` has all iterated real Fréchet
derivatives equal to `0` at one point of `s`, then it vanishes throughout `s`. -/
theorem eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfq₀ : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ hfq₀

/-- Two right Fueter regular functions on a preconnected open set `s` whose iterated real Fréchet
derivatives all agree at one point of `s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfg : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ hfg

end RightFueterOn

end TauCeti
