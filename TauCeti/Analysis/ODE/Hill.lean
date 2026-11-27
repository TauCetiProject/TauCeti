/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.ODE.Propagator.Holomorphic.Basic
import TauCeti.Analysis.ODE.SecondOrder.Linear
import TauCeti.Analysis.ODE.SecondOrder.ParameterJets
import TauCeti.Analysis.ODE.Wronskian

/-!
# Fundamental solutions of Hill's equation

For a continuous real potential `Q`, Hill's equation on the real line is
`w'' + (λ + Q) w = 0`, with complex spectral parameter `λ`. The solutions
`hillWI Q λ` and `hillWII Q λ` have initial data `(1, 0)` and `(0, 1)` at zero.
They span the solution space, have Wronskian one, and give the translation formulas
for any period of `Q`. At each point of the real line their values and first derivatives
are entire in `λ`.

The construction applies `TauCeti.propagator` to the system
`(w, v)' = (v, -(λ + Q) w)`, using `ContinuousLinearMap.jacobiODECoeff` for the companion
operator. The coefficient is affine in `λ`, so `TauCeti.differentiable_propagator_smul_add`
gives entireness.

## References

* NIST Digital Library of Mathematical Functions, [§28.29](https://dlmf.nist.gov/28.29),
  equations 28.29.1 and 28.29.4–5.
-/

public section

open Set ContinuousLinearMap
open scoped ComplexConjugate

namespace TauCeti

/-- A classical solution of Hill's equation on the real line with potential `Q` and parameter
`λ`. The equation is written as `w'' = -(λ + Q) w` to match the second-order ODE API. -/
structure IsHillSolution (Q : ℝ → ℝ) (lam : ℂ) (w : ℝ → ℂ) : Prop where
  /-- The solution is twice continuously differentiable in the real variable. -/
  contDiff : ContDiff ℝ 2 w
  /-- Hill's equation in solved form for the second derivative. -/
  iteratedDeriv_two (x : ℝ) : iteratedDeriv 2 w x = -(lam + (Q x : ℂ)) * w x

variable {Q : ℝ → ℝ} {lam : ℂ} {u w : ℝ → ℂ}

/-- The first derivative of a Hill solution has the derivative prescribed by the equation. -/
theorem IsHillSolution.hasDerivAt_deriv (hw : IsHillSolution Q lam w) (x : ℝ) :
    HasDerivAt (deriv w) (-(lam + (Q x : ℂ)) * w x) x := by
  rw [← hw.iteratedDeriv_two x]
  exact (hw.contDiff.contDiffOn (s := univ)).hasDerivAt_and_hasDerivAt_deriv
    isOpen_univ (mem_univ x) |>.2

/-- A function with two successive derivatives satisfying the first-order system for Hill's
equation is a classical solution when the potential is continuous. -/
theorem isHillSolution_of_hasDerivAt {v : ℝ → ℂ} (hQ : Continuous Q)
    (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x, HasDerivAt v (-(lam + (Q x : ℂ)) * w x) x) :
    IsHillSolution Q lam w := by
  have hc : Continuous (fun x ↦ -(lam + (Q x : ℂ))) :=
    (continuous_const.add (Complex.continuous_ofReal.comp hQ)).neg
  obtain ⟨hcw, heq⟩ := contDiffOn_two_of_hasDerivAt isOpen_univ hc.continuousOn
    (fun x _ ↦ hw x) (fun x _ ↦ hv x)
  exact ⟨contDiffOn_univ.mp hcw, fun x ↦ heq x (mem_univ x)⟩

/-- Two Hill solutions for a continuous potential agree if their values and derivatives agree
at one point. -/
theorem IsHillSolution.eq_of_initial_data (hu : IsHillSolution Q lam u)
    (hw : IsHillSolution Q lam w) (hQ : Continuous Q) {x : ℝ}
    (h₀ : u x = w x) (h₁ : deriv u x = deriv w x) : u = w := by
  have hc : Continuous (fun t ↦ -(lam + (Q t : ℂ))) :=
    (continuous_const.add (Complex.continuous_ofReal.comp hQ)).neg
  exact funext fun t ↦ eqOn_of_iteratedDeriv_eq_mul isOpen_univ ordConnected_univ
    hc.continuousOn hu.contDiff.contDiffOn (fun r _ ↦ hu.iteratedDeriv_two r)
    hw.contDiff.contDiffOn (fun r _ ↦ hw.iteratedDeriv_two r) (mem_univ x) h₀ h₁ (mem_univ t)

/-- The companion operator for Hill's equation. -/
private noncomputable def hillCoefficient (Q : ℝ → ℝ) (lam : ℂ) (x : ℝ) :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  jacobiODECoeff ((lam + (Q x : ℂ)) • (1 : ℂ →L[ℂ] ℂ))

private theorem hillCoefficient_apply (v : ℂ × ℂ) (x : ℝ) :
    hillCoefficient Q lam x v = (v.2, -(lam + (Q x : ℂ)) * v.1) := by
  simp only [hillCoefficient, jacobiODECoeff_apply, smul_apply, one_apply_eq_self, smul_eq_mul,
    neg_mul]

private theorem continuous_hillCoefficient (hQ : Continuous Q) :
    Continuous (hillCoefficient Q lam) :=
  (contDiff_jacobiODECoeff (𝕜 := ℂ) (F := ℂ) (n := 0)).continuous.comp
    ((continuous_const.add (Complex.continuous_ofReal.comp hQ)).smul continuous_const)

/-- The affine form of the companion operator in the spectral parameter. -/
private theorem hillCoefficient_eq_smul_add (x : ℝ) :
    hillCoefficient Q lam x =
      lam • (0 : (ℂ × ℂ) →L[ℂ] ℂ).prod (-fst ℂ ℂ ℂ) + hillCoefficient Q 0 x := by
  apply ContinuousLinearMap.ext
  intro v
  simp [hillCoefficient_apply, add_mul, add_comm]

/-- The state of the first-order system, evolved from the data `v` at zero. -/
private noncomputable def hillState (Q : ℝ → ℝ) (lam : ℂ) (v : ℂ × ℂ)
    (x : ℝ) : ℂ × ℂ :=
  propagator (hillCoefficient Q lam) x 0 v

@[simp]
private theorem hillState_zero (v : ℂ × ℂ) : hillState Q lam v 0 = v := by
  simp [hillState]

private theorem hasDerivAt_hillState (hQ : Continuous Q) (v : ℂ × ℂ) (x : ℝ) :
    HasDerivAt (hillState Q lam v)
      ((hillState Q lam v x).2, -(lam + (Q x : ℂ)) * (hillState Q lam v x).1) x := by
  let P := hillCoefficient Q lam
  have hP : Continuous P := continuous_hillCoefficient hQ
  have heq (t : ℝ) : propagator P t 0 = dysonSeriesLeft P t :=
    propagator_eq_of_hasDerivAt (hP.integrableOn_Icc (a := min 0 t) (b := max 0 t))
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 t) (right_mem_uIcc : t ∈ uIcc 0 t)
      (fun r _ ↦ by simpa only [ContinuousLinearMap.mul_def] using hasDerivAt_dysonSeriesLeft hP r)
      (dysonSeriesLeft_zero P)
  have h : HasDerivAt (fun t ↦ dysonSeriesLeft P t v)
      (P x (dysonSeriesLeft P x v)) x := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.apply ℂ (ℂ × ℂ) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_dysonSeriesLeft hP x)
  unfold hillState
  simpa only [← heq, P, hillCoefficient_apply] using h

private theorem hasDerivAt_fst_hillState (hQ : Continuous Q) (v : ℂ × ℂ) (x : ℝ) :
    HasDerivAt (fun t ↦ (hillState Q lam v t).1) (hillState Q lam v x).2 x :=
  (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_hillState (lam := lam) hQ v x)

private theorem isHillSolution_fst_hillState (hQ : Continuous Q) (v : ℂ × ℂ) :
    IsHillSolution Q lam (fun x ↦ (hillState Q lam v x).1) :=
  isHillSolution_of_hasDerivAt hQ (hasDerivAt_fst_hillState hQ v) fun x ↦
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_hillState (lam := lam) hQ v x)

private theorem differentiable_hillState_parameter (hQ : Continuous Q) (v : ℂ × ℂ) (x : ℝ) :
    Differentiable ℂ (fun lam ↦ hillState Q lam v x) := by
  let A := (0 : (ℂ × ℂ) →L[ℂ] ℂ).prod (-fst ℂ ℂ ℂ)
  have hB : Continuous (hillCoefficient Q 0) := continuous_hillCoefficient hQ
  have h (z : ℂ) : hillCoefficient Q z = fun r ↦ z • A + hillCoefficient Q 0 r :=
    funext (hillCoefficient_eq_smul_add (lam := z))
  have heq : (fun z ↦ hillState Q z v x) =
      fun z ↦ propagator (fun r ↦ z • A + hillCoefficient Q 0 r) x 0 v :=
    funext fun z ↦ congrArg (fun P ↦ propagator P x 0 v) (h z)
  rw [heq]
  exact (differentiable_propagator_smul_add A
    (hB.integrableOn_Icc (a := min 0 x) (b := max 0 x))
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 x) (right_mem_uIcc : x ∈ uIcc 0 x)).clm_apply
    (differentiable_const v)

/-- The first fundamental solution of Hill's equation, with value one and derivative zero
at the origin for continuous `Q`. -/
noncomputable def hillWI (Q : ℝ → ℝ) (lam : ℂ) (x : ℝ) : ℂ :=
  (hillState Q lam (1, 0) x).1

/-- The second fundamental solution of Hill's equation, with value zero and derivative one
at the origin for continuous `Q`. -/
noncomputable def hillWII (Q : ℝ → ℝ) (lam : ℂ) (x : ℝ) : ℂ :=
  (hillState Q lam (0, 1) x).1

/-- The initial value of the first fundamental solution. -/
@[simp] theorem hillWI_zero : hillWI Q lam 0 = 1 := by simp [hillWI]

/-- The initial value of the second fundamental solution. -/
@[simp] theorem hillWII_zero : hillWII Q lam 0 = 0 := by simp [hillWII]

/-- The initial derivative of the first fundamental solution. -/
@[simp] theorem deriv_hillWI_zero (hQ : Continuous Q) : deriv (hillWI Q lam) 0 = 0 := by
  unfold hillWI
  simpa only [hillState_zero] using (hasDerivAt_fst_hillState (lam := lam) hQ (1, 0) 0).deriv

/-- The initial derivative of the second fundamental solution. -/
@[simp] theorem deriv_hillWII_zero (hQ : Continuous Q) : deriv (hillWII Q lam) 0 = 1 := by
  unfold hillWII
  simpa only [hillState_zero] using (hasDerivAt_fst_hillState (lam := lam) hQ (0, 1) 0).deriv

/-- The first fundamental solution solves Hill's equation. -/
theorem isHillSolution_hillWI (hQ : Continuous Q) : IsHillSolution Q lam (hillWI Q lam) :=
  isHillSolution_fst_hillState hQ (1, 0)

/-- The second fundamental solution solves Hill's equation. -/
theorem isHillSolution_hillWII (hQ : Continuous Q) : IsHillSolution Q lam (hillWII Q lam) :=
  isHillSolution_fst_hillState hQ (0, 1)

/-- For fixed time, the first fundamental solution is entire in the spectral parameter. -/
theorem analyticOnNhd_hillWI (hQ : Continuous Q) (x : ℝ) :
    AnalyticOnNhd ℂ (fun lam ↦ hillWI Q lam x) univ :=
  (differentiable_hillState_parameter hQ (1, 0) x).fst.differentiableOn.analyticOnNhd isOpen_univ

/-- For fixed time, the second fundamental solution is entire in the spectral parameter. -/
theorem analyticOnNhd_hillWII (hQ : Continuous Q) (x : ℝ) :
    AnalyticOnNhd ℂ (fun lam ↦ hillWII Q lam x) univ :=
  (differentiable_hillState_parameter hQ (0, 1) x).fst.differentiableOn.analyticOnNhd isOpen_univ

/-- For fixed time, the time derivative of the first fundamental solution is entire in the
spectral parameter. -/
theorem analyticOnNhd_deriv_hillWI (hQ : Continuous Q) (x : ℝ) :
    AnalyticOnNhd ℂ (fun lam ↦ deriv (hillWI Q lam) x) univ := by
  unfold hillWI
  simpa only [funext (fun lam ↦ (hasDerivAt_fst_hillState (lam := lam) hQ (1, 0) x).deriv)]
    using (differentiable_hillState_parameter hQ (1, 0) x).snd.differentiableOn.analyticOnNhd
      isOpen_univ

/-- For fixed time, the time derivative of the second fundamental solution is entire in the
spectral parameter. -/
theorem analyticOnNhd_deriv_hillWII (hQ : Continuous Q) (x : ℝ) :
    AnalyticOnNhd ℂ (fun lam ↦ deriv (hillWII Q lam) x) univ := by
  unfold hillWII
  simpa only [funext (fun lam ↦ (hasDerivAt_fst_hillState (lam := lam) hQ (0, 1) x).deriv)]
    using (differentiable_hillState_parameter hQ (0, 1) x).snd.differentiableOn.analyticOnNhd
      isOpen_univ

/-- A linear combination of the fundamental solutions again solves Hill's equation. -/
theorem isHillSolution_linearCombination (hQ : Continuous Q) (a b : ℂ) :
    IsHillSolution Q lam (fun x ↦ a * hillWI Q lam x + b * hillWII Q lam x) := by
  have h : (fun x ↦ (hillState Q lam (a, b) x).1) =
      fun x ↦ a * hillWI Q lam x + b * hillWII Q lam x := by
    funext x
    have hv : (a, b) = a • ((1, 0) : ℂ × ℂ) + b • ((0, 1) : ℂ × ℂ) := by
      simp [Prod.smul_mk]
    conv_lhs => rw [hv]
    simp only [hillState, hillWI, hillWII, map_add, map_smul, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul]
  rw [← h]
  exact isHillSolution_fst_hillState hQ (a, b)

/-- A Hill solution is the linear combination of the fundamental solutions with coefficients
equal to its initial value and initial derivative. -/
theorem IsHillSolution.eq_linearCombination (hw : IsHillSolution Q lam w) (hQ : Continuous Q)
    (x : ℝ) : w x = w 0 * hillWI Q lam x + deriv w 0 * hillWII Q lam x := by
  have hw₀ := isHillSolution_linearCombination (lam := lam) hQ (w 0) (deriv w 0)
  have hI := (isHillSolution_hillWI (lam := lam) hQ).contDiff.differentiable (by norm_num) 0
  have hII := (isHillSolution_hillWII (lam := lam) hQ).contDiff.differentiable (by norm_num) 0
  have hd := (hI.hasDerivAt.const_mul (w 0)).add (hII.hasDerivAt.const_mul (deriv w 0))
  refine congrFun (hw.eq_of_initial_data hw₀ hQ (x := 0) ?_ ?_) x
  · simp only [hillWI_zero, hillWII_zero, mul_one, mul_zero, add_zero]
  · simpa [Pi.add_def, hQ] using hd.deriv.symm

/-- The Wronskian of the ordered fundamental pair of Hill solutions is one. -/
theorem hillWI_mul_deriv_hillWII_sub (hQ : Continuous Q) (x : ℝ) :
    hillWI Q lam x * deriv (hillWII Q lam) x - deriv (hillWI Q lam) x * hillWII Q lam x = 1 := by
  have hI := isHillSolution_hillWI (lam := lam) hQ
  have hII := isHillSolution_hillWII (lam := lam) hQ
  rw [mul_comm (deriv (hillWI Q lam) x)]
  exact wronskian_eq_one_of_hasDerivAt
    (fun t ↦ (hII.contDiff.differentiable (by norm_num) t).hasDerivAt) hII.hasDerivAt_deriv
    (fun t ↦ (hI.contDiff.differentiable (by norm_num) t).hasDerivAt) hI.hasDerivAt_deriv
    hillWII_zero (deriv_hillWII_zero hQ) hillWI_zero x

/-- Translating a solution by any period of the potential gives another solution. -/
theorem IsHillSolution.comp_add_period (hw : IsHillSolution Q lam w)
    {p : ℝ} (hp : Function.Periodic Q p) : IsHillSolution Q lam (fun x ↦ w (x + p)) := by
  refine ⟨hw.contDiff.comp (contDiff_id.add contDiff_const), fun x ↦ ?_⟩
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [funext (deriv_comp_add_const w p), deriv_comp_add_const, ← hp x]
  exact (hw.hasDerivAt_deriv (x + p)).deriv

/-- Translation by a period acts on the solution by re-expanding its value and derivative at
the end of that period in the fundamental pair. Applied to the two basic solutions at
`p = π`, this gives DLMF 28.29.4–5. -/
theorem IsHillSolution.add_period_eq (hw : IsHillSolution Q lam w) (hQ : Continuous Q)
    {p : ℝ} (hp : Function.Periodic Q p) (x : ℝ) :
    w (x + p) = w p * hillWI Q lam x + deriv w p * hillWII Q lam x := by
  simpa only [deriv_comp_add_const, zero_add] using
    (hw.comp_add_period hp).eq_linearCombination hQ x

/-- Conjugation takes solutions at `λ` to solutions at the conjugate spectral parameter. -/
theorem IsHillSolution.conj (hw : IsHillSolution Q lam w) :
    IsHillSolution Q (conj lam) (fun x ↦ conj (w x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hw.contDiff, fun x ↦ ?_⟩
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, ← Complex.star_def, deriv.star']
  rw [(hw.hasDerivAt_deriv x).deriv]
  simp

/-- Conjugating the first fundamental solution conjugates its spectral parameter. -/
@[simp] theorem conj_hillWI (hQ : Continuous Q) (x : ℝ) :
    conj (hillWI Q lam x) = hillWI Q (conj lam) x := by
  have hI := isHillSolution_hillWI (lam := lam) hQ
  refine congrFun (hI.conj.eq_of_initial_data (isHillSolution_hillWI hQ) hQ
    (x := 0) (by simp) ?_) x
  rw [← Complex.star_def, deriv.star, deriv_hillWI_zero hQ, deriv_hillWI_zero hQ, star_zero]

/-- Conjugating the second fundamental solution conjugates its spectral parameter. -/
@[simp] theorem conj_hillWII (hQ : Continuous Q) (x : ℝ) :
    conj (hillWII Q lam x) = hillWII Q (conj lam) x := by
  have hII := isHillSolution_hillWII (lam := lam) hQ
  refine congrFun (hII.conj.eq_of_initial_data (isHillSolution_hillWII hQ) hQ
    (x := 0) (by simp) ?_) x
  rw [← Complex.star_def, deriv.star, deriv_hillWII_zero hQ, deriv_hillWII_zero hQ, star_one]

/-- At a real spectral parameter the first fundamental solution is real-valued. -/
@[simp] theorem hillWI_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (hillWI Q (a : ℂ) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using conj_hillWI (lam := (a : ℂ)) hQ x)

/-- At a real spectral parameter the second fundamental solution is real-valued. -/
@[simp] theorem hillWII_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (hillWII Q (a : ℂ) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using conj_hillWII (lam := (a : ℂ)) hQ x)

/-- The first fundamental solution has a real first derivative at a real spectral parameter. -/
@[simp] theorem deriv_hillWI_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (deriv (hillWI Q (a : ℂ)) x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have h := congrArg (fun f : ℝ → ℂ ↦ deriv f x)
    (funext (conj_hillWI (lam := (a : ℂ)) hQ))
  have ha : star (a : ℂ) = (a : ℂ) := by simp
  simpa only [← Complex.star_def, deriv.star, ha] using h

/-- The second fundamental solution has a real first derivative at a real spectral parameter. -/
@[simp] theorem deriv_hillWII_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (deriv (hillWII Q (a : ℂ)) x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have h := congrArg (fun f : ℝ → ℂ ↦ deriv f x)
    (funext (conj_hillWII (lam := (a : ℂ)) hQ))
  have ha : star (a : ℂ) = (a : ℂ) := by simp
  simpa only [← Complex.star_def, deriv.star, ha] using h

/-- The cosine and the normalized sine satisfy the zero-potential equation with their
respective initial slopes. -/
private theorem hill_zero_potential_data (k : ℂ) :
    (IsHillSolution 0 (k ^ 2) (fun x ↦ Complex.cos (k * (x : ℂ))) ∧
      deriv (fun x : ℝ ↦ Complex.cos (k * (x : ℂ))) 0 = 0) ∧
    (k ≠ 0 → IsHillSolution 0 (k ^ 2) (fun x ↦ Complex.sin (k * (x : ℂ)) / k) ∧
      deriv (fun x : ℝ ↦ Complex.sin (k * (x : ℂ)) / k) 0 = 1) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ k * (t : ℂ)) k t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul k
  have hc (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.cos (k * (s : ℂ)))
      (-k * Complex.sin (k * (t : ℂ))) t := by
    simpa [Function.comp_def] using (Complex.hasDerivAt_cos _).scomp t (hd t)
  have hs (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.sin (k * (s : ℂ)))
      (k * Complex.cos (k * (t : ℂ))) t := by
    simpa [Function.comp_def] using (Complex.hasDerivAt_sin _).scomp t (hd t)
  have hQ : Continuous (0 : ℝ → ℝ) := continuous_const
  constructor
  · refine ⟨isHillSolution_of_hasDerivAt hQ hc (fun t ↦ ?_), by simp [(hc 0).deriv]⟩
    exact ((hs t).const_mul (-k)).congr_deriv (by simp; ring)
  · intro hk
    have h (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.sin (k * (s : ℂ)) / k)
        (Complex.cos (k * (t : ℂ))) t := by simpa [hk] using (hs t).div_const k
    refine ⟨isHillSolution_of_hasDerivAt hQ h (fun t ↦ ?_), by simp [(h 0).deriv]⟩
    exact (hc t).congr_deriv (by simp; field_simp)

/-- In zero potential the first solution is the cosine of a square root of the spectral
parameter times the real variable. -/
theorem hillWI_zero_potential (k : ℂ) (x : ℝ) :
    hillWI 0 (k ^ 2) x = Complex.cos (k * (x : ℂ)) := by
  obtain ⟨hc, hd⟩ := (hill_zero_potential_data k).1
  have hQ : Continuous (0 : ℝ → ℝ) := continuous_const
  exact congrFun ((isHillSolution_hillWI hQ).eq_of_initial_data hc hQ
    (x := 0) (by simp) (by simp [hQ, hd])) x

/-- In zero potential and at a nonzero spectral parameter, the second solution is the sine of
a square root of the parameter times the variable, divided by that square root. -/
theorem hillWII_zero_potential {k : ℂ} (hk : k ≠ 0) (x : ℝ) :
    hillWII 0 (k ^ 2) x = Complex.sin (k * (x : ℂ)) / k := by
  obtain ⟨hs, hd⟩ := (hill_zero_potential_data k).2 hk
  have hQ : Continuous (0 : ℝ → ℝ) := continuous_const
  exact congrFun ((isHillSolution_hillWII hQ).eq_of_initial_data hs hQ
    (x := 0) (by simp) (by simp [hQ, hd])) x

/-- In zero potential and at spectral parameter zero, the second solution is the identity. -/
@[simp] theorem hillWII_zero_potential_zero (x : ℝ) : hillWII 0 0 x = (x : ℂ) := by
  have h (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id' t)
  have hQ : Continuous (0 : ℝ → ℝ) := continuous_const
  have hw : IsHillSolution 0 0 (fun t : ℝ ↦ (t : ℂ)) :=
    isHillSolution_of_hasDerivAt hQ h fun t ↦ by simpa using hasDerivAt_const t (1 : ℂ)
  exact congrFun ((isHillSolution_hillWII hQ).eq_of_initial_data hw hQ
    (x := 0) (by simp) (by simp [hQ, (h 0).deriv])) x

end TauCeti
