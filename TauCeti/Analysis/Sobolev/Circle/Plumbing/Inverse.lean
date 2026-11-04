/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Plumbing.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Local inverses of ambient neck evaluation

Ambient neck evaluation is a holomorphic change of coordinates near the node, even when its
logarithmic boundary data vary holomorphically with the ambient coordinates and additional
parameters. Its normal derivative is diagonal, with the two nonzero entries given by the
exponentials of the constant logarithmic modes. Derivatives of the moving data do not contribute
at the node. The local inverse retains the additional parameters and preserves each designated
branch. Thus the construction applies before restriction to a possibly singular equation
`xy = s(t)`; it does not require the total hypersurface to be smooth.

The inverse constructed here is a germ at the node. This asserts neither global injectivity on
the bidisc nor the universal mapping property of a nodal family.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §§10–12.

The construction uses Mathlib's analytic inverse theorem for open partial homeomorphisms.
-/

public noncomputable section

open Complex Filter Topology

namespace TauCeti.CircleSobolev

variable {s : ℝ}

/-- The normal linear isomorphism of neck evaluation at the node. -/
def neckEvaluationLinearEquiv (p : CircleSobolev s ℂ × CircleSobolev s ℂ) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ)
    (Units.mk0 (exp (p.1.coeff 0)) (exp_ne_zero _))).prodCongr
    (ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ)
      (Units.mk0 (exp (p.2.coeff 0)) (exp_ne_zero _)))

/-- The normal derivative scales the two branches separately. -/
@[simp]
theorem neckEvaluationLinearEquiv_apply (p : CircleSobolev s ℂ × CircleSobolev s ℂ)
    (z : ℂ × ℂ) :
    neckEvaluationLinearEquiv p z = (exp (p.1.coeff 0) * z.1, exp (p.2.coeff 0) * z.2) := by
  simp [neckEvaluationLinearEquiv]

/-- Ambient neck evaluation together with the unchanged additional parameter. The data may
depend on all ambient variables; in particular the smoothing argument may be `xy`. -/
def neckEvaluationWithParameters {A : Type*}
    (p : (ℂ × ℂ) × A → CircleSobolev s ℂ × CircleSobolev s ℂ)
    (w : (ℂ × ℂ) × A) : (ℂ × ℂ) × A :=
  (neckEvaluation (p w) w.1, w.2)

/-- Evaluation with parameters has the prescribed neck coordinates and fixes the parameter. -/
@[simp]
theorem neckEvaluationWithParameters_apply {A : Type*}
    (p : (ℂ × ℂ) × A → CircleSobolev s ℂ × CircleSobolev s ℂ) (w : (ℂ × ℂ) × A) :
    neckEvaluationWithParameters p w = (neckEvaluation (p w) w.1, w.2) := (rfl)

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  {p : (ℂ × ℂ) × A → CircleSobolev s ℂ × CircleSobolev s ℂ} {t : A}

/-- Holomorphic moving logarithmic data give a jointly holomorphic ambient evaluation. -/
theorem analyticAt_neckEvaluationWithParameters
    (hp : AnalyticAt ℂ p (0, t)) :
    AnalyticAt ℂ (neckEvaluationWithParameters p) (0, t) := by
  exact (analyticAt_neckEvaluation hp analyticAt_fst (by simp) (by simp)).prod analyticAt_snd

/-- At the node the full derivative is the normal diagonal isomorphism times the identity on
parameters. In particular, derivatives of the moving boundary data do not affect this derivative. -/
theorem hasFDerivAt_neckEvaluationWithParameters
    (hp : AnalyticAt ℂ p (0, t)) :
    HasFDerivAt (neckEvaluationWithParameters p)
      (((neckEvaluationLinearEquiv (p (0, t))).prodCongr
        (ContinuousLinearEquiv.refl ℂ A)) : ((ℂ × ℂ) × A) →L[ℂ] ((ℂ × ℂ) × A)) (0, t) := by
  have hx := (hasFDerivAt_fst (𝕜 := ℂ) (p := (0 : ℂ × ℂ))).comp (0, t)
    (hasFDerivAt_fst (𝕜 := ℂ) (p := ((0 : ℂ × ℂ), t)))
  have hy := (hasFDerivAt_snd (𝕜 := ℂ) (p := (0 : ℂ × ℂ))).comp (0, t)
    (hasFDerivAt_fst (𝕜 := ℂ) (p := ((0 : ℂ × ℂ), t)))
  have hP := analyticAt_diskFunction (analyticAt_fst.comp hp)
    (analyticAt_fst.comp analyticAt_fst) (by simp : ‖(0 : ℂ)‖ < 1)
  have hQ := analyticAt_diskFunction (analyticAt_snd.comp hp)
    (analyticAt_snd.comp analyticAt_fst) (by simp : ‖(0 : ℂ)‖ < 1)
  have hcP := ((coeffCLM 0).analyticAt _).comp (analyticAt_fst.comp hp)
  have hcQ := ((coeffCLM 0).analyticAt _).comp (analyticAt_snd.comp hp)
  have h₁ := hx.mul (((hP.sub hQ).add hcQ).differentiableAt.hasFDerivAt.cexp)
  have h₂ := hy.mul (((hQ.sub hP).add hcP).differentiableAt.hasFDerivAt.cexp)
  convert (h₁.prodMk h₂).prodMk (hasFDerivAt_snd (𝕜 := ℂ) (p := ((0 : ℂ × ℂ), t))) using 1
  · ext w <;> simp [neckEvaluation_fst, neckEvaluation_snd]
  · ext w <;> simp [neckEvaluationLinearEquiv_apply, diskFunction_apply_zero, mul_comm]

variable [CompleteSpace A]

/-- A local ambient coordinate change at the node, retaining all parameters. Its inverse is
holomorphic as a germ. No smallness of the constant logarithmic modes is required. -/
def neckEvaluationChart (hp : AnalyticAt ℂ p (0, t)) :
    OpenPartialHomeomorph ((ℂ × ℂ) × A) ((ℂ × ℂ) × A) :=
  let h := analyticAt_neckEvaluationWithParameters hp
  let hd := hasFDerivAt_neckEvaluationWithParameters hp
  (hd.fderiv ▸ h.hasStrictFDerivAt).toOpenPartialHomeomorph _

/-- The forward coordinate change is the original ambient evaluation, not a replacement map. -/
@[simp]
theorem coe_neckEvaluationChart (hp : AnalyticAt ℂ p (0, t)) :
    (neckEvaluationChart hp : ((ℂ × ℂ) × A) → (ℂ × ℂ) × A) =
      neckEvaluationWithParameters p :=
  HasStrictFDerivAt.toOpenPartialHomeomorph_coe
    ((hasFDerivAt_neckEvaluationWithParameters hp).fderiv ▸
      (analyticAt_neckEvaluationWithParameters hp).hasStrictFDerivAt)

/-- The local coordinate change is defined at the central node. -/
theorem node_mem_neckEvaluationChart_source (hp : AnalyticAt ℂ p (0, t)) :
    (0, t) ∈ (neckEvaluationChart hp).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    ((hasFDerivAt_neckEvaluationWithParameters hp).fderiv ▸
      (analyticAt_neckEvaluationWithParameters hp).hasStrictFDerivAt)

/-- Its target also contains the central node. -/
theorem node_mem_neckEvaluationChart_target (hp : AnalyticAt ℂ p (0, t)) :
    (0, t) ∈ (neckEvaluationChart hp).target := by
  simpa using (neckEvaluationChart hp).map_source (node_mem_neckEvaluationChart_source hp)

/-- The ambient inverse is jointly holomorphic at the node and the chosen parameter. -/
theorem analyticAt_neckEvaluationChart_symm (hp : AnalyticAt ℂ p (0, t)) :
    AnalyticAt ℂ (neckEvaluationChart hp).symm (0, t) := by
  have ha : AnalyticAt ℂ (neckEvaluationChart hp) (0, t) := by
    simpa using analyticAt_neckEvaluationWithParameters hp
  have hd := hasFDerivAt_neckEvaluationWithParameters hp
  simpa using (neckEvaluationChart hp).analyticAt_symm'
    (i := (neckEvaluationLinearEquiv (p (0, t))).prodCongr (ContinuousLinearEquiv.refl ℂ A))
    (node_mem_neckEvaluationChart_source hp) ha (by simpa only [coe_neckEvaluationChart]
      using hd.fderiv)

/-- The inverse fixes the central node. -/
@[simp]
theorem neckEvaluationChart_symm_node (hp : AnalyticAt ℂ p (0, t)) :
    (neckEvaluationChart hp).symm (0, t) = (0, t) := by
  simpa using (neckEvaluationChart hp).left_inv (node_mem_neckEvaluationChart_source hp)

/-- The inverse preserves the additional parameter on its entire target. -/
@[simp]
theorem neckEvaluationChart_symm_snd (hp : AnalyticAt ℂ p (0, t))
    {w : (ℂ × ℂ) × A} (hw : w ∈ (neckEvaluationChart hp).target) :
    ((neckEvaluationChart hp).symm w).2 = w.2 := by
  have h := congrArg Prod.snd ((neckEvaluationChart hp).right_inv hw)
  simpa using h

/-- The inverse preserves the first designated branch, including its vanishing coordinate. -/
@[simp]
theorem neckEvaluationChart_symm_fst_fst_eq_zero_iff (hp : AnalyticAt ℂ p (0, t))
    {w : (ℂ × ℂ) × A} (hw : w ∈ (neckEvaluationChart hp).target) :
    ((neckEvaluationChart hp).symm w).1.1 = 0 ↔ w.1.1 = 0 := by
  have h := congrArg (fun z : (ℂ × ℂ) × A ↦ z.1.1)
    ((neckEvaluationChart hp).right_inv hw)
  simp only [coe_neckEvaluationChart, neckEvaluationWithParameters_apply] at h
  rw [← h, neckEvaluation_fst]
  simp

/-- The inverse preserves the second designated branch. -/
@[simp]
theorem neckEvaluationChart_symm_fst_snd_eq_zero_iff (hp : AnalyticAt ℂ p (0, t))
    {w : (ℂ × ℂ) × A} (hw : w ∈ (neckEvaluationChart hp).target) :
    ((neckEvaluationChart hp).symm w).1.2 = 0 ↔ w.1.2 = 0 := by
  have h := congrArg (fun z : (ℂ × ℂ) × A ↦ z.1.2)
    ((neckEvaluationChart hp).right_inv hw)
  simp only [coe_neckEvaluationChart, neckEvaluationWithParameters_apply] at h
  rw [← h, neckEvaluation_snd]
  simp

/-- Under the ambient inverse, the smoothing equation is divided by the nowhere-zero
exponential factor. This formula can be restricted to singular and permanent-node families. -/
theorem neckEvaluationChart_symm_fst_fst_mul_fst_snd (hp : AnalyticAt ℂ p (0, t))
    {w : (ℂ × ℂ) × A} (hw : w ∈ (neckEvaluationChart hp).target) :
    ((neckEvaluationChart hp).symm w).1.1 * ((neckEvaluationChart hp).symm w).1.2 =
      w.1.1 * w.1.2 / exp ((p ((neckEvaluationChart hp).symm w)).1.coeff 0 +
        (p ((neckEvaluationChart hp).symm w)).2.coeff 0) := by
  apply (eq_div_iff (exp_ne_zero _)).mpr
  rw [← neckEvaluation_fst_mul_snd]
  have h := congrArg Prod.fst ((neckEvaluationChart hp).right_inv hw)
  simpa using congrArg (fun z : ℂ × ℂ ↦ z.1 * z.2) h

end TauCeti.CircleSobolev
