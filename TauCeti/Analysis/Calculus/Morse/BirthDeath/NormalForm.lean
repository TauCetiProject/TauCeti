/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.BirthDeath.Basic
public import TauCeti.Analysis.Calculus.Morse.SplitModel
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# The multi-dimensional Cerf birth–death (`A₂`) normal form

Let `Eₛ` and `Eᵤ` be real inner product spaces. Coupling the one-dimensional birth–death potential
`TauCeti.birthDeathPotential` with the transverse split quadratic model `TauCeti.splitQuadratic` via
`TauCeti.separatedSum` produces the multi-dimensional Cerf birth–death normal form

`F_s(x, zₛ, zᵤ) = x³ / 3 - s x + (‖zₛ‖² - ‖zᵤ‖²) / 2` (`TauCeti.birthDeathNormalForm`)

on `WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))`. Under the transverse rescaling `(x, z) ↦ (x, √2 • z)`
(`TauCeti.birthDeathTransverseRescale`), this potential becomes the unhalved normal form
`x³ / 3 - s x + (‖zₛ‖² - ‖zᵤ‖²)` (`TauCeti.birthDeathNormalForm_birthDeathTransverseRescale`). The
halved normalization is natural for Riemannian gradient dynamics because the transverse Hessian is
the isometric involution `(wₛ, wᵤ) ↦ (wₛ, -wᵤ)` and the transverse negative gradient flow is
`t ↦ (e^{-t} zₛ, e^t zᵤ)`.

At the birth–death point `(s, z) = (0, 0)` on a Hilbert space (`[CompleteSpace Eₛ]` and
`[CompleteSpace Eᵤ]`), `F_s` satisfies all three coordinate-free `A₂` hypotheses:

1. **Corank-one Hessian kernel:** the kernel of `hessianOperator (birthDeathNormalForm 0) 0` is the
   one-dimensional line `ℝ ∙ birthDeathKernelVector` spanned by `(1, 0)`
   (`TauCeti.ker_hessianOperator_birthDeathNormalForm_zero`,
   `TauCeti.finrank_ker_hessianOperator_birthDeathNormalForm_zero`).
2. **Nonvanishing cubic invariant along the kernel:** the third Fréchet derivative of
   `birthDeathNormalForm s` at `z` evaluated three times at `birthDeathKernelVector` equals `2 ≠ 0`
   (`TauCeti.fderiv_fderiv_fderiv_birthDeathNormalForm_apply_kernelVector`,
   `TauCeti.iteratedDeriv_three_birthDeathNormalForm_kernelVector`).
3. **Parameter transversality along the kernel:** differentiating
   `s ↦ fderiv ℝ (birthDeathNormalForm s) z birthDeathKernelVector` yields `-1 ≠ 0`
   (`TauCeti.hasDerivAt_fderiv_birthDeathNormalForm_apply_kernelVector`).

Varying `s` across `0` yields the complete multi-dimensional bifurcation trichotomy across the whole
ambient space:

* **Before the birth (`s < 0`):** `F_s` has no critical points
  (`TauCeti.fderiv_birthDeathNormalForm_ne_zero`) and admits no global negative gradient trajectory
  on `ℝ` because the fold coordinate blows up in finite time
  (`TauCeti.not_isIntegralCurve_birthDeathNormalForm_of_neg`).
* **At the birth–death instant (`s = 0`):** the origin is the unique critical point (degenerate
  along `birthDeathKernelVector`), and the constant zero trajectory is the unique global negative
  gradient trajectory with finite limits at both ends
  (`TauCeti.eq_zero_of_isIntegralCurve_birthDeathNormalForm_zero`).
* **After the birth (`s > 0`):** `F_s` has exactly two critical points on the whole space, both
  nondegenerate: `birthDeathUpper s = (-√s, 0)` and `birthDeathLower s = (√s, 0)`. Thus `F_s` has
  nondegenerate critical points on `univ` if and only if `s ≠ 0`
  (`TauCeti.hasNondegenerateCriticalPointsOn_birthDeathNormalForm_iff`). Every global trajectory
  from `birthDeathUpper s` to `birthDeathLower s` is a unique time translate of
  `birthDeathNormalFormOrbit s` (`TauCeti.existsUnique_eq_birthDeathNormalFormOrbit_comp_add`), and
  no reverse trajectory runs from `birthDeathLower s` to `birthDeathUpper s` — see
  `TauCeti.not_isIntegralCurve_birthDeathNormalForm_of_tendsto_atBot_lower_of_tendsto_atTop_upper`.
  When `Eₛ` and `Eᵤ` are finite dimensional, `birthDeathUpper s` and `birthDeathLower s` have Morse
  indices `dim Eᵤ + 1` and `dim Eᵤ`.

## Main declarations

* `TauCeti.birthDeathNormalForm`, `TauCeti.birthDeathUpper`, `TauCeti.birthDeathLower`,
  `TauCeti.birthDeathNormalFormOrbit`, `TauCeti.birthDeathKernelVector`,
  `TauCeti.birthDeathTransverseRescale`.
* `TauCeti.fderiv_birthDeathNormalForm_eq_zero_iff`,
  `TauCeti.isNondegenerateCriticalPoint_birthDeathNormalForm_iff`,
  `TauCeti.ker_hessianOperator_birthDeathNormalForm_zero`,
  `TauCeti.finrank_ker_hessianOperator_birthDeathNormalForm_zero`,
  `TauCeti.fderiv_fderiv_fderiv_birthDeathNormalForm_apply_kernelVector`,
  `TauCeti.iteratedDeriv_three_birthDeathNormalForm_kernelVector`,
  `TauCeti.hasDerivAt_fderiv_birthDeathNormalForm_apply_kernelVector`,
  `TauCeti.hasNondegenerateCriticalPointsOn_birthDeathNormalForm_iff`.
* `TauCeti.not_isIntegralCurve_birthDeathNormalForm_of_neg`,
  `TauCeti.eq_zero_of_isIntegralCurve_birthDeathNormalForm_zero`,
  `TauCeti.existsUnique_eq_birthDeathNormalFormOrbit_comp_add`,
  `TauCeti.not_isIntegralCurve_birthDeathNormalForm_of_tendsto_atBot_lower_of_tendsto_atTop_upper`,
  `TauCeti.morseIndex_birthDeathNormalForm_upper`,
  `TauCeti.morseIndex_birthDeathNormalForm_lower`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173.
* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2.
-/

public section

open Filter InnerProductSpace Set
open scoped Gradient Topology

namespace TauCeti

/-! ### Definitions and coordinate normal forms -/

section Defs

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedAddCommGroup Eᵤ]

/-- **The multi-dimensional Cerf birth–death (`A₂`) normal form.** On the orthogonal `L²` sum
`WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))` of the fold line `ℝ` with a stable-unstable transverse model
`WithLp 2 (Eₛ × Eᵤ)`, `birthDeathNormalForm s` is the separated sum
`birthDeathPotential s x + splitQuadratic (zₛ, zᵤ) = x³ / 3 - s x + (‖zₛ‖² - ‖zᵤ‖²) / 2`. -/
noncomputable def birthDeathNormalForm (s : ℝ) :
    WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) → ℝ :=
  separatedSum (birthDeathPotential s) (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))

theorem birthDeathNormalForm_def (s : ℝ) :
    birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s =
      separatedSum (birthDeathPotential s) (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) :=
  (rfl)

theorem birthDeathNormalForm_apply (s : ℝ) (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    birthDeathNormalForm s z =
      birthDeathPotential s z.fst + (‖z.snd.fst‖ ^ 2 - ‖z.snd.snd‖ ^ 2) / 2 := by
  rw [birthDeathNormalForm, separatedSum_apply, splitQuadratic_apply]

@[simp]
theorem birthDeathNormalForm_zero_right (s : ℝ) :
    birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s 0 = 0 := by
  simp [birthDeathNormalForm]

/-- The upper newborn critical point `(-√s, 0)` of `birthDeathNormalForm s` (`s > 0`), of Morse
index `dim Eᵤ + 1` when `Eₛ` and `Eᵤ` are finite dimensional. -/
noncomputable def birthDeathUpper (s : ℝ) : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (-√s, 0)

theorem birthDeathUpper_def (s : ℝ) :
    birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) s = WithLp.toLp 2 (-√s, 0) :=
  (rfl)

/-- The lower newborn critical point `(√s, 0)` of `birthDeathNormalForm s` (`s > 0`), of Morse
index `dim Eᵤ` when `Eₛ` and `Eᵤ` are finite dimensional. -/
noncomputable def birthDeathLower (s : ℝ) : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (√s, 0)

theorem birthDeathLower_def (s : ℝ) :
    birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) s = WithLp.toLp 2 (√s, 0) :=
  (rfl)

@[simp] theorem birthDeathUpper_fst (s : ℝ) :
    (birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) s).fst = -√s := by simp [birthDeathUpper]

@[simp] theorem birthDeathUpper_snd (s : ℝ) :
    (birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) s).snd = 0 := by simp [birthDeathUpper]

@[simp] theorem birthDeathLower_fst (s : ℝ) :
    (birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) s).fst = √s := by simp [birthDeathLower]

@[simp] theorem birthDeathLower_snd (s : ℝ) :
    (birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) s).snd = 0 := by simp [birthDeathLower]

@[simp]
theorem birthDeathUpper_zero :
    birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0 = 0 :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathLower_zero :
    birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0 = 0 :=
  WithLp.prod_ext (by simp) (by simp)

theorem birthDeathUpper_ne_birthDeathLower {s : ℝ} (hs : 0 < s) :
    birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) s ≠ birthDeathLower s := by
  intro h
  have h1 := congrArg WithLp.fst h
  simp only [birthDeathUpper_fst, birthDeathLower_fst] at h1
  linarith [Real.sqrt_pos.2 hs]

@[simp]
theorem birthDeathNormalForm_upper (s : ℝ) :
    birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s (birthDeathUpper s) =
      2 * s * √s / 3 := by
  rw [birthDeathNormalForm_apply]
  simp

@[simp]
theorem birthDeathNormalForm_lower (s : ℝ) :
    birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s (birthDeathLower s) =
      -(2 * s * √s / 3) := by
  rw [birthDeathNormalForm_apply]
  simp

/-- The reference connecting trajectory `t ↦ (√s * tanh (√s * t), 0)` of
`birthDeathNormalForm s`. -/
noncomputable def birthDeathNormalFormOrbit (s t : ℝ) : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (birthDeathOrbit s t, 0)

theorem birthDeathNormalFormOrbit_def (s t : ℝ) :
    birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s t =
      WithLp.toLp 2 (birthDeathOrbit s t, 0) :=
  (rfl)

@[simp] theorem birthDeathNormalFormOrbit_fst (s t : ℝ) :
    (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s t).fst = birthDeathOrbit s t := by
  simp [birthDeathNormalFormOrbit]

@[simp] theorem birthDeathNormalFormOrbit_snd (s t : ℝ) :
    (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s t).snd = 0 := by
  simp [birthDeathNormalFormOrbit]

@[simp]
theorem birthDeathNormalFormOrbit_zero (s : ℝ) :
    birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s 0 = 0 :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathNormalFormOrbit_neg (s t : ℝ) :
    birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s (-t) =
      -birthDeathNormalFormOrbit s t :=
  WithLp.prod_ext (by simp) (by simp)

/-- The unit vector `(1, 0)` spanning the one-dimensional kernel of the Hessian of
`birthDeathNormalForm 0` at the origin. -/
noncomputable def birthDeathKernelVector : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (1, 0)

theorem birthDeathKernelVector_def :
    birthDeathKernelVector (Eₛ := Eₛ) (Eᵤ := Eᵤ) = WithLp.toLp 2 (1, 0) :=
  (rfl)

@[simp] theorem birthDeathKernelVector_fst :
    (birthDeathKernelVector (Eₛ := Eₛ) (Eᵤ := Eᵤ)).fst = 1 := by simp [birthDeathKernelVector]

@[simp] theorem birthDeathKernelVector_snd :
    (birthDeathKernelVector (Eₛ := Eₛ) (Eᵤ := Eᵤ)).snd = 0 := by simp [birthDeathKernelVector]

theorem birthDeathKernelVector_ne_zero :
    birthDeathKernelVector (Eₛ := Eₛ) (Eᵤ := Eᵤ) ≠ 0 := by
  intro h
  have h1 := congrArg WithLp.fst h
  simp at h1

@[simp]
theorem norm_birthDeathKernelVector :
    ‖birthDeathKernelVector (Eₛ := Eₛ) (Eᵤ := Eᵤ)‖ = 1 := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp

end Defs

section Rescale

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]

/-- For each parameter `s`, `birthDeathNormalFormOrbit s` is smooth. -/
@[fun_prop]
theorem contDiff_birthDeathNormalFormOrbit (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).symm.contDiff.comp
    ((contDiff_birthDeathOrbit s).prodMk contDiff_const)

@[fun_prop]
theorem continuous_birthDeathNormalFormOrbit (s : ℝ) :
    Continuous (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) :=
  (contDiff_birthDeathNormalFormOrbit (n := 0) s).continuous

@[fun_prop]
theorem differentiable_birthDeathNormalFormOrbit (s : ℝ) :
    Differentiable ℝ (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) :=
  (contDiff_birthDeathNormalFormOrbit (n := 1) s).differentiable one_ne_zero

/-- For `s ≥ 0`, `birthDeathNormalFormOrbit s` has velocity `(s - (birthDeathOrbit s t)², 0)` at
`t`. -/
theorem hasDerivAt_birthDeathNormalFormOrbit {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    HasDerivAt (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s)
      (WithLp.toLp 2 (s - birthDeathOrbit s t ^ 2, 0)) t := by
  rw [funext (birthDeathNormalFormOrbit_def s)]
  simpa [Function.comp_def] using
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).symm.hasFDerivAt.comp_hasDerivAt
      t ((hasDerivAt_birthDeathOrbit hs t).prodMk (hasDerivAt_const t (0 : WithLp 2 (Eₛ × Eᵤ))))

/-- For `s ≥ 0`, the derivative of `birthDeathNormalFormOrbit s` at `t` is
`WithLp.toLp 2 (s - birthDeathOrbit s t ^ 2, 0)`. -/
theorem deriv_birthDeathNormalFormOrbit {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    deriv (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) t =
      WithLp.toLp 2 (s - birthDeathOrbit s t ^ 2, 0) :=
  (hasDerivAt_birthDeathNormalFormOrbit hs t).deriv

/-- `birthDeathNormalFormOrbit s` tends to `birthDeathUpper s` at `-∞`. -/
theorem tendsto_birthDeathNormalFormOrbit_atBot (s : ℝ) :
    Tendsto (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) atBot (𝓝 (birthDeathUpper s)) := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (WithLp 2 (Eₛ × Eᵤ))).symm.continuous.tendsto (-√s, 0)
  exact h.comp ((tendsto_birthDeathOrbit_atBot s).prodMk_nhds tendsto_const_nhds)

/-- `birthDeathNormalFormOrbit s` tends to `birthDeathLower s` at `+∞`. -/
theorem tendsto_birthDeathNormalFormOrbit_atTop (s : ℝ) :
    Tendsto (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) atTop (𝓝 (birthDeathLower s)) := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (WithLp 2 (Eₛ × Eᵤ))).symm.continuous.tendsto (√s, 0)
  exact h.comp ((tendsto_birthDeathOrbit_atTop s).prodMk_nhds tendsto_const_nhds)

/-- **Equivalence with the unhalved quadratic normal form.** Rescaling the transverse factor by `√2`
gives a continuous linear equivalence `(x, z) ↦ (x, √2 • z)` pulling `birthDeathNormalForm s` back
to `x³ / 3 - s x + (‖zₛ‖² - ‖zᵤ‖²)`. -/
noncomputable def birthDeathTransverseRescale :
    WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ≃L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.smulLeft
        (Units.mk0 (√2 : ℝ) (Real.sqrt_pos.2 two_pos).ne')))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).symm

@[simp] theorem birthDeathTransverseRescale_fst (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    (birthDeathTransverseRescale z).fst = z.fst := by simp [birthDeathTransverseRescale]

@[simp] theorem birthDeathTransverseRescale_snd (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    (birthDeathTransverseRescale z).snd = (√2 : ℝ) • z.snd := by simp [birthDeathTransverseRescale]

@[simp]
theorem birthDeathTransverseRescale_symm_fst (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    (birthDeathTransverseRescale.symm z).fst = z.fst := by
  have h := congrArg WithLp.fst (birthDeathTransverseRescale.apply_symm_apply z)
  rwa [birthDeathTransverseRescale_fst] at h

@[simp]
theorem birthDeathTransverseRescale_symm_snd (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    (birthDeathTransverseRescale.symm z).snd = (√2 : ℝ)⁻¹ • z.snd := by
  have h := congrArg WithLp.snd (birthDeathTransverseRescale.apply_symm_apply z)
  rw [birthDeathTransverseRescale_snd] at h
  rw [← h, inv_smul_smul₀ (Real.sqrt_pos.2 two_pos).ne']

@[simp]
theorem birthDeathTransverseRescale_birthDeathUpper (s : ℝ) :
    birthDeathTransverseRescale (birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) = birthDeathUpper s :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathTransverseRescale_birthDeathLower (s : ℝ) :
    birthDeathTransverseRescale (birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) = birthDeathLower s :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathTransverseRescale_birthDeathNormalFormOrbit (s t : ℝ) :
    birthDeathTransverseRescale (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s t) =
      birthDeathNormalFormOrbit s t :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathTransverseRescale_birthDeathKernelVector :
    birthDeathTransverseRescale (birthDeathKernelVector (Eₛ := Eₛ) (Eᵤ := Eᵤ)) =
      birthDeathKernelVector :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathTransverseRescale_symm_birthDeathUpper (s : ℝ) :
    birthDeathTransverseRescale.symm (birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) =
      birthDeathUpper s :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathTransverseRescale_symm_birthDeathLower (s : ℝ) :
    birthDeathTransverseRescale.symm (birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) =
      birthDeathLower s :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathTransverseRescale_symm_birthDeathNormalFormOrbit (s t : ℝ) :
    birthDeathTransverseRescale.symm (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s t) =
      birthDeathNormalFormOrbit s t :=
  WithLp.prod_ext (by simp) (by simp)

@[simp]
theorem birthDeathTransverseRescale_symm_birthDeathKernelVector :
    birthDeathTransverseRescale.symm (birthDeathKernelVector (Eₛ := Eₛ) (Eᵤ := Eᵤ)) =
      birthDeathKernelVector :=
  WithLp.prod_ext (by simp) (by simp)

/-- Pulling `birthDeathNormalForm s` back along `birthDeathTransverseRescale` produces the unhalved
normal form `x³ / 3 - s x + (‖zₛ‖² - ‖zᵤ‖²)`. -/
theorem birthDeathNormalForm_birthDeathTransverseRescale (s : ℝ)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    birthDeathNormalForm s (birthDeathTransverseRescale z) =
      z.fst ^ 3 / 3 - s * z.fst + (‖z.snd.fst‖ ^ 2 - ‖z.snd.snd‖ ^ 2) := by
  rw [birthDeathNormalForm_apply, birthDeathTransverseRescale_fst, birthDeathTransverseRescale_snd,
    birthDeathPotential_apply, WithLp.smul_fst, WithLp.smul_snd, norm_smul, norm_smul,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, mul_pow, Real.sq_sqrt zero_le_two]
  ring

end Rescale

/-! ### Smoothness, critical points, and `A₂` invariants on inner product spaces -/

section InnerProduct

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ]

/-- `birthDeathNormalForm` is jointly smooth in `(s, z)`. -/
@[fun_prop]
theorem contDiff_birthDeathNormalForm_uncurry {n : WithTop ℕ∞} :
    ContDiff ℝ n (Function.uncurry (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ))) := by
  have heq : Function.uncurry (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ)) =
      fun p : ℝ × WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦
        birthDeathPotential p.1 p.2.fst + splitQuadratic p.2.snd := by
    funext ⟨s, z⟩
    simp [birthDeathNormalForm]
  rw [heq]
  have hfst : ContDiff ℝ n
      (fun p : ℝ × WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦ (p.1, p.2.fst)) :=
    contDiff_fst.prodMk ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).contDiff.comp contDiff_snd)
  have hsnd : ContDiff ℝ n
      (fun p : ℝ × WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦ p.2.snd) :=
    (WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).contDiff.comp contDiff_snd
  exact (contDiff_birthDeathPotential_uncurry.comp hfst).add (contDiff_splitQuadratic.comp hsnd)

/-- For each parameter `s`, `birthDeathNormalForm s` is smooth. -/
@[fun_prop]
theorem contDiff_birthDeathNormalForm (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) :=
  (contDiff_birthDeathPotential s).separatedSum contDiff_splitQuadratic

@[fun_prop]
theorem continuous_birthDeathNormalForm (s : ℝ) :
    Continuous (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) :=
  (contDiff_birthDeathNormalForm (n := 0) s).continuous

@[fun_prop]
theorem differentiable_birthDeathNormalForm (s : ℝ) :
    Differentiable ℝ (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) :=
  (contDiff_birthDeathNormalForm (n := 1) s).differentiable one_ne_zero

/-- The Hessian quadratic form of `birthDeathNormalForm s` at `z` is
`2 z.fst v.fst² + ‖v.snd.fst‖² - ‖v.snd.snd‖²`. -/
theorem hessianQuadraticForm_birthDeathNormalForm_apply (s : ℝ)
    (z v : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    hessianQuadraticForm (birthDeathNormalForm s) z v =
      2 * z.fst * v.fst ^ 2 + (‖v.snd.fst‖ ^ 2 - ‖v.snd.snd‖ ^ 2) := by
  rw [birthDeathNormalForm, hessianQuadraticForm_separatedSum_apply
      (contDiff_birthDeathPotential s).contDiffAt contDiff_splitQuadratic.contDiffAt,
    hessianQuadraticForm_birthDeathPotential_apply, hessianQuadraticForm_splitQuadratic_apply]

/-- Along the line generated by `birthDeathKernelVector`, `birthDeathNormalForm s` restricts to
`birthDeathPotential s`. -/
@[simp]
theorem birthDeathNormalForm_smul_kernelVector (s t : ℝ) :
    birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s (t • birthDeathKernelVector) =
      birthDeathPotential s t := by
  rw [birthDeathNormalForm_apply, WithLp.smul_fst, WithLp.smul_snd, birthDeathKernelVector_fst,
    birthDeathKernelVector_snd, smul_eq_mul, mul_one, smul_zero]
  simp

/-- **Cubic `A₂` invariant along the Hessian-kernel line.** Restricting `birthDeathNormalForm s` to
`t ↦ t • birthDeathKernelVector` has third derivative `2 ≠ 0` at every `t₀ : ℝ`. -/
theorem iteratedDeriv_three_birthDeathNormalForm_kernelVector (s t₀ : ℝ) :
    iteratedDeriv 3
      (fun t : ℝ ↦ birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s (t • birthDeathKernelVector))
      t₀ = 2 := by
  simp only [birthDeathNormalForm_smul_kernelVector, iteratedDeriv_three_birthDeathPotential]

/-- The directional derivative of `birthDeathNormalForm s` at `z` along `birthDeathKernelVector` is
`z.fst ^ 2 - s`. -/
@[simp]
theorem fderiv_birthDeathNormalForm_apply_kernelVector (s : ℝ)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    fderiv ℝ (birthDeathNormalForm s) z birthDeathKernelVector = z.fst ^ 2 - s := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))
  have hez : e z = (z.fst, z.snd) := by ext <;> simp [e]
  have hev : e birthDeathKernelVector = (1, 0) := by ext <;> simp [e]
  rw [birthDeathNormalForm_def, separatedSum_eq_comp, e.comp_right_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hez, hev,
    fderiv_comp_fst_add_comp_snd (differentiable_birthDeathPotential s z.fst)
      (differentiable_splitQuadratic z.snd)]
  simp [← toSpanSingleton_deriv]

/-- **Ambient cubic `A₂` invariant in arbitrary dimension.** The third Fréchet derivative of
`birthDeathNormalForm s` at `z`, evaluated three times at `birthDeathKernelVector`, equals
`2 ≠ 0`. -/
@[simp]
theorem fderiv_fderiv_fderiv_birthDeathNormalForm_apply_kernelVector (s : ℝ)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (birthDeathNormalForm s))) z
      birthDeathKernelVector birthDeathKernelVector birthDeathKernelVector = 2 := by
  let L := WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))
  rw [← fderiv_fderiv_fderiv_apply (contDiff_birthDeathNormalForm (n := 3) s).contDiffAt,
    funext (fderiv_birthDeathNormalForm_apply_kernelVector s)]
  have hfirst : fderiv ℝ (fun y : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦ y.fst ^ 2 - s) =
      L.smulRight ((2 : ℝ) • L) := by
    ext y w
    have hd : HasFDerivAt (fun q : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦ (L q) ^ 2 - s)
        (L.smulRight ((2 : ℝ) • L) y) y := by
      refine (((L.hasFDerivAt (x := y)).pow 2).sub_const s).congr_fderiv ?_
      ext u
      simp [L]
      ring
    exact DFunLike.congr_fun hd.fderiv w
  rw [hfirst, ContinuousLinearMap.fderiv]
  simp [L]

/-- **Parameter transversality of the `A₂` normal form.** Differentiating the directional
derivative of `birthDeathNormalForm ν` at `z` along `birthDeathKernelVector` with respect to `ν`
gives `-1 ≠ 0`. -/
theorem hasDerivAt_fderiv_birthDeathNormalForm_apply_kernelVector (s : ℝ)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    HasDerivAt
      (fun ν ↦ fderiv ℝ (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) ν) z birthDeathKernelVector)
      (-1) s := by
  simp only [fderiv_birthDeathNormalForm_apply_kernelVector]
  simpa using (hasDerivAt_id' s).const_sub (z.fst ^ 2)

/-- **Critical points of `birthDeathNormalForm s` on any inner product space.** A point `z` is
critical for `birthDeathNormalForm s` if and only if `z.fst ^ 2 = s` and `z.snd = 0`. -/
theorem fderiv_birthDeathNormalForm_eq_zero_iff {s : ℝ}
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    fderiv ℝ (birthDeathNormalForm s) z = 0 ↔ z.fst ^ 2 = s ∧ z.snd = 0 := by
  rw [birthDeathNormalForm_def,
    fderiv_separatedSum_eq_zero_iff (differentiable_birthDeathPotential s z.fst)
      (differentiable_splitQuadratic z.snd),
    fderiv_birthDeathPotential_eq_zero_iff, fderiv_splitQuadratic_eq_zero_iff]

/-- Before the birth (`s < 0`), `birthDeathNormalForm s` has no critical points on any inner product
space. -/
theorem fderiv_birthDeathNormalForm_ne_zero {s : ℝ} (hs : s < 0)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    fderiv ℝ (birthDeathNormalForm s) z ≠ 0 := by
  rw [ne_eq, fderiv_birthDeathNormalForm_eq_zero_iff]
  rintro ⟨h, -⟩
  nlinarith [sq_nonneg z.fst]

/-- At `s = 0`, the origin is the unique critical point of `birthDeathNormalForm 0` on any inner
product space. -/
@[simp]
theorem fderiv_birthDeathNormalForm_zero_eq_zero_iff
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    fderiv ℝ (birthDeathNormalForm 0) z = 0 ↔ z = 0 := by
  rw [fderiv_birthDeathNormalForm_eq_zero_iff, sq_eq_zero_iff]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ WithLp.prod_ext h₁ h₂, fun h ↦ by simp [h]⟩

/-- For `s > 0`, the critical points of `birthDeathNormalForm s` on any inner product space are
`birthDeathUpper s` and `birthDeathLower s`. -/
theorem fderiv_birthDeathNormalForm_eq_zero_iff_of_pos {s : ℝ} (hs : 0 < s)
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    fderiv ℝ (birthDeathNormalForm s) z = 0 ↔
      z = birthDeathUpper s ∨ z = birthDeathLower s := by
  rw [fderiv_birthDeathNormalForm_eq_zero_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h₁.trans (Real.sq_sqrt hs.le).symm) with hfst | hfst
    · exact .inr (WithLp.prod_ext hfst h₂)
    · exact .inl (WithLp.prod_ext hfst h₂)
  · rintro (rfl | rfl) <;> simp [Real.sq_sqrt hs.le]

/-- At `s = 0`, no point is a nondegenerate critical point of `birthDeathNormalForm 0`. -/
theorem not_isNondegenerateCriticalPoint_birthDeathNormalForm_zero
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    ¬IsNondegenerateCriticalPoint (birthDeathNormalForm 0) z := by
  rw [birthDeathNormalForm, isNondegenerateCriticalPoint_separatedSum_iff]
  rintro ⟨h₁, -⟩
  rw [isNondegenerateCriticalPoint_birthDeathPotential_iff] at h₁
  exact h₁.2 (sq_eq_zero_iff.1 h₁.1)

end InnerProduct

/-! ### Gradient, Hessian operator, critical points, and global trajectories on Hilbert spaces -/

section Hilbert

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ] [CompleteSpace Eₛ]
  [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ] [CompleteSpace Eᵤ]

/-- The gradient of `birthDeathNormalForm s` at `(x, (zₛ, zᵤ))` is `(x² - s, (zₛ, -zᵤ))`. -/
@[simp]
theorem gradient_birthDeathNormalForm (s : ℝ) (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    ∇ (birthDeathNormalForm s) z =
      WithLp.toLp 2 (z.fst ^ 2 - s, WithLp.toLp 2 (z.snd.fst, -z.snd.snd)) := by
  rw [birthDeathNormalForm, gradient_separatedSum
      (differentiable_birthDeathPotential s z.fst) (differentiable_splitQuadratic z.snd),
    gradient_birthDeathPotential, gradient_splitQuadratic]

/-- The Hessian operator of `birthDeathNormalForm s` at `(x, (zₛ, zᵤ))` sends `(v₁, (vₛ, vᵤ))` to
`(2 x v₁, (vₛ, -vᵤ))`. -/
@[simp]
theorem hessianOperator_birthDeathNormalForm_apply (s : ℝ)
    (z v : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    hessianOperator (birthDeathNormalForm s) z v =
      WithLp.toLp 2 (2 * z.fst * v.fst, WithLp.toLp 2 (v.snd.fst, -v.snd.snd)) := by
  rw [birthDeathNormalForm, hessianOperator_separatedSum_apply
      (contDiff_birthDeathPotential s).contDiffAt contDiff_splitQuadratic.contDiffAt,
    hessianOperator_birthDeathPotential, hessianOperator_splitQuadratic_apply,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- **Corank-one Hessian kernel at `(s, z) = (0, 0)`.** The kernel of
`hessianOperator (birthDeathNormalForm 0) 0` is the line `ℝ ∙ birthDeathKernelVector`. -/
theorem ker_hessianOperator_birthDeathNormalForm_zero :
    (hessianOperator (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0) 0).ker =
      ℝ ∙ birthDeathKernelVector := by
  ext v
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_span_singleton]
  constructor
  · intro hv
    rw [hessianOperator_birthDeathNormalForm_apply] at hv
    have hs : v.snd.fst = 0 := by simpa using congrArg (fun w ↦ w.snd.fst) hv
    have hu : -v.snd.snd = 0 := by simpa using congrArg (fun w ↦ w.snd.snd) hv
    exact ⟨v.fst, WithLp.prod_ext (by simp)
      (WithLp.prod_ext (by simp [hs]) (by simp [neg_eq_zero.1 hu]))⟩
  · rintro ⟨c, rfl⟩
    rw [hessianOperator_birthDeathNormalForm_apply]
    exact WithLp.prod_ext (by simp) (WithLp.prod_ext (by simp) (by simp))

/-- **The Hessian kernel at the birth–death point has dimension `1`**, even on infinite-dimensional
Hilbert spaces `Eₛ` and `Eᵤ`. -/
@[simp]
theorem finrank_ker_hessianOperator_birthDeathNormalForm_zero :
    Module.finrank ℝ
      (hessianOperator (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0) 0).ker = 1 := by
  rw [ker_hessianOperator_birthDeathNormalForm_zero,
    finrank_span_singleton birthDeathKernelVector_ne_zero]

/-- **Nondegenerate critical points of `birthDeathNormalForm s` on a Hilbert space.** A point `z`
is a nondegenerate critical point of `birthDeathNormalForm s` if and only if `z.fst ^ 2 = s`,
`z.fst ≠ 0`, and `z.snd = 0`. -/
theorem isNondegenerateCriticalPoint_birthDeathNormalForm_iff {s : ℝ}
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    IsNondegenerateCriticalPoint (birthDeathNormalForm s) z ↔
      z.fst ^ 2 = s ∧ z.fst ≠ 0 ∧ z.snd = 0 := by
  rw [birthDeathNormalForm_def, isNondegenerateCriticalPoint_separatedSum_iff,
    isNondegenerateCriticalPoint_birthDeathPotential_iff,
    isNondegenerateCriticalPoint_splitQuadratic_iff, and_assoc]

/-- For `s > 0`, `birthDeathUpper s = (-√s, 0)` is a nondegenerate critical point of
`birthDeathNormalForm s`. -/
theorem isNondegenerateCriticalPoint_birthDeathNormalForm_upper {s : ℝ} (hs : 0 < s) :
    IsNondegenerateCriticalPoint
      (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) (birthDeathUpper s) :=
  (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs).separatedSum
    isNondegenerateCriticalPoint_splitQuadratic_zero

/-- For `s > 0`, `birthDeathLower s = (√s, 0)` is a nondegenerate critical point of
`birthDeathNormalForm s`. -/
theorem isNondegenerateCriticalPoint_birthDeathNormalForm_lower {s : ℝ} (hs : 0 < s) :
    IsNondegenerateCriticalPoint
      (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) (birthDeathLower s) :=
  (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs).separatedSum
    isNondegenerateCriticalPoint_splitQuadratic_zero

/-- **Nondegenerate critical points of `birthDeathNormalForm s` (`s > 0`).** The nondegenerate
critical points are `birthDeathUpper s` and `birthDeathLower s`. -/
theorem isNondegenerateCriticalPoint_birthDeathNormalForm_iff_of_pos {s : ℝ} (hs : 0 < s)
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    IsNondegenerateCriticalPoint (birthDeathNormalForm s) z ↔
      z = birthDeathUpper s ∨ z = birthDeathLower s := by
  refine ⟨fun hz ↦ (fderiv_birthDeathNormalForm_eq_zero_iff_of_pos hs).1 hz.fderiv_eq_zero, ?_⟩
  rintro (rfl | rfl)
  · exact isNondegenerateCriticalPoint_birthDeathNormalForm_upper hs
  · exact isNondegenerateCriticalPoint_birthDeathNormalForm_lower hs

/-- **Morse characterization of the multi-dimensional birth–death family.** On any Hilbert space,
`birthDeathNormalForm s` has nondegenerate critical points on `univ` if and only if `s ≠ 0`. -/
@[simp]
theorem hasNondegenerateCriticalPointsOn_birthDeathNormalForm_iff {s : ℝ} :
    HasNondegenerateCriticalPointsOn
      (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) univ ↔ s ≠ 0 := by
  refine ⟨fun h hs0 ↦ ?_, fun hs ↦ ?_⟩
  · subst hs0
    exact not_isNondegenerateCriticalPoint_birthDeathNormalForm_zero 0
      (hasNondegenerateCriticalPointsOn_iff.1 h (mem_univ 0)
        (fderiv_birthDeathNormalForm_zero_eq_zero_iff.2 rfl))
  · rw [birthDeathNormalForm_def]
    exact (hasNondegenerateCriticalPointsOn_birthDeathPotential_iff.2 hs).separatedSum
      hasNondegenerateCriticalPointsOn_splitQuadratic

/-- A curve `γ` is a negative gradient trajectory of `birthDeathNormalForm s` if and only if its
fold component solves `x' = -∇ (birthDeathPotential s) x` and its transverse component solves
`ζ' = -∇ splitQuadratic ζ`. -/
theorem isIntegralCurve_birthDeathNormalForm_iff {s : ℝ}
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z) ↔
      IsIntegralCurve (fun t ↦ (γ t).fst) (fun _ x ↦ -∇ (birthDeathPotential s) x) ∧
        IsIntegralCurve (fun t ↦ (γ t).snd) (fun _ w ↦ -∇ splitQuadratic w) :=
  isIntegralCurve_separatedSum_iff
    (fun t ↦ differentiable_birthDeathPotential s (γ t).fst)
    (fun t ↦ differentiable_splitQuadratic (γ t).snd)

/-- For `s ≥ 0`, `birthDeathNormalFormOrbit s` solves the negative gradient equation of
`birthDeathNormalForm s`. -/
theorem isIntegralCurve_birthDeathNormalFormOrbit {s : ℝ} (hs : 0 ≤ s) :
    IsIntegralCurve (birthDeathNormalFormOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) s)
      (fun _ z ↦ -∇ (birthDeathNormalForm s) z) :=
  isIntegralCurve_birthDeathOrbit_separatedSum hs
    (differentiable_splitQuadratic 0)
    (by simp [gradient_splitQuadratic])

/-- **Before the birth (`s < 0`), `birthDeathNormalForm s` admits no global negative gradient
trajectory on `ℝ`**, because the fold coordinate blows up in finite time. -/
theorem not_isIntegralCurve_birthDeathNormalForm_of_neg {s : ℝ} (hs : s < 0)
    (γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    ¬IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z) :=
  not_isIntegralCurve_separatedSum_birthDeathPotential_of_neg hs differentiable_splitQuadratic γ

/-- **At the birth–death instant `s = 0`, the constant zero trajectory is the unique global
connecting trajectory.** -/
theorem eq_zero_of_isIntegralCurve_birthDeathNormalForm_zero
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm 0) z))
    {p q : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q)) :
    p = 0 ∧ q = 0 ∧ γ = 0 := by
  obtain ⟨h₁, h₂⟩ := isIntegralCurve_birthDeathNormalForm_iff.1 hγ
  have hγ₁ : (fun t ↦ (γ t).fst) = 0 := eq_zero_of_isIntegralCurve_birthDeathPotential_zero h₁
  have hp₁ : p.fst = 0 := by
    have hlim := ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto p).comp hbot
    rw [show (⇑(WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))) ∘ γ) = 0 from
      funext fun t ↦ congrFun hγ₁ t] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hq₁ : q.fst = 0 := by
    have hlim := ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto q).comp htop
    rw [show (⇑(WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))) ∘ γ) = 0 from
      funext fun t ↦ congrFun hγ₁ t] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  obtain ⟨hp₂, hq₂, hγ₂⟩ := eq_zero_of_isIntegralCurve_splitQuadratic h₂
    (((WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto p).comp hbot)
    (((WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto q).comp htop)
  exact ⟨WithLp.prod_ext hp₁ hp₂, WithLp.prod_ext hq₁ hq₂,
    funext fun t ↦ WithLp.prod_ext (congrFun hγ₁ t) (congrFun hγ₂ t)⟩

/-- **Classification of the newborn connecting trajectory in arbitrary dimension.** For `s > 0`,
every global negative gradient trajectory of `birthDeathNormalForm s` from `birthDeathUpper s` at
`-∞` to `birthDeathLower s` at `+∞` is a unique time translate
`t ↦ birthDeathNormalFormOrbit s (t + τ)`. -/
theorem existsUnique_eq_birthDeathNormalFormOrbit_comp_add {s : ℝ} (hs : 0 < s)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s))) :
    ∃! τ : ℝ, γ = fun t ↦ birthDeathNormalFormOrbit s (t + τ) :=
  existsUnique_eq_birthDeathOrbit_separatedSum hs differentiable_splitQuadratic hγ hbot htop

/-- **No reverse connecting trajectory exists in arbitrary dimension.** For `s > 0`, no negative
gradient trajectory of `birthDeathNormalForm s` runs from `birthDeathLower s` at `-∞` to
`birthDeathUpper s` at `+∞`. -/
theorem not_isIntegralCurve_birthDeathNormalForm_of_tendsto_atBot_lower_of_tendsto_atTop_upper
    {s : ℝ} (hs : 0 < s) {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hbot : Tendsto γ atBot (𝓝 (birthDeathLower s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathUpper s))) :
    ¬IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z) :=
  not_isIntegralCurve_separatedSum_birthDeathPotential_of_tendsto_atBot_of_tendsto_atTop
    hs differentiable_splitQuadratic hbot htop

end Hilbert

/-! ### Morse indices on finite-dimensional spaces -/

section FiniteDimensional

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
  [FiniteDimensional ℝ Eₛ] [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ]
  [FiniteDimensional ℝ Eᵤ]

/-- **Morse index of `birthDeathUpper s`.** For `s > 0`, the upper newborn critical point `(-√s, 0)`
has Morse index `dim Eᵤ + 1`. -/
@[simp]
theorem morseIndex_birthDeathNormalForm_upper {s : ℝ} (hs : 0 < s) :
    morseIndex (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) (birthDeathUpper s) =
      Module.finrank ℝ Eᵤ + 1 := by
  rw [birthDeathNormalForm, birthDeathUpper,
    morseIndex_separatedSum_birthDeathPotential_neg_sqrt hs
      isNondegenerateCriticalPoint_splitQuadratic_zero,
    morseIndex_splitQuadratic]

/-- **Morse index of `birthDeathLower s`.** For `s > 0`, the lower newborn critical point `(√s, 0)`
has Morse index `dim Eᵤ`. -/
@[simp]
theorem morseIndex_birthDeathNormalForm_lower {s : ℝ} (hs : 0 < s) :
    morseIndex (birthDeathNormalForm (Eₛ := Eₛ) (Eᵤ := Eᵤ) s) (birthDeathLower s) =
      Module.finrank ℝ Eᵤ := by
  rw [birthDeathNormalForm, birthDeathLower,
    morseIndex_separatedSum_birthDeathPotential_sqrt hs
      isNondegenerateCriticalPoint_splitQuadratic_zero,
    morseIndex_splitQuadratic]

end FiniteDimensional

end TauCeti

end
