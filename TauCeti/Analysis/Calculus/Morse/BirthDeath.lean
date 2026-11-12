/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.FoldPotential
public import TauCeti.Analysis.Calculus.Morse.Prod
public import TauCeti.Analysis.Calculus.Morse.SplitModel
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The multi-dimensional Cerf birth-death (`A₂`) normal form

Let `Eₛ` and `Eᵤ` be real inner product spaces. Coupling the one-dimensional cubic fold potential
`TauCeti.foldPotential` with the transverse split quadratic model `TauCeti.splitQuadratic` via
`TauCeti.separatedSum` produces the multi-dimensional Cerf birth-death normal form

`F_μ(x, zₛ, zᵤ) = x³ / 3 + μ x + (‖zₛ‖² - ‖zᵤ‖²) / 2` (`TauCeti.birthDeathPotential`)

on `WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))`. Under the transverse rescaling `(x, z) ↦ (x, √2 • z)`
(`TauCeti.birthDeathTransverseRescale`), this potential becomes the unhalved normal form
`x³ / 3 + μ x + (‖zₛ‖² - ‖zᵤ‖²)` (`TauCeti.birthDeathPotential_birthDeathTransverseRescale`). The
halved normalization is the canonical one for Riemannian gradient dynamics because the transverse
Hessian is the exact isometric involution `(wₛ, wᵤ) ↦ (wₛ, -wᵤ)` and the transverse negative
gradient flow is `t ↦ (e^{-t} zₛ, e^t zᵤ)`.

At the birth-death point `(μ, z) = (0, 0)` on a Hilbert space (`[CompleteSpace Eₛ]` and
`[CompleteSpace Eᵤ]`), `F_μ` satisfies all three coordinate-free `A₂` hypotheses:

1. **Corank-one Hessian kernel:** the kernel of `hessianOperator (birthDeathPotential 0) 0` is the
   one-dimensional line `ℝ ∙ birthDeathKernelVector` spanned by `(1, 0)`
   (`TauCeti.ker_hessianOperator_birthDeathPotential_zero`,
   `TauCeti.finrank_ker_hessianOperator_birthDeathPotential_zero`).
2. **Nonvanishing cubic invariant along the kernel:** the third directional derivative of
   `birthDeathPotential 0` at `0` along `birthDeathKernelVector` equals `2 ≠ 0`
   (`TauCeti.iteratedDeriv_three_birthDeathPotential_kernelVector`).
3. **Parameter transversality along the kernel:** differentiating
   `ν ↦ fderiv ℝ (birthDeathPotential ν) 0 birthDeathKernelVector` at `ν = 0` yields `1 ≠ 0`
   (`TauCeti.hasDerivAt_fderiv_birthDeathPotential_kernelVector`).

Varying `μ` across `0` yields the complete multi-dimensional bifurcation trichotomy:

* **For `μ > 0`**, `F_μ` has no critical points and no global negative-gradient trajectory converges
  at either `+∞` or `-∞`.
* **At `μ = 0`**, the origin is the unique critical point (degenerate along
  `birthDeathKernelVector`), and the constant zero trajectory is the unique global
  negative-gradient trajectory with finite limits at both ends
  (`TauCeti.eq_zero_of_isIntegralCurve_birthDeathPotential_zero`).
* **For `μ = -a² < 0` (`a > 0`)**, `F_{-a²}` has exactly two critical points, both nondegenerate:
  `birthDeathUpper a = (-a, 0)` and `birthDeathLower a = (a, 0)`. Thus `F_μ` has nondegenerate
  critical points on the whole space if and only if `μ ≠ 0`
  (`TauCeti.hasNondegenerateCriticalPointsOn_birthDeathPotential_iff`).

On any pair of real Hilbert spaces, every global negative-gradient trajectory of `F_{-a²}` (`a > 0`)
from `birthDeathUpper a` to `birthDeathLower a` has vanishing transverse component and is a unique
time translate of `birthDeathOrbit a s = (a * tanh (a * s), 0)`
(`TauCeti.existsUnique_birthDeathOrbit_add_of_isIntegralCurve`), no reverse trajectory exists from
`birthDeathLower a` to `birthDeathUpper a`
(`TauCeti.not_isIntegralCurve_birthDeathPotential_lower_to_upper`), and the formal-adjoint
trajectory operator `-d/ds + Hess F_{-a²}(γ)` is injective on `W^{1,2}`
(`TauCeti.ker_trajectoryOperator_neg_birthDeathPotential_eq_bot`). When `Eₛ` and `Eᵤ` are finite
dimensional, `birthDeathUpper a` has Morse index `dim Eᵤ + 1`, `birthDeathLower a` has Morse index
`dim Eᵤ`, and the linearized trajectory operator `D_γ` is Fredholm of index `1`, surjective, with
one-dimensional kernel spanned by `γ'`, while the endpoint operators are bijective.

## Main declarations

* `TauCeti.birthDeathPotential`, `TauCeti.birthDeathUpper`, `TauCeti.birthDeathLower`,
  `TauCeti.birthDeathOrbit`, `TauCeti.birthDeathKernelVector`,
  `TauCeti.birthDeathTransverseRescale`.
* `TauCeti.ker_hessianOperator_birthDeathPotential_zero`,
  `TauCeti.finrank_ker_hessianOperator_birthDeathPotential_zero`,
  `TauCeti.iteratedDeriv_three_birthDeathPotential_kernelVector`,
  `TauCeti.hasDerivAt_fderiv_birthDeathPotential_kernelVector`,
  `TauCeti.hasNondegenerateCriticalPointsOn_birthDeathPotential_iff`.
* `TauCeti.eq_zero_of_isIntegralCurve_birthDeathPotential_zero`,
  `TauCeti.existsUnique_birthDeathOrbit_add_of_isIntegralCurve`,
  `TauCeti.not_isIntegralCurve_birthDeathPotential_lower_to_upper`,
  `TauCeti.ker_trajectoryOperator_neg_birthDeathPotential_eq_bot`,
  `TauCeti.index_trajectoryOperator_birthDeathPotential`,
  `TauCeti.surjective_trajectoryOperator_birthDeathPotential`,
  `TauCeti.exists_ker_trajectoryOperator_birthDeathPotential_eq_span`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173.
* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2.
-/

public section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Topology

namespace TauCeti

private theorem withLp_prod_ext {α β : Type*} {x y : WithLp 2 (α × β)}
    (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h₁ h₂)

/-! ### Definitions and coordinate normal forms -/

section BirthDeathDefs

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedAddCommGroup Eᵤ]

/-- **The multi-dimensional Cerf birth-death (`A₂`) normal form.** On the orthogonal `L²` sum
`WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))` of the fold line `ℝ` with a stable-unstable transverse model
`WithLp 2 (Eₛ × Eᵤ)`, `birthDeathPotential μ` is the separated sum
`foldPotential μ x + splitQuadratic (zₛ, zᵤ) = x³ / 3 + μ x + (‖zₛ‖² - ‖zᵤ‖²) / 2`. -/
noncomputable def birthDeathPotential (μ : ℝ) :
    WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) → ℝ :=
  separatedSum (foldPotential μ) (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))

theorem birthDeathPotential_apply (μ : ℝ) (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    birthDeathPotential μ z =
      foldPotential μ z.fst + (‖z.snd.fst‖ ^ 2 - ‖z.snd.snd‖ ^ 2) / 2 := by
  rw [birthDeathPotential, separatedSum_apply, splitQuadratic_apply]

@[simp]
theorem birthDeathPotential_zero_right (μ : ℝ) :
    birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) μ 0 = 0 := by
  simp [birthDeathPotential]

/-- The upper newborn critical point `(-a, 0)` of `birthDeathPotential (-a²)` (`a > 0`), of Morse
index `dim Eᵤ + 1` when `Eₛ` and `Eᵤ` are finite dimensional. -/
noncomputable def birthDeathUpper (a : ℝ) : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (-a, 0)

/-- The lower newborn critical point `(a, 0)` of `birthDeathPotential (-a²)` (`a > 0`), of Morse
index `dim Eᵤ` when `Eₛ` and `Eᵤ` are finite dimensional. -/
noncomputable def birthDeathLower (a : ℝ) : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (a, 0)

@[simp] theorem birthDeathUpper_fst (a : ℝ) :
    (birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) a).fst = -a := by simp [birthDeathUpper]

@[simp] theorem birthDeathUpper_snd (a : ℝ) :
    (birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) a).snd = 0 := by simp [birthDeathUpper]

@[simp] theorem birthDeathLower_fst (a : ℝ) :
    (birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) a).fst = a := by simp [birthDeathLower]

@[simp] theorem birthDeathLower_snd (a : ℝ) :
    (birthDeathLower (Eₛ := Eₛ) (Eᵤ := Eᵤ) a).snd = 0 := by simp [birthDeathLower]

theorem birthDeathUpper_ne_birthDeathLower {a : ℝ} (ha : a ≠ 0) :
    birthDeathUpper (Eₛ := Eₛ) (Eᵤ := Eᵤ) a ≠ birthDeathLower a := by
  intro h
  have h1 := congrArg WithLp.fst h
  simp only [birthDeathUpper_fst, birthDeathLower_fst] at h1
  exact ha (by linarith)

@[simp]
theorem birthDeathPotential_upper (a : ℝ) :
    birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) (-a ^ 2) (birthDeathUpper a) =
      2 * a ^ 3 / 3 := by
  rw [birthDeathPotential_apply]
  simp [foldPotential_neg_sq_self]

@[simp]
theorem birthDeathPotential_lower (a : ℝ) :
    birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) (-a ^ 2) (birthDeathLower a) =
      -(2 * a ^ 3 / 3) := by
  rw [birthDeathPotential_apply]
  simp [foldPotential_neg_sq_self]

/-- The reference connecting trajectory `s ↦ (a * tanh (a * s), 0)` of
`birthDeathPotential (-a²)`. -/
noncomputable def birthDeathOrbit (a s : ℝ) : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (foldOrbit a s, 0)

@[simp] theorem birthDeathOrbit_fst (a s : ℝ) :
    (birthDeathOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) a s).fst = foldOrbit a s := by simp [birthDeathOrbit]

@[simp] theorem birthDeathOrbit_snd (a s : ℝ) :
    (birthDeathOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) a s).snd = 0 := by simp [birthDeathOrbit]

/-- The unit vector `(1, 0)` spanning the one-dimensional kernel of the Hessian of
`birthDeathPotential 0` at the origin. -/
noncomputable def birthDeathKernelVector : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) :=
  WithLp.toLp 2 (1, 0)

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

end BirthDeathDefs

section BirthDeathRescale

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]

/-- For `a > 0`, `birthDeathOrbit a` tends to `birthDeathUpper a` at `-∞`. -/
theorem tendsto_birthDeathOrbit_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (birthDeathOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) a) atBot (𝓝 (birthDeathUpper a)) := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (WithLp 2 (Eₛ × Eᵤ))).symm.continuous.tendsto (-a, 0)
  exact h.comp ((tendsto_foldOrbit_atBot ha).prodMk_nhds tendsto_const_nhds)

/-- For `a > 0`, `birthDeathOrbit a` tends to `birthDeathLower a` at `+∞`. -/
theorem tendsto_birthDeathOrbit_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (birthDeathOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) a) atTop (𝓝 (birthDeathLower a)) := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (WithLp 2 (Eₛ × Eᵤ))).symm.continuous.tendsto (a, 0)
  exact h.comp ((tendsto_foldOrbit_atTop ha).prodMk_nhds tendsto_const_nhds)

/-- **Equivalence with the unhalved quadratic normal form.** Rescaling the transverse factor by `√2`
gives a continuous linear equivalence `(x, z) ↦ (x, √2 • z)` pulling `birthDeathPotential μ` back to
`x³ / 3 + μ x + (‖zₛ‖² - ‖zᵤ‖²)`. -/
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

/-- Pulling `birthDeathPotential μ` back along `birthDeathTransverseRescale` produces the unhalved
normal form `x³ / 3 + μ x + (‖zₛ‖² - ‖zᵤ‖²)`. -/
theorem birthDeathPotential_birthDeathTransverseRescale (μ : ℝ)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    birthDeathPotential μ (birthDeathTransverseRescale z) =
      z.fst ^ 3 / 3 + μ * z.fst + (‖z.snd.fst‖ ^ 2 - ‖z.snd.snd‖ ^ 2) := by
  rw [birthDeathPotential_apply, birthDeathTransverseRescale_fst, birthDeathTransverseRescale_snd,
    foldPotential_apply, WithLp.smul_fst, WithLp.smul_snd, norm_smul, norm_smul,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, mul_pow, Real.sq_sqrt zero_le_two]
  ring

end BirthDeathRescale

/-! ### Smoothness and `A₂` invariants on inner product spaces -/

section BirthDeathInnerProduct

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ]

/-- `birthDeathPotential` is smooth in `(μ, z)`. -/
@[fun_prop]
theorem contDiff_birthDeathPotential_uncurry {n : WithTop ℕ∞} :
    ContDiff ℝ n (Function.uncurry (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ))) := by
  have heq : Function.uncurry (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ)) =
      fun p : ℝ × WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦
        Function.uncurry foldPotential (p.1, p.2.fst) + splitQuadratic p.2.snd := by
    funext ⟨μ, z⟩
    simp [birthDeathPotential]
  rw [heq]
  have hfst : ContDiff ℝ n
      (fun p : ℝ × WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦ (p.1, p.2.fst)) :=
    contDiff_fst.prodMk ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).contDiff.comp contDiff_snd)
  have hsnd : ContDiff ℝ n
      (fun p : ℝ × WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) ↦ p.2.snd) :=
    (WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).contDiff.comp contDiff_snd
  exact (contDiff_foldPotential_uncurry.comp hfst).add (contDiff_splitQuadratic.comp hsnd)

/-- For each parameter `μ`, `birthDeathPotential μ` is smooth. -/
@[fun_prop]
theorem contDiff_birthDeathPotential (μ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) μ) :=
  (contDiff_foldPotential μ).separatedSum contDiff_splitQuadratic

@[fun_prop]
theorem continuous_birthDeathPotential (μ : ℝ) :
    Continuous (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) μ) :=
  (contDiff_birthDeathPotential (n := 0) μ).continuous

@[fun_prop]
theorem differentiable_birthDeathPotential (μ : ℝ) :
    Differentiable ℝ (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) μ) :=
  (contDiff_birthDeathPotential (n := 1) μ).differentiable one_ne_zero

/-- The Hessian quadratic form of `birthDeathPotential μ` at `z` is
`2 z.fst v.fst² + ‖v.snd.fst‖² - ‖v.snd.snd‖²`. -/
theorem hessianQuadraticForm_birthDeathPotential_apply (μ : ℝ)
    (z v : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    hessianQuadraticForm (birthDeathPotential μ) z v =
      2 * z.fst * v.fst ^ 2 + (‖v.snd.fst‖ ^ 2 - ‖v.snd.snd‖ ^ 2) := by
  rw [birthDeathPotential, hessianQuadraticForm_separatedSum_apply
      (contDiff_foldPotential μ).contDiffAt contDiff_splitQuadratic.contDiffAt,
    hessianQuadraticForm_foldPotential_apply, hessianQuadraticForm_splitQuadratic_apply]

/-- Along the line generated by `birthDeathKernelVector`, `birthDeathPotential μ` restricts to
`foldPotential μ`. -/
@[simp]
theorem birthDeathPotential_smul_kernelVector (μ t : ℝ) :
    birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) μ (t • birthDeathKernelVector) =
      foldPotential μ t := by
  rw [birthDeathPotential_apply, WithLp.smul_fst, WithLp.smul_snd, birthDeathKernelVector_fst,
    birthDeathKernelVector_snd, smul_eq_mul, mul_one, smul_zero]
  simp

/-- **Cubic `A₂` invariant in arbitrary dimension.** Restricting `birthDeathPotential 0` to the
Hessian-kernel line `t ↦ t • birthDeathKernelVector` has third derivative `2 ≠ 0` at `t = 0`. -/
theorem iteratedDeriv_three_birthDeathPotential_kernelVector :
    iteratedDeriv 3
      (fun t : ℝ ↦ birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0 (t • birthDeathKernelVector))
      (0 : ℝ) = 2 := by
  simp only [birthDeathPotential_smul_kernelVector, iteratedDeriv_three_foldPotential]

/-- The directional derivative of `birthDeathPotential μ` at `z` along `birthDeathKernelVector` is
`z.fst ^ 2 + μ`. -/
theorem fderiv_birthDeathPotential_kernelVector (μ : ℝ)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    fderiv ℝ (birthDeathPotential μ) z birthDeathKernelVector = z.fst ^ 2 + μ := by
  have hlin : HasDerivAt (fun t : ℝ ↦ z + t • birthDeathKernelVector) birthDeathKernelVector 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const birthDeathKernelVector).const_add z).congr_deriv
      (one_smul _ _)
  have hf : HasFDerivAt (birthDeathPotential μ) (fderiv ℝ (birthDeathPotential μ) z)
      (z + (0 : ℝ) • birthDeathKernelVector) := by
    simpa using (differentiable_birthDeathPotential μ z).hasFDerivAt
  have hd : HasDerivAt (fun t : ℝ ↦ birthDeathPotential μ (z + t • birthDeathKernelVector))
      (fderiv ℝ (birthDeathPotential μ) z birthDeathKernelVector) 0 :=
    hf.comp_hasDerivAt 0 hlin
  have heq : (fun t : ℝ ↦ birthDeathPotential μ (z + t • birthDeathKernelVector)) =
      fun t ↦ foldPotential μ (z.fst + t) + splitQuadratic z.snd := by
    funext t
    simp [birthDeathPotential, separatedSum_apply]
  rw [heq] at hd
  have hd' : HasDerivAt (fun t : ℝ ↦ foldPotential μ (z.fst + t) + splitQuadratic z.snd)
      (z.fst ^ 2 + μ) 0 :=
    (((hasDerivAt_foldPotential μ (z.fst + 0)).comp (0 : ℝ)
      ((hasDerivAt_id' (0 : ℝ)).const_add z.fst)).add_const
        (splitQuadratic z.snd)).congr_deriv (by ring)
  exact hd.unique hd'

/-- **Parameter transversality of the `A₂` normal form.** Differentiating the directional
derivative of `birthDeathPotential ν` at `0` along `birthDeathKernelVector` with respect to `ν` at
`0` gives `1 ≠ 0`. -/
theorem hasDerivAt_fderiv_birthDeathPotential_kernelVector (μ : ℝ) :
    HasDerivAt
      (fun ν ↦ fderiv ℝ (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) ν) 0 birthDeathKernelVector)
      1 μ := by
  have heq : (fun ν ↦
      fderiv ℝ (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) ν) 0 birthDeathKernelVector) =
      fun ν ↦ ν := by
    funext ν
    simp [fderiv_birthDeathPotential_kernelVector]
  rw [heq]
  exact hasDerivAt_id' μ

/-- For `μ > 0`, `birthDeathPotential μ` has no critical points on any inner product space: its
directional derivative along `birthDeathKernelVector` is at least `μ > 0` everywhere. -/
theorem fderiv_birthDeathPotential_ne_zero_of_pos {μ : ℝ} (hμ : 0 < μ)
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    fderiv ℝ (birthDeathPotential μ) z ≠ 0 := by
  intro h
  have hval := congrArg (· birthDeathKernelVector) h
  rw [fderiv_birthDeathPotential_kernelVector, zero_apply] at hval
  nlinarith [sq_nonneg z.fst]

/-- At `μ = 0`, no point is a nondegenerate critical point of `birthDeathPotential 0`. -/
theorem not_isNondegenerateCriticalPoint_birthDeathPotential_zero
    (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    ¬ IsNondegenerateCriticalPoint (birthDeathPotential 0) z := by
  rw [birthDeathPotential, isNondegenerateCriticalPoint_separatedSum_iff]
  exact fun h ↦ not_isNondegenerateCriticalPoint_foldPotential_zero z.fst h.1

end BirthDeathInnerProduct

/-! ### Gradient, Hessian operator, critical points, and global trajectories on Hilbert spaces -/

section BirthDeathHilbert

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ] [CompleteSpace Eₛ]
  [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ] [CompleteSpace Eᵤ]

/-- The gradient of `birthDeathPotential μ` at `(x, (zₛ, zᵤ))` is `(x² + μ, (zₛ, -zᵤ))`. -/
@[simp]
theorem gradient_birthDeathPotential (μ : ℝ) (z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    ∇ (birthDeathPotential μ) z =
      WithLp.toLp 2 (z.fst ^ 2 + μ, WithLp.toLp 2 (z.snd.fst, -z.snd.snd)) := by
  rw [birthDeathPotential, gradient_separatedSum
      (differentiable_foldPotential μ z.fst)
      ((contDiff_splitQuadratic (n := 1)).differentiable one_ne_zero z.snd),
    gradient_foldPotential, gradient_splitQuadratic]

/-- The Hessian operator of `birthDeathPotential μ` at `(x, (zₛ, zᵤ))` sends `(v₁, (vₛ, vᵤ))` to
`(2 x v₁, (vₛ, -vᵤ))`. -/
@[simp]
theorem hessianOperator_birthDeathPotential_apply (μ : ℝ)
    (z v : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    hessianOperator (birthDeathPotential μ) z v =
      WithLp.toLp 2 (2 * z.fst * v.fst, WithLp.toLp 2 (v.snd.fst, -v.snd.snd)) := by
  rw [birthDeathPotential, hessianOperator_separatedSum_apply
      (contDiff_foldPotential μ).contDiffAt contDiff_splitQuadratic.contDiffAt,
    hessianOperator_foldPotential, hessianOperator_splitQuadratic_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]

/-- **Corank-one Hessian kernel at `(μ, z) = (0, 0)`.** The kernel of
`hessianOperator (birthDeathPotential 0) 0` is the line `ℝ ∙ birthDeathKernelVector`. -/
theorem ker_hessianOperator_birthDeathPotential_zero :
    (hessianOperator (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0) 0).ker =
      ℝ ∙ birthDeathKernelVector := by
  ext v
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_span_singleton]
  constructor
  · intro hv
    rw [hessianOperator_birthDeathPotential_apply] at hv
    have hs : v.snd.fst = 0 := by simpa using congrArg (fun w ↦ w.snd.fst) hv
    have hu : -v.snd.snd = 0 := by simpa using congrArg (fun w ↦ w.snd.snd) hv
    exact ⟨v.fst, withLp_prod_ext (by simp)
      (withLp_prod_ext (by simp [hs]) (by simp [neg_eq_zero.1 hu]))⟩
  · rintro ⟨c, rfl⟩
    rw [hessianOperator_birthDeathPotential_apply]
    exact withLp_prod_ext (by simp) (withLp_prod_ext (by simp) (by simp))

/-- **The Hessian kernel at the birth-death point has dimension `1`**, even on infinite-dimensional
Hilbert spaces `Eₛ` and `Eᵤ`. -/
@[simp]
theorem finrank_ker_hessianOperator_birthDeathPotential_zero :
    Module.finrank ℝ
      (hessianOperator (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0) 0).ker = 1 := by
  rw [ker_hessianOperator_birthDeathPotential_zero,
    finrank_span_singleton birthDeathKernelVector_ne_zero]

/-- At `μ = 0`, the origin is the unique critical point of `birthDeathPotential 0`. -/
@[simp]
theorem fderiv_birthDeathPotential_zero_eq_zero_iff
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    fderiv ℝ (birthDeathPotential 0) z = 0 ↔ z = 0 := by
  rw [← TauCeti.gradient_eq_zero_iff, gradient_birthDeathPotential]
  constructor
  · intro h
    have h1 : z.fst ^ 2 + 0 = 0 := congrArg WithLp.fst h
    have h2 : z.snd.fst = 0 := congrArg (fun w ↦ w.snd.fst) h
    have h3 : -z.snd.snd = 0 := congrArg (fun w ↦ w.snd.snd) h
    exact withLp_prod_ext (sq_eq_zero_iff.1 (by linarith)) (withLp_prod_ext h2 (neg_eq_zero.1 h3))
  · rintro rfl
    exact withLp_prod_ext (by simp) (withLp_prod_ext (by simp) (by simp))

/-- For `μ = -a²`, the critical points of `birthDeathPotential (-a²)` are `birthDeathUpper a` and
`birthDeathLower a`. -/
theorem fderiv_birthDeathPotential_neg_sq_eq_zero_iff {a : ℝ}
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    fderiv ℝ (birthDeathPotential (-a ^ 2)) z = 0 ↔
      z = birthDeathUpper a ∨ z = birthDeathLower a := by
  rw [← TauCeti.gradient_eq_zero_iff, gradient_birthDeathPotential]
  constructor
  · intro h
    have h1 : deriv (foldPotential (-a ^ 2)) z.fst = 0 := by
      rw [deriv_foldPotential]
      exact congrArg WithLp.fst h
    have h2 : z.snd.fst = 0 := congrArg (fun w ↦ w.snd.fst) h
    have h3 : z.snd.snd = 0 := neg_eq_zero.1 (congrArg (fun w ↦ w.snd.snd) h)
    rcases deriv_foldPotential_neg_sq_eq_zero_iff.1 h1 with hfst | hfst
    · exact .inl (withLp_prod_ext hfst (withLp_prod_ext h2 h3))
    · exact .inr (withLp_prod_ext hfst (withLp_prod_ext h2 h3))
  · rintro (rfl | rfl) <;>
      exact withLp_prod_ext (by simp) (withLp_prod_ext (by simp) (by simp))

/-- For `a ≠ 0`, `birthDeathUpper a = (-a, 0)` is a nondegenerate critical point of
`birthDeathPotential (-a²)`. -/
theorem isNondegenerateCriticalPoint_birthDeathPotential_upper {a : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPoint
      (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) (-a ^ 2)) (birthDeathUpper a) :=
  (isNondegenerateCriticalPoint_foldPotential_neg_sq_neg ha).separatedSum
    isNondegenerateCriticalPoint_splitQuadratic_zero

/-- For `a ≠ 0`, `birthDeathLower a = (a, 0)` is a nondegenerate critical point of
`birthDeathPotential (-a²)`. -/
theorem isNondegenerateCriticalPoint_birthDeathPotential_lower {a : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPoint
      (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) (-a ^ 2)) (birthDeathLower a) :=
  (isNondegenerateCriticalPoint_foldPotential_neg_sq_self ha).separatedSum
    isNondegenerateCriticalPoint_splitQuadratic_zero

/-- **Nondegenerate critical points of `birthDeathPotential (-a²)`.** For `a ≠ 0`, the
nondegenerate critical points are `birthDeathUpper a` and `birthDeathLower a`. -/
@[simp]
theorem isNondegenerateCriticalPoint_birthDeathPotential_neg_sq_iff {a : ℝ} (ha : a ≠ 0)
    {z : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    IsNondegenerateCriticalPoint (birthDeathPotential (-a ^ 2)) z ↔
      z = birthDeathUpper a ∨ z = birthDeathLower a := by
  refine ⟨fun hz ↦ fderiv_birthDeathPotential_neg_sq_eq_zero_iff.1 hz.fderiv_eq_zero, ?_⟩
  rintro (rfl | rfl)
  · exact isNondegenerateCriticalPoint_birthDeathPotential_upper ha
  · exact isNondegenerateCriticalPoint_birthDeathPotential_lower ha

/-- **Morse characterization of the multi-dimensional birth-death family.** On any Hilbert space,
`birthDeathPotential μ` has nondegenerate critical points on `univ` if and only if `μ ≠ 0`. -/
@[simp]
theorem hasNondegenerateCriticalPointsOn_birthDeathPotential_iff {μ : ℝ} :
    HasNondegenerateCriticalPointsOn
      (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) μ) univ ↔ μ ≠ 0 := by
  refine ⟨fun h h0 ↦ ?_, fun hμ ↦ hasNondegenerateCriticalPointsOn_iff.2 fun z _ hz ↦ ?_⟩
  · subst h0
    exact not_isNondegenerateCriticalPoint_birthDeathPotential_zero 0
      (hasNondegenerateCriticalPointsOn_iff.1 h (mem_univ 0)
        (fderiv_birthDeathPotential_zero_eq_zero_iff.2 rfl))
  · rcases lt_trichotomy μ 0 with hneg | rfl | hpos
    · have ha : √(-μ) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.2 hneg)).ne'
      have hμeq : μ = -(√(-μ)) ^ 2 := by rw [Real.sq_sqrt (neg_nonneg.2 hneg.le), neg_neg]
      rw [hμeq] at hz ⊢
      exact (isNondegenerateCriticalPoint_birthDeathPotential_neg_sq_iff ha).2
        (fderiv_birthDeathPotential_neg_sq_eq_zero_iff.1 hz)
    · exact absurd rfl hμ
    · exact absurd hz (fderiv_birthDeathPotential_ne_zero_of_pos hpos z)

/-- A curve `γ` is a negative-gradient trajectory of `birthDeathPotential μ` if and only if its
fold component solves `x' = -∇ (foldPotential μ) x` and its transverse component solves
`ζ' = -∇ splitQuadratic ζ`. -/
theorem isIntegralCurve_birthDeathPotential_iff {μ : ℝ}
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))} :
    IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential μ) z) ↔
      IsIntegralCurve (fun s ↦ (γ s).fst) (fun _ x ↦ -∇ (foldPotential μ) x) ∧
        IsIntegralCurve (fun s ↦ (γ s).snd) (fun _ w ↦ -∇ splitQuadratic w) :=
  isIntegralCurve_separatedSum_iff
    (fun s ↦ differentiable_foldPotential μ (γ s).fst)
    (fun s ↦ (contDiff_splitQuadratic (n := 1)).differentiable one_ne_zero (γ s).snd)

private theorem eq_zero_of_tendsto_exp_mul_atTop {F : Type*} [NormedAddCommGroup F] {v : F} {L : ℝ}
    (hlim : Tendsto (fun t : ℝ ↦ Real.exp t * ‖v‖) atTop (𝓝 L)) : v = 0 := by
  by_contra hne
  have hdiv := Real.tendsto_exp_atTop.atTop_mul_const (norm_pos_iff.2 hne)
  obtain ⟨s, hs1, hs2⟩ := ((hlim.eventually (Iio_mem_nhds (lt_add_one L))).and
    (hdiv.eventually (eventually_ge_atTop (L + 2)))).exists
  linarith

/-- Any global negative-gradient trajectory of `splitQuadratic` with finite limits at `-∞` and `+∞`
is identically zero, with both limits equal to `0`. -/
theorem eq_zero_of_isIntegralCurve_splitQuadratic {ζ : ℝ → WithLp 2 (Eₛ × Eᵤ)}
    (hζ : IsIntegralCurve ζ (fun _ w ↦ -∇ splitQuadratic w))
    {p q : WithLp 2 (Eₛ × Eᵤ)} (hbot : Tendsto ζ atBot (𝓝 p)) (htop : Tendsto ζ atTop (𝓝 q)) :
    p = 0 ∧ q = 0 ∧ ζ = 0 := by
  let z₀ := ζ 0
  have hflow : ∀ t, ζ t = splitQuadraticFlow t z₀ :=
    congrFun (eq_splitQuadraticFlow_of_isIntegralCurve hζ)
  have hzₛ : z₀.fst = 0 := eq_zero_of_tendsto_exp_mul_atTop (L := ‖p.fst‖) <| by
    have hlim := (((WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous.tendsto p).comp hbot).norm.comp
      tendsto_neg_atTop_atBot
    exact hlim.congr fun t ↦ by
      simp [hflow (-t), splitQuadraticFlow_apply, z₀, norm_smul,
        Real.norm_of_nonneg (Real.exp_pos t).le]
  have hzᵤ : z₀.snd = 0 := eq_zero_of_tendsto_exp_mul_atTop (L := ‖q.snd‖) <| by
    have hlim := (((WithLp.sndL 2 ℝ Eₛ Eᵤ).continuous.tendsto q).comp htop).norm
    exact hlim.congr fun t ↦ by
      simp [hflow t, splitQuadraticFlow_apply, z₀, norm_smul,
        Real.norm_of_nonneg (Real.exp_pos t).le]
  have hζ0 : ζ = 0 := by
    funext t
    rw [hflow t, splitQuadraticFlow_apply, hzₛ, hzᵤ, smul_zero, smul_zero]
    exact withLp_prod_ext rfl rfl
  subst hζ0
  exact ⟨tendsto_nhds_unique hbot tendsto_const_nhds,
    tendsto_nhds_unique htop tendsto_const_nhds, rfl⟩

/-- **The curve `birthDeathOrbit a` solves the negative-gradient equation of
`birthDeathPotential (-a²)`.** -/
theorem isIntegralCurve_birthDeathOrbit (a : ℝ) :
    IsIntegralCurve (birthDeathOrbit (Eₛ := Eₛ) (Eᵤ := Eᵤ) a)
      (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z) :=
  isIntegralCurve_birthDeathPotential_iff.2
    ⟨isIntegralCurve_foldOrbit a,
      isIntegralCurve_const_neg_gradient_iff.2 (by simp [gradient_splitQuadratic])⟩

/-- **For `μ > 0`, no negative-gradient trajectory of `birthDeathPotential μ` converges at `+∞`.**
-/
theorem not_tendsto_atTop_nhds_of_isIntegralCurve_birthDeathPotential_of_pos {μ : ℝ} (hμ : 0 < μ)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential μ) z))
    (q : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    ¬ Tendsto γ atTop (𝓝 q) := by
  intro hq
  exact not_tendsto_atTop_nhds_of_isIntegralCurve_foldPotential_of_pos hμ
    (isIntegralCurve_birthDeathPotential_iff.1 hγ).1 q.fst
    (((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto q).comp hq)

/-- **For `μ > 0`, no negative-gradient trajectory of `birthDeathPotential μ` converges at `-∞`.**
-/
theorem not_tendsto_atBot_nhds_of_isIntegralCurve_birthDeathPotential_of_pos {μ : ℝ} (hμ : 0 < μ)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential μ) z))
    (p : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) :
    ¬ Tendsto γ atBot (𝓝 p) := by
  intro hp
  exact not_tendsto_atBot_nhds_of_isIntegralCurve_foldPotential_of_pos hμ
    (isIntegralCurve_birthDeathPotential_iff.1 hγ).1 p.fst
    (((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto p).comp hp)

/-- **At the birth-death instant `μ = 0`, the constant zero trajectory is the unique global
connecting trajectory.** -/
theorem eq_zero_of_isIntegralCurve_birthDeathPotential_zero
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential 0) z))
    {p q : WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q)) :
    p = 0 ∧ q = 0 ∧ γ = 0 := by
  obtain ⟨h₁, h₂⟩ := isIntegralCurve_birthDeathPotential_iff.1 hγ
  obtain ⟨hp₁, hq₁, hγ₁⟩ := eq_zero_of_isIntegralCurve_foldPotential_zero h₁
    (((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto p).comp hbot)
    (((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto q).comp htop)
  obtain ⟨hp₂, hq₂, hγ₂⟩ := eq_zero_of_isIntegralCurve_splitQuadratic h₂
    (((WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto p).comp hbot)
    (((WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto q).comp htop)
  exact ⟨withLp_prod_ext hp₁ hp₂, withLp_prod_ext hq₁ hq₂,
    funext fun s ↦ withLp_prod_ext (congrFun hγ₁ s) (congrFun hγ₂ s)⟩

/-- **Classification of the newborn connecting trajectory in arbitrary dimension.** For `a > 0`,
every global negative-gradient trajectory of `birthDeathPotential (-a²)` from `birthDeathUpper a`
at `-∞` to `birthDeathLower a` at `+∞` is a unique time translate
`s ↦ birthDeathOrbit a (s + s₀)`. -/
theorem existsUnique_birthDeathOrbit_add_of_isIntegralCurve {a : ℝ} (ha : 0 < a)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a))) :
    ∃! s₀ : ℝ, γ = fun s ↦ birthDeathOrbit a (s + s₀) := by
  obtain ⟨h₁, h₂⟩ := isIntegralCurve_birthDeathPotential_iff.1 hγ
  have hbot₁ : Tendsto (fun s ↦ (γ s).fst) atBot (𝓝 (-a)) :=
    ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathUpper a)).comp hbot
  have htop₁ : Tendsto (fun s ↦ (γ s).fst) atTop (𝓝 a) :=
    ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathLower a)).comp htop
  have hbot₂ : Tendsto (fun s ↦ (γ s).snd) atBot (𝓝 0) :=
    ((WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathUpper a)).comp hbot
  have htop₂ : Tendsto (fun s ↦ (γ s).snd) atTop (𝓝 0) :=
    ((WithLp.sndL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathLower a)).comp htop
  obtain ⟨-, -, hγ₂⟩ := eq_zero_of_isIntegralCurve_splitQuadratic h₂ hbot₂ htop₂
  obtain ⟨s₀, hs₀, huniq⟩ := existsUnique_foldOrbit_add_of_isIntegralCurve ha h₁ hbot₁ htop₁
  refine ⟨s₀, funext fun s ↦ withLp_prod_ext (congrFun hs₀ s) (congrFun hγ₂ s),
    fun t₀ ht₀ ↦ huniq t₀ ?_⟩
  funext s
  exact congrArg WithLp.fst (congrFun ht₀ s)

/-- **No reverse connecting trajectory exists in arbitrary dimension.** For `a > 0`, no
negative-gradient trajectory of `birthDeathPotential (-a²)` runs from `birthDeathLower a` at `-∞`
to `birthDeathUpper a` at `+∞`. -/
theorem not_isIntegralCurve_birthDeathPotential_lower_to_upper {a : ℝ} (ha : 0 < a)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathLower a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathUpper a))) : False :=
  not_isIntegralCurve_foldPotential_self_to_neg ha
    (isIntegralCurve_birthDeathPotential_iff.1 hγ).1
    (((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathLower a)).comp hbot)
    (((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathUpper a)).comp htop)

/-! ### Formal-adjoint injectivity on arbitrary Hilbert spaces -/

/-- On any pair of real Hilbert spaces, the constant transverse adjoint equation
`w' - Hess splitQuadratic(0) w = 0` has no nonzero square-integrable solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_splitQuadratic_eq_bot :
    squareIntegrableSolutions
      (fun _ : ℝ ↦ -hessianOperator (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0) = ⊥ := by
  refine squareIntegrableSolutions_eq_bot_of_withLp
    (A₁ := fun _ : ℝ ↦ -(1 : ℝ) • ContinuousLinearMap.id ℝ Eₛ)
    (A₂ := fun _ : ℝ ↦ -(-1 : ℝ) • ContinuousLinearMap.id ℝ Eᵤ)
    (fun _ w ↦ withLp_prod_ext (by simp) (by simp)) ?_ ?_
  · exact squareIntegrableSolutions_neg_smul_id_eq_bot continuous_const
      (fun s ↦ (Real.hasDerivAt_exp s).congr_deriv (one_mul _).symm) Real.exp_zero
      (MeasureTheory.not_memLp_of_tendsto_norm_atTop two_ne_zero
        (tendsto_norm_atTop_atTop.comp Real.tendsto_exp_atTop))
  · exact squareIntegrableSolutions_neg_smul_id_eq_bot continuous_const
      (g := fun s ↦ Real.exp (-s))
      (fun s ↦ ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id' s).neg).congr_deriv (by ring))
      (by simp)
      (MeasureTheory.not_memLp_of_tendsto_norm_atBot two_ne_zero
        (tendsto_norm_atTop_atTop.comp (Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)))

/-- On any pair of real Hilbert spaces, along a negative-gradient trajectory of
`birthDeathPotential (-a²)` (`a > 0`) from `birthDeathUpper a` to `birthDeathLower a`, the adjoint
ODE `v' - Hess F_{-a²}(γ) v = 0` has no nonzero square-integrable solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_birthDeathPotential_eq_bot
    {a : ℝ} (ha : 0 < a) {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a))) :
    squareIntegrableSolutions
      (fun s ↦ -hessianOperator (birthDeathPotential (-a ^ 2)) (γ s)) = ⊥ := by
  have h₁ := (isIntegralCurve_birthDeathPotential_iff.1 hγ).1
  have hbot₁ : Tendsto (fun s ↦ (γ s).fst) atBot (𝓝 (-a)) :=
    ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathUpper a)).comp hbot
  have htop₁ : Tendsto (fun s ↦ (γ s).fst) atTop (𝓝 a) :=
    ((WithLp.fstL 2 ℝ ℝ (WithLp 2 (Eₛ × Eᵤ))).continuous.tendsto (birthDeathLower a)).comp htop
  exact squareIntegrableSolutions_eq_bot_of_withLp
    (A₁ := fun s ↦ -hessianOperator (foldPotential (-a ^ 2)) (γ s).fst)
    (A₂ := fun _ ↦ -hessianOperator (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0)
    (fun _ _ ↦ withLp_prod_ext (by simp) (withLp_prod_ext (by simp) (by simp)))
    (squareIntegrableSolutions_neg_hessianOperator_foldPotential_eq_bot ha h₁ hbot₁ htop₁)
    squareIntegrableSolutions_neg_hessianOperator_splitQuadratic_eq_bot

/-- **Hilbert-space injectivity of the formal adjoint along a newborn connecting trajectory.** On
arbitrary real Hilbert spaces `Eₛ` and `Eᵤ`, for `a > 0` and any negative-gradient trajectory `γ`
from `birthDeathUpper a` to `birthDeathLower a`, the formal adjoint operator
`ξ ↦ ξ' - Hess F_{-a²}(γ) ξ` has trivial kernel on `W^{1,2}`. -/
theorem ker_trajectoryOperator_neg_birthDeathPotential_eq_bot
    {a : ℝ} (ha : 0 < a) {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a)))
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (γ s)) :
    (WeakDerivStep.trajectoryOperator (p := 2) (-AL)).ker = ⊥ := by
  have hnegAL : (-AL) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -hessianOperator (birthDeathPotential (-a ^ 2)) (γ s) := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with s hs1 hs2
    rw [hs1, Pi.neg_apply, hs2]
  have hcont : Continuous fun s ↦ -hessianOperator (birthDeathPotential (-a ^ 2)) (γ s) :=
    (((contDiff_birthDeathPotential (n := 2) _).contDiff_hessianOperator (m := 0)
      (by norm_num)).continuous.comp hγ.continuous).neg
  exact (WeakDerivStep.ker_trajectoryOperator_eq_bot_iff hcont (-AL) hnegAL).2
    (squareIntegrableSolutions_neg_hessianOperator_birthDeathPotential_eq_bot ha hγ hbot htop)

end BirthDeathHilbert

/-! ### Morse indices and Fredholm regularity on finite-dimensional spaces -/

section BirthDeathFiniteDimensional

open TauCeti.WeakDerivStep

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
  [FiniteDimensional ℝ Eₛ] [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ]
  [FiniteDimensional ℝ Eᵤ]

/-- **Morse index of `birthDeathUpper a`.** For `a > 0`, the upper newborn critical point `(-a, 0)`
has Morse index `dim Eᵤ + 1`. -/
@[simp]
theorem morseIndex_birthDeathPotential_upper {a : ℝ} (ha : 0 < a) :
    morseIndex (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) (-a ^ 2)) (birthDeathUpper a) =
      Module.finrank ℝ Eᵤ + 1 := by
  rw [birthDeathPotential, morseIndex_separatedSum
      (contDiff_foldPotential _).contDiffAt contDiff_splitQuadratic.contDiffAt,
    birthDeathUpper_fst, morseIndex_foldPotential_neg_sq_neg ha, morseIndex_splitQuadratic,
    add_comm]

/-- **Morse index of `birthDeathLower a`.** For `a > 0`, the lower newborn critical point `(a, 0)`
has Morse index `dim Eᵤ`. -/
@[simp]
theorem morseIndex_birthDeathPotential_lower {a : ℝ} (ha : 0 < a) :
    morseIndex (birthDeathPotential (Eₛ := Eₛ) (Eᵤ := Eᵤ) (-a ^ 2)) (birthDeathLower a) =
      Module.finrank ℝ Eᵤ := by
  rw [birthDeathPotential, morseIndex_separatedSum
      (contDiff_foldPotential _).contDiffAt contDiff_splitQuadratic.contDiffAt,
    birthDeathLower_fst, morseIndex_foldPotential_neg_sq_self ha, morseIndex_splitQuadratic,
    zero_add]

/-- Along any negative-gradient trajectory of `birthDeathPotential (-a²)` (`a ≠ 0`) from
`birthDeathUpper a` to `birthDeathLower a`, the linearized operator `D_γ` on `W^{1,2}` is
Fredholm. -/
theorem isFredholm_trajectoryOperator_birthDeathPotential {a : ℝ} (ha : a ≠ 0)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a)))
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (γ s)) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  hγ.isFredholm_trajectoryOperator_hessianOperator (contDiff_birthDeathPotential _)
    (isNondegenerateCriticalPoint_birthDeathPotential_upper ha)
    (isNondegenerateCriticalPoint_birthDeathPotential_lower ha) hbot htop hAL

/-- **The linearized operator along the newborn connecting trajectory has Fredholm index `1`.** -/
theorem index_trajectoryOperator_birthDeathPotential {a : ℝ} (ha : 0 < a)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a)))
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (γ s)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [hγ.index_trajectoryOperator_hessianOperator (contDiff_birthDeathPotential _)
    (isNondegenerateCriticalPoint_birthDeathPotential_upper ha.ne')
    (isNondegenerateCriticalPoint_birthDeathPotential_lower ha.ne') hbot htop hAL,
    morseIndex_birthDeathPotential_upper ha, morseIndex_birthDeathPotential_lower ha]
  push_cast
  ring

/-- **Transversality of the newborn connecting trajectory in arbitrary finite dimension.** For
`a > 0`, along any negative-gradient trajectory from `birthDeathUpper a` to `birthDeathLower a`,
the linearized trajectory operator `D_γ` is surjective from `W^{1,2}` onto `L²`. -/
theorem surjective_trajectoryOperator_birthDeathPotential {a : ℝ} (ha : 0 < a)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a)))
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (γ s)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) := by
  have hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL s = ContinuousLinearMap.adjoint (AL s) := by
    filter_upwards [hAL] with s hs
    rw [hs]
    exact (contDiff_birthDeathPotential _).contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
      |>.clm_adjoint_eq.symm
  exact (surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj
    (isFredholm_trajectoryOperator_birthDeathPotential ha.ne' hγ hbot htop hAL).isClosed_range).2
    (ker_trajectoryOperator_neg_birthDeathPotential_eq_bot ha hγ hbot htop hAL)

/-- **The kernel of `D_γ` along the newborn connecting trajectory is one-dimensional.** -/
theorem finrank_ker_trajectoryOperator_birthDeathPotential_eq_one {a : ℝ} (ha : 0 < a)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a)))
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (γ s)) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = 1 := by
  have hidx := index_trajectoryOperator_birthDeathPotential ha hγ hbot htop hAL
  rw [ContinuousLinearMap.index_of_surjective _
    (surjective_trajectoryOperator_birthDeathPotential ha hγ hbot htop hAL)] at hidx
  omega

/-- **The kernel of `D_γ` along the newborn connecting trajectory is spanned by the velocity `γ'`.**
-/
theorem exists_ker_trajectoryOperator_birthDeathPotential_eq_span {a : ℝ} (ha : 0 < a)
    {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathPotential (-a ^ 2)) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper a)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower a)))
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (γ s)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) 2
            (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv γ ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u := by
  obtain ⟨u, hu0, hu, hux⟩ :=
    hγ.exists_ne_zero_trajectoryOperator_hessianOperator_eq_zero (contDiff_birthDeathPotential _)
      hbot htop (birthDeathUpper_ne_birthDeathLower ha.ne') hAL
  refine ⟨-u, ?_, eq_span_singleton_of_mem_of_finrank_eq_one
    (finrank_ker_trajectoryOperator_birthDeathPotential_eq_one ha hγ hbot htop hAL)
    (by simpa using hu) (neg_ne_zero.2 hu0)⟩
  have hprev := map_neg (prevL (ContinuousLinearMap.id ℝ
    (Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) u
  simp only [prevL_apply] at hprev
  filter_upwards [hux, Lp.coeFn_neg (prev _ u)] with s hs hneg
  rw [hprev, hneg, Pi.neg_apply, hs, (hγ s).deriv]

/-- At the constant trajectory `birthDeathUpper a` (`a ≠ 0`), the linearized operator is bijective
from `W^{1,2}` onto `L²`. -/
theorem bijective_trajectoryOperator_birthDeathPotential_upper {a : ℝ} (ha : a ≠ 0)
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (birthDeathUpper a)) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_birthDeathPotential_upper ha) hAL

/-- At the constant trajectory `birthDeathLower a` (`a ≠ 0`), the linearized operator is bijective
from `W^{1,2}` onto `L²`. -/
theorem bijective_trajectoryOperator_birthDeathPotential_lower {a : ℝ} (ha : a ≠ 0)
    {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathPotential (-a ^ 2)) (birthDeathLower a)) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_birthDeathPotential_lower ha) hAL

end BirthDeathFiniteDimensional

end TauCeti

end
