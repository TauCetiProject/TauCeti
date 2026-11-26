/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.ConormalShear
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.FDeriv.EuclideanMatrix
import TauCeti.Analysis.Calculus.FDeriv.Homothety
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Change of variables in divergence-form equations

Let `Φ` map an open set `U ⊆ ℝⁿ` injectively onto an open set `V`, with derivative `DΦ(x)` of
Jacobian matrix `M(x)` and Jacobian determinant `J(x) = |det DΦ(x)|`. A weak solution
`u ∈ H¹(V)` of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` in `V`

becomes, after the change of variables `u' = u ∘ Φ`, a weak solution of an equation of the same
form in `U`,

`-∂ᵢ(a'ⁱʲ ∂ⱼu') + b'ⁱ ∂ᵢu' + c' u' = f'` in `U`,

with the pulled-back coefficients

* `a'(x) = J(x) M(x)⁻¹ a(Φ x) M(x)⁻ᵀ` (`TauCeti.PDE.pullbackPrincipal`),
* `b'(x) = J(x) M(x)⁻¹ b(Φ x)` (`TauCeti.PDE.pullbackDrift`),
* `c'(x) = J(x) c(Φ x)` and `f'(x) = J(x) f(Φ x)` (`TauCeti.PDE.pullbackDensity`).

The zeroth-order coefficient and the right-hand side transform as densities, because the
volume element changes by the factor `J`. The transformed principal coefficient is again
uniformly elliptic and bounded when `DΦ` and its inverse are bounded and `J` is bounded below
(`TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipal`), and it is `r`-Hölder when `a` is, `Φ` is
Lipschitz and the inverse of `DΦ` and the Jacobian are `r`-Hölder, with an explicit constant
(`TauCeti.PDE.holderOnWith_matrixBilinearForm_pullbackPrincipal`); for `r = 1` this is
Lipschitz continuity. The transformed drift is `r`-Hölder under the same conditions
(`TauCeti.PDE.holderOnWith_pullbackDrift`). If moreover `Φ` has an inverse change of
variables, the transformed drift, zeroth-order coefficient and right-hand side stay in `Lᵖ`
(`TauCeti.PDE.memLp_pullbackDrift`, `TauCeti.PDE.memLp_pullbackDensity`); with `p = ∞`, bounded
lower-order coefficients stay bounded.

A right-hand side in divergence form `-∂ᵢGⁱ` transforms like the drift: the vector field `G`
becomes `G'(x) = J(x) M(x)⁻¹ G(Φ x)`
(`TauCeti.PDE.setIntegral_inner_pullbackDrift_gradient_compL`). So the class of equations with
Hölder principal coefficients and Hölder divergence data, the setting of the Schauder estimates
for divergence-form equations, is preserved by changes of variables whose derivatives are Hölder,
such as the flattening of a `C^{1,α}` boundary.

This is the change of variables that flattens the boundary of a domain: if `Φ` maps a piece of a
half-space onto a neighbourhood of a boundary point of `Ω`, a weak solution in `Ω` becomes a weak
solution near a flat boundary portion, where regularity up to the boundary can be proved by
difference quotients in the tangential directions.

## The argument

The chain rule for weak gradients (`TauCeti.W1p.gradient_compL_ae`) gives
`∇u'(x) = DΦ(x)* ∇u(Φ x)`, so `∇u(Φ x) = M(x)⁻ᵀ ∇u'(x)` wherever `DΦ(x)` is invertible. Hence
`⟪a(Φ x) ∇u(Φ x), ∇w(Φ x)⟫ J(x) = ⟪a'(x) ∇u'(x), ∇w'(x)⟫`, and similarly for the lower-order terms
(`TauCeti.PDE.energyIntegrand_pullback`). The change of variables formula for integrals
(`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) turns the energy form on `V`
into the transformed energy form on `U` (`TauCeti.PDE.energyFormH1_compL`). If `Ψ` is an inverse
change of variables, precomposition with `Ψ` maps `H¹₀(U)` into `H¹₀(V)` and is inverse to
precomposition with `Φ`, so every test function on `U` comes from one on `V`, and the weak
formulation transfers (`TauCeti.PDE.energyFormH1_compL_eq_setIntegral`).

## Main declarations

* `TauCeti.PDE.pullbackPrincipal`, `TauCeti.PDE.pullbackDrift`, `TauCeti.PDE.pullbackDensity`:
  the transformed coefficients.
* `TauCeti.PDE.energyFormH1_compL`: the energy form is invariant under the change of variables.
* `TauCeti.PDE.energyFormH1_compL_eq_setIntegral_add_setIntegral_inner`: weak solutions with a
  right-hand side `f - ∂ᵢGⁱ` are carried to weak solutions.
* `TauCeti.PDE.energyFormH1_compL_eq_setIntegral`: its case `G = 0`.
* `TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipal`: uniform ellipticity and boundedness are
  preserved, with explicit constants.
* `TauCeti.PDE.matrixBilinearForm_pullbackPrincipal_eq_bilinearComp`: the bilinear form of the
  transformed principal coefficient, written with a left inverse `T` of `DΦ`, and
  `TauCeti.PDE.pullbackPrincipal_apply_apply_of_comp_eq_id`: its entries in the same terms.
* `TauCeti.PDE.matrixBilinearForm_pullbackPrincipal_of_fderiv_eq_transvectionL`: the same when
  `DΦ(x)` is a transvection `y ↦ y + ⟪ν, y⟫ s` with `⟪ν, s⟫ = 0`.
* `TauCeti.PDE.matrixBilinearForm_pullbackPrincipal_reflection_of_fderiv_eq`: a constant
  symmetric matrix pulled back by a map whose derivative is the conormal shear
  (`TauCeti.PDE.conormalShearVector`) is invariant under the reflection in `ν⊥`.
* `TauCeti.PDE.holderOnWith_matrixBilinearForm_pullbackPrincipal`: Hölder principal
  coefficients stay Hölder, with the same exponent and an explicit constant; in particular
  Lipschitz ones stay Lipschitz.
* `TauCeti.PDE.holderOnWith_pullbackDrift`: Hölder drifts and divergence data stay Hölder, with an
  explicit constant.
* `TauCeti.PDE.setIntegral_inner_pullbackDrift_gradient_compL`: the divergence-datum integral is
  invariant under the change of variables.
* `TauCeti.PDE.memLp_pullbackDensity`, `TauCeti.PDE.memLp_pullbackDrift`: the transformed
  zeroth-order coefficient, right-hand side and drift stay in `Lᵖ`.
* `TauCeti.PDE.exists_uniformlyEllipticOn_and_holderOnWith_pullbackPrincipal`: for mutually
  inverse changes of variables of order one with Jacobian determinants at least one in absolute
  value, a uniformly elliptic `r`-Hölder principal coefficient stays so where `x ↦ DΨ(Φ x)` is
  `r`-Hölder.
* `TauCeti.PDE.exists_uniformlyEllipticOn_and_lipschitzOnWith_pullbackPrincipal`: for a change of
  variables `Φ` of order one with an inverse `Ψ` of order two, both with Jacobian determinants at
  least one in absolute value, a uniformly elliptic Lipschitz principal coefficient stays so on
  compact convex pieces.
* `TauCeti.PDE.exists_uniformlyEllipticOn_pullbackPrincipal`: for mutually inverse changes of
  variables of order one with Jacobian determinants at least one in absolute value, a uniformly
  elliptic principal coefficient stays uniformly elliptic.
* `TauCeti.PDE.contDiffOn_pullbackPrincipal_apply`: for such changes of variables, the entries of
  the transformed principal coefficient are `Cⁿ` where `Φ` is `Cⁿ`, `Ψ` is `Cⁿ⁺¹` and the entries
  of `a` are `Cⁿ`.
* `TauCeti.PDE.exists_forall_energyFormH1_compL_restrictL_eq`: a weak solution, restricted to an
  open subset and carried by a change of variables with an inverse, solves the transformed
  equation, with bounded lower-order coefficients and square-integrable right-hand side.
* `TauCeti.PDE.energyFormH1_w1pCompL_restrictL_eq_setIntegral`: for a pure divergence-form
  equation with a right-hand side `F ∈ H¹` and Jacobian determinants of absolute value one, the
  transformed right-hand side is `F ∘ Φ ∈ H¹`.
* `TauCeti.PDE.eLpNorm_pullbackDensity_le`: for such changes of variables with Jacobian
  determinants of absolute value one, the transformed density has at most the `Lᵖ` norm of the
  original one.
* `TauCeti.PDE.energyFormH1_pullbackPrincipal_smul_add_const`: under a homothety `z ↦ ε z + c`
  the transformed principal coefficient is a positive multiple of `a (ε z + c)`, and
  `TauCeti.PDE.exists_supersolution_comp_smul_add_const`: a rescaled weak supersolution of
  `-div (a ∇u) ≥ 0` is a weak supersolution for the rescaled coefficients.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, proof of Theorem 4 (flattening
  the boundary transforms the equation into one of the same form).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.1 and the proof of Theorem 8.12.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped InnerProductSpace

namespace TauCeti

namespace PDE

/-! ### The transformed coefficients -/

section Coefficients

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transformed principal coefficient `a'(x) = J(x) M(x)⁻¹ a(Φ x) M(x)⁻ᵀ` of a
divergence-form operator under the change of variables `Φ`, where `M(x)` is the Jacobian matrix
of `Φ` at `x` and `J(x) = |det DΦ(x)|`. -/
def pullbackPrincipal (Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  |(fderiv ℝ Φ x).det| •
    (((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ * a (Φ x) *
      ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ᵀ)

/-- The transformed drift `b'(x) = J(x) M(x)⁻¹ b(Φ x)` of a divergence-form operator under the
change of variables `Φ`, where `M(x)` is the Jacobian matrix of `Φ` at `x` and
`J(x) = |det DΦ(x)|`. -/
def pullbackDrift (Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  |(fderiv ℝ Φ x).det| •
    toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ (b (Φ x))

/-- The pullback `x ↦ |det DΦ(x)| f(Φ x)` of a density `f` under the change of variables `Φ`.
The zeroth-order coefficient and the right-hand side of a divergence-form equation transform in
this way. -/
def pullbackDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → E)
    (f : E → ℝ) (x : E) : ℝ :=
  |(fderiv ℝ Φ x).det| * f (Φ x)

theorem pullbackPrincipal_apply (Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    pullbackPrincipal Φ a x = |(fderiv ℝ Φ x).det| •
      (((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ * a (Φ x) *
        ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ᵀ) :=
  (rfl)

theorem pullbackDrift_apply (Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) :
    pullbackDrift Φ b x = |(fderiv ℝ Φ x).det| •
      toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ (b (Φ x)) :=
  (rfl)

@[simp]
theorem pullbackDensity_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → E)
    (f : E → ℝ) (x : E) : pullbackDensity Φ f x = |(fderiv ℝ Φ x).det| * f (Φ x) :=
  (rfl)

@[simp]
theorem pullbackDrift_zero (Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :
    pullbackDrift Φ (0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) = 0 := by
  funext x; simp [pullbackDrift_apply]

@[simp]
theorem pullbackDensity_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → E) :
    pullbackDensity Φ (0 : E → ℝ) = 0 := by
  funext x; simp

/-- Where `DΦ(x)` is invertible, the map of the inverse Jacobian matrix is a right inverse of
`DΦ(x)`. -/
private theorem fderiv_apply_toEuclideanCLM_inv_apply {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {x : EuclideanSpace ℝ ι} (hx : (fderiv ℝ Φ x).det ≠ 0) (v : EuclideanSpace ℝ ι) :
    fderiv ℝ Φ x (toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ v) =
      v := by
  obtain ⟨M, hMD⟩ : ∃ M, toEuclideanCLM (𝕜 := ℝ) M = fderiv ℝ Φ x :=
    ⟨_, StarAlgEquiv.apply_symm_apply _ _⟩
  rw [← hMD, det_toEuclideanCLM] at hx
  rw [← hMD, StarAlgEquiv.symm_apply_apply,
    toEuclideanCLM_apply_toEuclideanCLM_nonsing_inv_apply hx]

/-- Where `DΦ(x)` is invertible, the adjoint of the map of the inverse Jacobian matrix is a left
inverse of `DΦ(x)*`. -/
private theorem adjoint_toEuclideanCLM_inv_adjoint_fderiv_apply
    {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x : EuclideanSpace ℝ ι}
    (hx : (fderiv ℝ Φ x).det ≠ 0) (v : EuclideanSpace ℝ ι) :
    (toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹).adjoint
      ((fderiv ℝ Φ x).adjoint v) = v := by
  refine ext_inner_right ℝ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    fderiv_apply_toEuclideanCLM_inv_apply hx]

/-- **The transformed principal coefficient on pulled-back covectors.** Where `DΦ(x)` is
invertible, the bilinear form of `a'(x)` evaluated on `DΦ(x)* η` and `DΦ(x)* ξ` is
`|det DΦ(x)|` times the bilinear form of `a(Φ x)` evaluated on `η` and `ξ`. -/
theorem matrixBilinearForm_pullbackPrincipal {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) {x : EuclideanSpace ℝ ι}
    (hx : (fderiv ℝ Φ x).det ≠ 0) (η ξ : EuclideanSpace ℝ ι) :
    matrixBilinearForm (pullbackPrincipal Φ a x) ((fderiv ℝ Φ x).adjoint η)
        ((fderiv ℝ Φ x).adjoint ξ) =
      |(fderiv ℝ Φ x).det| * matrixBilinearForm (a (Φ x)) η ξ := by
  -- As operators, `a'(x) = J T a(Φ x) T*` with `T* DΦ(x)* = id`, where `T` is the map of `M⁻¹`.
  rw [pullbackPrincipal_apply, matrixBilinearForm_smul_apply, matrixBilinearForm_apply,
    matrixBilinearForm_apply, ← inner_toEuclideanCLM, ← inner_toEuclideanCLM,
    ← conjTranspose_eq_transpose_of_trivial, inner_toEuclideanCLM_mul_mul_conjTranspose,
    ← adjoint_toEuclideanCLM, adjoint_toEuclideanCLM_inv_adjoint_fderiv_apply hx,
    adjoint_toEuclideanCLM_inv_adjoint_fderiv_apply hx]

/-- **The transformed drift on pulled-back covectors.** Where `DΦ(x)` is invertible,
`⟪b'(x), DΦ(x)* ξ⟫ = |det DΦ(x)| ⟪b(Φ x), ξ⟫`. -/
theorem inner_pullbackDrift_adjoint {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {x : EuclideanSpace ℝ ι}
    (hx : (fderiv ℝ Φ x).det ≠ 0) (ξ : EuclideanSpace ℝ ι) :
    ⟪pullbackDrift Φ b x, (fderiv ℝ Φ x).adjoint ξ⟫_ℝ =
      |(fderiv ℝ Φ x).det| * ⟪b (Φ x), ξ⟫_ℝ := by
  rw [pullbackDrift_apply, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right,
    fderiv_apply_toEuclideanCLM_inv_apply hx]

/-- **The transformed energy integrand.** Where `DΦ(x)` is invertible, the energy integrand of
the transformed coefficients on jets whose gradients are pulled back by `DΦ(x)*` is
`|det DΦ(x)|` times the energy integrand of the original coefficients at `Φ x`. -/
theorem energyIntegrand_pullback {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ ι → ℝ) {x : EuclideanSpace ℝ ι} (hx : (fderiv ℝ Φ x).det ≠ 0)
    (U V : ℝ × EuclideanSpace ℝ ι) :
    energyIntegrand (pullbackPrincipal Φ a x) (pullbackDrift Φ b x) (pullbackDensity Φ c x)
        (U.1, (fderiv ℝ Φ x).adjoint U.2) (V.1, (fderiv ℝ Φ x).adjoint V.2) =
      |(fderiv ℝ Φ x).det| * energyIntegrand (a (Φ x)) (b (Φ x)) (c (Φ x)) U V := by
  simp only [energyIntegrand_apply, driftForm_apply, massForm_apply,
    matrixBilinearForm_pullbackPrincipal a hx, inner_pullbackDrift_adjoint b hx,
    pullbackDensity_apply]
  ring

/-- **The transformed principal coefficient through a left inverse of `DΦ`.** If `T` is a left
inverse of `DΦ(x)`, the bilinear form of `a'(x)` is `|det DΦ(x)|` times the bilinear form of
`a(Φ x)` evaluated on `T* η` and `T* ξ`. -/
theorem matrixBilinearForm_pullbackPrincipal_eq_bilinearComp
    {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    {x : EuclideanSpace ℝ ι} {T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    (hT : T ∘L fderiv ℝ Φ x = ContinuousLinearMap.id ℝ _) :
    matrixBilinearForm (pullbackPrincipal Φ a x) =
      |(fderiv ℝ Φ x).det| •
        (matrixBilinearForm (a (Φ x))).bilinearComp T.adjoint T.adjoint := by
  have hdet : (fderiv ℝ Φ x).det ≠ 0 := by
    have h : T.det * (fderiv ℝ Φ x).det = 1 := by
      rw [← ContinuousLinearMap.det_comp, hT, ContinuousLinearMap.det_id]
    exact right_ne_zero_of_mul_eq_one h
  -- `DΦ(x)* ∘ T* = (T ∘ DΦ(x))* = id`, so every covector is `DΦ(x)*` of its image under `T*`.
  have hinv (η : EuclideanSpace ℝ ι) : (fderiv ℝ Φ x).adjoint (T.adjoint η) = η := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp, hT,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
  ext η ξ
  conv_lhs => rw [← hinv η, ← hinv ξ]
  rw [matrixBilinearForm_pullbackPrincipal a hdet]
  simp

/-- **The transformed principal coefficient along a shear.** If `DΦ(x)` is the transvection
`y ↦ y + ⟪ν, y⟫ s` with `⟪ν, s⟫ = 0`, the bilinear form of `a'(x)` is that of `a(Φ x)` read
through `y ↦ y - ⟪s, y⟫ ν`, the adjoint of the inverse shear. -/
theorem matrixBilinearForm_pullbackPrincipal_of_fderiv_eq_transvectionL
    {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    {x ν s : EuclideanSpace ℝ ι} (hs : ⟪ν, s⟫_ℝ = 0) (hΦ : fderiv ℝ Φ x = transvectionL ν s) :
    matrixBilinearForm (pullbackPrincipal Φ a x) =
      (matrixBilinearForm (a (Φ x))).bilinearComp (transvectionL (-s) ν)
        (transvectionL (-s) ν) := by
  rw [matrixBilinearForm_pullbackPrincipal_eq_bilinearComp a (T := transvectionL ν (-s))
      (by rw [hΦ, transvectionL_neg_comp_transvectionL hs]),
    hΦ, det_transvectionL, hs, add_zero, abs_one, one_smul, adjoint_transvectionL]

/-- **Entries of the transformed principal coefficient through a left inverse of `DΦ`.** If `T`
is a left inverse of `DΦ(x)`, the entry `(i, j)` of `a'(x)` is
`|det DΦ(x)| ∑ₖₗ (T eₖ)ᵢ aₖₗ(Φ x) (T eₗ)ⱼ`. -/
theorem pullbackPrincipal_apply_apply_of_comp_eq_id
    {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    {x : EuclideanSpace ℝ ι} {T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    (hT : T ∘L fderiv ℝ Φ x = ContinuousLinearMap.id ℝ _) (i j : ι) :
    pullbackPrincipal Φ a x i j = |(fderiv ℝ Φ x).det| * ∑ k, ∑ l,
      (T (EuclideanSpace.single k 1)).ofLp i * a (Φ x) k l *
        (T (EuclideanSpace.single l 1)).ofLp j := by
  have h := congrArg (fun B => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (matrixBilinearForm_pullbackPrincipal_eq_bilinearComp a hT)
  -- The coordinates of `T* eₘ` are those of the columns of `T`.
  have hadj (m k : ι) : (T.adjoint (EuclideanSpace.single m 1)).ofLp k =
      (T (EuclideanSpace.single k 1)).ofLp m := by
    have h1 := EuclideanSpace.inner_single_left (𝕜 := ℝ) k 1
      (T.adjoint (EuclideanSpace.single m 1))
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm,
      EuclideanSpace.inner_single_left] at h1
    simpa using h1.symm
  -- Evaluating both bilinear forms on `eᵢ` and `eⱼ` expands them into coordinates.
  simp only [matrixBilinearForm_apply, ContinuousLinearMap.bilinearComp_apply, smul_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, PiLp.single_apply, hadj, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  rw [h]
  simp only [Finset.mul_sum, mul_assoc]

/-- **The transformed drift through a left inverse of `DΦ`.** If `T` is a left inverse of
`DΦ(x)`, then `b'(x) = |det DΦ(x)| T b(Φ x)`. -/
theorem pullbackDrift_eq_smul_apply {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {x : EuclideanSpace ℝ ι}
    {T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    (hT : T ∘L fderiv ℝ Φ x = ContinuousLinearMap.id ℝ _) :
    pullbackDrift Φ b x = |(fderiv ℝ Φ x).det| • T (b (Φ x)) := by
  have hdet : (fderiv ℝ Φ x).det ≠ 0 := by
    have h : T.det * (fderiv ℝ Φ x).det = 1 := by
      rw [← ContinuousLinearMap.det_comp, hT, ContinuousLinearMap.det_id]
    exact right_ne_zero_of_mul_eq_one h
  -- The map of `M(x)⁻¹` is a right inverse of `DΦ(x)`, so it agrees with the left inverse `T`.
  rw [pullbackDrift_apply]
  conv_rhs => rw [← fderiv_apply_toEuclideanCLM_inv_apply hdet (b (Φ x)),
    ← ContinuousLinearMap.comp_apply, hT, ContinuousLinearMap.id_apply]

/-- **The pulled-back matrix is invariant under the reflection.** For symmetric `A` with
`⟪ν, A ν⟫ ≠ 0` and a map `Φ` whose derivative at `x` is the shear `y ↦ y + ⟪ν, y⟫ s`, `s` the
conormal shear vector, the form of the constant matrix `A` pulled back by `Φ` at `x`
(`TauCeti.PDE.pullbackPrincipal`) is invariant under the reflection in `ν⊥`: in the sheared
coordinates the conormal direction of `A` is the normal `ν`. -/
theorem matrixBilinearForm_pullbackPrincipal_reflection_of_fderiv_eq {A : Matrix ι ι ℝ}
    {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0) (hq : matrixBilinearForm A ν ν ≠ 0)
    (hAs : ∀ η ξ : EuclideanSpace ℝ ι, matrixBilinearForm A η ξ = matrixBilinearForm A ξ η)
    {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x : EuclideanSpace ℝ ι}
    (hΦ : fderiv ℝ Φ x = transvectionL ν (conormalShearVector A ν)) (ξ η : EuclideanSpace ℝ ι) :
    matrixBilinearForm (pullbackPrincipal Φ (fun _ => A) x)
        ((ℝ ∙ ν)ᗮ.reflection ξ) ((ℝ ∙ ν)ᗮ.reflection η) =
      matrixBilinearForm (pullbackPrincipal Φ (fun _ => A) x) ξ η := by
  rw [matrixBilinearForm_pullbackPrincipal_of_fderiv_eq_transvectionL (fun _ => A)
      (inner_conormalShearVector_right_eq_zero hν hq) hΦ, transvectionL_neg_left]
  exact matrixBilinearForm_transvectionL_conormalShearVector_reflection hν hq hAs ξ η

end Coefficients

/-! ### Uniform ellipticity of the transformed principal coefficient -/

section Ellipticity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {L L' : ℝ}

/-- The lower ellipticity bound of the transformed principal coefficient at a point: if `a(Φ x)`
has lower constant `λ ≥ 0`, `‖DΦ(x)‖ ≤ L` and `c ≤ |det DΦ(x)|`, then `a'(x)` has lower constant
`c λ / L²`. -/
private theorem mul_norm_sq_le_toQuadraticForm'_pullbackPrincipal
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam c : ℝ} {x : EuclideanSpace ℝ ι}
    (ha : ∀ ζ : EuclideanSpace ℝ ι, lam * ‖ζ‖ ^ 2 ≤ (a (Φ x)).toQuadraticForm' ζ) (hlam : 0 ≤ lam)
    (hL0 : 0 < L) (hL : ‖fderiv ℝ Φ x‖ ≤ L) (hL' : ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖)
    (hL'0 : 0 ≤ L') (hc : 0 < c) (hdet : c ≤ |(fderiv ℝ Φ x).det|) (ξ : EuclideanSpace ℝ ι) :
    c * lam / L ^ 2 * ‖ξ‖ ^ 2 ≤ (pullbackPrincipal Φ a x).toQuadraticForm' ξ := by
  have hdet0 : (fderiv ℝ Φ x).det ≠ 0 := abs_pos.1 (hc.trans_le hdet)
  have hunit : IsUnit (fderiv ℝ Φ x) := ContinuousLinearMap.isUnit_iff_bijective.2 <|
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hdet0.isUnit)
  -- Write `ξ = DΦ(x)* ζ`; then `ξᵀ a' ξ = J ζᵀ a ζ ≥ c λ ‖ζ‖²` and `‖ξ‖ ≤ L ‖ζ‖`.
  obtain ⟨ζ, rfl, -⟩ :=
    (fderiv ℝ Φ x).exists_adjoint_apply_eq_and_norm_le hunit hL'0 hL' ξ
  have hζ : ‖(fderiv ℝ Φ x).adjoint ζ‖ ≤ L * ‖ζ‖ := by
    refine ((fderiv ℝ Φ x).adjoint.le_opNorm ζ).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right hL (norm_nonneg _)
  rw [toQuadraticForm'_apply, ← matrixBilinearForm_apply,
    matrixBilinearForm_pullbackPrincipal a hdet0, matrixBilinearForm_apply,
    ← toQuadraticForm'_apply]
  calc c * lam / L ^ 2 * ‖(fderiv ℝ Φ x).adjoint ζ‖ ^ 2
      ≤ c * lam / L ^ 2 * (L * ‖ζ‖) ^ 2 := by gcongr
    _ = c * (lam * ‖ζ‖ ^ 2) := by field_simp
    _ ≤ |(fderiv ℝ Φ x).det| * (a (Φ x)).toQuadraticForm' ζ :=
        mul_le_mul hdet (ha ζ) (by positivity) (abs_nonneg _)

/-- The upper bound of the transformed principal coefficient at a point: if `a(Φ x)` has upper
constant `Λ ≥ 0`, `‖DΦ(x)‖ ≤ L` and `‖v‖ ≤ L' ‖DΦ(x) v‖`, then `a'(x)` has upper constant
`Lⁿ L'² Λ`. -/
private theorem abs_matrixBilinearForm_pullbackPrincipal_le
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Lam : ℝ} {x : EuclideanSpace ℝ ι}
    (ha : ∀ η ξ : EuclideanSpace ℝ ι, |matrixBilinearForm (a (Φ x)) η ξ| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hLam : 0 ≤ Lam) (hL : ‖fderiv ℝ Φ x‖ ≤ L) (hL' : ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖)
    (hL'0 : 0 ≤ L') (hdet0 : (fderiv ℝ Φ x).det ≠ 0) (η ξ : EuclideanSpace ℝ ι) :
    |matrixBilinearForm (pullbackPrincipal Φ a x) η ξ| ≤
      L ^ Fintype.card ι * L' ^ 2 * Lam * ‖η‖ * ‖ξ‖ := by
  have hunit : IsUnit (fderiv ℝ Φ x) := ContinuousLinearMap.isUnit_iff_bijective.2 <|
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hdet0.isUnit)
  -- Write `η = DΦ(x)* ζ'` and `ξ = DΦ(x)* ζ`, with `‖ζ'‖ ≤ L' ‖η‖` and `‖ζ‖ ≤ L' ‖ξ‖`, and
  -- bound `|det DΦ(x)| ≤ ‖DΦ(x)‖ⁿ ≤ Lⁿ`.
  obtain ⟨ζ', rfl, hζ'⟩ :=
    (fderiv ℝ Φ x).exists_adjoint_apply_eq_and_norm_le hunit hL'0 hL' η
  obtain ⟨ζ, rfl, hζ⟩ :=
    (fderiv ℝ Φ x).exists_adjoint_apply_eq_and_norm_le hunit hL'0 hL' ξ
  have hdetle : |(fderiv ℝ Φ x).det| ≤ L ^ Fintype.card ι := by
    refine ((fderiv ℝ Φ x).abs_det_le_opNorm_pow).trans ?_
    rw [finrank_euclideanSpace]
    exact pow_le_pow_left₀ (norm_nonneg _) hL _
  rw [matrixBilinearForm_pullbackPrincipal a hdet0, abs_mul, abs_abs]
  calc |(fderiv ℝ Φ x).det| * |matrixBilinearForm (a (Φ x)) ζ' ζ|
      ≤ L ^ Fintype.card ι * (Lam * ‖ζ'‖ * ‖ζ‖) :=
        mul_le_mul hdetle (ha ζ' ζ) (abs_nonneg _) ((abs_nonneg _).trans hdetle)
    _ ≤ L ^ Fintype.card ι * (Lam * (L' * ‖(fderiv ℝ Φ x).adjoint ζ'‖) *
          (L' * ‖(fderiv ℝ Φ x).adjoint ζ‖)) := by
        gcongr
        exact (abs_nonneg _).trans hdetle
    _ = L ^ Fintype.card ι * L' ^ 2 * Lam * ‖(fderiv ℝ Φ x).adjoint ζ'‖ *
          ‖(fderiv ℝ Φ x).adjoint ζ‖ := by ring

/-- **Uniform ellipticity is preserved by a change of variables.** Let `a` be uniformly elliptic
and bounded on `t` with constants `λ ≤ Λ`, and let `Φ` map a nonempty set `s` into `t`, with
`‖DΦ‖ ≤ L`, `‖v‖ ≤ L' ‖DΦ(x) v‖` for every `v`, and `c ≤ |det DΦ|` on `s` for some `c > 0`. Then
the transformed principal coefficient `a'` is uniformly elliptic and bounded on `s` with
constants `c λ / L²` and `Lⁿ L'² Λ`, where `n` is the dimension. -/
theorem UniformlyEllipticOn.pullbackPrincipal [Nonempty ι] {s t : Set (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ}
    (ha : UniformlyEllipticOn t a lam Lam) (hmaps : MapsTo Φ s t) (hs : s.Nonempty)
    (hL : ∀ x ∈ s, ‖fderiv ℝ Φ x‖ ≤ L) (hL' : ∀ x ∈ s, ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖)
    (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ Φ x).det|) :
    UniformlyEllipticOn s (PDE.pullbackPrincipal Φ a) (c * lam / L ^ 2)
      (L ^ Fintype.card ι * L' ^ 2 * Lam) := by
  obtain ⟨hlam, hlamLam, ha⟩ := uniformlyEllipticOn_iff.1 ha
  -- At a point `x₀ ∈ s`, `1 ≤ ‖DΦ(x₀)‖ L' ≤ L L'`, so `L' ≥ 0` and `L > 0`.
  obtain ⟨x₀, hx₀⟩ := hs
  have h1 := (fderiv ℝ Φ x₀).one_le_opNorm_mul_of_forall_norm_le (hL' x₀ hx₀)
  have hL'0 : 0 ≤ L' := (pos_of_mul_pos_right (one_pos.trans_le h1) (norm_nonneg _)).le
  have hLL' : 1 ≤ L * L' := h1.trans (mul_le_mul_of_nonneg_right (hL x₀ hx₀) hL'0)
  have hL0 : 0 < L := pos_of_mul_pos_left (one_pos.trans_le hLL') hL'0
  refine uniformlyEllipticOn_iff.2 ⟨by positivity, ?_, fun x hx => ⟨fun ξ => ?_, fun η ξ => ?_⟩⟩
  · -- `c λ / L² ≤ Lⁿ λ L'² ≤ Lⁿ L'² Λ`, using `c ≤ |det DΦ| ≤ Lⁿ` and `1 ≤ L L'`.
    have hcL : c ≤ L ^ Fintype.card ι := by
      refine (hdet x₀ hx₀).trans (((fderiv ℝ Φ x₀).abs_det_le_opNorm_pow).trans ?_)
      rw [finrank_euclideanSpace]
      exact pow_le_pow_left₀ (norm_nonneg _) (hL x₀ hx₀) _
    have hL'2 : 1 / L ^ 2 ≤ L' ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hΛ := mul_le_mul_of_nonneg_left hlamLam
      (by positivity : (0 : ℝ) ≤ L ^ Fintype.card ι * L' ^ 2)
    calc c * lam / L ^ 2 = c * lam * (1 / L ^ 2) := by ring
      _ ≤ L ^ Fintype.card ι * lam * L' ^ 2 := by gcongr
      _ ≤ L ^ Fintype.card ι * L' ^ 2 * Lam := by linarith
  · exact mul_norm_sq_le_toQuadraticForm'_pullbackPrincipal (ha (hmaps hx)).1 hlam.le hL0
      (hL x hx) (hL' x hx) hL'0 hc (hdet x hx) ξ
  · rw [← matrixBilinearForm_apply]
    refine abs_matrixBilinearForm_pullbackPrincipal_le (fun η ξ => ?_)
      (hlam.le.trans hlamLam) (hL x hx) (hL' x hx) hL'0 (abs_pos.1 (hc.trans_le (hdet x hx))) η ξ
    rw [matrixBilinearForm_apply]
    exact (ha (hmaps hx)).2 η ξ

end Ellipticity

/-! ### Hölder continuity of the transformed coefficients -/

section Holder

open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Hölder principal coefficients stay Hölder.** Let `Φ` map `s` into `t`, and let `T` be a
pointwise left inverse of `DΦ` on `s`. If `x ↦ a(x)` is `r`-Hölder with constant `Ka` and bounded
by `M` on `t` in the operator norm of its bilinear forms, `Φ` is `KΦ`-Lipschitz on `s`, `T` is
`r`-Hölder with constant `KT` and bounded by `L` on `s`, and the Jacobian `|det DΦ|` is `r`-Hölder
with constant `KJ` and bounded by `J` on `s`, then the transformed principal coefficient
`a'(x) = |det DΦ(x)| DΦ(x)⁻¹ a(Φ x) DΦ(x)⁻ᵀ` is `r`-Hölder on `s` with constant
`Ka KΦ^r J L² + M (J KT + L KJ) L + M J L KT`. For `r = 1` this says that Lipschitz principal
coefficients stay Lipschitz under a change of variables with Lipschitz derivative. -/
theorem holderOnWith_matrixBilinearForm_pullbackPrincipal
    {s t : Set (EuclideanSpace ℝ ι)} {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {KΦ KT KJ Ka r L J M : ℝ≥0} (hmaps : MapsTo Φ s t)
    (hT : ∀ x ∈ s, T x ∘L fderiv ℝ Φ x = ContinuousLinearMap.id ℝ _)
    (hΦ : LipschitzOnWith KΦ Φ s) (hTh : HolderOnWith KT r T s) (hTL : ∀ x ∈ s, ‖T x‖ ≤ L)
    (hJ : HolderOnWith KJ r (fun x => |(fderiv ℝ Φ x).det|) s)
    (hJb : ∀ x ∈ s, |(fderiv ℝ Φ x).det| ≤ J)
    (ha : HolderOnWith Ka r (fun y => matrixBilinearForm (a y)) t)
    (haM : ∀ y ∈ t, ‖matrixBilinearForm (a y)‖ ≤ M) :
    HolderOnWith (Ka * KΦ ^ (r : ℝ) * (J * L) * L + M * (J * KT + L * KJ) * L +
        M * (J * L) * KT) r (fun x => matrixBilinearForm (pullbackPrincipal Φ a x)) s := by
  -- The coefficient is `(a ∘ Φ)(|det DΦ| T* ·, T* ·)`, each factor Hölder and bounded on `s`.
  have haΦ : HolderOnWith (Ka * KΦ ^ (r : ℝ)) r (fun x => matrixBilinearForm (a (Φ x))) s := by
    simpa only [mul_one, Function.comp_def] using ha.comp hΦ.holderOnWith hmaps
  have hTa : HolderOnWith KT r (fun x => (T x).adjoint) s :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := EuclideanSpace ℝ ι)
      (F := EuclideanSpace ℝ ι)).isometry.comp_holderOnWith hTh
  have hTaL (x : EuclideanSpace ℝ ι) (hx : x ∈ s) : ‖(T x).adjoint‖ ≤ L := by
    rw [LinearIsometryEquiv.norm_map]
    exact hTL x hx
  have hJn (x : EuclideanSpace ℝ ι) (hx : x ∈ s) : ‖|(fderiv ℝ Φ x).det|‖ ≤ J := by
    rw [Real.norm_eq_abs, abs_abs]
    exact hJb x hx
  refine (ContinuousLinearMap.holderOnWith_bilinearComp haΦ (hJ.smul_of_norm_le hTa hJn hTaL) hTa
    (fun x hx => haM _ (hmaps hx)) (fun x hx => ?_) hTaL).congr fun x hx => ?_
  · rw [norm_smul, NNReal.coe_mul]
    exact mul_le_mul (hJn x hx) (hTaL x hx) (norm_nonneg _) J.coe_nonneg
  · rw [matrixBilinearForm_pullbackPrincipal_eq_bilinearComp a (hT x hx)]
    ext η ξ
    simp

/-- **Hölder drifts stay Hölder.** Let `Φ` map `s` into `t`, and let `T` be a pointwise left
inverse of `DΦ` on `s`. If `b` is `r`-Hölder with constant `Kb` and bounded by `M` on `t`, `Φ` is
`KΦ`-Lipschitz on `s`, `T` is `r`-Hölder with constant `KT` and bounded by `L` on `s`, and the
Jacobian `|det DΦ|` is `r`-Hölder with constant `KJ` and bounded by `J` on `s`, then the
transformed vector field `b'(x) = |det DΦ(x)| DΦ(x)⁻¹ b(Φ x)` is `r`-Hölder on `s` with constant
`J (L Kb KΦ^r + M KT) + L M KJ`. A vector field `G` in a divergence datum `div G` transforms in
the same way (`TauCeti.PDE.setIntegral_inner_pullbackDrift_gradient_compL`). -/
theorem holderOnWith_pullbackDrift {s t : Set (EuclideanSpace ℝ ι)}
    {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {KΦ KT KJ Kb r L J M : ℝ≥0} (hmaps : MapsTo Φ s t)
    (hT : ∀ x ∈ s, T x ∘L fderiv ℝ Φ x = ContinuousLinearMap.id ℝ _)
    (hΦ : LipschitzOnWith KΦ Φ s) (hTh : HolderOnWith KT r T s) (hTL : ∀ x ∈ s, ‖T x‖ ≤ L)
    (hJ : HolderOnWith KJ r (fun x => |(fderiv ℝ Φ x).det|) s)
    (hJb : ∀ x ∈ s, |(fderiv ℝ Φ x).det| ≤ J) (hb : HolderOnWith Kb r b t)
    (hbM : ∀ y ∈ t, ‖b y‖ ≤ M) :
    HolderOnWith (J * (L * (Kb * KΦ ^ (r : ℝ)) + M * KT) + L * M * KJ) r (pullbackDrift Φ b) s := by
  -- The drift is `|det DΦ| T (b ∘ Φ)`, each factor Hölder and bounded on `s`.
  have hbΦ : HolderOnWith (Kb * KΦ ^ (r : ℝ)) r (fun x => b (Φ x)) s := by
    simpa only [mul_one, Function.comp_def] using hb.comp hΦ.holderOnWith hmaps
  have hTb : HolderOnWith (L * (Kb * KΦ ^ (r : ℝ)) + M * KT) r (fun x => T x (b (Φ x))) s :=
    ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)).holderOnWith_comp₂
      hTh hbΦ hTL fun x hx => hbM _ (hmaps hx)).mono_const
      (mul_le_of_le_one_left zero_le ContinuousLinearMap.norm_id_le)
  have hJn (x : EuclideanSpace ℝ ι) (hx : x ∈ s) : ‖|(fderiv ℝ Φ x).det|‖ ≤ J := by
    rw [Real.norm_eq_abs, abs_abs]
    exact hJb x hx
  refine (hJ.smul_of_norm_le hTb hJn fun x hx => ?_).congr fun x hx =>
    (pullbackDrift_eq_smul_apply b (hT x hx)).symm
  rw [NNReal.coe_mul]
  exact ((T x).le_opNorm _).trans
    (mul_le_mul (hTL x hx) (hbM _ (hmaps hx)) (norm_nonneg _) L.coe_nonneg)

end Holder

/-! ### The energy form and weak solutions under a change of variables -/

section WeakSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {U V : Opens (EuclideanSpace ℝ ι)} {p : ENNReal} [Fact (1 ≤ p)]
  {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L c₀ : ℝ}

omit [DecidableEq ι] in
/-- **Change of variables in a density integral against a Sobolev function.** If `Φ` maps `U`
onto `V`, then `∫_U f' (w ∘ Φ) = ∫_V f w` for every `w ∈ W^{1,p}(V)`, where
`f' = |det DΦ| (f ∘ Φ)` is the pulled-back density. -/
theorem setIntegral_pullbackDensity_mul_value_compL (hp : p ≠ ⊤) (hΦ : DifferentiableOn ℝ Φ U)
    (hinj : InjOn Φ U) (hmaps : MapsTo Φ U V)
    (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L) (hc₀ : 0 < c₀)
    (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    (himage : Φ '' U = V) (f : EuclideanSpace ℝ ι → ℝ) (w : W1p mu V p) :
    ∫ x in U, pullbackDensity Φ f x * W1p.value (W1p.compL Φ hp hΦ hinj hmaps hL hc₀ hdet w) x
        ∂mu =
      ∫ y in V, f y * W1p.value w y ∂mu := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul mu U.isOpen.measurableSet
    (fun x hx => ((hΦ x hx).differentiableAt (U.isOpen.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt)
    hinj fun y => f y * W1p.value w y
  rw [himage] at h
  rw [h]
  refine setIntegral_congr_ae U.isOpen.measurableSet ?_
  filter_upwards [ae_restrict_iff' U.isOpen.measurableSet |>.1
    (W1p.value_compL_ae Φ hp hΦ hinj hmaps hL hc₀ hdet w)] with x hx hxU
  rw [hx hxU, pullbackDensity_apply, smul_eq_mul, mul_assoc]

/-- **Change of variables in a divergence datum.** If `Φ` maps `U` onto `V`, then
`∫_U ⟪G', ∇(w ∘ Φ)⟫ = ∫_V ⟪G, ∇w⟫` for every `w ∈ W^{1,p}(V)`, where
`G' = |det DΦ| DΦ⁻¹ (G ∘ Φ)` is the transformed vector field: a divergence datum `div G`
transforms like the drift. -/
theorem setIntegral_inner_pullbackDrift_gradient_compL (hp : p ≠ ⊤)
    (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U) (hmaps : MapsTo Φ U V)
    (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L) (hc₀ : 0 < c₀)
    (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    (himage : Φ '' U = V) (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (w : W1p mu V p) :
    ∫ x in U, ⟪pullbackDrift Φ G x,
        W1p.gradient (W1p.compL Φ hp hΦ hinj hmaps hL hc₀ hdet w) x⟫_ℝ ∂mu =
      ∫ y in V, ⟪G y, W1p.gradient w y⟫_ℝ ∂mu := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul mu U.isOpen.measurableSet
    (fun x hx => ((hΦ x hx).differentiableAt (U.isOpen.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt)
    hinj fun y => ⟪G y, W1p.gradient w y⟫_ℝ
  rw [himage] at h
  rw [h]
  refine setIntegral_congr_ae U.isOpen.measurableSet ?_
  filter_upwards [ae_restrict_iff' U.isOpen.measurableSet |>.1
    (W1p.gradient_compL_ae Φ hp hΦ hinj hmaps hL hc₀ hdet w)] with x hx hxU
  rw [hx hxU, inner_pullbackDrift_adjoint G (abs_pos.1 (hc₀.trans_le (hdet x hxU))),
    smul_eq_mul]

/-- **The energy form is invariant under a change of variables.** If `Φ` maps `U` onto `V`, the
energy form on `V` with coefficients `a`, `b`, `c` of two functions `u, w ∈ H¹(V)` equals the
energy form on `U` with the transformed coefficients `a'`, `b'`, `c'` of `u ∘ Φ` and `w ∘ Φ`. -/
theorem energyFormH1_compL (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U) (hmaps : MapsTo Φ U V)
    (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L) (hc₀ : 0 < c₀)
    (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    (himage : Φ '' U = V) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u w : W1p mu V 2) :
    energyFormH1 (pullbackPrincipal Φ a) (pullbackDrift Φ b) (pullbackDensity Φ c)
        (W1p.compL Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet u)
        (W1p.compL Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet w) =
      energyFormH1 a b c u w := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul mu U.isOpen.measurableSet
    (fun x hx => ((hΦ x hx).differentiableAt (U.isOpen.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt)
    hinj fun y => energyIntegrand (a y) (b y) (c y) (jetField u y) (jetField w y)
  rw [himage] at h
  rw [energyFormH1_def, energyFormH1_def, h]
  refine setIntegral_congr_ae U.isOpen.measurableSet ?_
  filter_upwards [ae_restrict_iff' U.isOpen.measurableSet |>.1
      (W1p.value_compL_ae Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet u),
    ae_restrict_iff' U.isOpen.measurableSet |>.1
      (W1p.gradient_compL_ae Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet u),
    ae_restrict_iff' U.isOpen.measurableSet |>.1
      (W1p.value_compL_ae Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet w),
    ae_restrict_iff' U.isOpen.measurableSet |>.1
      (W1p.gradient_compL_ae Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet w)]
    with x hu hgu hw hgw hxU
  rw [jetField_apply, jetField_apply, hu hxU, hgu hxU, hw hxU, hgw hxU, smul_eq_mul,
    energyIntegrand_pullback a b c (abs_pos.1 (hc₀.trans_le (hdet x hxU)))
      (W1p.value u (Φ x), W1p.gradient u (Φ x)) (W1p.value w (Φ x), W1p.gradient w (Φ x)),
    jetField_apply, jetField_apply]

/-- **Weak solutions with a divergence datum are carried to weak solutions by a change of
variables.** Let `Φ` map `U` into `V` and `Ψ` map `V` into `U`, inverse to each other, both
differentiable with bounded derivative and Jacobian bounded below. If `u ∈ H¹(V)` is a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f - ∂ᵢGⁱ` in `V`, tested against `H¹₀(V)`, then
`u ∘ Φ ∈ H¹(U)` is a weak solution of `-∂ᵢ(a'ⁱʲ ∂ⱼu') + b'ⁱ ∂ᵢu' + c' u' = f' - ∂ᵢG'ⁱ` in `U`,
tested against `H¹₀(U)`, with the transformed coefficients, the pulled-back right-hand side
`f' = |det DΦ| (f ∘ Φ)` and the transformed vector field `G' = |det DΦ| DΦ⁻¹ (G ∘ Φ)`. -/
theorem energyFormH1_compL_eq_setIntegral_add_setIntegral_inner (hΦ : DifferentiableOn ℝ Φ U)
    (hinj : InjOn Φ U) (hmaps : MapsTo Φ U V)
    (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L)
    (hc₀ : 0 < c₀) (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    {Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L' c₁ : ℝ} (hΨ : DifferentiableOn ℝ Ψ V)
    (hΨmaps : MapsTo Ψ V U) (hΨL : ∀ y ∈ (V : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Ψ y‖ ≤ L')
    (hc₁ : 0 < c₁) (hΨdet : ∀ y ∈ (V : Set (EuclideanSpace ℝ ι)), c₁ ≤ |(fderiv ℝ Ψ y).det|)
    (hΨΦ : LeftInvOn Ψ Φ U) (hΦΨ : RightInvOn Ψ Φ V) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ}
    {u : W1p mu V 2}
    (hu : ∀ w : W1p0 mu V 2, energyFormH1 a b c u (w : W1p mu V 2) =
      ∫ y in V, f y * W1p.value (w : W1p mu V 2) y ∂mu +
        ∫ y in V, ⟪G y, W1p.gradient (w : W1p mu V 2) y⟫_ℝ ∂mu)
    (φ : W1p0 mu U 2) :
    energyFormH1 (pullbackPrincipal Φ a) (pullbackDrift Φ b) (pullbackDensity Φ c)
        (W1p.compL Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet u) (φ : W1p mu U 2) =
      ∫ x in U, pullbackDensity Φ f x * W1p.value (φ : W1p mu U 2) x ∂mu +
        ∫ x in U, ⟪pullbackDrift Φ G x, W1p.gradient (φ : W1p mu U 2) x⟫_ℝ ∂mu := by
  have hp : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  have himage : Φ '' U = V :=
    Subset.antisymm hmaps.image_subset (hΦΨ.surjOn hΨmaps)
  -- The test function `φ` on `U` is `w ∘ Φ` for `w = φ ∘ Ψ ∈ H¹₀(V)`.
  set w := W1p.compL Ψ hp hΨ hΦΨ.injOn hΨmaps hΨL hc₁ hΨdet (φ : W1p mu U 2)
  have hw : w ∈ w1p0Submodule mu V 2 :=
    W1p.compL_mem_w1p0Submodule_of_leftInvOn Ψ hp hΨ hΦΨ.injOn hΨmaps hΨL hc₁
      hΨdet hΦ.continuousOn hmaps hΦΨ φ.property
  have hφ : W1p.compL Φ hp hΦ hinj hmaps hL hc₀ hdet w = φ :=
    W1p.compL_compL_of_leftInvOn Φ hp hΦ hinj hmaps hL hc₀ hdet hΨ hΦΨ.injOn
      hΨmaps hΨL hc₁ hΨdet hΨΦ (φ : W1p mu U 2)
  rw [← hφ, energyFormH1_compL hΦ hinj hmaps hL hc₀ hdet himage,
    setIntegral_pullbackDensity_mul_value_compL hp hΦ hinj hmaps hL hc₀ hdet himage,
    setIntegral_inner_pullbackDrift_gradient_compL hp hΦ hinj hmaps hL hc₀ hdet himage]
  exact hu ⟨w, hw⟩

/-- **Weak solutions are carried to weak solutions by a change of variables.** Let `Φ` map `U`
into `V` and `Ψ` map `V` into `U`, inverse to each other, both differentiable with bounded
derivative and Jacobian bounded below. If `u ∈ H¹(V)` is a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` in `V`, tested against `H¹₀(V)`, then `u ∘ Φ ∈ H¹(U)` is a weak
solution of `-∂ᵢ(a'ⁱʲ ∂ⱼu') + b'ⁱ ∂ᵢu' + c' u' = f'` in `U`, tested against `H¹₀(U)`, with the
transformed coefficients and the pulled-back right-hand side `f' = |det DΦ| (f ∘ Φ)`. -/
theorem energyFormH1_compL_eq_setIntegral (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U)
    (hmaps : MapsTo Φ U V) (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L)
    (hc₀ : 0 < c₀) (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    {Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L' c₁ : ℝ} (hΨ : DifferentiableOn ℝ Ψ V)
    (hΨmaps : MapsTo Ψ V U) (hΨL : ∀ y ∈ (V : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Ψ y‖ ≤ L')
    (hc₁ : 0 < c₁) (hΨdet : ∀ y ∈ (V : Set (EuclideanSpace ℝ ι)), c₁ ≤ |(fderiv ℝ Ψ y).det|)
    (hΨΦ : LeftInvOn Ψ Φ U) (hΦΨ : RightInvOn Ψ Φ V) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ}
    {u : W1p mu V 2}
    (hu : ∀ w : W1p0 mu V 2, energyFormH1 a b c u (w : W1p mu V 2) =
      ∫ y in V, f y * W1p.value (w : W1p mu V 2) y ∂mu)
    (φ : W1p0 mu U 2) :
    energyFormH1 (pullbackPrincipal Φ a) (pullbackDrift Φ b) (pullbackDensity Φ c)
        (W1p.compL Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet u) (φ : W1p mu U 2) =
      ∫ x in U, pullbackDensity Φ f x * W1p.value (φ : W1p mu U 2) x ∂mu := by
  have h := energyFormH1_compL_eq_setIntegral_add_setIntegral_inner hΦ hinj hmaps hL hc₀ hdet hΨ
    hΨmaps hΨL hc₁ hΨdet hΨΦ hΦΨ (a := a) (b := b) (c := c) (f := f) (G := 0) (u := u)
    (fun w => by
      rw [hu w]
      simp only [Pi.zero_apply, inner_zero_left, integral_zero, add_zero]) φ
  simpa only [pullbackDrift_zero, Pi.zero_apply, inner_zero_left, integral_zero, add_zero] using h

end WeakSolution

/-! ### Integrability of the transformed lower-order coefficients -/

section Integrability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {U V : Opens (EuclideanSpace ℝ ι)}
  {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L L' c₀ : ℝ}

/-- If `Φ` maps `U` into `V` with an inverse `Ψ` differentiable on `V`, the transformed drift at
`x ∈ U` is `|det DΦ(x)| DΨ(Φ x) b(Φ x)`. -/
theorem pullbackDrift_eq_of_invOn (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V)
    (hΨ : DifferentiableOn ℝ Ψ V) (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ (U : Set (EuclideanSpace ℝ ι))) :
    pullbackDrift Φ b x = |(fderiv ℝ Φ x).det| • fderiv ℝ Ψ (Φ x) (b (Φ x)) := by
  rw [pullbackDrift_apply, toEuclideanCLM_inv_fderiv_of_invOn hΦ hmaps hΨ hΦΨ hΨΦ hx]

/-- **The transformed drift is bounded pointwise.** If `Φ` maps `U` into `V` with an inverse `Ψ`
differentiable on `V`, `‖DΦ(x)‖ ≤ L` and `‖DΨ(Φ x)‖ ≤ L'`, then
`‖b'(x)‖ ≤ Lⁿ L' ‖b(Φ x)‖`, where `n` is the dimension. -/
theorem norm_pullbackDrift_le (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V)
    (hΨ : DifferentiableOn ℝ Ψ V) (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ (U : Set (EuclideanSpace ℝ ι))) (hL : ‖fderiv ℝ Φ x‖ ≤ L)
    (hL' : ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    ‖pullbackDrift Φ b x‖ ≤ L ^ Fintype.card ι * L' * ‖b (Φ x)‖ := by
  have hdet : |(fderiv ℝ Φ x).det| ≤ L ^ Fintype.card ι := by
    refine ((fderiv ℝ Φ x).abs_det_le_opNorm_pow).trans ?_
    rw [finrank_euclideanSpace]
    exact pow_le_pow_left₀ (norm_nonneg _) hL _
  rw [pullbackDrift_eq_of_invOn hΦ hmaps hΨ hΦΨ hΨΦ b hx, norm_smul, Real.norm_eq_abs, abs_abs,
    mul_assoc]
  exact mul_le_mul hdet (((fderiv ℝ Ψ (Φ x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL' (norm_nonneg _)))
    (norm_nonneg _) ((abs_nonneg _).trans hdet)

omit [DecidableEq ι] in
/-- **Transformed densities stay in `Lᵖ`.** Let `Φ` map `U` injectively into `V`, with
`‖DΦ‖ ≤ L` and `c₀ ≤ |det DΦ|` on `U` for some `c₀ > 0`. If `f ∈ Lᵖ(V)`, then
`f' = |det DΦ| (f ∘ Φ) ∈ Lᵖ(U)`. This applies to the zeroth-order coefficient (`p = ∞`) and to
the right-hand side (`p = 2`). -/
theorem memLp_pullbackDensity (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U)
    (hmaps : MapsTo Φ U V) (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L)
    (hc₀ : 0 < c₀) (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    {p : ENNReal} {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f p (mu.restrict V)) :
    MemLp (pullbackDensity Φ f) p (mu.restrict U) := by
  have hfΦ : MemLp (f ∘ Φ) p (mu.restrict U) :=
    (hf.of_measure_le_smul (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc₀).ne')
      (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc₀
        hdet)).comp_of_map (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
  have hJ : AEStronglyMeasurable (fun x => |(fderiv ℝ Φ x).det|) (mu.restrict U) :=
    (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ Φ))).aestronglyMeasurable
  refine hfΦ.of_le_mul (c := L ^ Fintype.card ι) (hJ.mul hfΦ.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
  rw [pullbackDensity_apply, norm_mul, Real.norm_eq_abs, abs_abs, Function.comp_apply]
  refine mul_le_mul_of_nonneg_right (((fderiv ℝ Φ x).abs_det_le_opNorm_pow).trans ?_)
    (norm_nonneg _)
  rw [finrank_euclideanSpace]
  exact pow_le_pow_left₀ (norm_nonneg _) (hL x hx) _

/-- **The transformed drift stays in `Lᵖ`.** Let `Φ` map `U` into `V`, with `‖DΦ‖ ≤ L` and
`c₀ ≤ |det DΦ|` on `U` for some `c₀ > 0`, and let `Ψ` be an inverse of `Φ`, differentiable on
`V` with `‖DΨ‖ ≤ L'` there. If `b ∈ Lᵖ(V)`, then the transformed drift
`b' = |det DΦ| DΦ⁻¹ (b ∘ Φ) ∈ Lᵖ(U)`. With `p = ∞`, a bounded drift stays bounded. -/
theorem memLp_pullbackDrift (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V)
    (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L)
    (hc₀ : 0 < c₀) (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    (hΨ : DifferentiableOn ℝ Ψ V) (hΨL : ∀ y ∈ (V : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Ψ y‖ ≤ L')
    (hΨΦ : LeftInvOn Ψ Φ U) (hΦΨ : RightInvOn Ψ Φ V) {p : ENNReal}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hb : MemLp b p (mu.restrict V)) :
    MemLp (pullbackDrift Φ b) p (mu.restrict U) := by
  have hbΦ : MemLp (b ∘ Φ) p (mu.restrict U) :=
    (hb.of_measure_le_smul (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc₀).ne')
      (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hΨΦ.injOn hmaps hc₀
        hdet)).comp_of_map (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
  have hJ : AEStronglyMeasurable (fun x => |(fderiv ℝ Φ x).det|) (mu.restrict U) :=
    (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ Φ))).aestronglyMeasurable
  -- On `U` the transformed drift is `|det DΦ| DΨ(Φ ·) (b ∘ Φ)`, which is measurable.
  have hmeas : AEStronglyMeasurable (fun x => |(fderiv ℝ Φ x).det| • fderiv ℝ Ψ (Φ x) (b (Φ x)))
      (mu.restrict U) :=
    hJ.smul
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ ι)).aestronglyMeasurable_comp₂
        hbΦ.aestronglyMeasurable
        ((measurable_fderiv ℝ Ψ).comp_aemeasurable
          (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)).aestronglyMeasurable)
  refine hbΦ.of_le_mul (c := L ^ Fintype.card ι * L') (hmeas.congr ?_) ?_
  · filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact (pullbackDrift_eq_of_invOn hΦ hmaps hΨ hΦΨ hΨΦ b hx).symm
  · filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact norm_pullbackDrift_le hΦ hmaps hΨ hΦΨ hΨΦ b hx (hL x hx) (hΨL _ (hmaps hx))

end Integrability

/-! ### Mutually inverse changes of variables -/

section Inverse

open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {U U' : Opens (EuclideanSpace ℝ ι)}
  {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L L' : ℝ}

/-- **Ellipticity under mutually inverse changes of variables.** Let `Φ` and `Ψ` be mutually
inverse changes of variables of order one, with Jacobian determinants at least one in absolute
value, and let `Φ` map a nonempty subset `s` of its domain into `t`. If `a` is uniformly elliptic
and bounded on `t`, the pulled-back principal coefficient is uniformly elliptic and bounded on
`s`. -/
theorem exists_uniformlyEllipticOn_pullbackPrincipal [Nonempty ι]
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1)
    (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L' 1) (hΨΦ : LeftInvOn Ψ Φ U')
    (hΦΨ : RightInvOn Ψ Φ U) {s t : Set (EuclideanSpace ℝ ι)} (hsU : s ⊆ U') (hsne : s.Nonempty)
    (hmaps : MapsTo Φ s t) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn t a lam Lam) :
    ∃ lam' Lam' : ℝ, UniformlyEllipticOn s (pullbackPrincipal Φ a) lam' Lam' := by
  -- `DΦ` is bounded by `L`, and `DΨ(Φ x)` inverts it with norm at most `L'`.
  refine ⟨_, _, ha.pullbackPrincipal hmaps hsne (fun x hx => hΦ.norm_fderiv_le x (hsU hx))
    (L' := L') (fun x hx v => ?_) one_pos fun x hx =>
      (hΦ.abs_det_fderiv_eq_one hΨ hΨΦ hΦΨ (hsU hx)).ge⟩
  calc ‖v‖ = ‖fderiv ℝ Ψ (Φ x) (fderiv ℝ Φ x v)‖ := by
        rw [← ContinuousLinearMap.comp_apply, hΦ.fderiv_comp_fderiv_eq_id hΨ hΨΦ hΦΨ (hsU hx),
          ContinuousLinearMap.id_apply]
    _ ≤ ‖fderiv ℝ Ψ (Φ x)‖ * ‖fderiv ℝ Φ x v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ L' * ‖fderiv ℝ Φ x v‖ := mul_le_mul_of_nonneg_right
        (hΨ.norm_fderiv_le (k := 0) _ (hΦ.mapsTo (hsU hx))) (norm_nonneg _)

/-- **Ellipticity and Hölder bounds under mutually inverse changes of variables.** Let `Φ` and
`Ψ` be mutually inverse changes of variables of order one, with Jacobian determinants at least one
in absolute value, and let `Φ` map a nonempty subset `s` of its domain into `t`, Lipschitz on `s`
and with `x ↦ DΨ(Φ x)` `r`-Hölder on `s`. If `a` is uniformly elliptic and `r`-Hölder on `t`, the
pulled-back principal coefficient is uniformly elliptic and `r`-Hölder on `s`. This applies to the
flattening of a `C^{1,r}` boundary, whose inverse has an `r`-Hölder derivative. -/
theorem exists_uniformlyEllipticOn_and_holderOnWith_pullbackPrincipal [Nonempty ι]
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1)
    (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L' 1) (hΨΦ : LeftInvOn Ψ Φ U')
    (hΦΨ : RightInvOn Ψ Φ U) {s t : Set (EuclideanSpace ℝ ι)}
    (hsU : s ⊆ U') (hsne : s.Nonempty) (hmaps : MapsTo Φ s t) {KΦ KT r : ℝ≥0}
    (hΦl : LipschitzOnWith KΦ Φ s) (hT : HolderOnWith KT r (fun x => fderiv ℝ Ψ (Φ x)) s)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {K : ℝ≥0}
    (ha : UniformlyEllipticOn t a lam Lam)
    (hK : HolderOnWith K r (fun y => matrixBilinearForm (a y)) t) :
    ∃ (lam' Lam' : ℝ) (K' : ℝ≥0), UniformlyEllipticOn s (pullbackPrincipal Φ a) lam' Lam' ∧
      HolderOnWith K' r (fun x => matrixBilinearForm (pullbackPrincipal Φ a x)) s := by
  have hcomp (x : EuclideanSpace ℝ ι) (hx : x ∈ s) :=
    hΦ.fderiv_comp_fderiv_eq_id hΨ hΨΦ hΦΨ (hsU hx)
  have habs (x : EuclideanSpace ℝ ι) (hx : x ∈ s) : |(fderiv ℝ Φ x).det| = 1 :=
    hΦ.abs_det_fderiv_eq_one hΨ hΨΦ hΦΨ (hsU hx)
  have hΨL (x : EuclideanSpace ℝ ι) (hx : x ∈ s) : ‖fderiv ℝ Ψ (Φ x)‖ ≤ L' :=
    hΨ.norm_fderiv_le (k := 0) _ (hΦ.mapsTo (hsU hx))
  obtain ⟨lam', Lam', hellip⟩ :=
    exists_uniformlyEllipticOn_pullbackPrincipal hΦ hΨ hΨΦ hΦΨ hsU hsne hmaps ha
  -- Hölder bound: the Jacobian is constant on `s`, and `DΨ ∘ Φ` is the left inverse of `DΦ`.
  exact ⟨lam', Lam', _, hellip, holderOnWith_matrixBilinearForm_pullbackPrincipal (KJ := 0)
    (J := 1) hmaps hcomp hΦl hT (fun x hx => (hΨL x hx).trans (Real.le_coe_toNNReal L'))
    (fun x hx y hy => by simp only [habs x hx, habs y hy, edist_self, zero_le])
    (fun x hx => by rw [habs x hx, NNReal.coe_one]) hK
    fun y hy => (ha.opNorm_matrixBilinearForm_le hy).trans (Real.le_coe_toNNReal Lam)⟩

/-- **Ellipticity and Lipschitz bounds under mutually inverse changes of variables.** Let `Φ` and
`Ψ` be mutually inverse changes of variables, `Φ` of order one and `Ψ` of order two, with Jacobian
determinants at least one in absolute value, and let `Φ` map a nonempty subset `s` of a compact
convex subset of its domain into `t`. If `a` is uniformly elliptic and Lipschitz on `t`, the
pulled-back principal coefficient is uniformly elliptic and Lipschitz on `s`. -/
theorem exists_uniformlyEllipticOn_and_lipschitzOnWith_pullbackPrincipal [Nonempty ι]
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1)
    (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L' 1) (hΨΦ : LeftInvOn Ψ Φ U')
    (hΦΨ : RightInvOn Ψ Φ U) {B s t : Set (EuclideanSpace ℝ ι)} (hB : IsCompact B)
    (hBc : Convex ℝ B) (hBU : B ⊆ U') (hs : s ⊆ B) (hsne : s.Nonempty) (hmaps : MapsTo Φ s t)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {K : ℝ≥0}
    (ha : UniformlyEllipticOn t a lam Lam)
    (hK : LipschitzOnWith K (fun y => matrixBilinearForm (a y)) t) :
    ∃ (lam' Lam' : ℝ) (K' : ℝ≥0), UniformlyEllipticOn s (pullbackPrincipal Φ a) lam' Lam' ∧
      LipschitzOnWith K' (fun x => matrixBilinearForm (pullbackPrincipal Φ a x)) s := by
  -- `Φ` and `DΨ ∘ Φ` are `C¹` on `U'`, hence Lipschitz on the compact convex set `B`.
  obtain ⟨KΦ, hKΦ⟩ := (hΦ.contDiffOn.mono hBU).exists_lipschitzOnWith (by norm_num) hBc hB
  have hT : ContDiffOn ℝ 1 (fun x => fderiv ℝ Ψ (Φ x)) U' :=
    (hΨ.contDiffOn.fderiv_of_isOpen U.isOpen (by norm_num)).comp hΦ.contDiffOn hΦ.mapsTo
  obtain ⟨KT, hKT⟩ := (hT.mono hBU).exists_lipschitzOnWith one_ne_zero hBc hB
  obtain ⟨lam', Lam', K', hellip, hK'⟩ :=
    exists_uniformlyEllipticOn_and_holderOnWith_pullbackPrincipal hΦ (hΨ.mono one_le_two) hΨΦ hΦΨ
      (hs.trans hBU) hsne hmaps (hKΦ.mono hs) (hKT.mono hs).holderOnWith ha hK.holderOnWith
  exact ⟨lam', Lam', K', hellip, holderOnWith_one.1 hK'⟩

/-- **Smoothness of the transformed principal coefficient.** Let `Φ` and `Ψ` be mutually inverse
changes of variables of order one, with Jacobian determinants at least one in absolute value, and
let `Φ` map a subset `s` of its domain into `t`. If `Φ` is `Cⁿ` on `s`, `Ψ` is `Cⁿ⁺¹` on its
domain and the entries of `a` are `Cⁿ` on `t`, then the entries of the pulled-back principal
coefficient are `Cⁿ` on `s`. -/
theorem contDiffOn_pullbackPrincipal_apply (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1)
    (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L' 1) (hΨΦ : LeftInvOn Ψ Φ U')
    (hΦΨ : RightInvOn Ψ Φ U) {n : WithTop ℕ∞} {s t : Set (EuclideanSpace ℝ ι)} (hsU : s ⊆ U')
    (hmaps : MapsTo Φ s t) (hΦn : ContDiffOn ℝ n Φ s) (hΨn : ContDiffOn ℝ (n + 1) Ψ U)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (ha : ∀ k l, ContDiffOn ℝ n (fun y => a y k l) t)
    (i j : ι) : ContDiffOn ℝ n (fun x => pullbackPrincipal Φ a x i j) s := by
  -- The coordinates of `DΨ(Φ x) eₖ` are `Cⁿ` on `s`.
  have hT (m k : ι) : ContDiffOn ℝ n
      (fun x => (fderiv ℝ Ψ (Φ x) (EuclideanSpace.single k 1)).ofLp m) s :=
    (EuclideanSpace.proj (𝕜 := ℝ) m).contDiff.comp_contDiffOn
      (((hΨn.fderiv_of_isOpen U.isOpen le_rfl).comp hΦn fun x hx => hΦ.mapsTo (hsU hx)).clm_apply
        (contDiffOn_const (c := EuclideanSpace.single k 1)))
  -- Since `DΨ(Φ x)` is a left inverse of `DΦ(x)` and `|det DΦ(x)| = 1`, the entry `(i, j)` of
  -- `a'(x)` is `∑ₖₗ (DΨ(Φ x) eₖ)ᵢ aₖₗ(Φ x) (DΨ(Φ x) eₗ)ⱼ`.
  refine ContDiffOn.congr (f := fun x => ∑ k, ∑ l,
      (fderiv ℝ Ψ (Φ x) (EuclideanSpace.single k 1)).ofLp i * a (Φ x) k l *
        (fderiv ℝ Ψ (Φ x) (EuclideanSpace.single l 1)).ofLp j)
    (ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ =>
      ((hT i k).mul ((ha k l).comp hΦn hmaps)).mul (hT j l)) fun x hx => ?_
  rw [pullbackPrincipal_apply_apply_of_comp_eq_id a
    (hΦ.fderiv_comp_fderiv_eq_id hΨ hΨΦ hΦΨ (hsU hx)) i j,
    hΦ.abs_det_fderiv_eq_one hΨ hΨΦ hΦΨ (hsU hx), one_mul]

/-- **Restricting and transforming a weak solution.** Let `Φ` be a change of variables from `Ω'`
into an open `D ⊆ Ω`, with inverse change of variables `Ψ` from `D` into `Ω'`. If `u ∈ H¹(Ω)` is a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω` with `b, c ∈ L∞(Ω)` and
`f ∈ L²(Ω)`, then `u ∘ Φ` is a weak solution in `Ω'` of the transformed equation, whose
lower-order coefficients are bounded and whose right-hand side is in `L²(Ω')`. -/
theorem exists_forall_energyFormH1_compL_restrictL_eq
    {Omega D Ω' : Opens (EuclideanSpace ℝ ι)} {c₀ c₁ : ℝ} (hD : D ≤ Omega)
    (hΦ : Wkp.IsChangeOfVariables 1 Ω' D Φ L c₀) (hΨ : Wkp.IsChangeOfVariables 1 D Ω' Ψ L' c₁)
    (hΨΦ : LeftInvOn Ψ Φ Ω') (hΦΨ : RightInvOn Ψ Φ D) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    MemLp (pullbackDrift Φ b) ⊤ (mu.restrict Ω') ∧ MemLp (pullbackDensity Φ c) ⊤ (mu.restrict Ω') ∧
      ∃ f' : Lp ℝ 2 (mu.restrict Ω'), ∀ v : W1p0 mu Ω' 2,
        energyFormH1 (pullbackPrincipal Φ a) (pullbackDrift Φ b) (pullbackDensity Φ c)
          (hΦ.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hD u)) (v : W1p mu Ω' 2) =
          ∫ x in Ω', f' x * W1p.value (v : W1p mu Ω' 2) x ∂mu := by
  have hDΩ : (D : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hD
  have hf' := memLp_pullbackDensity hΦ.differentiableOn hΦ.injOn hΦ.mapsTo hΦ.norm_fderiv_le
    hΦ.pos hΦ.le_abs_det ((Lp.memLp f).mono_measure (Measure.restrict_mono_set mu hDΩ))
  refine ⟨memLp_pullbackDrift hΦ.differentiableOn hΦ.mapsTo hΦ.norm_fderiv_le hΦ.pos
      hΦ.le_abs_det hΨ.differentiableOn hΨ.norm_fderiv_le hΨΦ hΦΨ
      (hb.mono_measure (Measure.restrict_mono_set mu hDΩ)),
    memLp_pullbackDensity hΦ.differentiableOn hΦ.injOn hΦ.mapsTo hΦ.norm_fderiv_le hΦ.pos
      hΦ.le_abs_det (hc.mono_measure (Measure.restrict_mono_set mu hDΩ)),
    hf'.toLp _, fun v => ?_⟩
  rw [energyFormH1_compL_eq_setIntegral hΦ.differentiableOn hΦ.injOn hΦ.mapsTo
    hΦ.norm_fderiv_le hΦ.pos hΦ.le_abs_det hΨ.differentiableOn hΨ.mapsTo hΨ.norm_fderiv_le
    hΨ.pos hΨ.le_abs_det hΨΦ hΦΨ (energyFormH1_restrictL_eq_setIntegral hD hu) v]
  exact integral_congr_ae (hf'.coeFn_toLp.mono fun x hx => by simp only [hx])

/-- **Transforming a weak solution with an `H¹` right-hand side.** Let `Φ` be a change of variables
from `Ω'` into an open `D ⊆ Ω`, with inverse change of variables `Ψ`, both with Jacobian
determinants at least one in absolute value. If `u ∈ H¹(Ω)` is a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω` with `F ∈ H¹(Ω)`, then `u ∘ Φ` is a weak solution in `Ω'` of the
transformed equation `-∂ᵢ(a'ⁱʲ ∂ⱼ(u ∘ Φ)) = F ∘ Φ`, whose right-hand side lies in `H¹(Ω')`. -/
theorem energyFormH1_w1pCompL_restrictL_eq_setIntegral
    {Omega D Ω' : Opens (EuclideanSpace ℝ ι)} (hD : D ≤ Omega)
    (hΦ : Wkp.IsChangeOfVariables 1 Ω' D Φ L 1) (hΨ : Wkp.IsChangeOfVariables 1 D Ω' Ψ L' 1)
    (hΨΦ : LeftInvOn Ψ Φ Ω') (hΦΨ : RightInvOn Ψ Φ D) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {F u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (v : W1p0 mu Ω' 2) :
    energyFormH1 (pullbackPrincipal Φ a) 0 0
        (hΦ.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hD u)) (v : W1p mu Ω' 2) =
      ∫ x in Ω', W1p.value (hΦ.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hD F)) x *
        W1p.value (v : W1p mu Ω' 2) x ∂mu := by
  have h := energyFormH1_compL_eq_setIntegral hΦ.differentiableOn hΦ.injOn hΦ.mapsTo
    hΦ.norm_fderiv_le hΦ.pos hΦ.le_abs_det hΨ.differentiableOn hΨ.mapsTo hΨ.norm_fderiv_le
    hΨ.pos hΨ.le_abs_det hΨΦ hΦΨ (energyFormH1_restrictL_eq_setIntegral hD hu) v
  rw [pullbackDrift_zero, pullbackDensity_zero] at h
  -- Since `|det DΦ| = 1`, the pulled-back density of `F` is `F ∘ Φ`.
  refine h.trans (integral_congr_ae ?_)
  filter_upwards [hΦ.value_w1pCompL_ae ENNReal.ofNat_ne_top (W1p.restrictL hD F),
    hΦ.ae_comp (W1p.value_restrictL_ae hD F), ae_restrict_mem Ω'.isOpen.measurableSet]
    with x h1 h2 hx
  rw [pullbackDensity_apply, hΦ.abs_det_fderiv_eq_one hΨ hΨΦ hΦΨ hx, one_mul, h1, h2]

omit [DecidableEq ι] in
/-- **The `Lᵖ` norm of a pulled-back density.** For mutually inverse changes of variables of
order one with Jacobian determinants at least one in absolute value, the transformed density
`f' = |det DΦ| (f ∘ Φ)` has at most the `Lᵖ` norm of `f`. -/
theorem eLpNorm_pullbackDensity_le (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1)
    (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L' 1) (hΨΦ : LeftInvOn Ψ Φ U')
    (hΦΨ : RightInvOn Ψ Φ U) {q : ENNReal} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : AEStronglyMeasurable f (mu.restrict U)) :
    eLpNorm (pullbackDensity Φ f) q (mu.restrict U') ≤ eLpNorm f q (mu.restrict U) := by
  have hmap : (mu.restrict (U' : Set (EuclideanSpace ℝ ι))).map Φ ≤ mu.restrict U := by
    simpa using hΦ.map_restrict_le mu
  have heq : pullbackDensity Φ f =ᵐ[mu.restrict U'] f ∘ Φ := by
    filter_upwards [ae_restrict_mem U'.isOpen.measurableSet] with y hy
    rw [pullbackDensity_apply, hΦ.abs_det_fderiv_eq_one hΨ hΨΦ hΦΨ hy, one_mul,
      Function.comp_apply]
  rw [eLpNorm_congr_ae heq, ← eLpNorm_map_measure (hf.mono_measure hmap) hΦ.aemeasurable]
  exact eLpNorm_mono_measure f hmap

end Inverse

/-! ### Homotheties -/

section Homothety

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- Under the homothety `z ↦ ε z + c`, `ε > 0`, the transformed principal coefficient is the
coefficient at the image point, multiplied by `ε ^ card ι ε⁻²`. -/
theorem matrixBilinearForm_pullbackPrincipal_smul_add_const {ε : ℝ} (hε : 0 < ε)
    (c : EuclideanSpace ℝ ι) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) :
    matrixBilinearForm (pullbackPrincipal (fun z => ε • z + c) a z) =
      (ε ^ Fintype.card ι * (ε⁻¹ * ε⁻¹)) • matrixBilinearForm (a (ε • z + c)) := by
  have hT : (ε⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) ∘L
      fderiv ℝ (fun z : EuclideanSpace ℝ ι => ε • z + c) z =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) := by
    rw [fderiv_smul_add_const, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.id_comp, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  rw [matrixBilinearForm_pullbackPrincipal_eq_bilinearComp a hT,
    abs_det_fderiv_smul_add_const hε, finrank_euclideanSpace]
  ext η ξ
  simp [ContinuousLinearMap.adjoint_id, mul_assoc]

/-- Under the homothety `z ↦ ε z + c`, `ε > 0`, the energy form of the transformed principal
coefficient is `ε ^ card ι ε⁻²` times the energy form of the composed coefficient `a ∘ T`. -/
theorem energyFormH1_pullbackPrincipal_smul_add_const {ε : ℝ} (hε : 0 < ε)
    (c : EuclideanSpace ℝ ι) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    {U : Opens (EuclideanSpace ℝ ι)} (u v : W1p mu U 2) :
    energyFormH1 (pullbackPrincipal (fun z => ε • z + c) a) 0 0 u v =
      (ε ^ Fintype.card ι * (ε⁻¹ * ε⁻¹)) * energyFormH1 (fun z => a (ε • z + c)) 0 0 u v := by
  rw [energyFormH1_zero_zero_eq_setIntegral, energyFormH1_zero_zero_eq_setIntegral,
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  dsimp only
  rw [matrixBilinearForm_pullbackPrincipal_smul_add_const hε c a z, smul_apply, smul_apply,
    smul_eq_mul]

omit [DecidableEq ι] in
/-- **Rescaling a supersolution.** Let `u ∈ H¹(Ω)` be a weak supersolution of
`-div (a ∇u) ≥ 0` in `Ω`, and let the homothety `T z = ε z + c`, `ε > 0`, map an open set `U` into
`Ω`. Then `u ∘ T ∈ H¹(U)` is a weak supersolution of `-div ((a ∘ T) ∇v) ≥ 0` in `U`. -/
theorem exists_supersolution_comp_smul_add_const {Ω : Opens (EuclideanSpace ℝ ι)}
    {u : W1p mu Ω 2} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hu : ∀ v : W1p0 mu Ω 2, (∀ᵐ x ∂mu.restrict (Ω : Set (EuclideanSpace ℝ ι)),
      0 ≤ W1p.value (v : W1p mu Ω 2) x) → 0 ≤ energyFormH1 a 0 0 u (v : W1p mu Ω 2))
    {ε : ℝ} (hε : 0 < ε) (c : EuclideanSpace ℝ ι) (U : Opens (EuclideanSpace ℝ ι))
    (hUΩ : MapsTo (fun z => ε • z + c) U Ω) :
    ∃ uε : W1p mu U 2, W1p.value uε =ᵐ[mu.restrict (U : Set (EuclideanSpace ℝ ι))]
        (fun z => W1p.value u (ε • z + c)) ∧
      ∀ v : W1p0 mu U 2, (∀ᵐ z ∂mu.restrict (U : Set (EuclideanSpace ℝ ι)),
        0 ≤ W1p.value (v : W1p mu U 2) z) →
        0 ≤ energyFormH1 (fun z => a (ε • z + c)) 0 0 uε (v : W1p mu U 2) := by
  classical
  set V : Opens (EuclideanSpace ℝ ι) := ⟨(fun y => ε⁻¹ • y + -(ε⁻¹ • c)) ⁻¹' U,
      U.isOpen.preimage (by fun_prop)⟩
  have hST : ∀ z : EuclideanSpace ℝ ι, ε⁻¹ • (ε • z + c) + -(ε⁻¹ • c) = z := fun z => by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hε.ne', one_smul, add_neg_cancel_right]
  have hTS : ∀ y : EuclideanSpace ℝ ι, ε • (ε⁻¹ • y + -(ε⁻¹ • c)) + c = y := fun y => by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hε.ne', one_smul, smul_neg, smul_smul,
      mul_inv_cancel₀ hε.ne', one_smul, neg_add_cancel_right]
  -- Membership in the preimage `V` is membership of the image under the inverse homothety.
  have hT := Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε c (U := U) (V := V)
    (fun z hz => show ε⁻¹ • (ε • z + c) + -(ε⁻¹ • c) ∈ (U : Set (EuclideanSpace ℝ ι)) by
      rwa [hST z])
  have hS := Wkp.IsChangeOfVariables.smul_add_const (k := 1) (inv_pos.2 hε) (-(ε⁻¹ • c))
    (U := V) (V := U) (fun y hy => hy)
  have himage : (fun z => ε • z + c) '' U = V :=
    Subset.antisymm hT.mapsTo.image_subset fun y hy => ⟨_, hy, hTS y⟩
  have hVΩ : V ≤ Ω := fun y hy => hTS y ▸ hUΩ hy
  have hp : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  refine ⟨hT.w1pCompL hp (W1p.restrictL hVΩ u), ?_, fun v hv => ?_⟩
  · filter_upwards [hT.value_w1pCompL_ae hp (W1p.restrictL hVΩ u),
      hT.ae_comp (W1p.value_restrictL_ae hVΩ u)] with z h1 h2
    rw [h1, h2]
  · -- The test function `v ∘ T⁻¹` on `V` is nonnegative, vanishes on the boundary, and pulls
    -- back to `v`.
    set w := hS.w1pCompL hp (v : W1p mu U 2)
    have hw0 : w ∈ w1p0Submodule mu V 2 :=
      hS.w1pCompL_mem_w1p0Submodule_of_leftInvOn hp hT.differentiableOn.continuousOn hT.mapsTo
        (fun y _ => hTS y) v.property
    have hwpos : ∀ᵐ y ∂mu.restrict (V : Set (EuclideanSpace ℝ ι)), 0 ≤ W1p.value w y := by
      filter_upwards [hS.value_w1pCompL_ae hp (v : W1p mu U 2), hS.ae_comp hv] with y h1 h2
      rw [h1]
      exact h2
    have hvw : hT.w1pCompL hp w = v :=
      W1p.compL_compL_of_leftInvOn _ hp hT.differentiableOn hT.injOn hT.mapsTo hT.norm_fderiv_le
        hT.pos hT.le_abs_det hS.differentiableOn hS.injOn hS.mapsTo hS.norm_fderiv_le hS.pos
        hS.le_abs_det (fun z _ => hST z) _
    have h := energyFormH1_compL hT.differentiableOn hT.injOn hT.mapsTo hT.norm_fderiv_le hT.pos
      hT.le_abs_det himage a 0 0 (W1p.restrictL hVΩ u) w
    rw [pullbackDrift_zero, pullbackDensity_zero, hvw,
      energyFormH1_pullbackPrincipal_smul_add_const hε c a] at h
    have hnn := energyFormH1_restrictL_nonneg hVΩ hu ⟨w, hw0⟩ hwpos
    rw [← h] at hnn
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 hnn

end Homothety

end PDE

end TauCeti
