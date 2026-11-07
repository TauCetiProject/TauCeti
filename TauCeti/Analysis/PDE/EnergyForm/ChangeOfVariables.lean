/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import Mathlib.Analysis.CStarAlgebra.Matrix

import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Change of variables in divergence-form equations

Let `Φ` map an open set `U ⊆ ℝⁿ` injectively onto an open set `V`, with derivative `DΦ(x)` of
Jacobian matrix `M(x)` and Jacobian determinant `J(x) = |det DΦ(x)|`. A weak solution
`u ∈ H¹(V)` of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` in `V`

becomes, after the change of variables `ũ = u ∘ Φ`, a weak solution of an equation of the same
form in `U`,

`-∂ᵢ(ãⁱʲ ∂ⱼũ) + b̃ⁱ ∂ᵢũ + c̃ ũ = f̃` in `U`,

with the pulled-back coefficients

* `ã(x) = J(x) M(x)⁻¹ a(Φ x) M(x)⁻ᵀ` (`TauCeti.PDE.pullbackPrincipal`),
* `b̃(x) = J(x) M(x)⁻¹ b(Φ x)` (`TauCeti.PDE.pullbackDrift`),
* `c̃(x) = J(x) c(Φ x)` and `f̃(x) = J(x) f(Φ x)` (`TauCeti.PDE.pullbackDensity`).

The zeroth-order coefficient and the right-hand side transform as densities, because the
volume element changes by the factor `J`. The transformed principal coefficient is again
uniformly elliptic and bounded when `DΦ` and its inverse are bounded and `J` is bounded below
(`TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipal`).

This is the change of variables that flattens the boundary of a domain: if `Φ` maps a piece of a
half-space onto a neighbourhood of a boundary point of `Ω`, a weak solution in `Ω` becomes a weak
solution near a flat boundary portion, where regularity up to the boundary can be proved by
difference quotients in the tangential directions.

## The argument

The chain rule for weak gradients (`TauCeti.W1p.gradient_compL_ae`) gives
`∇ũ(x) = DΦ(x)* ∇u(Φ x)`, so `∇u(Φ x) = M(x)⁻ᵀ ∇ũ(x)` wherever `DΦ(x)` is invertible. Hence
`⟪a(Φ x) ∇u(Φ x), ∇w(Φ x)⟫ J(x) = ⟪ã(x) ∇ũ(x), ∇w̃(x)⟫`, and similarly for the lower-order terms
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
* `TauCeti.PDE.energyFormH1_compL_eq_setIntegral`: weak solutions are carried to weak solutions.
* `TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipal`: uniform ellipticity and boundedness are
  preserved, with explicit constants.

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

/-- The transformed principal coefficient `ã(x) = J(x) M(x)⁻¹ a(Φ x) M(x)⁻ᵀ` of a
divergence-form operator under the change of variables `Φ`, where `M(x)` is the Jacobian matrix
of `Φ` at `x` and `J(x) = |det DΦ(x)|`. -/
def pullbackPrincipal (Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  |(fderiv ℝ Φ x).det| •
    (((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ * a (Φ x) *
      ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹ᵀ)

/-- The transformed drift `b̃(x) = J(x) M(x)⁻¹ b(Φ x)` of a divergence-form operator under the
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

/-- **The transformed principal coefficient on pulled-back covectors.** Where `DΦ(x)` is
invertible, the bilinear form of `ã(x)` evaluated on `DΦ(x)* η` and `DΦ(x)* ξ` is
`|det DΦ(x)|` times the bilinear form of `a(Φ x)` evaluated on `η` and `ξ`. -/
theorem matrixBilinearForm_pullbackPrincipal {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) {x : EuclideanSpace ℝ ι}
    (hx : (fderiv ℝ Φ x).det ≠ 0) (η ξ : EuclideanSpace ℝ ι) :
    matrixBilinearForm (pullbackPrincipal Φ a x) ((fderiv ℝ Φ x).adjoint η)
        ((fderiv ℝ Φ x).adjoint ξ) =
      |(fderiv ℝ Φ x).det| * matrixBilinearForm (a (Φ x)) η ξ := by
  -- Write `DΦ(x)` as the map of its Jacobian matrix `M`, so that `DΦ(x)*` is the map of `Mᵀ`.
  obtain ⟨M, hMD⟩ : ∃ M, toEuclideanCLM (𝕜 := ℝ) M = fderiv ℝ Φ x :=
    ⟨_, StarAlgEquiv.apply_symm_apply _ _⟩
  rw [← hMD, det_toEuclideanCLM] at hx
  have hM := isUnit_iff_ne_zero.2 hx
  have h1 : M⁻¹ᵀ * Mᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hM, transpose_one]
  rw [pullbackPrincipal_apply, ← hMD, StarAlgEquiv.symm_apply_apply, adjoint_toEuclideanCLM,
    conjTranspose_eq_transpose_of_trivial, matrixBilinearForm_smul_apply, matrixBilinearForm_apply,
    matrixBilinearForm_apply, ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec_mulVec,
    Matrix.mul_assoc, h1, Matrix.mul_one, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc, mul_nonsing_inv _ hM, Matrix.one_mul]

/-- **The transformed drift on pulled-back covectors.** Where `DΦ(x)` is invertible,
`⟪b̃(x), DΦ(x)* ξ⟫ = |det DΦ(x)| ⟪b(Φ x), ξ⟫`. -/
theorem inner_pullbackDrift_adjoint {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {x : EuclideanSpace ℝ ι}
    (hx : (fderiv ℝ Φ x).det ≠ 0) (ξ : EuclideanSpace ℝ ι) :
    ⟪pullbackDrift Φ b x, (fderiv ℝ Φ x).adjoint ξ⟫_ℝ =
      |(fderiv ℝ Φ x).det| * ⟪b (Φ x), ξ⟫_ℝ := by
  obtain ⟨M, hMD⟩ : ∃ M, toEuclideanCLM (𝕜 := ℝ) M = fderiv ℝ Φ x :=
    ⟨_, StarAlgEquiv.apply_symm_apply _ _⟩
  rw [← hMD, det_toEuclideanCLM] at hx
  rw [pullbackDrift_apply, ← hMD, StarAlgEquiv.symm_apply_apply, adjoint_toEuclideanCLM,
    conjTranspose_eq_transpose_of_trivial, real_inner_smul_left,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, star_trivial, star_trivial, mulVec_transpose,
    ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hx), one_mulVec]

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

end Coefficients

/-! ### Uniform ellipticity of the transformed principal coefficient -/

section Ellipticity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι} {L L' : ℝ}

omit [DecidableEq ι] in
/-- If `D` is invertible with `‖v‖ ≤ L' ‖D v‖` for every `v`, then every `ξ` is `D* ζ` for some `ζ`
with `‖ζ‖ ≤ L' ‖ξ‖`. -/
private theorem exists_adjoint_eq_and_norm_le (hL' : ∀ v, ‖v‖ ≤ L' * ‖D v‖) (hL'0 : 0 ≤ L')
    (hD : D.det ≠ 0) (ξ : EuclideanSpace ℝ ι) : ∃ ζ, D.adjoint ζ = ξ ∧ ‖ζ‖ ≤ L' * ‖ξ‖ := by
  set e := D.toContinuousLinearEquivOfDetNeZero hD
  set E' := e.symm.toContinuousLinearMap
  have he : ∀ v, D (e.symm v) = v := fun v =>
    (D.toContinuousLinearEquivOfDetNeZero_apply hD _).symm.trans (e.apply_symm_apply v)
  have hE' : E'.comp D = ContinuousLinearMap.id ℝ _ := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, ← D.toContinuousLinearEquivOfDetNeZero_apply hD,
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, ContinuousLinearMap.id_apply]
  refine ⟨E'.adjoint ξ, ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp, hE',
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
  · refine (E'.adjoint.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [LinearIsometryEquiv.norm_map]
    refine E'.opNorm_le_bound hL'0 fun v => ?_
    simpa only [he, E', ContinuousLinearEquiv.coe_coe] using hL' (e.symm v)

omit [DecidableEq ι] in
/-- The bounds `‖DΦ‖ ≤ L` and `‖v‖ ≤ L' ‖DΦ(x) v‖` at a single point of a nonempty set force
`0 < L`, `0 ≤ L'` and `1 ≤ L L'`. -/
private theorem pos_and_nonneg_and_one_le_mul [Nonempty ι] {s : Set (EuclideanSpace ℝ ι)}
    (hs : s.Nonempty) (hL : ∀ x ∈ s, ‖fderiv ℝ Φ x‖ ≤ L)
    (hL' : ∀ x ∈ s, ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖) : 0 < L ∧ 0 ≤ L' ∧ 1 ≤ L * L' := by
  obtain ⟨x₀, hx₀⟩ := hs
  obtain ⟨v₀, hv₀⟩ := exists_norm_eq (EuclideanSpace ℝ ι) zero_le_one
  have h1 := hL' x₀ hx₀ v₀
  have hN := (fderiv ℝ Φ x₀).le_of_opNorm_le (hL x₀ hx₀) v₀
  rw [hv₀] at h1 hN
  rw [mul_one] at hN
  have hL'0 : 0 ≤ L' := by
    by_contra h
    nlinarith [norm_nonneg (fderiv ℝ Φ x₀ v₀)]
  have hLL' : 1 ≤ L * L' := by nlinarith [mul_le_mul_of_nonneg_left hN hL'0]
  refine ⟨lt_of_le_of_ne ((norm_nonneg _).trans (hL x₀ hx₀)) fun h => ?_, hL'0, hLL'⟩
  rw [← h, zero_mul] at hLL'
  linarith

/-- The lower ellipticity bound of the transformed principal coefficient at a point: if `a(Φ x)`
has lower constant `λ ≥ 0`, `‖DΦ(x)‖ ≤ L` and `c ≤ |det DΦ(x)|`, then `ã(x)` has lower constant
`c λ / L²`. -/
private theorem mul_norm_sq_le_toQuadraticForm'_pullbackPrincipal
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam c : ℝ} {x : EuclideanSpace ℝ ι}
    (ha : ∀ ζ : EuclideanSpace ℝ ι, lam * ‖ζ‖ ^ 2 ≤ (a (Φ x)).toQuadraticForm' ζ) (hlam : 0 ≤ lam)
    (hL0 : 0 < L) (hL : ‖fderiv ℝ Φ x‖ ≤ L) (hL' : ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖)
    (hL'0 : 0 ≤ L') (hc : 0 < c) (hdet : c ≤ |(fderiv ℝ Φ x).det|) (ξ : EuclideanSpace ℝ ι) :
    c * lam / L ^ 2 * ‖ξ‖ ^ 2 ≤ (pullbackPrincipal Φ a x).toQuadraticForm' ξ := by
  have hdet0 : (fderiv ℝ Φ x).det ≠ 0 := abs_pos.1 (hc.trans_le hdet)
  -- Write `ξ = DΦ(x)* ζ`; then `ξᵀ ã ξ = J ζᵀ a ζ ≥ c λ ‖ζ‖²` and `‖ξ‖ ≤ L ‖ζ‖`.
  obtain ⟨ζ, rfl, -⟩ := exists_adjoint_eq_and_norm_le hL' hL'0 hdet0 ξ
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
constant `Λ ≥ 0`, `‖DΦ(x)‖ ≤ L` and `‖v‖ ≤ L' ‖DΦ(x) v‖`, then `ã(x)` has upper constant
`Lⁿ L'² Λ`. -/
private theorem abs_matrixBilinearForm_pullbackPrincipal_le
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Lam : ℝ} {x : EuclideanSpace ℝ ι}
    (ha : ∀ η ξ : EuclideanSpace ℝ ι, |matrixBilinearForm (a (Φ x)) η ξ| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hLam : 0 ≤ Lam) (hL : ‖fderiv ℝ Φ x‖ ≤ L) (hL' : ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖)
    (hL'0 : 0 ≤ L') (hdet0 : (fderiv ℝ Φ x).det ≠ 0) (η ξ : EuclideanSpace ℝ ι) :
    |matrixBilinearForm (pullbackPrincipal Φ a x) η ξ| ≤
      L ^ Fintype.card ι * L' ^ 2 * Lam * ‖η‖ * ‖ξ‖ := by
  -- Write `η = DΦ(x)* ζ'` and `ξ = DΦ(x)* ζ`, with `‖ζ'‖ ≤ L' ‖η‖` and `‖ζ‖ ≤ L' ‖ξ‖`, and
  -- bound `|det DΦ(x)| ≤ ‖DΦ(x)‖ⁿ ≤ Lⁿ`.
  obtain ⟨ζ', rfl, hζ'⟩ := exists_adjoint_eq_and_norm_le hL' hL'0 hdet0 η
  obtain ⟨ζ, rfl, hζ⟩ := exists_adjoint_eq_and_norm_le hL' hL'0 hdet0 ξ
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
the transformed principal coefficient `ã` is uniformly elliptic and bounded on `s` with
constants `c λ / L²` and `Lⁿ L'² Λ`, where `n` is the dimension. -/
theorem UniformlyEllipticOn.pullbackPrincipal [Nonempty ι] {s t : Set (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ}
    (ha : UniformlyEllipticOn t a lam Lam) (hmaps : MapsTo Φ s t) (hs : s.Nonempty)
    (hL : ∀ x ∈ s, ‖fderiv ℝ Φ x‖ ≤ L) (hL' : ∀ x ∈ s, ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖)
    (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ Φ x).det|) :
    UniformlyEllipticOn s (PDE.pullbackPrincipal Φ a) (c * lam / L ^ 2)
      (L ^ Fintype.card ι * L' ^ 2 * Lam) := by
  obtain ⟨hlam, hlamLam, ha⟩ := uniformlyEllipticOn_iff.1 ha
  obtain ⟨hL0, hL'0, hLL'⟩ := pos_and_nonneg_and_one_le_mul hs hL hL'
  refine uniformlyEllipticOn_iff.2 ⟨by positivity, ?_, fun x hx => ⟨fun ξ => ?_, fun η ξ => ?_⟩⟩
  · -- `c λ / L² ≤ Lⁿ λ L'² ≤ Lⁿ L'² Λ`, using `c ≤ |det DΦ| ≤ Lⁿ` and `1 ≤ L L'`.
    obtain ⟨x₀, hx₀⟩ := hs
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

/-! ### The energy form and weak solutions under a change of variables -/

section WeakSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {U V : Opens (EuclideanSpace ℝ ι)} {p : ENNReal} [Fact (1 ≤ p)]
  {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L c₀ : ℝ}

omit [DecidableEq ι] in
/-- **Change of variables in a density integral against a Sobolev function.** If `Φ` maps `U`
onto `V`, then `∫_U f̃ (w ∘ Φ) = ∫_V f w` for every `w ∈ W^{1,p}(V)`, where
`f̃ = |det DΦ| (f ∘ Φ)` is the pulled-back density. -/
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

/-- **The energy form is invariant under a change of variables.** If `Φ` maps `U` onto `V`, the
energy form on `V` with coefficients `a`, `b`, `c` of two functions `u, w ∈ H¹(V)` equals the
energy form on `U` with the transformed coefficients `ã`, `b̃`, `c̃` of `u ∘ Φ` and `w ∘ Φ`. -/
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

/-- **Weak solutions are carried to weak solutions by a change of variables.** Let `Φ` map `U`
into `V` and `Ψ` map `V` into `U`, inverse to each other, both differentiable with bounded
derivative and Jacobian bounded below. If `u ∈ H¹(V)` is a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` in `V`, tested against `H¹₀(V)`, then `u ∘ Φ ∈ H¹(U)` is a weak
solution of `-∂ᵢ(ãⁱʲ ∂ⱼũ) + b̃ⁱ ∂ᵢũ + c̃ ũ = f̃` in `U`, tested against `H¹₀(U)`, with the
transformed coefficients and the pulled-back right-hand side `f̃ = |det DΦ| (f ∘ Φ)`. -/
theorem energyFormH1_compL_eq_setIntegral (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U)
    (hmaps : MapsTo Φ U V) (hL : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Φ x‖ ≤ L)
    (hc₀ : 0 < c₀) (hdet : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), c₀ ≤ |(fderiv ℝ Φ x).det|)
    {Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L' c' : ℝ} (hΨ : DifferentiableOn ℝ Ψ V)
    (hΨmaps : MapsTo Ψ V U) (hΨL : ∀ y ∈ (V : Set (EuclideanSpace ℝ ι)), ‖fderiv ℝ Ψ y‖ ≤ L')
    (hc' : 0 < c') (hΨdet : ∀ y ∈ (V : Set (EuclideanSpace ℝ ι)), c' ≤ |(fderiv ℝ Ψ y).det|)
    (hΨΦ : LeftInvOn Ψ Φ U) (hΦΨ : RightInvOn Ψ Φ V) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ}
    {u : W1p mu V 2}
    (hu : ∀ w : W1p0 mu V 2, energyFormH1 a b c u (w : W1p mu V 2) =
      ∫ y in V, f y * W1p.value (w : W1p mu V 2) y ∂mu)
    (φ : W1p0 mu U 2) :
    energyFormH1 (pullbackPrincipal Φ a) (pullbackDrift Φ b) (pullbackDensity Φ c)
        (W1p.compL Φ ENNReal.ofNat_ne_top hΦ hinj hmaps hL hc₀ hdet u) (φ : W1p mu U 2) =
      ∫ x in U, pullbackDensity Φ f x * W1p.value (φ : W1p mu U 2) x ∂mu := by
  have hp : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  have himage : Φ '' U = V :=
    Subset.antisymm hmaps.image_subset (hΦΨ.surjOn hΨmaps)
  -- The test function `φ` on `U` is `w ∘ Φ` for `w = φ ∘ Ψ ∈ H¹₀(V)`.
  set w := W1p.compL Ψ hp hΨ hΦΨ.injOn hΨmaps hΨL hc' hΨdet (φ : W1p mu U 2)
  have hw : w ∈ w1p0Submodule mu V 2 :=
    W1p.compL_mem_w1p0Submodule_of_leftInvOn Ψ hp hΨ hΦΨ.injOn hΨmaps hΨL hc'
      hΨdet hΦ.continuousOn hmaps hΦΨ φ.2
  have hφ : W1p.compL Φ hp hΦ hinj hmaps hL hc₀ hdet w = φ :=
    W1p.compL_compL_of_leftInvOn Φ hp hΦ hinj hmaps hL hc₀ hdet hΨ hΦΨ.injOn
      hΨmaps hΨL hc' hΨdet hΨΦ (φ : W1p mu U 2)
  rw [← hφ, energyFormH1_compL hΦ hinj hmaps hL hc₀ hdet himage,
    setIntegral_pullbackDensity_mul_value_compL hp hΦ hinj hmaps hL hc₀ hdet himage]
  exact hu ⟨w, hw⟩

end WeakSolution

end PDE

end TauCeti
