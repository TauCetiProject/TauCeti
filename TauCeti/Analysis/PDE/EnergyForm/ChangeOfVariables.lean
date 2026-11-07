/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Divergence-form equations under a change of variables

Let `Φ` map an open set `U ⊆ ℝⁿ` onto an open set `V ⊆ ℝⁿ`, with inverse `Ψ : V → U`, both
changes of variables of order one (`TauCeti.Wkp.IsChangeOfVariables`: differentiable, with bounded
derivative and Jacobian determinant bounded away from zero). Write `DΦ(y)` for the Jacobian matrix
of `Φ` at `y` and `J(y) = |det DΦ(y)|`. This file shows that the weak formulation of the
divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` in `V`

is carried by `v = u ∘ Φ` to the weak formulation of an equation of the same form in `U`, with the
coefficients

* `a_Φ(y) = J(y) DΦ(y)⁻¹ a(Φ y) DΦ(y)⁻ᵀ` (`TauCeti.PDE.pullbackPrincipalCoeff`);
* `b_Φ(y) = J(y) DΦ(y)⁻¹ b(Φ y)` (`TauCeti.PDE.pullbackDriftCoeff`);
* `c_Φ(y) = J(y) c(Φ y)` and `f_Φ(y) = J(y) f(Φ y)` (`TauCeti.PDE.pullbackDensity`).

Precisely, for `u ∈ H¹(V)` and `z ∈ H¹(U)` the energy forms agree,
`a_Φ(u ∘ Φ, z) = a(u, z ∘ Ψ)` (`TauCeti.PDE.energyFormH1_pullback_compL`), and so do the forcing
terms, `∫_U f_Φ z = ∫_V f (z ∘ Ψ)`. Since `z ↦ z ∘ Ψ` maps `H¹₀(U)` into `H¹₀(V)`, a weak solution
on `V` becomes a weak solution of the transported equation on `U`
(`TauCeti.PDE.energyFormH1_pullback_compL_eq_setIntegral`). Uniform ellipticity is preserved, with
constants controlled by the bounds on `DΦ`, `DΨ` and the Jacobians
(`TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipalCoeff`), and the transported lower-order
coefficients and forcing stay bounded, respectively square integrable.

Only the first derivatives of `Φ` and `Ψ` enter. Regularity of the transported coefficients beyond
measurability and boundedness, such as Lipschitz continuity of `a_Φ`, needs more derivatives of `Φ`
and is not treated here. Changes of variables of this kind are how boundary regularity is proved
for divergence-form equations on curved domains: flattening the boundary turns the equation near a
boundary point into one of the same type near a flat boundary portion, where the half-space theory
applies.

## The computation

By the chain rule `∇(u ∘ Φ)(y) = DΦ(y)ᵀ ∇u(Φ y)` and `∇(z ∘ Ψ)(Φ y) = DΦ(y)⁻ᵀ ∇z(y)`, since
`DΨ(Φ y) = DΦ(y)⁻¹`. Substituting `x = Φ y` in `∫_V ⟨a ∇u, ∇(z ∘ Ψ)⟩` gives
`∫_U J ⟨a(Φ y) DΦ⁻ᵀ ∇v, DΦ⁻ᵀ ∇z⟩ = ∫_U ⟨a_Φ ∇v, ∇z⟩`, and likewise for the lower-order terms
(`TauCeti.PDE.energyIntegrand_pullback` is the pointwise identity). The substitution is Mathlib's
change of variables formula `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`.

## Main declarations

* `TauCeti.PDE.pullbackPrincipalCoeff`, `TauCeti.PDE.pullbackDriftCoeff`,
  `TauCeti.PDE.pullbackDensity`: the transported coefficients.
* `TauCeti.PDE.energyFormH1_pullback_compL`: the energy forms agree.
* `TauCeti.PDE.setIntegral_pullbackDensity_mul_value`: the forcing terms agree.
* `TauCeti.PDE.energyFormH1_pullback_compL_eq_setIntegral`: weak solutions are transported to weak
  solutions.
* `TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipalCoeff`: uniform ellipticity of the transported
  principal coefficient.
* `TauCeti.PDE.memLp_pullbackDensity`, `TauCeti.PDE.memLp_top_pullbackDriftCoeff`: the
  transported forcing, mass and drift stay in `Lᵖ`, respectively `L^∞`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, proof of Theorem 4 (the
  transformed equation after flattening the boundary).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.4, proof of Theorem 8.12 (global regularity via a flattening of the boundary).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Matrix Filter
open scoped InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι]

/-! ### Pointwise linear algebra -/

section Pointwise

variable [DecidableEq ι]

/-- **The pointwise change of variables in the energy integrand.** Let `N` be a matrix whose
operator `S` is a right inverse of `T`, `T ∘ S = id`, and let `J` be a scalar. The energy integrand
with principal coefficient `J N A Nᵀ`, drift `J N b` and mass `J c`, evaluated at the jets
`(s, Tᵀ g)` and `(t, k)`, is `J` times the energy integrand of `(A, b, c)` at the jets `(s, g)` and
`(t, Sᵀ k)`.

At `T = DΦ(y)`, `N = DΦ(y)⁻¹` and `J = |det DΦ(y)|` this is the identity between the integrands of
the transported and the original energy form. -/
theorem energyIntegrand_pullback {T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {N : Matrix ι ι ℝ} (h : T ∘L toEuclideanCLM (𝕜 := ℝ) N = ContinuousLinearMap.id ℝ _)
    (A : Matrix ι ι ℝ) (b : EuclideanSpace ℝ ι) (c J s t : ℝ) (g k : EuclideanSpace ℝ ι) :
    energyIntegrand (J • (N * A * Nᵀ)) (J • toEuclideanCLM (𝕜 := ℝ) N b) (J * c)
        (s, ContinuousLinearMap.adjoint T g) (t, k) =
      J * energyIntegrand A b c (s, g)
        (t, ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) N) k) := by
  have hST : ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) N)
      (ContinuousLinearMap.adjoint T g) = g := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp, h,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
  have hTS : T (J • toEuclideanCLM (𝕜 := ℝ) N b) = J • b := by
    rw [map_smul, ← ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.id_apply]
  rw [energyIntegrand_apply, energyIntegrand_apply, matrixBilinearForm_smul_apply,
    matrixBilinearForm_mul_mul_transpose]
  simp only [hST, driftForm_apply, massForm_apply, ContinuousLinearMap.adjoint_inner_right, hTS,
    real_inner_smul_left]
  ring

end Pointwise

/-! ### The transported coefficients -/

section Coefficients

variable (Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)

section Matrix

variable [DecidableEq ι]

/-- The **principal coefficient transported along `Φ`**,
`a_Φ(y) = |det DΦ(y)| DΦ(y)⁻¹ a(Φ y) DΦ(y)⁻ᵀ`, where `DΦ(y)` is the Jacobian matrix of `Φ` at `y`.
If `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` weakly, then `u ∘ Φ` solves `-∂ᵢ((a_Φ)ⁱʲ ∂ⱼ(u ∘ Φ)) = 0` weakly
(`TauCeti.PDE.energyFormH1_pullback_compL_eq_setIntegral`). -/
def pullbackPrincipalCoeff (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (y : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  |(fderiv ℝ Φ y).det| • (((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ * a (Φ y) *
    (((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹)ᵀ)

/-- The **drift coefficient transported along `Φ`**, `b_Φ(y) = |det DΦ(y)| DΦ(y)⁻¹ b(Φ y)`. -/
def pullbackDriftCoeff (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  |(fderiv ℝ Φ y).det| •
    toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ (b (Φ y))

theorem pullbackPrincipalCoeff_def (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (y : EuclideanSpace ℝ ι) :
    pullbackPrincipalCoeff Φ a y =
      |(fderiv ℝ Φ y).det| • (((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ * a (Φ y) *
        (((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹)ᵀ) :=
  (rfl)

theorem pullbackDriftCoeff_def (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ ι) :
    pullbackDriftCoeff Φ b y = |(fderiv ℝ Φ y).det| •
      toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ (b (Φ y)) :=
  (rfl)

end Matrix

/-- A **scalar density transported along `Φ`**, `f_Φ(y) = |det DΦ(y)| f(Φ y)`. It is the transported
mass coefficient and the transported forcing term, and `∫_U f_Φ = ∫_{Φ(U)} f` when `Φ` is an
injective change of variables on `U`. -/
def pullbackDensity (f : EuclideanSpace ℝ ι → ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  |(fderiv ℝ Φ y).det| * f (Φ y)

omit [Fintype ι] in
@[simp]
theorem pullbackDensity_apply (f : EuclideanSpace ℝ ι → ℝ) (y : EuclideanSpace ℝ ι) :
    pullbackDensity Φ f y = |(fderiv ℝ Φ y).det| * f (Φ y) :=
  (rfl)

end Coefficients

/-! ### Transporting the weak formulation -/

section Transport

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {U V : Opens (EuclideanSpace ℝ ι)} {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {L L' κ κ' : ℝ}

/-- **The forcing term under a change of variables.** With `Φ`, `Ψ` as in
`TauCeti.PDE.energyFormH1_pullback_compL`, for every `f` and `z ∈ H¹(U)`,
`∫_U f_Φ z = ∫_V f (z ∘ Ψ)`, where `f_Φ = |det DΦ| (f ∘ Φ)`. -/
theorem setIntegral_pullbackDensity_mul_value (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (f : EuclideanSpace ℝ ι → ℝ) (z : W1p mu U 2) :
    ∫ y in U, pullbackDensity Φ f y * W1p.value z y ∂mu =
      ∫ x in V, f x * W1p.value (W1p.compL Ψ ENNReal.ofNat_ne_top hΨ.differentiableOn hΨ.injOn
        hΨ.mapsTo hΨ.norm_fderiv_le hΨ.pos hΨ.le_abs_det z) x ∂mu := by
  rw [hΦ.setIntegral_eq (hΦ.image_eq_of_rightInvOn hΨ.mapsTo hΦΨ)]
  refine integral_congr_ae ?_
  filter_upwards [hΦ.ae_comp (W1p.value_compL_ae Ψ ENNReal.ofNat_ne_top hΨ.differentiableOn
      hΨ.injOn hΨ.mapsTo hΨ.norm_fderiv_le hΨ.pos hΨ.le_abs_det z),
    ae_restrict_mem U.isOpen.measurableSet] with y hw hy
  rw [hw, hΨΦ hy, pullbackDensity_apply, smul_eq_mul, mul_assoc]

variable [DecidableEq ι]

/-- For a change of variables `Φ` from `U` onto `V` with inverse `Ψ`, the operator of the inverse
Jacobian matrix of `Φ` at `y ∈ U` is `DΨ(Φ y)`. -/
theorem toEuclideanCLM_inv_fderiv (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) {y : EuclideanSpace ℝ ι} (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) :
    toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ =
      fderiv ℝ Ψ (Φ y) := by
  rw [Matrix.inv_eq_right_inv (B := (toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Ψ (Φ y))),
    StarAlgEquiv.apply_symm_apply]
  rw [← map_mul, ContinuousLinearMap.mul_def,
    hΦ.fderiv_comp_fderiv_eq_id hΨ.differentiableOn hΦΨ hΨΦ hy,
    ← ContinuousLinearMap.one_def, map_one]

/-- **The energy form under a change of variables.** Let `Φ` be a change of variables of order one
from `U` onto `V` with inverse `Ψ`, itself a change of variables of order one. For `u ∈ H¹(V)` and
`z ∈ H¹(U)`, the energy form on `U` with the transported coefficients, evaluated at `u ∘ Φ` and `z`,
equals the energy form on `V` evaluated at `u` and `z ∘ Ψ`:

`a_Φ(u ∘ Φ, z) = a(u, z ∘ Ψ)`.

No integrability of the coefficients is needed: the two integrands correspond under the
substitution `x = Φ y`, integrable or not. -/
theorem energyFormH1_pullback_compL (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u : W1p mu V 2) (z : W1p mu U 2) :
    energyFormH1 (pullbackPrincipalCoeff Φ a) (pullbackDriftCoeff Φ b) (pullbackDensity Φ c)
        (W1p.compL Φ ENNReal.ofNat_ne_top hΦ.differentiableOn hΦ.injOn hΦ.mapsTo
          hΦ.norm_fderiv_le hΦ.pos hΦ.le_abs_det u) z =
      energyFormH1 a b c u
        (W1p.compL Ψ ENNReal.ofNat_ne_top hΨ.differentiableOn hΨ.injOn hΨ.mapsTo
          hΨ.norm_fderiv_le hΨ.pos hΨ.le_abs_det z) := by
  set v := W1p.compL Φ ENNReal.ofNat_ne_top hΦ.differentiableOn hΦ.injOn hΦ.mapsTo
    hΦ.norm_fderiv_le hΦ.pos hΦ.le_abs_det u
  set w := W1p.compL Ψ ENNReal.ofNat_ne_top hΨ.differentiableOn hΨ.injOn hΨ.mapsTo
    hΨ.norm_fderiv_le hΨ.pos hΨ.le_abs_det z
  rw [energyFormH1_def, energyFormH1_def,
    hΦ.setIntegral_eq (hΦ.image_eq_of_rightInvOn hΨ.mapsTo hΦΨ)]
  refine integral_congr_ae ?_
  -- The jets of `v = u ∘ Φ` on `U`, and those of `w = z ∘ Ψ` at `Φ y`, by the chain rule.
  filter_upwards [W1p.value_compL_ae Φ ENNReal.ofNat_ne_top hΦ.differentiableOn hΦ.injOn
      hΦ.mapsTo hΦ.norm_fderiv_le hΦ.pos hΦ.le_abs_det u,
    W1p.gradient_compL_ae Φ ENNReal.ofNat_ne_top hΦ.differentiableOn hΦ.injOn
      hΦ.mapsTo hΦ.norm_fderiv_le hΦ.pos hΦ.le_abs_det u,
    hΦ.ae_comp (W1p.value_compL_ae Ψ ENNReal.ofNat_ne_top hΨ.differentiableOn hΨ.injOn
      hΨ.mapsTo hΨ.norm_fderiv_le hΨ.pos hΨ.le_abs_det z),
    hΦ.ae_comp (W1p.gradient_compL_ae Ψ ENNReal.ofNat_ne_top hΨ.differentiableOn hΨ.injOn
      hΨ.mapsTo hΨ.norm_fderiv_le hΨ.pos hΨ.le_abs_det z),
    ae_restrict_mem U.isOpen.measurableSet] with y hv hgv hw hgw hy
  rw [jetField_apply, jetField_apply, jetField_apply, jetField_apply, hv, hgv, hw, hgw,
    hΨΦ hy]
  rw [smul_eq_mul, pullbackPrincipalCoeff_def, pullbackDriftCoeff_def, pullbackDensity_apply,
    ← toEuclideanCLM_inv_fderiv hΦ hΨ hΦΨ hΨΦ hy]
  refine energyIntegrand_pullback ?_ _ _ _ _ _ _ _ _
  rw [toEuclideanCLM_inv_fderiv hΦ hΨ hΦΨ hΨΦ hy,
    hΦ.fderiv_comp_fderiv_eq_id hΨ.differentiableOn hΦΨ hΨΦ hy]

/-- **Weak solutions under a change of variables.** Let `Φ` be a change of variables of order one
from `U` onto `V` with inverse `Ψ`, itself a change of variables of order one. If `u ∈ H¹(V)` is a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` in `V`, tested against `H¹₀(V)`, then
`u ∘ Φ ∈ H¹(U)` is a weak solution in `U` of the equation with the transported coefficients
`a_Φ`, `b_Φ`, `c_Φ` and forcing `f_Φ = |det DΦ| (f ∘ Φ)`, tested against `H¹₀(U)`. -/
theorem energyFormH1_pullback_compL_eq_setIntegral (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ}
    {u : W1p mu V 2}
    (hu : ∀ w : W1p0 mu V 2, energyFormH1 a b c u (w : W1p mu V 2) =
      ∫ x in V, f x * W1p.value (w : W1p mu V 2) x ∂mu)
    (z : W1p0 mu U 2) :
    energyFormH1 (pullbackPrincipalCoeff Φ a) (pullbackDriftCoeff Φ b) (pullbackDensity Φ c)
        (W1p.compL Φ ENNReal.ofNat_ne_top hΦ.differentiableOn hΦ.injOn hΦ.mapsTo
          hΦ.norm_fderiv_le hΦ.pos hΦ.le_abs_det u) (z : W1p mu U 2) =
      ∫ y in U, pullbackDensity Φ f y * W1p.value (z : W1p mu U 2) y ∂mu := by
  have hz := W1p.compL_mem_w1p0Submodule_of_leftInvOn Ψ ENNReal.ofNat_ne_top hΨ.differentiableOn
    hΨ.injOn hΨ.mapsTo hΨ.norm_fderiv_le hΨ.pos hΨ.le_abs_det hΦ.differentiableOn.continuousOn
    hΦ.mapsTo hΦΨ z.2
  rw [energyFormH1_pullback_compL hΦ hΨ hΦΨ hΨΦ,
    setIntegral_pullbackDensity_mul_value hΦ hΨ hΦΨ hΨΦ]
  exact hu ⟨_, hz⟩


/-! ### Ellipticity and bounds of the transported coefficients -/

/-- The bilinear form of the transported principal coefficient at `y ∈ U` is
`|det DΦ(y)|` times the bilinear form of `a(Φ y)` evaluated at `DΨ(Φ y)ᵀ η` and `DΨ(Φ y)ᵀ ξ`. -/
theorem matrixBilinearForm_pullbackPrincipalCoeff (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) (η ξ : EuclideanSpace ℝ ι) :
    matrixBilinearForm (pullbackPrincipalCoeff Φ a y) η ξ =
      |(fderiv ℝ Φ y).det| * matrixBilinearForm (a (Φ y))
        (ContinuousLinearMap.adjoint (fderiv ℝ Ψ (Φ y)) η)
        (ContinuousLinearMap.adjoint (fderiv ℝ Ψ (Φ y)) ξ) := by
  rw [pullbackPrincipalCoeff_def, matrixBilinearForm_smul_apply,
    matrixBilinearForm_mul_mul_transpose, toEuclideanCLM_inv_fderiv hΦ hΨ hΦΨ hΨΦ hy]

/-- The transported drift at `y ∈ U` is `|det DΦ(y)| DΨ(Φ y) b(Φ y)`. -/
theorem pullbackDriftCoeff_eq (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    {y : EuclideanSpace ℝ ι} (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) :
    pullbackDriftCoeff Φ b y = |(fderiv ℝ Φ y).det| • fderiv ℝ Ψ (Φ y) (b (Φ y)) := by
  rw [pullbackDriftCoeff_def, toEuclideanCLM_inv_fderiv hΦ hΨ hΦΨ hΨΦ hy]

/-- The lower ellipticity bound of the transported principal coefficient at `y ∈ U`:
`κ λ / L² ‖ξ‖² ≤ ξᵀ a_Φ(y) ξ`, since `‖ξ‖ ≤ L ‖DΨ(Φ y)ᵀ ξ‖` and `κ ≤ |det DΦ(y)|`. -/
private theorem pullbackPrincipalCoeff_lower_bound {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {lam Lam : ℝ} (ha : UniformlyEllipticOn (V : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ) (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ')
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U) (hL : 0 < L) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) (ξ : EuclideanSpace ℝ ι) :
    κ * lam / L ^ 2 * ‖ξ‖ ^ 2 ≤ (pullbackPrincipalCoeff Φ a y).toQuadraticForm' ξ := by
  set S := ContinuousLinearMap.adjoint (fderiv ℝ Ψ (Φ y))
  -- `ξ = DΦ(y)ᵀ DΨ(Φ y)ᵀ ξ`, because `DΨ(Φ y) ∘ DΦ(y) = id`.
  have hξ : ‖ξ‖ ≤ L * ‖S ξ‖ := by
    have hST : fderiv ℝ Ψ (Φ y) ∘L fderiv ℝ Φ y = ContinuousLinearMap.id ℝ _ := by
      have h := hΨ.fderiv_comp_fderiv_eq_id hΦ.differentiableOn hΨΦ hΦΨ (hΦ.mapsTo hy)
      rwa [hΨΦ hy] at h
    have h : ContinuousLinearMap.adjoint (fderiv ℝ Φ y) (S ξ) = ξ := by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp, hST,
        ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
    calc ‖ξ‖ = ‖ContinuousLinearMap.adjoint (fderiv ℝ Φ y) (S ξ)‖ := by rw [h]
      _ ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ Φ y)‖ * ‖S ξ‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖S ξ‖ := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul_of_nonneg_right (hΦ.norm_fderiv_le y hy) (norm_nonneg _)
  rw [← matrixBilinearForm_self, matrixBilinearForm_pullbackPrincipalCoeff hΦ hΨ hΦΨ hΨΦ a hy,
    matrixBilinearForm_self]
  have hsq : ‖ξ‖ ^ 2 / L ^ 2 ≤ ‖S ξ‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg ξ, norm_nonneg (S ξ)]
  calc κ * lam / L ^ 2 * ‖ξ‖ ^ 2 = κ * (lam * (‖ξ‖ ^ 2 / L ^ 2)) := by ring
    _ ≤ |(fderiv ℝ Φ y).det| * (lam * ‖S ξ‖ ^ 2) :=
      mul_le_mul (hΦ.le_abs_det y hy) (mul_le_mul_of_nonneg_left hsq ha.pos.le)
        (by have := ha.pos; positivity) (abs_nonneg _)
    _ ≤ |(fderiv ℝ Φ y).det| * (a (Φ y)).toQuadraticForm' (S ξ) :=
      mul_le_mul_of_nonneg_left (ha.lower_bound (hΦ.mapsTo hy) (S ξ)) (abs_nonneg _)

/-- The upper bound of the transported principal coefficient at `y ∈ U`:
`|ηᵀ a_Φ(y) ξ| ≤ Λ L'² / κ' ‖η‖ ‖ξ‖`, since `‖DΨ(Φ y)‖ ≤ L'` and `|det DΦ(y)| ≤ 1 / κ'`. -/
private theorem pullbackPrincipalCoeff_upper_bound {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {lam Lam : ℝ} (ha : UniformlyEllipticOn (V : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ) (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ')
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) (η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ (pullbackPrincipalCoeff Φ a y *ᵥ ξ)| ≤ Lam * L' ^ 2 / κ' * ‖η‖ * ‖ξ‖ := by
  set S := ContinuousLinearMap.adjoint (fderiv ℝ Ψ (Φ y))
  have hS : ‖S‖ ≤ L' := by
    rw [LinearIsometryEquiv.norm_map]
    exact hΨ.norm_fderiv_le _ (hΦ.mapsTo hy)
  rw [← matrixBilinearForm_apply, matrixBilinearForm_pullbackPrincipalCoeff hΦ hΨ hΦΨ hΨΦ a hy,
    abs_mul, abs_abs, matrixBilinearForm_apply]
  have hη : ‖S η‖ ≤ L' * ‖η‖ :=
    (S.le_opNorm η).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have hξ : ‖S ξ‖ ≤ L' * ‖ξ‖ :=
    (S.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have hκ' := inv_nonneg.2 hΨ.pos.le
  calc |(fderiv ℝ Φ y).det| * |S η ⬝ᵥ (a (Φ y) *ᵥ S ξ)|
      ≤ κ'⁻¹ * (Lam * ‖S η‖ * ‖S ξ‖) :=
        mul_le_mul (hΦ.abs_det_le_inv hΨ hΦΨ hΨΦ hy) (ha.upper_bound (hΦ.mapsTo hy) (S η) (S ξ))
          (abs_nonneg _) hκ'
    _ ≤ κ'⁻¹ * (Lam * (L' * ‖η‖) * (L' * ‖ξ‖)) := by
        have := ha.upper_nonneg
        have := (norm_nonneg _).trans hS
        gcongr
    _ = Lam * L' ^ 2 / κ' * ‖η‖ * ‖ξ‖ := by ring

/-- **Uniform ellipticity is preserved by a change of variables.** Let `Φ` be a change of variables
of order one from a nonempty `U` onto `V`, with constants `L`, `κ` and inverse `Ψ`, a change of
variables of order one with constants `L'`, `κ'`. If `a` is uniformly elliptic on `V` with
constants `λ ≤ Λ`, then the transported principal coefficient is uniformly elliptic on `U` with
constants `κ λ / L²` and `Λ L'² / κ'`. -/
theorem UniformlyEllipticOn.pullbackPrincipalCoeff [Nonempty ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (V : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ) (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ')
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hU : (U : Set (EuclideanSpace ℝ ι)).Nonempty) :
    UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) (pullbackPrincipalCoeff Φ a)
      (κ * lam / L ^ 2) (Lam * L' ^ 2 / κ') := by
  -- `1 ≤ ‖DΦ(y)‖ ‖DΨ(Φ y)‖ ≤ L L'` at any point `y ∈ U`, because `DΦ(y) ∘ DΨ(Φ y) = id`.
  obtain ⟨y₀, hy₀⟩ := hU
  have hLL' : 1 ≤ L * L' := by
    have h := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ Φ y₀) (fderiv ℝ Ψ (Φ y₀))
    rw [hΦ.fderiv_comp_fderiv_eq_id hΨ.differentiableOn hΦΨ hΨΦ hy₀,
      ContinuousLinearMap.norm_id] at h
    exact h.trans (mul_le_mul (hΦ.norm_fderiv_le y₀ hy₀) (hΨ.norm_fderiv_le _ (hΦ.mapsTo hy₀))
      (norm_nonneg _) ((norm_nonneg _).trans (hΦ.norm_fderiv_le y₀ hy₀)))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hΦ.norm_fderiv_le y₀ hy₀)
  have hL : 0 < L := lt_of_le_of_ne hL0 fun h => by rw [← h, zero_mul] at hLL'; linarith
  have hκκ' : κ ≤ κ'⁻¹ :=
    (hΦ.le_abs_det y₀ hy₀).trans (hΦ.abs_det_le_inv hΨ hΦΨ hΨΦ hy₀)
  refine UniformlyEllipticOn.of_bounds (by have := ha.pos; have := hΦ.pos; positivity) ?_
    (fun y hy ξ => pullbackPrincipalCoeff_lower_bound ha hΦ hΨ hΦΨ hΨΦ hL hy ξ)
    (fun y hy η ξ => pullbackPrincipalCoeff_upper_bound ha hΦ hΨ hΦΨ hΨΦ hy η ξ)
  -- `κ λ / L² ≤ λ κ'⁻¹ L'² ≤ Λ L'² / κ'`, since `κ ≤ κ'⁻¹` and `1 ≤ (L L')²`.
  have hκ' := hΨ.pos
  rw [div_le_div_iff₀ (by positivity) hκ']
  have h1 : κ * κ' ≤ 1 :=
    (mul_le_mul_of_nonneg_right hκκ' hκ'.le).trans (inv_mul_cancel₀ hκ'.ne').le
  calc κ * lam * κ' = κ * κ' * lam := by ring
    _ ≤ 1 * lam := mul_le_mul_of_nonneg_right h1 ha.pos.le
    _ ≤ (L * L') ^ 2 * Lam := mul_le_mul (one_le_pow₀ hLL') ha.le ha.pos.le (by positivity)
    _ = Lam * L' ^ 2 * L ^ 2 := by ring

/-- The transported drift is bounded: if `‖b‖ ≤ β` at `Φ y`, then `‖b_Φ(y)‖ ≤ L' β / κ'`. -/
theorem norm_pullbackDriftCoeff_le (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {β : ℝ}
    {y : EuclideanSpace ℝ ι} (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) (hb : ‖b (Φ y)‖ ≤ β) :
    ‖pullbackDriftCoeff Φ b y‖ ≤ L' * β / κ' := by
  rw [pullbackDriftCoeff_eq hΦ hΨ hΦΨ hΨΦ b hy, norm_smul, Real.norm_eq_abs, abs_abs]
  have hS := hΨ.norm_fderiv_le _ (hΦ.mapsTo hy)
  have hJ := hΦ.abs_det_le_inv hΨ hΦΨ hΨΦ hy
  have hβ : 0 ≤ β := (norm_nonneg _).trans hb
  calc |(fderiv ℝ Φ y).det| * ‖fderiv ℝ Ψ (Φ y) (b (Φ y))‖
      ≤ κ'⁻¹ * (L' * β) :=
        mul_le_mul hJ (((fderiv ℝ Ψ (Φ y)).le_opNorm _).trans
          (mul_le_mul hS hb (norm_nonneg _) ((norm_nonneg _).trans hS)))
          (norm_nonneg _) (inv_nonneg.2 hΨ.pos.le)
    _ = L' * β / κ' := by ring

omit [DecidableEq ι] in
/-- **Transported densities stay in `Lᵖ`.** If `f ∈ Lᵖ(V)`, then
`f_Φ = |det DΦ| (f ∘ Φ) ∈ Lᵖ(U)`. With `p = 2` this is the transported forcing term, and with
`p = ∞` the transported mass coefficient. -/
theorem memLp_pullbackDensity (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) {p : ENNReal} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : MemLp f p (mu.restrict V)) : MemLp (pullbackDensity Φ f) p (mu.restrict U) := by
  have hfΦ := hΦ.memLp_comp hf
  have hJ : AEStronglyMeasurable (fun y => |(fderiv ℝ Φ y).det|) (mu.restrict U) :=
    (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ Φ))).aestronglyMeasurable
  refine hfΦ.of_le_mul (c := κ'⁻¹) (hJ.mul hfΦ.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with y hy
  rw [pullbackDensity_apply, norm_mul, Real.norm_eq_abs, abs_abs, Function.comp_apply]
  exact mul_le_mul_of_nonneg_right (hΦ.abs_det_le_inv hΨ hΦΨ hΨΦ hy) (norm_nonneg _)

/-- **The transported drift stays essentially bounded.** If `b ∈ L^∞(V)`, then the transported
drift `b_Φ ∈ L^∞(U)`. -/
theorem memLp_top_pullbackDriftCoeff (hΦ : Wkp.IsChangeOfVariables 1 U V Φ L κ)
    (hΨ : Wkp.IsChangeOfVariables 1 V U Ψ L' κ') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hb : MemLp b ⊤ (mu.restrict V)) : MemLp (pullbackDriftCoeff Φ b) ⊤ (mu.restrict U) := by
  have hbΦ := hΦ.memLp_comp hb
  have hJ : AEStronglyMeasurable (fun y => |(fderiv ℝ Φ y).det|) (mu.restrict U) :=
    (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ Φ))).aestronglyMeasurable
  -- On `U` the transported drift is `|det DΦ| DΨ(Φ ·) (b ∘ Φ)`, which is measurable.
  have hmeas : AEStronglyMeasurable (fun y => |(fderiv ℝ Φ y).det| • fderiv ℝ Ψ (Φ y) (b (Φ y)))
      (mu.restrict U) :=
    hJ.smul
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ ι)).aestronglyMeasurable_comp₂
        hbΦ.aestronglyMeasurable
        ((measurable_fderiv ℝ Ψ).comp_aemeasurable hΦ.aemeasurable).aestronglyMeasurable)
  refine hbΦ.of_le_mul (c := L' / κ') (hmeas.congr ?_) ?_
  · filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with y hy
    exact (pullbackDriftCoeff_eq hΦ hΨ hΦΨ hΨΦ b hy).symm
  · filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with y hy
    rw [Function.comp_apply, div_mul_eq_mul_div]
    exact norm_pullbackDriftCoeff_le hΦ hΨ hΦΨ hΨΦ hy le_rfl

end Transport

end PDE

end TauCeti
