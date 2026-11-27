/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.Euclidean

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Examples: the second fundamental form of the unit cylinder

The unit cylinder `{x₀² + x₁² = 1} ⊆ ℝ³` is the image of the map
`cyl : ℝ² → ℝ³, (θ, z) ↦ (cos θ, sin θ, z)`, which preserves inner products of tangent vectors:
`d cyl (v) = v₀ τ + v₁ e₂` with `τ = (-sin θ, cos θ, 0)` and `e₂` orthonormal. So `cyl` is a local
isometry from the flat plane onto the cylinder with its induced metric, and its second fundamental
form, shape operator, principal curvatures and mean curvature vector at `(θ, z)` are those of the
cylinder at `cyl (θ, z)`. With the outward unit normal `ν = (cos θ, sin θ, 0)`, `e_θ = (1, 0)` and
`e_z = (0, 1)`:

* `B(v, w) = -v₀ w₀ ν`, so `B(e_θ, e_θ) = -ν` and `B(e_z, e_z) = 0`
  (`TauCeti.CylinderCheck.immersionSecondFundamentalFormAt_cyl`,
  `TauCeti.CylinderCheck.immersionSecondFundamentalFormAt_cyl_eθ`,
  `TauCeti.CylinderCheck.immersionSecondFundamentalFormAt_cyl_ez`). The two diagonal values
  differ, so the model `B = -g ν` of the sphere does not hold for every immersion.
* `S_ν v = -v₀ e_θ`, so `S_ν e_θ = -e_θ` and `S_ν e_z = 0`
  (`TauCeti.CylinderCheck.immersionShapeOperatorAt_cyl_apply`), and the principal curvatures in
  the outward direction are `0, -1` in decreasing order, with the eigenvalue `0` counted
  (`TauCeti.CylinderCheck.immersionPrincipalCurvatures_cyl`). Their product, the Gauss curvature,
  is `(-1) · 0 = 0`, while the unit sphere gives `(-1) · (-1) = 1`. In the inward direction `-ν`
  they are `1, 0` (`TauCeti.CylinderCheck.immersionPrincipalCurvatures_cyl_neg`).
* `tr B = -ν` and `H = -ν / 2`
  (`TauCeti.CylinderCheck.immersionMeanCurvatureVector_cyl`); `H` does not involve a choice of
  normal, and reversing `ν` reverses the signs of both principal curvatures and of `ν`.

These are the cylinder Checks of the RiemannianGeometry roadmap, R5a and R5a.2.
-/

public section

noncomputable section

open Bundle Manifold Module Real
open scoped InnerProductSpace Manifold ContDiff

namespace TauCeti.CylinderCheck

open TauCeti.Manifold CovariantDerivative

/-- The Euclidean plane, with coordinates `(θ, z)`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
/-- Euclidean three-space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
/-- The coordinate `θ` of the plane. -/
local notation "π₀" => (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
/-- The coordinate `z` of the plane. -/
local notation "π₁" => (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

/-- The standard basis vectors of `ℝ³`. -/
abbrev e (i : Fin 3) : ℝ³ := EuclideanSpace.single i 1

/-- The coordinate vector `e_θ` of the plane. -/
abbrev eθ : ℝ² := EuclideanSpace.single 0 1

/-- The coordinate vector `e_z` of the plane. -/
abbrev ez : ℝ² := EuclideanSpace.single 1 1

/-- The parametrization `(θ, z) ↦ (cos θ, sin θ, z)` of the unit cylinder. -/
def cyl (y : ℝ²) : ℝ³ := cos (y 0) • e 0 + sin (y 0) • e 1 + y 1 • e 2

/-- The outward unit normal `(cos θ, sin θ, 0)` of the cylinder. -/
def ν (y : ℝ²) : ℝ³ := cos (y 0) • e 0 + sin (y 0) • e 1

/-- The unit tangent vector `(-sin θ, cos θ, 0)` of the cylinder in the direction of `θ`. -/
def τ (y : ℝ²) : ℝ³ := -sin (y 0) • e 0 + cos (y 0) • e 1

/-- The derivative of `ν` is `(π₀ ·) • τ`. -/
theorem hasFDerivAt_ν (y : ℝ²) : HasFDerivAt ν ((π₀).smulRight (τ y)) y := by
  have hfun : ν = fun y ↦ cos (π₀ y) • e 0 + sin (π₀ y) • e 1 := by
    funext y
    simp [ν]
  have hc := ((π₀).hasFDerivAt (x := y)).cos.smul_const (e 0)
  have hs := ((π₀).hasFDerivAt (x := y)).sin.smul_const (e 1)
  rw [hfun]
  refine (hc.add hs).congr_fderiv ?_
  ext1 v
  simp [τ, smul_smul, mul_comm]

/-- The derivative of `τ` is `-(π₀ ·) • ν`. -/
theorem hasFDerivAt_τ (y : ℝ²) : HasFDerivAt τ ((π₀).smulRight (-ν y)) y := by
  have hfun : τ = fun y ↦ -sin (π₀ y) • e 0 + cos (π₀ y) • e 1 := by
    funext y
    simp [τ]
  have hc := (((π₀).hasFDerivAt (x := y)).sin.neg).smul_const (e 0)
  have hs := ((π₀).hasFDerivAt (x := y)).cos.smul_const (e 1)
  rw [hfun]
  refine (hc.add hs).congr_fderiv ?_
  ext1 v
  simp [ν, smul_smul, mul_comm]
  abel

/-- The derivative of the parametrization is `w ↦ w₀ τ + w₁ e₂`. -/
theorem hasFDerivAt_cyl (y : ℝ²) :
    HasFDerivAt cyl ((π₀).smulRight (τ y) + (π₁).smulRight (e 2)) y := by
  have hfun : cyl = fun y ↦ ν y + π₁ y • e 2 := by
    funext y
    simp [cyl, ν]
  rw [hfun]
  exact (hasFDerivAt_ν y).add ((π₁).hasFDerivAt.smul_const (e 2))

/-- The parametrization is `C²`. -/
theorem contDiff_cyl : ContDiff ℝ 2 cyl := by
  have hfun : cyl = fun y ↦ cos (π₀ y) • e 0 + sin (π₀ y) • e 1 + π₁ y • e 2 := by
    funext y
    simp [cyl]
  rw [hfun]
  fun_prop

/-- The differential of the parametrization: `d cyl (w) = w₀ τ + w₁ e₂`. -/
theorem mfderiv_cyl (y w : ℝ²) :
    mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) cyl y w = w 0 • τ y + w 1 • e 2 := by
  rw [(hasFDerivAt_cyl y).hasMFDerivAt.mfderiv]
  rfl

/-- `τ` and `ν` are orthogonal. -/
theorem inner_τ_ν (y : ℝ²) : ⟪τ y, ν y⟫_ℝ = 0 := by
  simp only [τ, ν, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

/-- `ν` is a unit vector. -/
theorem inner_ν_ν (y : ℝ²) : ⟪ν y, ν y⟫_ℝ = 1 := by
  simp only [ν, PiLp.inner_apply, Fin.sum_univ_three]
  simp

/-- `e₂` and `ν` are orthogonal. -/
theorem inner_e₂_ν (y : ℝ²) : ⟪e 2, ν y⟫_ℝ = 0 := by
  simp only [ν, PiLp.inner_apply, Fin.sum_univ_three]
  simp

/-- The outward normal `ν` is orthogonal to the image of the differential. -/
theorem inner_mfderiv_cyl_ν (y u : ℝ²) :
    ⟪(mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) cyl y u : ℝ³), ν y⟫_ℝ = 0 := by
  have h : ⟪u 0 • τ y + u 1 • e 2, ν y⟫_ℝ = 0 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_τ_ν, inner_e₂_ν,
      mul_zero, mul_zero, add_zero]
  exact (congrArg (fun z : ℝ³ ↦ ⟪z, ν y⟫_ℝ) (mfderiv_cyl y u)).trans h

/-- The outward normal `ν` is normal to the cylinder. -/
theorem ν_mem_orthogonalNormalSpace (y : ℝ²) :
    (ν y : TangentSpace 𝓘(ℝ, ℝ³) (cyl y)) ∈ orthogonalNormalSpace 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) cyl y := by
  rw [orthogonalNormalSpace_def]
  refine (Submodule.mem_orthogonal
    (LinearMap.range (mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) cyl y).toLinearMap) _).2 ?_
  rintro _ ⟨u, rfl⟩
  exact inner_mfderiv_cyl_ν y u

/-- **The second fundamental form of the unit cylinder**: `B(v, w) = -v₀ w₀ ν`. -/
theorem immersionSecondFundamentalFormAt_cyl (x v w : ℝ²) :
    immersionSecondFundamentalFormAt (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x
      v w = -(v 0 * w 0) • ν x := by
  have hf : ContMDiffAt 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) 2 cyl x := contDiff_cyl.contMDiff x
  have hc (u : ℝ²) : MDifferentiableAt 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ²).tangent
      (fun z ↦ (⟨z, u⟩ : TangentBundle 𝓘(ℝ, ℝ²) ℝ²)) x :=
    ((contMDiff_tangentBundle_mk_const u (n := 1)).mdifferentiable one_ne_zero) x
  have hY : (fun y ↦ (mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) cyl y w : ℝ³)) =
      fun y ↦ w 0 • τ y + w 1 • e 2 :=
    funext fun y ↦ mfderiv_cyl y w
  have hD : HasFDerivAt (fun y ↦ w 0 • τ y + w 1 • e 2) (w 0 • (π₀).smulRight (-ν x)) x :=
    ((hasFDerivAt_τ x).const_smul (w 0)).add_const _
  have hdY : MDifferentiableAt 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³)
      (fun y ↦ (mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) cyl y w : ℝ³)) x := by
    rw [hY]
    exact hD.differentiableAt.mdifferentiableAt
  have hval : mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) (fun y ↦ (mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ³) cyl y w : ℝ³)) x v =
      -(v 0 * w 0) • ν x := by
    rw [hY, hD.hasMFDerivAt.mfderiv]
    change w 0 • (v 0 • -ν x) = -(v 0 * w 0) • ν x
    module
  rw [immersionSecondFundamentalFormAt_apply (X := fun _ ↦ v) (Y := fun _ ↦ w) hf (hc v) (hc w),
    immersionSecondFundamentalForm_model_space (I := 𝓘(ℝ, ℝ²)) (X := fun _ ↦ v)
      (Y := fun _ ↦ w) (hf.mdifferentiableAt (by norm_num)) hdY, hval]
  exact (Submodule.starProjection_eq_self_iff).2
    (Submodule.smul_mem _ _ (ν_mem_orthogonalNormalSpace x))

/-- `B(e_θ, e_θ) = -ν` on the unit cylinder. -/
theorem immersionSecondFundamentalFormAt_cyl_eθ (x : ℝ²) :
    immersionSecondFundamentalFormAt (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x
      eθ eθ = -ν x := by
  rw [immersionSecondFundamentalFormAt_cyl]
  change -((1 : ℝ) * 1) • ν x = -ν x
  rw [mul_one, neg_smul, one_smul]

/-- `B(e_z, e_z) = 0` on the unit cylinder. -/
theorem immersionSecondFundamentalFormAt_cyl_ez (x : ℝ²) :
    immersionSecondFundamentalFormAt (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x
      ez ez = 0 := by
  rw [immersionSecondFundamentalFormAt_cyl]
  change -((0 : ℝ) * 0) • ν x = 0
  rw [mul_zero, neg_zero, zero_smul]

/-- The pairing of the shape operator of the cylinder with a tangent vector. -/
theorem inner_immersionShapeOperatorAt_cyl (x v w : ℝ²) :
    ⟪immersionShapeOperatorAt (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x (ν x) v,
      w⟫_ℝ = ⟪-(v 0) • eθ, w⟫_ℝ := by
  refine (inner_immersionShapeOperatorAt (ν x) v w).trans
    ((congrArg (fun z ↦ ⟪z, ν x⟫_ℝ) (immersionSecondFundamentalFormAt_cyl x v w)).trans ?_)
  rw [real_inner_smul_left, inner_ν_ν, real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp

/-- **The shape operator of the unit cylinder** in the outward direction: `S_ν v = -v₀ e_θ`. -/
theorem immersionShapeOperatorAt_cyl_apply (x v : ℝ²) :
    immersionShapeOperatorAt (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x (ν x) v =
      -(v 0) • eθ := by
  refine ext_inner_right ℝ fun w ↦ inner_immersionShapeOperatorAt_cyl x v w

/-- **The principal curvatures of the unit cylinder** in the outward direction are `0, -1`, in
decreasing order: the zero eigenvalue is counted. -/
theorem immersionPrincipalCurvatures_cyl (x : ℝ²)
    (ht : (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³).IsTorsionFree)
    (hm : finrank ℝ ℝ² = 2) :
    immersionPrincipalCurvatures 𝓘(ℝ, ℝ²) cyl x ht hm (ν x) = ![0, -1] := by
  let b : Module.Basis (Fin 2) ℝ ℝ² :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.reindex (Equiv.swap 0 1)
  refine immersionPrincipalCurvatures_eq_of_eigenbasis ht hm (ν x) b ?_ fun i ↦ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · have hb0 : b 0 = ez := by
      simp [b, Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left,
        EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis]
    have hb1 : b 1 = eθ := by
      simp [b, Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right,
        EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis]
    have h0 : immersionShapeOperatorAt (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x
        (ν x) (b 0) = (0 : ℝ) • b 0 := by
      rw [hb0]
      refine (immersionShapeOperatorAt_cyl_apply x ez).trans ?_
      change -(ez 0) • eθ = (0 : ℝ) • ez
      simp
    have h1 : immersionShapeOperatorAt (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x
        (ν x) (b 1) = (-1 : ℝ) • b 1 := by
      rw [hb1]
      refine (immersionShapeOperatorAt_cyl_apply x eθ).trans ?_
      change -(eθ 0) • eθ = (-1 : ℝ) • eθ
      simp
    fin_cases i
    · exact h0
    · exact h1

/-- In the inward direction `-ν` the principal curvatures of the unit cylinder are `1, 0`. -/
theorem immersionPrincipalCurvatures_cyl_neg (x : ℝ²)
    (ht : (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³).IsTorsionFree)
    (hm : finrank ℝ ℝ² = 2) :
    immersionPrincipalCurvatures 𝓘(ℝ, ℝ²) cyl x ht hm (-ν x) = ![1, 0] := by
  funext i
  refine (immersionPrincipalCurvatures_neg ht hm (ν x) i).trans ?_
  rw [immersionPrincipalCurvatures_cyl]
  fin_cases i <;> simp

/-- The standard basis of the plane, as an orthonormal basis of the tangent space at `x`. -/
def tangentBasis (x : ℝ²) : OrthonormalBasis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℝ²) x) :=
  OrthonormalBasis.mk (v := ⇑(EuclideanSpace.basisFun (Fin 2) ℝ))
    (by
      have h := orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal
      exact orthonormal_iff_ite.2 h)
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.span_eq.ge

/-- The vectors of `TauCeti.CylinderCheck.tangentBasis` are `e_θ` and `e_z`. -/
theorem tangentBasis_apply (x : ℝ²) (i : Fin 2) :
    tangentBasis x i = (EuclideanSpace.single i 1 : ℝ²) := by
  unfold tangentBasis
  exact (congrFun (OrthonormalBasis.coe_mk _ _) i).trans (EuclideanSpace.basisFun_apply (Fin 2) ℝ i)

/-- **The mean curvature vector of the unit cylinder** is `H = -ν / 2`: the trace of `B` is `-ν`,
divided by the dimension `2`. -/
theorem immersionMeanCurvatureVector_cyl (x : ℝ²) :
    immersionMeanCurvatureVector (I := 𝓘(ℝ, ℝ²)) (leviCivitaConnection 𝓘(ℝ, ℝ³) ℝ³) cyl x =
      -(1 / 2 : ℝ) • ν x := by
  have h0 := immersionSecondFundamentalFormAt_cyl_eθ x
  have h1 := immersionSecondFundamentalFormAt_cyl_ez x
  rw [immersionMeanCurvatureVector_eq_sum (tangentBasis x), Fin.sum_univ_two,
    tangentBasis_apply, tangentBasis_apply, h0, h1, finrank_euclideanSpace_fin]
  change ((2 : ℕ) : ℝ)⁻¹ • (-ν x + 0) = -(1 / 2 : ℝ) • ν x
  rw [add_zero, smul_neg, ← neg_smul]
  norm_num

end TauCeti.CylinderCheck
