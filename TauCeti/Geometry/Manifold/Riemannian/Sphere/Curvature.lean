/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Immersion
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Curvature of the round sphere

The unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1`, with its round
metric, has constant sectional curvature `1`: its curvature tensor is

`R(u, v) w = ⟪v, w⟫ u - ⟪u, w⟫ v`,

its Ricci tensor is `n - 1` times the metric, and its scalar curvature is `n (n - 1)`.

The computation uses the gradients `X_a` of the height functions `p ↦ ⟪a, p⟫`, for `a ∈ E`. In
ambient coordinates `X_a p = a - ⟪a, p⟫ p` is the tangential part of `a`, so these fields span
every tangent space. The Gauss formula for the isometric inclusion `Sⁿ → E` gives
`∇_{X_a} X_b = -⟪b, p⟫ X_a`, and the differential of the inclusion gives the bracket
`[X_a, X_b] = ⟪a, p⟫ X_b - ⟪b, p⟫ X_a`; the curvature of these fields follows by the Leibniz rule.

## Main results

* `TauCeti.curvatureTensor_sphere`: the curvature tensor of the round sphere.
* `TauCeti.hasConstantSectionalCurvature_sphere`: the round sphere has constant sectional
  curvature `1`.
* `TauCeti.ricciTensor_sphere`: the Ricci tensor of the round `n`-sphere is `n - 1` times the
  metric.
* `TauCeti.scalarCurvature_sphere`: the scalar curvature of the round `n`-sphere is `n (n - 1)`.
* `TauCeti.scalarCurvature_sphereRoundMetric_ofLE`: the same, for the round metric regarded as a
  smooth metric.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 8.34 (the round sphere has constant sectional curvature) and Theorem 8.2 (the Gauss
  formula).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold Metric Module VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

local notation "ι" => ((↑) : sphere (0 : E) 1 → E)
local notation "∇" => leviCivitaConnection (𝓡 n) (sphere (0 : E) 1)

/-- The height function `p ↦ ⟪a, p⟫` on the unit sphere is smooth. -/
private theorem contMDiff_height (a : E) :
    ContMDiff (𝓡 n) 𝓘(ℝ) ω fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E) :=
  (innerSL ℝ a).contDiff.contMDiff.comp contMDiff_coe_sphere

private theorem mvfderiv_height (a : E) (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p v =
      inner ℝ a (mvfderiv (𝓡 n) ι p v) := by
  have h : (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) = innerSL ℝ a ∘ ι :=
    funext fun q ↦ (innerSL_apply_apply ℝ a (q : E)).symm
  rw [h, TauCeti.mvfderiv_comp_apply_of_differentiableAt (innerSL ℝ a).differentiableAt
    ((contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero),
    (innerSL ℝ a).fderiv, innerSL_apply_apply]

variable (n) in
/-- The gradient of the height function `p ↦ ⟪a, p⟫`. -/
private def field (a : E) (p : sphere (0 : E) 1) : TangentSpace (𝓡 n) p :=
  Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p

private theorem contMDiff_field (a : E) :
    ContMDiff (𝓡 n) (𝓡 n).tangent ∞
      (fun p ↦ (⟨p, field n a p⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
  Manifold.contMDiff_mgradient ((contMDiff_height (n := n) a).of_le le_top)

private theorem mdifferentiableAt_field (a : E) (p : sphere (0 : E) 1) :
    MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun p ↦ (⟨p, field n a p⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) p :=
  (contMDiff_field a p).mdifferentiableAt (by simp)

/-- The height function differentiates along `v` as the inner product with its gradient. -/
private theorem inner_mvfderiv_coe (a : E) (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    inner ℝ a (mvfderiv (𝓡 n) ι p v) = inner ℝ (field n a p) v := by
  rw [field, Manifold.inner_mgradient, mvfderiv_height]

/-- In ambient coordinates, the gradient of `p ↦ ⟪a, p⟫` is the tangential part of `a`. -/
private theorem mvfderiv_coe_field (a : E) (p : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ι p (field n a p) = a - inner ℝ a (p : E) • (p : E) := by
  have hp : inner ℝ (p : E) (p : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have ht : a - inner ℝ a (p : E) • (p : E) ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      real_inner_smul_right, hp, real_inner_comm]
    ring
  let u : TangentSpace (𝓡 n) p := (sphereTangentEquiv p).symm ⟨_, ht⟩
  have hu : mvfderiv (𝓡 n) ι p u = a - inner ℝ a (p : E) • (p : E) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← coe_sphereTangentEquiv_apply,
      LinearIsometryEquiv.apply_symm_apply]
  have hfield : field n a p = u := by
    refine (Manifold.eq_mgradient_iff.2 fun v ↦ ?_).symm
    rw [inner_tangentSpace_sphere, hu, mvfderiv_height, inner_sub_left, real_inner_smul_left,
      inner_coe_mvfderiv_subtypeVal_sphere, mul_zero, sub_zero]
  rw [hfield, hu]

/-- Every tangent vector is the value of the gradient of a height function. -/
private theorem field_mvfderiv_coe (p : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) p) :
    field n (mvfderiv (𝓡 n) ι p w) p = w := by
  apply injective_mvfderiv_subtypeVal_sphere p
  rw [mvfderiv_coe_field, real_inner_comm, inner_coe_mvfderiv_subtypeVal_sphere, zero_smul,
    sub_zero]

/-- The ambient derivative of the gradient of `p ↦ ⟪b, p⟫`, in ambient coordinates. -/
private theorem mvfderiv_mvfderiv_coe_field (b : E) (p : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) ι y (field n b y)) p v =
      -(inner ℝ (field n b p) v • (p : E) + inner ℝ b (p : E) • mvfderiv (𝓡 n) ι p v) := by
  have heq : (fun y ↦ mvfderiv (𝓡 n) ι y (field n b y)) =
      fun y : sphere (0 : E) 1 ↦ b - inner ℝ b (y : E) • (y : E) :=
    funext fun y ↦ mvfderiv_coe_field b y
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ι p :=
    (contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero
  have hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ) (fun q : sphere (0 : E) 1 ↦ inner ℝ b (q : E)) p :=
    (contMDiff_height (n := n) b p).mdifferentiableAt (by simp)
  have hhι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun q : sphere (0 : E) 1 ↦ inner ℝ b (q : E) • (q : E)) p :=
    hh.smul hι
  rw [heq, mvfderiv_fun_sub mdifferentiableAt_const hhι, mvfderiv_const,
    mvfderiv_fun_smul hh hι]
  simp only [zero_sub, neg_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    mvfderiv_height, inner_mvfderiv_coe]
  rw [add_comm]

/-- The Levi-Civita connection on gradients of height functions: `∇_{X_a} X_b = -⟪b, p⟫ X_a`. -/
private theorem leviCivitaConnection_field (a b : E) (p : sphere (0 : E) 1) :
    ∇ (field n b) p (field n a p) = -inner ℝ b (p : E) • field n a p := by
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [(isLeviCivitaConnection_leviCivitaConnection (I := 𝓡 n)).inner_apply_eq_inner_mvfderiv
      (contMDiff_coe_sphere (m := 2) p) inner_tangentSpace_sphere
      (mdifferentiableAt_field a p) (mdifferentiableAt_field b p),
    mvfderiv_mvfderiv_coe_field]
  simp only [inner_neg_left, inner_add_left, real_inner_smul_left,
    inner_coe_mvfderiv_subtypeVal_sphere, ← inner_tangentSpace_sphere]
  ring

/-- The Lie bracket of gradients of height functions: `[X_a, X_b] = ⟪a, p⟫ X_b - ⟪b, p⟫ X_a`. -/
private theorem mlieBracket_field (a b : E) (p : sphere (0 : E) 1) :
    mlieBracket (𝓡 n) (field n a) (field n b) p =
      inner ℝ a (p : E) • field n b p - inner ℝ b (p : E) • field n a p := by
  apply injective_mvfderiv_subtypeVal_sphere p
  rw [mvfderiv_mlieBracket (contMDiff_coe_sphere (m := 2) p) (by simp)
      (mdifferentiableAt_field a p) (mdifferentiableAt_field b p),
    mvfderiv_mvfderiv_coe_field, mvfderiv_mvfderiv_coe_field, map_sub, map_smul, map_smul,
    real_inner_comm (field n a p)]
  module

/-- The second covariant derivative of gradients of height functions. -/
private theorem leviCivitaConnection_leviCivitaConnection_field (a b c : E)
    (p : sphere (0 : E) 1) :
    ∇ (fun y ↦ ∇ (field n c) y (field n b y)) p (field n a p) =
      (inner ℝ b (p : E) * inner ℝ c (p : E)) • field n a p -
        inner ℝ (field n a p) (field n c p) • field n b p := by
  have hfun : (fun y ↦ ∇ (field n c) y (field n b y)) =
      (fun q : sphere (0 : E) 1 ↦ -inner ℝ c (q : E)) • field n b :=
    funext fun y ↦ leviCivitaConnection_field b c y
  have hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ) (fun q : sphere (0 : E) 1 ↦ -inner ℝ c (q : E)) p :=
    ((contMDiff_height (n := n) c).neg p).mdifferentiableAt (by simp)
  rw [hfun, ∇.isCovariantDerivativeOnUniv.leibniz (mdifferentiableAt_field b p) hg]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    leviCivitaConnection_field, mvfderiv_fun_neg, neg_apply, mvfderiv_height,
    inner_mvfderiv_coe, smul_smul]
  rw [real_inner_comm (field n c p)]
  module

/-- The curvature operator on gradients of height functions has the constant-curvature form. -/
private theorem curvatureOperator_field (a b c : E) (p : sphere (0 : E) 1) :
    ∇.curvatureOperator (field n a) (field n b) (field n c) p =
      inner ℝ (field n b p) (field n c p) • field n a p -
        inner ℝ (field n a p) (field n c p) • field n b p := by
  rw [curvatureOperator_apply, leviCivitaConnection_leviCivitaConnection_field,
    leviCivitaConnection_leviCivitaConnection_field, mlieBracket_field, map_sub, map_smul,
    map_smul, leviCivitaConnection_field, leviCivitaConnection_field]
  module

/-- The round sphere has the constant-curvature tensor with parameter `1`:
`R(u, v) w = ⟪v, w⟫ u - ⟪u, w⟫ v`. -/
@[simp] theorem curvatureTensor_sphere (p : sphere (0 : E) 1) (u v w : TangentSpace (𝓡 n) p) :
    ∇.curvatureTensor p u v w = inner ℝ v w • u - inner ℝ u w • v := by
  rw [← field_mvfderiv_coe p u, ← field_mvfderiv_coe p v, ← field_mvfderiv_coe p w,
    ∇.curvatureTensor_apply p (contMDiff_field _) (contMDiff_field _) (contMDiff_field _),
    curvatureOperator_field]

/-- The round sphere has constant sectional curvature `1`. -/
theorem hasConstantSectionalCurvature_sphere :
    ∇.HasConstantSectionalCurvature (isMetricCompatible_leviCivitaConnection (𝓡 n)) 1 :=
  ∇.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub
    (isMetricCompatible_leviCivitaConnection (𝓡 n)) 1 fun p w u v ↦ by
      rw [curvatureTensor_sphere, one_smul]

/-- The Ricci tensor of the round `n`-sphere is `n - 1` times the round metric. -/
@[simp 1100] theorem ricciTensor_sphere (p : sphere (0 : E) 1) (u v : TangentSpace (𝓡 n) p) :
    ∇.ricciTensor p u v = ((n : ℝ) - 1) * inner ℝ u v := by
  have hdim : finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    rw [TauCeti.finrank_tangentSpace, finrank_euclideanSpace_fin]
  rw [∇.ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub p 1 fun w u v ↦ by
      rw [curvatureTensor_sphere, one_smul], hdim]
  simp

/-- The scalar curvature of the round `n`-sphere is `n (n - 1)`. -/
@[simp] theorem scalarCurvature_sphere (p : sphere (0 : E) 1) :
    ∇.scalarCurvature p = n * ((n : ℝ) - 1) := by
  have hdim : finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    rw [TauCeti.finrank_tangentSpace, finrank_euclideanSpace_fin]
  rw [∇.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub p 1 fun w u v ↦ by
      rw [curvatureTensor_sphere, one_smul], hdim, mul_one]

/-- The scalar curvature of the round metric on the unit `n`-sphere, regarded as a smooth metric,
is `n (n - 1)`. -/
@[simp]
theorem scalarCurvature_sphereRoundMetric_ofLE (p : sphere (0 : E) 1) :
    ((sphereRoundMetric (E := E) (n := n)).ofLE le_top).scalarCurvature p = n * ((n : ℝ) - 1) := by
  rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection _
    (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm]
  exact scalarCurvature_sphere p

end TauCeti
