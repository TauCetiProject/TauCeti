/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Algebra.Lie.InvariantForm
public import TauCeti.Geometry.Lie.Basic
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional

/-!
# The Levi-Civita connection and curvature of a bi-invariant metric

Let `G` be a Lie group with a Riemannian metric which is *left-invariant*: the left-invariant
vector fields `X_a = mulInvariantVectorField a` satisfy `⟪X_a g, X_b g⟫ = ⟪a, b⟫` for every `g`.
Equivalently, every left translation preserves the inner product of tangent vectors at the
identity; this holds when each left translation is a local Riemannian isometry
(`TauCeti.IsLocalRiemannianIsometry`). Inner products of left-invariant fields are then constant,
and the bracket of left-invariant fields is the left-invariant field of the bracket of Mathlib's
Lie algebra `GroupLieAlgebra I G` (`mulInvariantVector_mlieBracket`), so the Koszul formula
computes the Levi-Civita connection on left-invariant fields from the Lie bracket alone:

`2 ⟪∇_{X_a} X_b, X_c⟫ = ⟪⁅a, b⁆, c⟫ - ⟪⁅b, c⁆, a⟫ + ⟪⁅c, a⁆, b⟫`.

If moreover the inner product at the identity is invariant under the adjoint action of the Lie
algebra, `⟪⁅a, b⁆, c⟫ = -⟪b, ⁅a, c⁆⟫` (Mathlib's `LinearMap.BilinForm.lieInvariant`), we call the
metric *ad-invariant left-invariant*. Then the formula collapses to

`∇_{X_a} X_b = ½ X_⁅a, b⁆`.

Every bi-invariant metric is ad-invariant left-invariant: invariance of the inner product under the
adjoint action of `G` implies this infinitesimal invariance by differentiation. On a connected group
the converse holds, so the two notions agree; on a disconnected group an ad-invariant left-invariant
metric need not be bi-invariant. With Lee's sign convention
`R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z`, the Jacobi identity then gives

`R(X_a, X_b) X_c = -¼ X_⁅⁅a, b⁆, c⁆`,

so the curvature tensor at the identity is `R(a, b)c = -¼ ⁅⁅a, b⁆, c⁆` and the sectional numerator
is `⟪R(a, b)b, a⟫ = ¼ ⟪⁅a, b⁆, ⁅a, b⁆⟫`. Hence an ad-invariant left-invariant metric, in
particular a bi-invariant metric, has nonnegative sectional curvature, and the numerator of the
plane spanned by `a` and `b` vanishes exactly when `a` and `b` commute. These formulas are the
curvature input for the geometry of compact Lie groups and, through Riemannian submersions, of
their normal homogeneous spaces.

The connection statements hold for every connection satisfying Mathlib's
`CovariantDerivative.IsLeviCivitaConnection`, for a `C¹` metric on a `C³` Lie group. The statements
about the pointwise curvature tensor `CovariantDerivative.curvatureTensor` and sectional curvature
`CovariantDerivative.sectionalCurvature` assume a smooth Lie group and a smooth connection.

## Main results

* `CovariantDerivative.IsLeviCivitaConnection.inner_apply_mulInvariantVectorField`: the Koszul
  formula on left-invariant fields of a left-invariant metric.
* `CovariantDerivative.IsLeviCivitaConnection.apply_mulInvariantVectorField`: for an
  ad-invariant left-invariant metric, `∇_{X_a} X_b = ½ X_⁅a, b⁆`.
* `CovariantDerivative.IsLeviCivitaConnection.curvatureOperator_mulInvariantVectorField`: for an
  ad-invariant left-invariant metric, `R(X_a, X_b) X_c = -¼ X_⁅⁅a, b⁆, c⁆`.
* `CovariantDerivative.IsLeviCivitaConnection.curvatureTensor_mulInvariantVectorField` and
  `CovariantDerivative.IsLeviCivitaConnection.curvatureTensor_one`: the same for the pointwise
  curvature tensor, at any point and at the identity.
* `CovariantDerivative.IsLeviCivitaConnection.inner_curvatureTensor_one`: the sectional numerator
  `⟪R(a, b)b, a⟫ = ¼ ⟪⁅a, b⁆, ⁅a, b⁆⟫`, with
  `CovariantDerivative.IsLeviCivitaConnection.inner_curvatureTensor_one_eq_zero_iff`.
* `CovariantDerivative.IsLeviCivitaConnection.sectionalCurvature_nonneg`: an ad-invariant
  left-invariant metric, in particular a bi-invariant metric, has nonnegative sectional curvature.

## Implementation notes

Lie algebra elements are taken in the carrier `TangentSpace I (1 : G)` rather than in Mathlib's
abbreviation `GroupLieAlgebra I G`. The inner product of a Riemannian bundle is found by unifying
the fibre type with an application of the bundle to a base point, which succeeds for the former
and not for the latter. The two types are reducibly equal, so the Lie bracket applies to both.

## References

* J. Milnor, *Curvatures of left invariant metrics on Lie groups*, Advances in Math. 21 (1976),
  293–329.
* J. Cheeger and D. G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland (1975),
  Chapter 3.
-/

public section

open Bundle Manifold VectorField
open scoped ContDiff Manifold

noncomputable section

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace CovariantDerivative.IsLeviCivitaConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

section Connection

variable [LieGroup I 3 G] [RiemannianBundle (fun g : G ↦ TangentSpace I g)]

/-- Ad-invariance of the inner product at the identity, stated with `inner`:
`⟪⁅x, y⁆, z⟫ = -⟪y, ⁅x, z⁆⟫`. -/
private theorem inner_lie_left
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (x y z : TangentSpace I (1 : G)) :
    inner ℝ ⁅x, y⁆ z = -inner ℝ y ⁅x, z⁆ := by
  simpa only [innerₗ_apply_apply] using had x y z

/-- For an ad-invariant inner product at the identity, `⟪⁅b, c⁆, a⟫ = ⟪⁅a, b⁆, c⟫`: the `inner`
form of `LinearMap.BilinForm.lieInvariant.apply_lie_cyclic`. -/
private theorem inner_lie_cyclic
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b c : TangentSpace I (1 : G)) :
    inner ℝ ⁅b, c⁆ a = inner ℝ ⁅a, b⁆ c := by
  simpa only [innerₗ_apply_apply] using
    had.apply_lie_cyclic ⟨fun x y ↦ real_inner_comm y x⟩ a b c

variable [IsContMDiffRiemannianBundle I 1 E (fun g : G ↦ TangentSpace I g)]
  {cov : CovariantDerivative I E (fun g : G ↦ TangentSpace I g)}

/-- The **Koszul formula for left-invariant fields**. For a left-invariant metric on a Lie group,
the inner product of the covariant derivative of one left-invariant field along another with a
third is given by the Lie bracket at the identity:
`⟪∇_{X_a} X_b, X_c⟫ = (⟪⁅a, b⁆, c⟫ - ⟪⁅b, c⁆, a⟫ + ⟪⁅c, a⁆, b⟫) / 2`. -/
theorem inner_apply_mulInvariantVectorField (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (a b c : TangentSpace I (1 : G)) (g : G) :
    inner ℝ (cov (mulInvariantVectorField b) g (mulInvariantVectorField a g))
        (mulInvariantVectorField c g) =
      (inner ℝ ⁅a, b⁆ c - inner ℝ ⁅b, c⁆ a + inner ℝ ⁅c, a⁆ b) / 2 := by
  refine (hcov.apply_eq I (mdifferentiableAt_mulInvariantVectorField a)
    (mdifferentiableAt_mulInvariantVectorField b)
    (mdifferentiableAt_mulInvariantVectorField c)).trans ?_
  -- Brackets of left-invariant fields are left-invariant fields of brackets.
  rw [← mulInvariantVector_mlieBracket a c, ← mulInvariantVector_mlieBracket b a,
    ← mulInvariantVector_mlieBracket c b]
  -- Inner products of left-invariant fields are constant, so the derivative terms vanish.
  simp only [hL, mvfderiv_const, zero_apply, ← GroupLieAlgebra.bracket_def]
  rw [← lie_skew c b, ← lie_skew b a, ← lie_skew c a, inner_neg_right, inner_neg_right,
    inner_neg_left, real_inner_comm c ⁅a, b⁆, real_inner_comm a ⁅b, c⁆, real_inner_comm b ⁅a, c⁆]
  ring

/-- For an **ad-invariant left-invariant metric** on a Lie group, the covariant derivative of a
left-invariant field along another is half their bracket: `∇_{X_a} X_b = ½ X_⁅a, b⁆`. The metric
is left-invariant, and its inner product at the identity is invariant under the adjoint action of
the Lie algebra; every bi-invariant metric is of this kind. -/
theorem apply_mulInvariantVectorField (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b : TangentSpace I (1 : G)) (g : G) :
    cov (mulInvariantVectorField b) g (mulInvariantVectorField a g) =
      mulInvariantVectorField ((2 : ℝ)⁻¹ • ⁅a, b⁆) g := by
  have : ContMDiffMul I 1 G := .of_le (n := 3) (by norm_num)
  refine ext_inner_right ℝ fun w ↦ ?_
  -- Every tangent vector at `g` is the value of a left-invariant field (this uses that left
  -- multiplication is differentiable).
  obtain ⟨c, rfl⟩ : ∃ c : TangentSpace I (1 : G), mulInvariantVectorField c g = w :=
    ⟨_, TauCeti.mulInvariantVectorField_mfderiv_inv_mul w⟩
  rw [hcov.inner_apply_mulInvariantVectorField hL, hL, inner_lie_cyclic had a b c,
    inner_lie_cyclic had b c a, inner_lie_cyclic had a b c, real_inner_smul_left]
  ring

/-- The vector-field form of `apply_mulInvariantVectorField`, for rewriting inside iterated
covariant derivatives. -/
private theorem apply_mulInvariantVectorField_eq (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b : TangentSpace I (1 : G)) :
    (fun g ↦ cov (mulInvariantVectorField b) g (mulInvariantVectorField a g)) =
      mulInvariantVectorField ((2 : ℝ)⁻¹ • ⁅a, b⁆) :=
  funext (hcov.apply_mulInvariantVectorField hL had a b)

/-- For an ad-invariant left-invariant metric, the curvature operator on left-invariant fields
is `R(X_a, X_b) X_c = -¼ X_⁅⁅a, b⁆, c⁆`, with Lee's sign convention
`R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z`. -/
theorem curvatureOperator_mulInvariantVectorField (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b c : TangentSpace I (1 : G)) :
    cov.curvatureOperator (mulInvariantVectorField a) (mulInvariantVectorField b)
        (mulInvariantVectorField c) =
      mulInvariantVectorField (-(4 : ℝ)⁻¹ • ⁅⁅a, b⁆, c⁆) := by
  ext g
  rw [curvatureOperator_apply, hcov.apply_mulInvariantVectorField_eq hL had b c,
    hcov.apply_mulInvariantVectorField_eq hL had a c, ← mulInvariantVector_mlieBracket,
    ← GroupLieAlgebra.bracket_def,
    hcov.apply_mulInvariantVectorField hL had, hcov.apply_mulInvariantVectorField hL had,
    hcov.apply_mulInvariantVectorField hL had]
  -- The Jacobi identity `⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆` combines the three terms.
  have key : (2 : ℝ)⁻¹ • ⁅a, (2 : ℝ)⁻¹ • ⁅b, c⁆⁆ =
      -(4 : ℝ)⁻¹ • ⁅⁅a, b⁆, c⁆ + (2 : ℝ)⁻¹ • ⁅b, (2 : ℝ)⁻¹ • ⁅a, c⁆⁆ +
        (2 : ℝ)⁻¹ • ⁅⁅a, b⁆, c⁆ := by
    rw [lie_smul (2 : ℝ)⁻¹ a ⁅b, c⁆, lie_smul (2 : ℝ)⁻¹ b ⁅a, c⁆, leibniz_lie a b c]
    module
  rw [key, mulInvariantVectorField_add, mulInvariantVectorField_add, Pi.add_apply, Pi.add_apply]
  abel

end Connection

section Tensor

variable [LieGroup I ∞ G] [T2Space G] [RiemannianBundle (fun g : G ↦ TangentSpace I g)]
  {cov : CovariantDerivative I E (fun g : G ↦ TangentSpace I g)}
  [ContMDiffCovariantDerivative cov ∞]

section C1

variable [IsContMDiffRiemannianBundle I 1 E (fun g : G ↦ TangentSpace I g)]

/-- For an ad-invariant left-invariant metric on a smooth Lie group, the curvature tensor on
values of left-invariant fields is `R(X_a g, X_b g) (X_c g) = -¼ X_⁅⁅a, b⁆, c⁆ g`. -/
theorem curvatureTensor_mulInvariantVectorField (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b c : TangentSpace I (1 : G)) (g : G) :
    cov.curvatureTensor g (mulInvariantVectorField a g) (mulInvariantVectorField b g)
        (mulInvariantVectorField c g) =
      mulInvariantVectorField (-(4 : ℝ)⁻¹ • ⁅⁅a, b⁆, c⁆) g := by
  rw [curvatureTensor_apply cov g (contMDiff_mulInvariantVectorField_infty a)
    (contMDiff_mulInvariantVectorField_infty b) (contMDiff_mulInvariantVectorField_infty c),
    hcov.curvatureOperator_mulInvariantVectorField hL had]

/-- For an ad-invariant left-invariant metric on a smooth Lie group, the curvature tensor at
the identity is `R(a, b)c = -¼ ⁅⁅a, b⁆, c⁆`. -/
theorem curvatureTensor_one (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b c : TangentSpace I (1 : G)) :
    cov.curvatureTensor 1 a b c = -(4 : ℝ)⁻¹ • ⁅⁅a, b⁆, c⁆ := by
  have h := hcov.curvatureTensor_mulInvariantVectorField hL had a b c 1
  simp only [mulInvariantVectorField_one] at h
  exact h

/-- For an ad-invariant left-invariant metric on a smooth Lie group, the sectional numerator on
values of left-invariant fields is `⟪R(X_a g, X_b g) (X_b g), X_a g⟫ = ¼ ⟪⁅a, b⁆, ⁅a, b⁆⟫`. -/
theorem inner_curvatureTensor_mulInvariantVectorField (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b : TangentSpace I (1 : G)) (g : G) :
    inner ℝ (cov.curvatureTensor g (mulInvariantVectorField a g) (mulInvariantVectorField b g)
        (mulInvariantVectorField b g)) (mulInvariantVectorField a g) =
      (4 : ℝ)⁻¹ * inner ℝ ⁅a, b⁆ ⁅a, b⁆ := by
  rw [hcov.curvatureTensor_mulInvariantVectorField hL had, hL, real_inner_smul_left,
    ← lie_skew ⁅a, b⁆ b, inner_neg_left, inner_lie_left had, ← lie_skew a b, inner_neg_right]
  ring

/-- For an ad-invariant left-invariant metric on a smooth Lie group, the sectional numerator at
the identity is `⟪R(a, b)b, a⟫ = ¼ ⟪⁅a, b⁆, ⁅a, b⁆⟫`. -/
theorem inner_curvatureTensor_one (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b : TangentSpace I (1 : G)) :
    inner ℝ (cov.curvatureTensor 1 a b b) a = (4 : ℝ)⁻¹ * inner ℝ ⁅a, b⁆ ⁅a, b⁆ := by
  have h := hcov.inner_curvatureTensor_mulInvariantVectorField hL had a b 1
  simp only [mulInvariantVectorField_one] at h
  exact h

/-- For an ad-invariant left-invariant metric on a smooth Lie group, the sectional numerator
`⟪R(a, b)b, a⟫` at the identity vanishes exactly when `a` and `b` commute. -/
theorem inner_curvatureTensor_one_eq_zero_iff (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b : TangentSpace I (1 : G)) :
    inner ℝ (cov.curvatureTensor 1 a b b) a = 0 ↔ ⁅a, b⁆ = 0 := by
  rw [hcov.inner_curvatureTensor_one hL had, mul_eq_zero, inner_self_eq_zero]
  norm_num

end C1

/-- An ad-invariant left-invariant metric on a smooth Lie group, in particular a bi-invariant
metric, has **nonnegative sectional curvature**. -/
theorem sectionalCurvature_nonneg
    [IsContMDiffRiemannianBundle I 2 E (fun g : G ↦ TangentSpace I g)]
    (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (g : G) (u v : TangentSpace I g) :
    0 ≤ cov.sectionalCurvature hcov.isMetricCompatible g u v := by
  -- Every tangent vector at `g` is the value of a left-invariant field.
  obtain ⟨a, rfl⟩ : ∃ a : TangentSpace I (1 : G), mulInvariantVectorField a g = u :=
    ⟨_, TauCeti.mulInvariantVectorField_mfderiv_inv_mul u⟩
  obtain ⟨b, rfl⟩ : ∃ b : TangentSpace I (1 : G), mulInvariantVectorField b g = v :=
    ⟨_, TauCeti.mulInvariantVectorField_mfderiv_inv_mul v⟩
  rw [sectionalCurvature_apply, hcov.inner_curvatureTensor_mulInvariantVectorField hL had]
  exact div_nonneg (mul_nonneg (by norm_num) real_inner_self_nonneg)
    (Matrix.posSemidef_gram ℝ _).det_nonneg

end Tensor

end CovariantDerivative.IsLeviCivitaConnection
