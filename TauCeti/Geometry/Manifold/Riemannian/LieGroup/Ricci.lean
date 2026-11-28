/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.Positive
public import TauCeti.Geometry.Manifold.Riemannian.LieGroup.BiInvariant
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The Ricci curvature of a bi-invariant metric

Let `G` be a Lie group with an *ad-invariant left-invariant* metric: the left-invariant vector
fields `X_a = mulInvariantVectorField a` have constant inner products, and the inner product at
the identity satisfies `⟪⁅a, b⁆, c⟫ = -⟪b, ⁅a, c⁆⟫`. Every bi-invariant metric is of this kind.
Its curvature on left-invariant fields is `R(X_a, X_b) X_c = -¼ X_⁅⁅a, b⁆, c⁆`
(`CovariantDerivative.IsLeviCivitaConnection.curvatureTensor_mulInvariantVectorField`). Taking the
trace `Ric(u, v) = trace (w ↦ R(w, u) v)` of `c ↦ -¼ ⁅⁅c, a⁆, b⁆ = -¼ (ad b ∘ ad a) c` gives

`Ric(X_a, X_b) = -¼ B(a, b)`,

where `B = killingForm ℝ 𝔤` is the Killing form `B(a, b) = trace (ad a ∘ ad b)` of the Lie algebra
`𝔤 = T₁G`. The Ricci tensor is therefore the same bilinear form on `𝔤` at every point, independent
of the choice of ad-invariant inner product.

Since the inner product at the identity is a positive-definite invariant form, the Killing form is
nonpositive and vanishes on the diagonal exactly on the centre of `𝔤`
(`LinearMap.BilinForm.killingForm_self_eq_zero_iff_of_posDef`). Hence an ad-invariant
left-invariant metric has nonnegative Ricci curvature, `Ric(X_a, X_a) = 0` exactly when `a` is
central, and the Ricci tensor is positive definite at some (equivalently every) point exactly when
`𝔤` has trivial centre.

When the metric at the identity is the negative of the Killing form, `⟪a, b⟫ = -B(a, b)`, which
requires the Killing form to be negative definite (as it is for the Lie algebra of a compact
semisimple group), the metric is Einstein:
`Ric = ¼ g`, and its scalar curvature is `dim G / 4`. For instance `SU(2)` with `g = -B` is the
round three-sphere of radius `2√2`, whose Ricci tensor is `2 r⁻² g = ¼ g`.

## Main results

* `CovariantDerivative.IsLeviCivitaConnection.ricciTensor_mulInvariantVectorField`: for an
  ad-invariant left-invariant metric, `Ric(X_a g, X_b g) = -¼ B(a, b)` at every point `g`.
* `CovariantDerivative.IsLeviCivitaConnection.ricciTensor_one`: at the identity, the Ricci tensor
  is `-¼` times the Killing form.
* `CovariantDerivative.IsLeviCivitaConnection.ricciTensor_self_nonneg`: such a metric has
  nonnegative Ricci curvature.
* `CovariantDerivative.IsLeviCivitaConnection.ricciTensor_mulInvariantVectorField_self_eq_zero_iff`:
  `Ric(X_a g, X_a g) = 0` exactly when `a` is central.
* `CovariantDerivative.IsLeviCivitaConnection.posDef_ricciTensor_iff_center_eq_bot`: the Ricci
  tensor is positive definite at a point exactly when the Lie algebra has trivial centre.
* `CovariantDerivative.IsLeviCivitaConnection.ricciTensor_eq_of_inner_eq_neg_killingForm` and
  `CovariantDerivative.IsLeviCivitaConnection.scalarCurvature_eq_of_inner_eq_neg_killingForm`: for
  the metric `-B`, `Ric = ¼ g` and the scalar curvature is `dim G / 4`.

## References

* J. Milnor, *Curvatures of left invariant metrics on Lie groups*, Advances in Math. 21 (1976),
  293–329, §7.
* J. Cheeger and D. G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland (1975),
  Chapter 3.
-/

public section

open Bundle Manifold LieAlgebra
open scoped ContDiff Manifold

noncomputable section

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace CovariantDerivative.IsLeviCivitaConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [RiemannianBundle (fun g : G ↦ TangentSpace I g)]
  [IsContMDiffRiemannianBundle I 1 E (fun g : G ↦ TangentSpace I g)]
  {cov : CovariantDerivative I E (fun g : G ↦ TangentSpace I g)}
  [ContMDiffCovariantDerivative cov ∞]

/-- For an **ad-invariant left-invariant metric** on a Lie group, in particular a bi-invariant
metric, the Ricci tensor on values of left-invariant fields is `-¼` times the Killing form of the
Lie algebra: `Ric(X_a g, X_b g) = -¼ B(a, b)`. -/
theorem ricciTensor_mulInvariantVectorField (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a b : TangentSpace I (1 : G)) (g : G) :
    cov.ricciTensor g (mulInvariantVectorField a g) (mulInvariantVectorField b g) =
      -(4 : ℝ)⁻¹ * killingForm ℝ (TangentSpace I (1 : G)) a b := by
  let e := TauCeti.mulInvariantVectorFieldEquiv I g
  -- Transported to the identity, `w ↦ R(w, X_a g) (X_b g)` is `c ↦ -¼ ⁅⁅c, a⁆, b⁆`, which is
  -- `-¼ (ad b ∘ ad a)`.
  have hconj : ((cov.curvatureTensor g).flip (mulInvariantVectorField a g)).flip
      (mulInvariantVectorField b g) =
      e.toLinearEquiv.conj (-(4 : ℝ)⁻¹ • (ad ℝ (TangentSpace I (1 : G)) b ∘ₗ ad ℝ _ a)) := by
    refine LinearMap.ext fun w ↦ ?_
    obtain ⟨c, rfl⟩ := e.toLinearEquiv.surjective w
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    simp only [e, ContinuousLinearEquiv.coe_toLinearEquiv,
      TauCeti.mulInvariantVectorFieldEquiv_apply, LinearMap.flip_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, ad_apply]
    rw [show ⁅b, ⁅a, c⁆⁆ = ⁅⁅c, a⁆, b⁆ by
      rw [← lie_skew ⁅c, a⁆ b, ← lie_skew c a, lie_neg, neg_neg]]
    exact hcov.curvatureTensor_mulInvariantVectorField hL had c a b g
  rw [ricciTensor_apply, hconj, LinearMap.trace_conj', map_smul, smul_eq_mul,
    ← killingForm_apply_apply, LieModule.traceForm_comm]

/-- For an ad-invariant left-invariant metric on a Lie group, the Ricci tensor at the identity is
`-¼` times the Killing form of the Lie algebra. -/
theorem ricciTensor_one (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G)))) :
    cov.ricciTensor 1 = -(4 : ℝ)⁻¹ • killingForm ℝ (TangentSpace I (1 : G)) := by
  ext a b
  have h := hcov.ricciTensor_mulInvariantVectorField hL had a b 1
  simp only [mulInvariantVectorField_one] at h
  rw [h, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]

/-- For an ad-invariant left-invariant metric on a Lie group, `Ric(X_a g, X_a g) = 0` exactly when
`a` lies in the centre of the Lie algebra. -/
theorem ricciTensor_mulInvariantVectorField_self_eq_zero_iff (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (a : TangentSpace I (1 : G)) (g : G) :
    cov.ricciTensor g (mulInvariantVectorField a g) (mulInvariantVectorField a g) = 0 ↔
      a ∈ center ℝ (TangentSpace I (1 : G)) := by
  rw [hcov.ricciTensor_mulInvariantVectorField hL had, mul_eq_zero, neg_eq_zero,
    inv_eq_zero, or_iff_right (by norm_num)]
  exact LinearMap.BilinForm.killingForm_self_eq_zero_iff_of_posDef
    (innerₗ (TangentSpace I (1 : G))) TauCeti.isSymm_innerₗ
    TauCeti.posDef_toQuadraticMap_innerₗ had a

/-- An ad-invariant left-invariant metric on a Lie group, in particular a bi-invariant metric, has
**nonnegative Ricci curvature**. -/
theorem ricciTensor_self_nonneg (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (g : G) (u : TangentSpace I g) :
    0 ≤ cov.ricciTensor g u u := by
  -- Every tangent vector at `g` is the value of a left-invariant field.
  obtain ⟨a, rfl⟩ := TauCeti.exists_mulInvariantVectorField_eq u
  rw [hcov.ricciTensor_mulInvariantVectorField hL had, neg_mul]
  exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    (LinearMap.BilinForm.killingForm_self_nonpos_of_posDef
      (innerₗ (TangentSpace I (1 : G))) TauCeti.isSymm_innerₗ
      TauCeti.posDef_toQuadraticMap_innerₗ had a))

/-- For an ad-invariant left-invariant metric on a Lie group, the Ricci tensor is **positive
definite** at a point `g` exactly when the Lie algebra has trivial centre. In particular it is
positive definite at one point if and only if it is at every point. -/
theorem posDef_ricciTensor_iff_center_eq_bot (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))))
    (g : G) :
    (LinearMap.BilinMap.toQuadraticMap (cov.ricciTensor g)).PosDef ↔
      center ℝ (TangentSpace I (1 : G)) = ⊥ := by
  rw [← LinearMap.BilinForm.posDef_neg_killingForm_iff_center_eq_bot_of_posDef
    (innerₗ (TangentSpace I (1 : G))) TauCeti.isSymm_innerₗ
    TauCeti.posDef_toQuadraticMap_innerₗ had]
  let e := TauCeti.mulInvariantVectorFieldEquiv I g
  -- Transported to the identity, the Ricci quadratic form at `g` is `¼` of that of `-B`.
  have h (a : TangentSpace I (1 : G)) :
      0 < LinearMap.BilinMap.toQuadraticMap (cov.ricciTensor g) (e a) ↔
        0 < (-killingForm ℝ (TangentSpace I (1 : G))).toQuadraticMap a := by
    simp only [e, LinearMap.BilinMap.toQuadraticMap_apply,
      TauCeti.mulInvariantVectorFieldEquiv_apply, hcov.ricciTensor_mulInvariantVectorField hL had,
      LinearMap.neg_apply]
    constructor <;> intro <;> linarith
  refine ⟨fun hpos a ha ↦ (h a).1 (hpos (e a) (e.map_ne_zero_iff.2 ha)), fun hpos u hu ↦ ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective u
  exact (h a).2 (hpos a (e.map_ne_zero_iff.1 hu))

/-- A left-invariant metric whose inner product at the identity is the negative of the Killing
form, `⟪a, b⟫ = -B(a, b)`, is **Einstein with constant `¼`**: `Ric = ¼ g` at every point. Such an
inner product is automatically ad-invariant. -/
theorem ricciTensor_eq_of_inner_eq_neg_killingForm (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (hB : ∀ a b : TangentSpace I (1 : G),
      inner ℝ a b = -killingForm ℝ (TangentSpace I (1 : G)) a b)
    (g : G) :
    cov.ricciTensor g = (4 : ℝ)⁻¹ • innerₗ (TangentSpace I g) := by
  -- The inner product `-B` is ad-invariant because the Killing form is.
  have had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))) := by
    intro x y z
    simp only [innerₗ_apply_apply, hB]
    rw [LieModule.traceForm_lieInvariant ℝ _ _ x y z]
  refine LinearMap.ext₂ fun u v ↦ ?_
  obtain ⟨a, rfl⟩ := (TauCeti.mulInvariantVectorFieldEquiv I g).surjective u
  obtain ⟨b, rfl⟩ := (TauCeti.mulInvariantVectorFieldEquiv I g).surjective v
  simp only [TauCeti.mulInvariantVectorFieldEquiv_apply, LinearMap.smul_apply, innerₗ_apply_apply,
    smul_eq_mul, hcov.ricciTensor_mulInvariantVectorField hL had, hL, hB]
  ring

/-- A left-invariant metric whose inner product at the identity is the negative of the Killing
form has constant **scalar curvature `dim G / 4`**. -/
theorem scalarCurvature_eq_of_inner_eq_neg_killingForm (hcov : cov.IsLeviCivitaConnection)
    (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
    (hB : ∀ a b : TangentSpace I (1 : G),
      inner ℝ a b = -killingForm ℝ (TangentSpace I (1 : G)) a b)
    (g : G) :
    cov.scalarCurvature g = (Module.finrank ℝ E : ℝ) / 4 := by
  rw [scalarCurvature_eq_of_ricciTensor_eq_smul_inner cov g _
    (hcov.ricciTensor_eq_of_inner_eq_neg_killingForm hL hB g), TauCeti.finrank_tangentSpace]
  ring

end CovariantDerivative.IsLeviCivitaConnection
