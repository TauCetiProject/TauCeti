/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.LocalIsometry

/-!
# Nondegenerate metrics on open submanifolds

This file restricts a smooth symmetric nondegenerate metric `g` on `M`, of any signature, to an
open submanifold `U`. Mathlib models every tangent space on the model vector space, so at
`x ∈ U` the restricted metric `g|_U` is the ambient form read through the canonical
identification `T_x U ≃ T_x M`; the content is that this field is again smooth, symmetric and
nondegenerate.

The inclusion `U → M` is then a local isometry from `g|_U` to `g`, so the naturality of
Levi-Civita connections under local isometries applies to it: a Levi-Civita connection of `g|_U`
differentiates the restriction of a vector field on `M` as a Levi-Civita connection of `g`
differentiates the field itself. Since the Koszul formula can be read through the inclusion, the
same argument shows, with no connection on all of `M`, that Levi-Civita connections of the
restrictions of `g` to two open sets differentiate the restrictions of a vector field on `M` in
the same way at every point of their intersection.

For the metric of a smooth Riemannian bundle, restriction agrees with the restriction of the
Riemannian bundle to `U`.

## Main definitions and results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`:

* `restrictOpenTangentSpace`: the restriction of a smooth nondegenerate metric to an open
  submanifold, with `restrictOpenTangentSpace_apply`.
* `restrictOpenTangentSpace_eq_of_apply_eq`: metrics that agree on an open set have equal
  restrictions to it.
* `isLocalIsometry_subtype_val`: the inclusion of an open submanifold is a local isometry.
* `ofRiemannianBundle_restrictOpenTangentSpace`: the positive-definite comparison with the
  restricted Riemannian bundle.
* `IsLeviCivitaConnection.tangentSpaceOpenEquiv_apply_mpullback`: Levi-Civita connections of `g`
  and of `g|_U` differentiate restrictions of ambient vector fields in the same way at points
  of `U`.
* `IsLeviCivitaConnection.tangentSpaceOpenEquiv_apply_mpullback_eq`: Levi-Civita connections of
  `g|_U` and `g|_V` differentiate restrictions of ambient vector fields in the same way at points
  of `U ∩ V`.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3 (the Levi-Civita connection is local and natural under isometries).
* `TauCeti.Geometry.Manifold.Riemannian.Restriction`: the positive-definite restriction of a
  Riemannian metric to an open submanifold, which this file parallels.
-/

public section

open Bundle FiberBundle VectorField TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The restriction of a smooth nondegenerate metric to an open submanifold `U`: at `x ∈ U` it
pairs tangent vectors as the ambient metric does, through the canonical identification of
`T_x U` with `T_x M`. -/
def restrictOpenTangentSpace (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (U : Opens M) : ContMDiffNondegenerateMetric (I := I) (M := U) where
  toContMDiffSection := ⟨restrictOpenTangentSpaceBilin g U,
    fun x ↦ contMDiffAt_restrictOpenTangentSpaceBilin (g.contMDiff x)⟩
  -- The section built above coerces to `restrictOpenTangentSpaceBilin g U` by definition, so the
  -- fibrewise laws are proved for that field and then supplied with `exact`.
  symm x := by
    have key : (restrictOpenTangentSpaceBilin (fun y ↦ g y) U x).toBilinForm.IsSymm :=
      ⟨fun v w ↦ by
        simp only [ContinuousLinearMap.toBilinForm_apply, restrictOpenTangentSpaceBilin_apply]
        exact g.apply_comm x _ _⟩
    exact key
  nondegenerate x := by
    -- The restricted form is the congruence of the ambient form by the canonical isomorphism.
    have key : (restrictOpenTangentSpaceBilin (fun y ↦ g y) U x).toBilinForm.Nondegenerate := by
      convert (g.nondegenerate x).congr (tangentSpaceOpenEquiv (I := I) x).symm.toLinearEquiv
        using 1
      ext v w
      simp only [ContinuousLinearMap.toBilinForm_apply, restrictOpenTangentSpaceBilin_apply,
        LinearMap.BilinForm.congr_apply, ContinuousLinearEquiv.toLinearEquiv_symm,
        LinearEquiv.symm_symm, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact key

variable (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (U : Opens M)

/-- The restricted metric is the ambient metric under the canonical tangent-space
identification. -/
@[simp]
theorem restrictOpenTangentSpace_apply (x : U) (v w : TangentSpace I x) :
    g.restrictOpenTangentSpace U x v w =
      g x (tangentSpaceOpenEquiv (I := I) x v) (tangentSpaceOpenEquiv (I := I) x w) :=
  restrictOpenTangentSpaceBilin_apply _ U x v w

/-- Two smooth nondegenerate metrics that agree on an open set `U` have equal restrictions
to `U`. -/
theorem restrictOpenTangentSpace_eq_of_apply_eq
    {g₁ g₂ : ContMDiffNondegenerateMetric (I := I) (M := M)} (h : ∀ x ∈ U, g₁ x = g₂ x) :
    g₁.restrictOpenTangentSpace U = g₂.restrictOpenTangentSpace U := by
  ext x v w
  simp only [restrictOpenTangentSpace_apply, h x x.2]

/-- The inclusion of an open submanifold is a local isometry from the restricted metric to the
ambient one. -/
theorem isLocalIsometry_subtype_val :
    (g.restrictOpenTangentSpace U).IsLocalIsometry g (Subtype.val : U → M) where
  contMDiff := contMDiff_subtype_val
  isInvertible_mfderiv x := ⟨tangentSpaceOpenEquiv (I := I) x, (mfderiv_subtype_val x).symm⟩
  apply_mfderiv x v w := by
    simp only [mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe, restrictOpenTangentSpace_apply]

open scoped TauCeti in
/-- Restricting the metric of a smooth Riemannian bundle to an open submanifold gives the metric
of the restricted Riemannian bundle. -/
theorem ofRiemannianBundle_restrictOpenTangentSpace
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    (ofRiemannianBundle I M).restrictOpenTangentSpace U = ofRiemannianBundle I U := by
  ext x v w
  rw [restrictOpenTangentSpace_apply, ofRiemannianBundle_apply, ofRiemannianBundle_apply]
  -- The inner product of the ambient fibre is `RiemannianBundle.g.inner` by definition of the
  -- fibrewise instance.
  exact (inner_tangentSpace_open U x v w).symm

section LeviCivita

variable [FiniteDimensional ℝ E] {U}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {covU : CovariantDerivative I E (fun x : U ↦ TangentSpace I x)}
  {Y : Π x : M, TangentSpace I x}

/-- **Restriction of Levi-Civita connections to an open submanifold.** If `∇` is a Levi-Civita
connection of `g` and `∇ᵁ` one of its restriction to `U`, then `∇ᵁ` differentiates the restriction
`Y|_U` of a vector field `Y` differentiable at `x ∈ U` as `∇` differentiates `Y`, under the
canonical tangent-space identification. -/
theorem IsLeviCivitaConnection.tangentSpaceOpenEquiv_apply_mpullback
    (hU : (g.restrictOpenTangentSpace U).IsLeviCivitaConnection covU)
    (h : g.IsLeviCivitaConnection cov) {x : U} (hY : MDiffAt (T% Y) (x : M))
    (v : TangentSpace I x) :
    tangentSpaceOpenEquiv (I := I) x (covU (mpullback I I Subtype.val Y) x v) =
      cov Y x (tangentSpaceOpenEquiv (I := I) x v) := by
  have := (g.isLocalIsometry_subtype_val U).mfderiv_apply_mpullback_of_isLeviCivitaConnection
    hU h hY v
  simpa only [mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] using this

/-- **Levi-Civita connections of restrictions agree on overlaps.** Let `∇ᵁ` and `∇ⱽ` be
Levi-Civita connections of the restrictions of `g` to open sets `U` and `V`. At a point
`x ∈ U ∩ V` they differentiate the restrictions of a vector field `Y` differentiable at `x` in
the same way, under the canonical tangent-space identifications. No Levi-Civita connection of `g`
on all of `M` is needed. -/
theorem IsLeviCivitaConnection.tangentSpaceOpenEquiv_apply_mpullback_eq {V : Opens M}
    {covV : CovariantDerivative I E (fun x : V ↦ TangentSpace I x)}
    (hU : (g.restrictOpenTangentSpace U).IsLeviCivitaConnection covU)
    (hV : (g.restrictOpenTangentSpace V).IsLeviCivitaConnection covV) {x : M} (hxU : x ∈ U)
    (hxV : x ∈ V) (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    tangentSpaceOpenEquiv (I := I) (⟨x, hxU⟩ : U)
        (covU (mpullback I I Subtype.val Y) ⟨x, hxU⟩
          ((tangentSpaceOpenEquiv (I := I) (⟨x, hxU⟩ : U)).symm v)) =
      tangentSpaceOpenEquiv (I := I) (⟨x, hxV⟩ : V)
        (covV (mpullback I I Subtype.val Y) ⟨x, hxV⟩
          ((tangentSpaceOpenEquiv (I := I) (⟨x, hxV⟩ : V)).symm v)) := by
  -- Both sides are computed by the Koszul expression of `g` at `x`, through the inclusions.
  set X : Π y : M, TangentSpace I y := extend E v
  have hX : MDiffAt (T% X) x := mdifferentiableAt_extend I E v
  refine g.injective_apply_mdifferentiableAt_vectorField x ?_
  ext Z hZ
  have hkU := (g.isLocalIsometry_subtype_val U).two_apply_mfderiv_eq_koszul (x := ⟨x, hxU⟩) hU hX
    hY hZ (v := (tangentSpaceOpenEquiv (I := I) (⟨x, hxU⟩ : U)).symm v) (by simp [X])
  have hkV := (g.isLocalIsometry_subtype_val V).two_apply_mfderiv_eq_koszul (x := ⟨x, hxV⟩) hV hX
    hY hZ (v := (tangentSpaceOpenEquiv (I := I) (⟨x, hxV⟩ : V)).symm v) (by simp [X])
  simp only [mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] at hkU hkV
  dsimp only
  linarith

end LeviCivita

end TauCeti.Manifold.ContMDiffNondegenerateMetric
