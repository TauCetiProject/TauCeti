/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Curvature
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Prod

/-!
# O'Neill tensors and horizontal curvature of Riemannian product projections

For a Riemannian product `M × N`, the first projection `Prod.fst : M × N → M` is a Riemannian
submersion (`TauCeti.isRiemannianSubmersion_fst`) whose horizontal and vertical distributions are
both integrable and parallel along the Levi-Civita connection of the product metric. Consequently,
both O'Neill tensors `oneillA` and `oneillT` vanish identically, and horizontal lifts preserve the
`(0, 4)` Riemann curvature tensor and sectional curvature of `M`.

## Main results

* `TauCeti.starProjection_orthogonal_ker_fst_prodVectorField` and
  `TauCeti.starProjection_ker_fst_prodVectorField`: horizontal and vertical projections of a
  product vector field `(Y₁, Y₂)` along `Prod.fst` isolate `(Y₁, 0)` and `(0, Y₂)`.
* `TauCeti.oneillA_fst` and `TauCeti.oneillT_fst`: O'Neill's fundamental tensors vanish identically
  for `Prod.fst : M × N → M`.
* `TauCeti.riemannCurvatureTensor_horizontalLift_fst` and
  `TauCeti.sectionalCurvature_horizontalLift_fst`: horizontal lifts along `Prod.fst` preserve
  Riemannian and sectional curvature regardless of the geometry of `N`.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966), 459–469.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7.
-/

public section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold TauCeti

noncomputable section

namespace TauCeti

section Projections

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- For the first projection `Prod.fst : M × N → M` with the product Riemannian metric, the
orthogonal projection onto `(ker df_p)ᗮ` sends a product vector field `(Y₁, Y₂)` to `(Y₁, 0)`. -/
theorem starProjection_orthogonal_ker_fst_prodVectorField
    (Y₁ : Π x : M, TangentSpace I x) (Y₂ : Π y : N, TangentSpace J y) (p : M × N) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection
        (Manifold.prodVectorField Y₁ Y₂ p) =
      Manifold.prodVectorField Y₁ (0 : Π y : N, TangentSpace J y) p := by
  apply (Manifold.tangentSpaceProdEquiv p).injective
  rw [starProjection_orthogonal_ker_fst, ContinuousLinearEquiv.apply_symm_apply,
    Manifold.tangentSpaceProdEquiv_prodVectorField,
    Manifold.tangentSpaceProdEquiv_prodVectorField]
  rfl

/-- For the first projection `Prod.fst : M × N → M` with the product Riemannian metric, the
orthogonal projection onto `ker df_p` sends a product vector field `(Y₁, Y₂)` to `(0, Y₂)`. -/
theorem starProjection_ker_fst_prodVectorField
    (Y₁ : Π x : M, TangentSpace I x) (Y₂ : Π y : N, TangentSpace J y) (p : M × N) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection
        (Manifold.prodVectorField Y₁ Y₂ p) =
      Manifold.prodVectorField (0 : Π x : M, TangentSpace I x) Y₂ p := by
  apply (Manifold.tangentSpaceProdEquiv p).injective
  rw [starProjection_ker_fst, ContinuousLinearEquiv.apply_symm_apply,
    Manifold.tangentSpaceProdEquiv_prodVectorField,
    Manifold.tangentSpaceProdEquiv_prodVectorField]
  rfl

section ONeill

variable
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- O'Neill's horizontal tensor vanishes identically for the Riemannian product projection
`Prod.fst : M × N → M`. -/
@[simp]
theorem oneillA_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillA p = 0 := by
  rw [(isRiemannianSubmersion_fst (I := I) (J := J)).oneillA_eq_zero_iff_horizontalLift]
  intro u v
  let Y₁ : Π x : M, TangentSpace I x := FiberBundle.extend E v
  have hY₁ : MDiffAt (T% Y₁) p.1 := FiberBundle.mdifferentiableAt_extend I E v
  have h0N : MDiffAt (T% (0 : Π z : N, TangentSpace J z)) p.2 :=
    (contMDiff_zeroSection ℝ (TangentSpace J)).mdifferentiableAt one_ne_zero
  have hY : MDiffAt (T% (Manifold.prodVectorField Y₁ (0 : Π z : N, TangentSpace J z))) p :=
    Manifold.mdifferentiableAt_prodVectorField hY₁ h0N
  have hYp : Manifold.prodVectorField Y₁ (0 : Π z : N, TangentSpace J z) p =
      (isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p v := by
    rw [horizontalLift_fst]
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [Manifold.tangentSpaceProdEquiv_prodVectorField, ContinuousLinearEquiv.apply_symm_apply]
    ext <;> simp [Y₁, FiberBundle.extend_apply_self]
  have hYh (q : M × N) :
      Manifold.prodVectorField Y₁ (0 : Π z : N, TangentSpace J z) q ∈
        (mfderiv (I.prod J) I (@Prod.fst M N) q).kerᗮ := by
    rw [← Submodule.starProjection_eq_self_iff,
      starProjection_orthogonal_ker_fst_prodVectorField]
  rw [← hYp, (isRiemannianSubmersion_fst
        (I := I) (J := J)).oneillA_apply_of_eventually_mem_orthogonal_ker hY (.of_forall hYh),
    starProjection_ker_fst,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ h0N,
    (CovariantDerivative.leviCivitaConnection J N).isCovariantDerivativeOnUniv.zero]
  simp only [zero_apply, Prod.mk_zero_zero, map_zero]

/-- O'Neill's vertical tensor vanishes identically for the Riemannian product projection
`Prod.fst : M × N → M`. -/
@[simp]
theorem oneillT_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillT p = 0 := by
  rw [(isRiemannianSubmersion_fst (I := I) (J := J)).oneillT_eq_zero_iff]
  intro u v _ hv
  let Y₂ : Π y : N, TangentSpace J y :=
    FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p v).2
  have h0M : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) p.1 :=
    (contMDiff_zeroSection ℝ (TangentSpace I)).mdifferentiableAt one_ne_zero
  have hY₂ : MDiffAt (T% Y₂) p.2 := FiberBundle.mdifferentiableAt_extend J F _
  have hY : MDiffAt (T% (Manifold.prodVectorField (0 : Π x : M, TangentSpace I x) Y₂)) p :=
    Manifold.mdifferentiableAt_prodVectorField h0M hY₂
  have hYp : Manifold.prodVectorField (0 : Π x : M, TangentSpace I x) Y₂ p = v := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hv, starProjection_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [Manifold.tangentSpaceProdEquiv_prodVectorField, ContinuousLinearEquiv.apply_symm_apply]
    ext <;> simp [Y₂, FiberBundle.extend_apply_self]
  have hYv (q : M × N) :
      Manifold.prodVectorField (0 : Π x : M, TangentSpace I x) Y₂ q ∈
        (mfderiv (I.prod J) I (@Prod.fst M N) q).ker := by
    rw [← Submodule.starProjection_eq_self_iff, starProjection_ker_fst_prodVectorField]
  rw [← hYp, (isRiemannianSubmersion_fst
        (I := I) (J := J)).oneillT_apply_of_eventually_mem_ker hY (.of_forall hYv),
    starProjection_orthogonal_ker_fst,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField h0M hY₂,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.zero]
  simp only [zero_apply, Prod.mk_zero_zero, map_zero]

section Curvature

variable [T2Space M] [T2Space N]

/-- For the Riemannian product projection `Prod.fst : M × N → M`, O'Neill's horizontal curvature
equation has vanishing `A`-correction, so horizontal lifts preserve the `(0, 4)` Riemann curvature
tensor regardless of the geometry of `N`. -/
theorem riemannCurvatureTensor_horizontalLift_fst (p : M × N)
    (u v w z : TangentSpace I p.1) :
    (leviCivitaConnection (I.prod J) (M × N)).riemannCurvatureTensor p
        ((isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p u)
        ((isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p v)
        ((isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p w)
        ((isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p z) =
      (leviCivitaConnection I M).riemannCurvatureTensor p.1 u v w z :=
  ((isRiemannianSubmersion_fst (I := I) (J := J)).riemannCurvatureTensor_eq_of_oneillA_eq_zero
    (oneillA_fst p) u v w z).symm

/-- For the Riemannian product projection `Prod.fst : M × N → M`, horizontal lifts preserve
sectional curvature regardless of the geometry of `N`. -/
theorem sectionalCurvature_horizontalLift_fst (p : M × N)
    (u v : TangentSpace I p.1) :
    (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (I.prod J)) p
        ((isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p u)
        ((isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) p.1 u v :=
  (((isRiemannianSubmersion_fst
      (I := I) (J := J)).forall_sectionalCurvature_eq_horizontalLift_iff.mpr
    (oneillA_fst p)) u v).symm

end Curvature

end ONeill

end Projections

end TauCeti
