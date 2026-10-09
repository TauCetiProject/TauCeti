/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Curvature of a product metric

Give `M × N` the product of smooth Riemannian metrics on `M` and `N`. Its Riemann curvature tensor
is the product of the curvature tensors of the factors:

`R((u₁, u₂), (v₁, v₂)) (w₁, w₂) = (R(u₁, v₁) w₁, R(u₂, v₂) w₂)`,

and its Ricci tensor is the sum of the Ricci tensors of the factors:

`Ric((u₁, u₂), (v₁, v₂)) = Ric(u₁, v₁) + Ric(u₂, v₂)`.

So mixed curvature terms vanish, and a flat factor contributes nothing to the Ricci tensor. This
reduces the Ricci tensor of the product geometries `S² × ℝ` and `ℍ² × ℝ` to that of their surface
factor. Since every isometry preserves the Ricci tensor
(`TauCeti.RiemannianIsometry.ricciTensor_mfderiv`), it is the curvature input for showing that the
isometries of these geometries preserve the line factor.

The curvature tensor is evaluated on smooth product fields, on which the Levi-Civita connection
of the product acts factor by factor (`TauCeti.Manifold.leviCivitaConnection_prodVectorField`) and
whose Lie brackets are computed factor by factor
(`TauCeti.Manifold.mlieBracket_prodVectorField`).

## Main results

* `TauCeti.Manifold.curvatureOperator_leviCivitaConnection_prodVectorField`: the curvature operator
  of the product metric on smooth product fields.
* `TauCeti.Manifold.tangentSpaceProdEquiv_curvatureTensor_leviCivitaConnection_prod`: the curvature
  tensor of the product metric is the product of the curvature tensors.
* `TauCeti.Manifold.ricciTensor_leviCivitaConnection_prod`: the Ricci tensor of the product metric
  is the sum of the Ricci tensors.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7
  (the curvature tensor and the Ricci tensor).
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff Manifold TauCeti

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {X₁ Y₁ Z₁ : Π x : M, TangentSpace I x} {X₂ Y₂ Z₂ : Π y : N, TangentSpace J y}

/-- The curvature operator of the product metric on smooth product fields is the product of the
curvature operators of the factors. -/
theorem curvatureOperator_leviCivitaConnection_prodVectorField (hX₁ : CMDiff ∞ (T% X₁))
    (hY₁ : CMDiff ∞ (T% Y₁)) (hZ₁ : CMDiff ∞ (T% Z₁)) (hX₂ : CMDiff ∞ (T% X₂))
    (hY₂ : CMDiff ∞ (T% Y₂)) (hZ₂ : CMDiff ∞ (T% Z₂)) :
    (leviCivitaConnection (I.prod J) (M × N)).curvatureOperator (prodVectorField X₁ X₂)
        (prodVectorField Y₁ Y₂) (prodVectorField Z₁ Z₂) =
      prodVectorField ((leviCivitaConnection I M).curvatureOperator X₁ Y₁ Z₁)
        ((leviCivitaConnection J N).curvatureOperator X₂ Y₂ Z₂) := by
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)
  have hd {W₁ : Π x : M, TangentSpace I x} {W₂ : Π y : N, TangentSpace J y}
      (h₁ : CMDiff ∞ (T% W₁)) (h₂ : CMDiff ∞ (T% W₂)) (p : M × N) :
      MDiffAt (T% W₁) p.1 ∧ MDiffAt (T% W₂) p.2 :=
    ⟨(h₁ p.1).mdifferentiableAt (by simp), (h₂ p.2).mdifferentiableAt (by simp)⟩
  -- The first covariant derivatives of `Z` along `X` and `Y` are again product fields.
  have hcov (W₁ : Π x : M, TangentSpace I x) (W₂ : Π y : N, TangentSpace J y) :
      (fun q ↦ leviCivitaConnection (I.prod J) (M × N) (prodVectorField Z₁ Z₂) q
          (prodVectorField W₁ W₂ q)) =
        prodVectorField (fun x ↦ leviCivitaConnection I M Z₁ x (W₁ x))
          (fun y ↦ leviCivitaConnection J N Z₂ y (W₂ y)) :=
    funext fun q ↦ leviCivitaConnection_prodVectorField (hd hZ₁ hZ₂ q).1 (hd hZ₁ hZ₂ q).2
  have hYZ₁ := (leviCivitaConnection I M).contMDiff_apply hY₁ hZ₁
  have hYZ₂ := (leviCivitaConnection J N).contMDiff_apply hY₂ hZ₂
  have hXZ₁ := (leviCivitaConnection I M).contMDiff_apply hX₁ hZ₁
  have hXZ₂ := (leviCivitaConnection J N).contMDiff_apply hX₂ hZ₂
  funext p
  apply (tangentSpaceProdEquiv p).injective
  rw [curvatureOperator_apply, hcov, hcov,
    leviCivitaConnection_prodVectorField (hd hYZ₁ hYZ₂ p).1 (hd hYZ₁ hYZ₂ p).2,
    leviCivitaConnection_prodVectorField (hd hXZ₁ hXZ₂ p).1 (hd hXZ₁ hXZ₂ p).2,
    mlieBracket_prodVectorField (hd hX₁ hX₂ p).1 (hd hY₁ hY₂ p).1 (hd hX₁ hX₂ p).2
      (hd hY₁ hY₂ p).2,
    leviCivitaConnection_prodVectorField (hd hZ₁ hZ₂ p).1 (hd hZ₁ hZ₂ p).2, map_sub, map_sub]
  simp only [tangentSpaceProdEquiv_prodVectorField, curvatureOperator_apply, Prod.mk_sub_mk]

variable [T2Space M] [T2Space N]

/-- **The curvature tensor of a product metric** is the product of the curvature tensors of the
factors: `R((u₁, u₂), (v₁, v₂)) (w₁, w₂) = (R(u₁, v₁) w₁, R(u₂, v₂) w₂)`. -/
theorem tangentSpaceProdEquiv_curvatureTensor_leviCivitaConnection_prod (p : M × N)
    (u v w : TangentSpace (I.prod J) p) :
    tangentSpaceProdEquiv p ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p u v w) =
      ((leviCivitaConnection I M).curvatureTensor p.1 (tangentSpaceProdEquiv p u).1
          (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1,
        (leviCivitaConnection J N).curvatureTensor p.2 (tangentSpaceProdEquiv p u).2
          (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2) := by
  set e := tangentSpaceProdEquiv (I := I) (J := J) p
  -- Extend the components of `u`, `v` and `w` to smooth vector fields on the factors.
  obtain ⟨X₁, hX₁, hX₁p⟩ := exists_contMDiff_section_eq I E (V := TangentSpace I) (e u).1
  obtain ⟨X₂, hX₂, hX₂p⟩ := exists_contMDiff_section_eq J F (V := TangentSpace J) (e u).2
  obtain ⟨Y₁, hY₁, hY₁p⟩ := exists_contMDiff_section_eq I E (V := TangentSpace I) (e v).1
  obtain ⟨Y₂, hY₂, hY₂p⟩ := exists_contMDiff_section_eq J F (V := TangentSpace J) (e v).2
  obtain ⟨Z₁, hZ₁, hZ₁p⟩ := exists_contMDiff_section_eq I E (V := TangentSpace I) (e w).1
  obtain ⟨Z₂, hZ₂, hZ₂p⟩ := exists_contMDiff_section_eq J F (V := TangentSpace J) (e w).2
  have hvalue {W₁ : Π x : M, TangentSpace I x} {W₂ : Π y : N, TangentSpace J y}
      {t : TangentSpace (I.prod J) p} (h₁ : W₁ p.1 = (e t).1) (h₂ : W₂ p.2 = (e t).2) :
      prodVectorField W₁ W₂ p = t := by
    apply e.injective
    rw [tangentSpaceProdEquiv_prodVectorField, h₁, h₂]
  rw [← hvalue hX₁p hX₂p, ← hvalue hY₁p hY₂p, ← hvalue hZ₁p hZ₂p,
    curvatureTensor_apply _ p (contMDiff_prodVectorField hX₁ hX₂)
      (contMDiff_prodVectorField hY₁ hY₂) (contMDiff_prodVectorField hZ₁ hZ₂),
    curvatureOperator_leviCivitaConnection_prodVectorField hX₁ hY₁ hZ₁ hX₂ hY₂ hZ₂]
  simp only [e, tangentSpaceProdEquiv_prodVectorField, curvatureTensor_apply _ _ hX₁ hY₁ hZ₁,
    curvatureTensor_apply _ _ hX₂ hY₂ hZ₂]

/-- **The Ricci tensor of a product metric** is the sum of the Ricci tensors of the factors:
`Ric((u₁, u₂), (v₁, v₂)) = Ric(u₁, v₁) + Ric(u₂, v₂)`. -/
theorem ricciTensor_leviCivitaConnection_prod (p : M × N) (u v : TangentSpace (I.prod J) p) :
    (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p u v =
      (leviCivitaConnection I M).ricciTensor p.1 (tangentSpaceProdEquiv p u).1
          (tangentSpaceProdEquiv p v).1 +
        (leviCivitaConnection J N).ricciTensor p.2 (tangentSpaceProdEquiv p u).2
          (tangentSpaceProdEquiv p v).2 := by
  set e := tangentSpaceProdEquiv (I := I) (J := J) p
  -- Read in the product decomposition, `w ↦ R(w, u) v` is block diagonal.
  have hconj : e.toLinearEquiv.conj
      ((((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p).flip u).flip v) =
      ((((leviCivitaConnection I M).curvatureTensor p.1).flip (e u).1).flip (e v).1).prodMap
        ((((leviCivitaConnection J N).curvatureTensor p.2).flip (e u).2).flip (e v).2) := by
    refine LinearMap.ext fun z ↦ ?_
    rw [LinearEquiv.conj_apply_apply, LinearMap.flip_apply, LinearMap.flip_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      tangentSpaceProdEquiv_curvatureTensor_leviCivitaConnection_prod, e.apply_symm_apply,
      LinearMap.prodMap_apply, LinearMap.flip_apply, LinearMap.flip_apply, LinearMap.flip_apply,
      LinearMap.flip_apply]
  rw [ricciTensor_apply, ricciTensor_apply, ricciTensor_apply,
    ← LinearMap.trace_conj' _ e.toLinearEquiv, hconj, LinearMap.trace_prodMap']

end TauCeti.Manifold
