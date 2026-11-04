/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Horizontal curvature of a warped product

For the warped metric `g_M + f² g_N`, horizontal vectors have exactly the curvature of the
base: `R((u, 0), (v, 0)) (w, 0) = (R_M(u, v) w, 0)`. Consequently a horizontal plane has the
same sectional curvature as the corresponding plane in the base. These identities supply
the horizontal terms in curvature contractions of warped products.

The tangent-product equivalence identifies horizontal vectors without introducing another
tangent-space carrier. The proof uses horizontal lifts of smooth base fields and the
Levi-Civita connection formula for a warped product. No nonvanishing assumption on `f` is
needed: all correction terms vanish on horizontal fields. The sectional formula also holds
on dependent pairs, since both sides use the same totalized Gram-determinant quotient.

The curvature convention is `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`.

## Main results

* `TauCeti.Manifold.IsWarpedProduct.tangentSpaceProdEquiv_curvatureTensor_horizontal`:
  horizontal curvature agrees with base curvature.
* `TauCeti.Manifold.IsWarpedProduct.sectionalCurvature_horizontal`:
  horizontal sectional curvature agrees with base sectional curvature.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Proposition 42.
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff Manifold

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
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  [IsContMDiffRiemannianBundle (I.prod J) ∞ (E × F)
    (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  {f : M → ℝ}

private theorem IsWarpedProduct.leviCivitaConnection_horizontal
    (h : IsWarpedProduct I J N f) (hf : MDifferentiable I 𝓘(ℝ) f)
    {Z : Π x : M, TangentSpace I x} (hZ : MDifferentiable I I.tangent (T% Z))
    (X : Π x : M, TangentSpace I x) :
    (fun p ↦ leviCivitaConnection (I.prod J) (M × N) (prodVectorField Z 0) p
      (prodVectorField X 0 p)) =
      prodVectorField (fun x ↦ leviCivitaConnection I M Z x (X x)) 0 := by
  funext p
  apply (tangentSpaceProdEquiv p).injective
  rw [h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₂ := 0) (hf p.1) (hZ p.1)
    ((contMDiff_zeroSection ℝ (TangentSpace J) (n := 1)).mdifferentiable one_ne_zero p.2)]
  simp only [tangentSpaceProdEquiv_prodVectorField]
  simp

private theorem IsWarpedProduct.curvatureOperator_horizontal
    (h : IsWarpedProduct I J N f) (hf : MDifferentiable I 𝓘(ℝ) f)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    (leviCivitaConnection (I.prod J) (M × N)).curvatureOperator
      (prodVectorField X 0) (prodVectorField Y 0) (prodVectorField Z 0) =
      prodVectorField ((leviCivitaConnection I M).curvatureOperator X Y Z) 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)
  have h0 : MDifferentiable J J.tangent (T% (0 : Π y : N, TangentSpace J y)) :=
    (contMDiff_zeroSection ℝ (TangentSpace J) (n := 1)).mdifferentiable one_ne_zero
  have hbracket : mlieBracket (I.prod J) (prodVectorField X 0) (prodVectorField Y 0) =
      prodVectorField (J := J) (N := N) (mlieBracket I X Y) 0 := by
    funext p
    rw [mlieBracket_prodVectorField ((hX p.1).mdifferentiableAt (by simp))
      ((hY p.1).mdifferentiableAt (by simp)) (h0 p.2) (h0 p.2), mlieBracket_zero_left]
  have hYZ := (leviCivitaConnection I M).contMDiff_apply hY hZ
  have hXZ := (leviCivitaConnection I M).contMDiff_apply hX hZ
  funext p
  rw [curvatureOperator_apply,
    h.leviCivitaConnection_horizontal hf (hZ.mdifferentiable (by simp)),
    h.leviCivitaConnection_horizontal hf (hZ.mdifferentiable (by simp)),
    congrFun (h.leviCivitaConnection_horizontal hf (hYZ.mdifferentiable (by simp)) X) p,
    congrFun (h.leviCivitaConnection_horizontal hf (hXZ.mdifferentiable (by simp)) Y) p,
    hbracket, congrFun (h.leviCivitaConnection_horizontal hf
      (hZ.mdifferentiable (by simp)) (mlieBracket I X Y)) p]
  apply (tangentSpaceProdEquiv p).injective
  simp only [map_sub, tangentSpaceProdEquiv_prodVectorField, curvatureOperator_apply,
    Prod.mk_sub_mk, Pi.zero_apply, sub_self]

variable [T2Space M] [T2Space N]

/-- Horizontal curvature of a warped product is the horizontal lift of the base curvature.
This tensor identity holds for arbitrary vectors, including zero and dependent triples. -/
theorem IsWarpedProduct.tangentSpaceProdEquiv_curvatureTensor_horizontal
    (h : IsWarpedProduct I J N f) (hf : MDifferentiable I 𝓘(ℝ) f)
    (p : M × N) (u v w : TangentSpace I p.1) :
    tangentSpaceProdEquiv p
      ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
        ((tangentSpaceProdEquiv p).symm (u, 0))
        ((tangentSpaceProdEquiv p).symm (v, 0))
        ((tangentSpaceProdEquiv p).symm (w, 0))) =
      ((leviCivitaConnection I M).curvatureTensor p.1 u v w, 0) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  have h0 : CMDiff ∞ (T% (0 : Π y : N, TangentSpace J y)) :=
    contMDiff_zeroSection ℝ (TangentSpace J)
  have hvalue (W : Π x : M, TangentSpace I x) :
      (tangentSpaceProdEquiv p).symm (W p.1, 0) = prodVectorField (J := J) W 0 p := by
    apply (tangentSpaceProdEquiv p).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, tangentSpaceProdEquiv_prodVectorField]
    rfl
  rw [hvalue, hvalue, hvalue, curvatureTensor_apply _ p
    (contMDiff_prodVectorField hX h0) (contMDiff_prodVectorField hY h0)
    (contMDiff_prodVectorField hZ h0), h.curvatureOperator_horizontal hf hX hY hZ,
    tangentSpaceProdEquiv_prodVectorField, curvatureTensor_apply _ _ hX hY hZ]
  rfl

/-- The sectional curvature of a horizontal plane in a warped product is its base sectional
curvature. On dependent pairs both totalized quotients are zero, so no independence guard is
needed for this equality. -/
theorem IsWarpedProduct.sectionalCurvature_horizontal
    (h : IsWarpedProduct I J N f) (hf : MDifferentiable I 𝓘(ℝ) f)
    (p : M × N) (u v : TangentSpace I p.1) :
    (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (I.prod J) (M := M × N)) p
      ((tangentSpaceProdEquiv p).symm (u, 0))
      ((tangentSpaceProdEquiv p).symm (v, 0)) =
    (leviCivitaConnection I M).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection I (M := M)) p.1 u v := by
  simp only [sectionalCurvature_apply, Matrix.real_det_gram_fin_two]
  simp only [h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_horizontal hf,
    ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, mul_zero, add_zero]

end TauCeti.Manifold
