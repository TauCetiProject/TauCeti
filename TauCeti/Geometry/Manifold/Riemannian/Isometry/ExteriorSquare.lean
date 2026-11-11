/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Curvature endomorphisms under local Riemannian isometries

The exterior square of the differential of a local Riemannian isometry intertwines the
curvature endomorphisms on bivectors. This holds on the entire exterior square, including
nondecomposable bivectors. Consequently the curvature endomorphisms are conjugate and have
the same characteristic polynomial, so their eigenvalues and algebraic multiplicities agree.
The eigenvector equation is transported in both directions.

These statements use Mathlib's Gram inner product on exterior powers and the existing
`CovariantDerivative.curvatureEndomorphism`, whose convention is
`⟪Rop(u ∧ v), w ∧ z⟫ = ⟪R(u,v)z,w⟫`. They follow from
`IsLocalRiemannianIsometry.mfderiv_curvatureTensor` and
`exteriorPower.inner_map_map`; no new exterior bundle or metric is introduced.
Local isometries need not be globally injective or surjective, so the results also apply
in individual sheets of a Riemannian covering.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7–8 (curvature naturality and the curvature operator).
-/

public section

open Bundle Manifold CovariantDerivative
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

/-- The exterior square of the differential of a local Riemannian isometry intertwines
curvature endomorphisms on all bivectors. -/
@[simp]
theorem map_curvatureEndomorphism (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (a : ⋀[ℝ]^2 (TangentSpace I x)) :
    exteriorPower.map 2 (mfderiv I J f x).toLinearMap
        ((leviCivitaConnection I M).curvatureEndomorphism
          (isMetricCompatible_leviCivitaConnection I) x a) =
      (leviCivitaConnection J N).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (exteriorPower.map 2 (mfderiv I J f x).toLinearMap a) := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  have heL : e.toLinearEquiv.toLinearMap = (mfderiv I J f x).toLinearMap :=
    LinearMap.ext he
  have heI : e.toLinearIsometry.toLinearMap = e.toLinearEquiv.toLinearMap := by
    ext v
    simp
  have hinner (b c : ⋀[ℝ]^2 (TangentSpace I x)) :
      ⟪exteriorPower.map 2 e.toLinearEquiv.toLinearMap b,
        exteriorPower.map 2 e.toLinearEquiv.toLinearMap c⟫ = ⟪b, c⟫ := by
    simpa only [heI] using exteriorPower.inner_map_map e.toLinearIsometry b c
  have hmap : exteriorPower.map 2 e.toLinearEquiv.toLinearMap ∘ₗ
        (leviCivitaConnection I M).curvatureEndomorphism
          (isMetricCompatible_leviCivitaConnection I) x =
      (leviCivitaConnection J N).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection J) (f x) ∘ₗ
          exteriorPower.map 2 e.toLinearEquiv.toLinearMap := by
    apply exteriorPower.linearMap_ext_inner_ιMulti
    intro u v
    let w : Fin 2 → TangentSpace I x := e.symm ∘ v
    have hv : exteriorPower.ιMulti ℝ 2 v =
        exteriorPower.map 2 e.toLinearEquiv.toLinearMap (exteriorPower.ιMulti ℝ 2 w) := by
      rw [exteriorPower.map_apply_ιMulti]
      congr 1
      funext i
      exact (e.apply_symm_apply (v i)).symm
    rw [hv]
    simp only [LinearMap.comp_apply]
    rw [hinner]
    simp only [exteriorPower.map_apply_ιMulti, inner_curvatureEndomorphism_ιMulti,
      Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, he,
      hf.inner_curvatureTensor_mfderiv]
  rw [← heL]
  exact LinearMap.congr_fun hmap a

/-- The curvature endomorphism at the image point is conjugate to the one at the source
by the exterior square of any linear equivalence representing the differential. -/
theorem curvatureEndomorphism_eq_conj (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace J (f x))
    (he : ∀ v, e v = mfderiv I J f x v) :
    (leviCivitaConnection J N).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection J) (f x) =
      (e.exteriorPower 2).conj ((leviCivitaConnection I M).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection I) x) := by
  have heL : e.toLinearMap = (mfderiv I J f x).toLinearMap := LinearMap.ext he
  apply LinearMap.ext
  intro b
  obtain ⟨a, rfl⟩ := (e.exteriorPower 2).surjective b
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa only [← LinearEquiv.coe_toLinearMap, LinearEquiv.exteriorPower_toLinearMap, heL]
    using (hf.map_curvatureEndomorphism x a).symm

/-- A local Riemannian isometry preserves the characteristic polynomial of the curvature
endomorphism, and hence its eigenvalues with their algebraic multiplicities. -/
theorem charpoly_curvatureEndomorphism (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    ((leviCivitaConnection J N).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection J) (f x)).charpoly =
      ((leviCivitaConnection I M).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection I) x).charpoly := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  rw [hf.curvatureEndomorphism_eq_conj x e.toLinearEquiv he, LinearEquiv.charpoly_conj]

/-- The eigenvector equation for the curvature endomorphism is preserved and reflected by
the exterior square of the differential of a local Riemannian isometry. -/
theorem curvatureEndomorphism_map_eq_smul_iff (hf : IsLocalRiemannianIsometry I J f)
    (x : M) (a : ⋀[ℝ]^2 (TangentSpace I x)) (κ : ℝ) :
    (leviCivitaConnection J N).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (exteriorPower.map 2 (mfderiv I J f x).toLinearMap a) =
          κ • exteriorPower.map 2 (mfderiv I J f x).toLinearMap a ↔
      (leviCivitaConnection I M).curvatureEndomorphism
        (isMetricCompatible_leviCivitaConnection I) x a = κ • a := by
  rw [← hf.map_curvatureEndomorphism, ← map_smul]
  exact (exteriorPower.map_injective_field (hf.mfderiv_injective x)).eq_iff

end TauCeti.IsLocalRiemannianIsometry
