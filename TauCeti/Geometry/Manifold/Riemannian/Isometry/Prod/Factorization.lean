/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Prod
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod.Basic

/-!
# Factorization of product Riemannian isometries

A Riemannian isometry between nonempty products whose underlying function separates into
factor maps is the product of factor Riemannian isometries. The factor maps need not be
assumed bijective, smooth, or metric-preserving: these properties follow from the product
isometry. The metric argument uses tangent vectors supported in just one factor.

Thus an argument establishing separation of the underlying function suffices to identify
an isometry of a product geometry as an element of the product of its factor isometry
groups.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2
  (product metrics and Riemannian isometries).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487,
  Section 4 (the product geometries).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold TauCeti

namespace TauCeti.RiemannianIsometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℝ F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [RiemannianBundle (fun y : N' ↦ TangentSpace J' y)]

/-- A product isometry with separated underlying map is a product of factor isometries.
Only nonemptiness of the source factors is required; the target factors are then nonempty
by surjectivity. The factors may have different model spaces and may have boundary. -/
theorem exists_prodCongr_of_eq_prodMap
    (Q : RiemannianIsometry (I.prod J) (I'.prod J') (M × N) (M' × N'))
    [Nonempty M] [Nonempty N] (f : M → M') (g : N → N')
    (hQ : ⇑Q = Prod.map f g) :
    ∃ (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J' N N'),
      Φ.prodCongr Ψ = Q := by
  obtain ⟨φ, ψ, hφ, hψ⟩ := Q.toDiffeomorph.exists_factors_of_eq_prodMap f g
    (by simpa using hQ)
  have hsep : ⇑Q = Prod.map φ ψ := by simpa only [hφ, hψ] using hQ
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨y₀⟩ := ‹Nonempty N›
  have hinnerφ : ∀ x (v w : TangentSpace I x),
      inner ℝ (mfderiv I I' φ x v) (mfderiv I I' φ x w) = inner ℝ v w := by
    intro x v w
    have h := Q.inner_mfderiv (x, y₀)
      ((Manifold.tangentSpaceProdEquiv (x, y₀)).symm (v, 0))
      ((Manifold.tangentSpaceProdEquiv (x, y₀)).symm (w, 0))
    rw [Manifold.inner_tangentSpace_prod, Manifold.inner_tangentSpace_prod] at h
    rw [hsep] at h
    simp only [Manifold.mfderiv_prodMap_apply (p := (x, y₀)) (φ.mdifferentiable (by simp) x)
      (ψ.mdifferentiable (by simp) y₀), Prod.map, ContinuousLinearEquiv.apply_symm_apply,
      map_zero, inner_zero_left, add_zero] at h
    exact h
  have hinnerψ : ∀ y (v w : TangentSpace J y),
      inner ℝ (mfderiv J J' ψ y v) (mfderiv J J' ψ y w) = inner ℝ v w := by
    intro y v w
    have h := Q.inner_mfderiv (x₀, y)
      ((Manifold.tangentSpaceProdEquiv (x₀, y)).symm (0, v))
      ((Manifold.tangentSpaceProdEquiv (x₀, y)).symm (0, w))
    rw [Manifold.inner_tangentSpace_prod, Manifold.inner_tangentSpace_prod] at h
    rw [hsep] at h
    simp only [Manifold.mfderiv_prodMap_apply (p := (x₀, y)) (φ.mdifferentiable (by simp) x₀)
      (ψ.mdifferentiable (by simp) y), Prod.map, ContinuousLinearEquiv.apply_symm_apply,
      map_zero, inner_zero_left, zero_add] at h
    exact h
  let Φ : RiemannianIsometry I I' M M' := ⟨φ, hinnerφ⟩
  let Ψ : RiemannianIsometry J J' N N' := ⟨ψ, hinnerψ⟩
  have hΦ : ⇑Φ = φ := (coe_toDiffeomorph Φ).symm
  have hΨ : ⇑Ψ = ψ := (coe_toDiffeomorph Ψ).symm
  refine ⟨Φ, Ψ, RiemannianIsometry.ext fun p => ?_⟩
  rw [prodCongr_apply]
  simpa only [hΦ, hΨ, Prod.map] using congrFun hsep.symm p

/-- An isometry of nonempty products is a product of factor isometries exactly when its
underlying function separates. This criterion requires no curvature or connectedness
assumptions. -/
theorem exists_prodCongr_iff
    (Q : RiemannianIsometry (I.prod J) (I'.prod J') (M × N) (M' × N'))
    [Nonempty M] [Nonempty N] :
    (∃ (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J' N N'),
      Φ.prodCongr Ψ = Q) ↔ ∃ (f : M → M') (g : N → N'), ⇑Q = Prod.map f g := by
  constructor
  · rintro ⟨Φ, Ψ, rfl⟩
    exact ⟨Φ, Ψ, coe_prodCongr Φ Ψ⟩
  · rintro ⟨f, g, hQ⟩
    exact Q.exists_prodCongr_of_eq_prodMap f g hQ

end TauCeti.RiemannianIsometry
