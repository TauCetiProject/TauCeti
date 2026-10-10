/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod

/-!
# Isometries preserve product factors with distinct Ricci constants

For a product of two Einstein metrics with distinct Ricci constants, every isometry
preserves the inner product on each tangent factor separately. Consequently its differential
preserves the horizontal and vertical tangent subspaces. This is the infinitesimal step in
identifying the full isometry groups of product geometries such as the hyperbolic plane
crossed with a line: the Ricci constants are respectively `-1` and `0`.

The argument combines the product Ricci formula with metric and Ricci invariance under
isometries. No connectedness, completeness, compactness, or absence of boundary is needed.

Reference: J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
(Ricci curvature and Riemannian products).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold
open scoped Manifold ContDiff TauCeti

namespace TauCeti.RiemannianIsometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun x : N ↦ TangentSpace J x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun x : N ↦ TangentSpace J x)]
  {a b : ℝ}

local notation "split" => TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J)

/-- An isometry of a product with distinct Ricci constants preserves the inner product
of the first tangent components. -/
theorem inner_mfderiv_fst_of_ricciTensor_eq_smul_inner
    (Φ : RiemannianIsometry (I.prod J) (I.prod J) (M × N) (M × N))
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ x u v, (leviCivitaConnection J N).ricciTensor x u v = b * inner ℝ u v)
    (hab : a ≠ b) (p : M × N) (u v : TangentSpace (I.prod J) p) :
    inner ℝ (split (Φ p) (mfderiv (I.prod J) (I.prod J) Φ p u)).1
        (split (Φ p) (mfderiv (I.prod J) (I.prod J) Φ p v)).1 =
      inner ℝ (split p u).1 (split p v).1 := by
  have hmetric := Φ.inner_mfderiv p u v
  rw [TauCeti.Manifold.inner_tangentSpace_prod,
    TauCeti.Manifold.inner_tangentSpace_prod] at hmetric
  have hricci := Φ.ricciTensor_mfderiv p u v
  simp only [TauCeti.Manifold.ricciTensor_leviCivitaConnection_prod, hM, hN] at hricci
  apply (mul_left_cancel₀ (sub_ne_zero.mpr hab))
  linear_combination hricci - b * hmetric

/-- An isometry of a product with distinct Ricci constants preserves the inner product
of the second tangent components. -/
theorem inner_mfderiv_snd_of_ricciTensor_eq_smul_inner
    (Φ : RiemannianIsometry (I.prod J) (I.prod J) (M × N) (M × N))
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ x u v, (leviCivitaConnection J N).ricciTensor x u v = b * inner ℝ u v)
    (hab : a ≠ b) (p : M × N) (u v : TangentSpace (I.prod J) p) :
    inner ℝ (split (Φ p) (mfderiv (I.prod J) (I.prod J) Φ p u)).2
        (split (Φ p) (mfderiv (I.prod J) (I.prod J) Φ p v)).2 =
      inner ℝ (split p u).2 (split p v).2 := by
  have hmetric := Φ.inner_mfderiv p u v
  rw [TauCeti.Manifold.inner_tangentSpace_prod,
    TauCeti.Manifold.inner_tangentSpace_prod] at hmetric
  have hfst := Φ.inner_mfderiv_fst_of_ricciTensor_eq_smul_inner hM hN hab p u v
  linarith

/-- The vertical tangent subspace is preserved and reflected by the differential
of every isometry of a product with distinct Ricci constants. -/
theorem fst_mfderiv_eq_zero_iff_of_ricciTensor_eq_smul_inner
    (Φ : RiemannianIsometry (I.prod J) (I.prod J) (M × N) (M × N))
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ x u v, (leviCivitaConnection J N).ricciTensor x u v = b * inner ℝ u v)
    (hab : a ≠ b) (p : M × N) (u : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) (I.prod J) Φ p u : E × F).1 = 0 ↔ (u : E × F).1 = 0 := by
  have h := (congrArg (fun t : ℝ => t = 0)
    (Φ.inner_mfderiv_fst_of_ricciTensor_eq_smul_inner hM hN hab p u u)).to_iff
  simp only [inner_self_eq_zero, TauCeti.Manifold.tangentSpaceProdEquiv_apply] at h
  -- The projection notation reads the product tangent-space synonym in the model;
  -- the identification lemma reads it in the factor tangent-space synonyms.
  convert h using 1 <;> rfl

/-- The horizontal tangent subspace is preserved and reflected by the differential
of every isometry of a product with distinct Ricci constants. -/
theorem snd_mfderiv_eq_zero_iff_of_ricciTensor_eq_smul_inner
    (Φ : RiemannianIsometry (I.prod J) (I.prod J) (M × N) (M × N))
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ x u v, (leviCivitaConnection J N).ricciTensor x u v = b * inner ℝ u v)
    (hab : a ≠ b) (p : M × N) (u : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) (I.prod J) Φ p u : E × F).2 = 0 ↔ (u : E × F).2 = 0 := by
  have h := (congrArg (fun t : ℝ => t = 0)
    (Φ.inner_mfderiv_snd_of_ricciTensor_eq_smul_inner hM hN hab p u u)).to_iff
  simp only [inner_self_eq_zero, TauCeti.Manifold.tangentSpaceProdEquiv_apply] at h
  -- The projection notation reads the product tangent-space synonym in the model;
  -- the identification lemma reads it in the factor tangent-space synonyms.
  convert h using 1 <;> rfl

end TauCeti.RiemannianIsometry
