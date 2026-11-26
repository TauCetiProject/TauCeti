/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.UnitSection
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# A smooth unit section trivializes a real line bundle smoothly

Let `E → B` be a `C^n` real vector bundle of rank one with a `C^n` fibrewise inner product, and
`u` a `C^n` section of unit vectors. The homeomorphism
`TauCeti.VectorBundle.unitSectionHomeomorph : B × ℝ ≃ₜ TotalSpace F E`, `(b, t) ↦ t • u b`, with
inverse `v ↦ (b, ⟪v, u b⟫)`, is then a `C^n` diffeomorphism,
`TauCeti.VectorBundle.unitSectionDiffeomorph`. Smoothness of the map is that of fibrewise scalar
multiplication along a varying base point (`ContMDiff.smul_totalSpace`), and smoothness of the
inverse is that of the inner product of two smooth maps into the bundle
(`ContMDiff.inner_bundle`).
-/

public section

open Bundle Module Set
open scoped Manifold ContDiff

namespace TauCeti.VectorBundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ∞ω}
  [IsContMDiffRiemannianBundle IB n F E] {u : ∀ b, E b}

variable (IB F E) in
/-- **A smooth unit section trivializes a real line bundle smoothly.** For a `C^n` section `u` of
unit vectors of a real vector bundle of rank one with a `C^n` fibrewise inner product, the map
`(b, t) ↦ t • u b` is a `C^n` diffeomorphism `B × ℝ ≃ TotalSpace F E`, with inverse
`v ↦ (b, ⟪v, u b⟫)`. -/
noncomputable def unitSectionDiffeomorph (hF : finrank ℝ F = 1)
    (hu : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n fun b ↦ TotalSpace.mk' F b (u b))
    (hu1 : ∀ b, ‖u b‖ = 1) :
    Diffeomorph (IB.prod 𝓘(ℝ, ℝ)) (IB.prod 𝓘(ℝ, F)) (B × ℝ) (TotalSpace F E) n where
  toEquiv :=
    letI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := IB) (n := n)
      (F := F) (V := E)
    (unitSectionHomeomorph F E hF hu.continuous hu1).toEquiv
  contMDiff_toFun := by
    let := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := IB) (n := n)
      (F := F) (V := E)
    rw [Homeomorph.coe_toEquiv, funext (unitSectionHomeomorph_apply hF hu.continuous hu1)]
    exact ContMDiff.smul_totalSpace (g := fun p : B × ℝ ↦ TotalSpace.mk' F p.1 (u p.1))
      contMDiff_snd (hu.comp contMDiff_fst)
  contMDiff_invFun := by
    let := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := IB) (n := n)
      (F := F) (V := E)
    rw [Homeomorph.coe_symm_toEquiv,
      funext (unitSectionHomeomorph_symm_apply hF hu.continuous hu1)]
    refine (Bundle.contMDiff_proj E).prodMk ?_
    exact ContMDiff.inner_bundle (v := fun p : TotalSpace F E ↦ p.snd)
      (w := fun p : TotalSpace F E ↦ u p.proj) contMDiff_id (hu.comp (Bundle.contMDiff_proj E))

variable (hF : finrank ℝ F = 1)
  (hu : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n fun b ↦ TotalSpace.mk' F b (u b)) (hu1 : ∀ b, ‖u b‖ = 1)

@[simp]
theorem unitSectionDiffeomorph_apply (p : B × ℝ) :
    unitSectionDiffeomorph IB F E hF hu hu1 p = TotalSpace.mk' F p.1 (p.2 • u p.1) :=
  letI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := IB) (n := n)
    (F := F) (V := E)
  unitSectionHomeomorph_apply hF hu.continuous hu1 p

@[simp]
theorem unitSectionDiffeomorph_symm_apply (p : TotalSpace F E) :
    (unitSectionDiffeomorph IB F E hF hu hu1).symm p = (p.proj, inner ℝ p.snd (u p.proj)) :=
  letI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := IB) (n := n)
    (F := F) (V := E)
  unitSectionHomeomorph_symm_apply hF hu.continuous hu1 p

/-- The diffeomorphism `unitSectionDiffeomorph` is the homeomorphism `unitSectionHomeomorph`. -/
theorem toHomeomorph_unitSectionDiffeomorph :
    letI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := IB) (n := n)
      (F := F) (V := E)
    (unitSectionDiffeomorph IB F E hF hu hu1).toHomeomorph =
      unitSectionHomeomorph F E hF hu.continuous hu1 :=
  (rfl)

end TauCeti.VectorBundle
