/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Radial.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Smooth radial coordinates with variable radius

A positive `C^n` radius on the base identifies the entire smooth normal bundle of a
Euclidean immersion with its variable-radius open ball bundle. The identification preserves
base points and fixes the zero section. Unlike a constant radius, a variable radius can
shrink towards infinity on a noncompact submanifold, as needed to parametrize its tubular
neighbourhood by the whole normal bundle.

The construction composes `normalBundleRadialPartialDiffeomorph` at unit radius with
`vectorBundleScalarDiffeomorph`; it uses their smoothness and inverse laws rather than
reproving the radial calculus. As with the fixed-radius construction, install
`normalFiberBundle` locally to use the resulting partial diffeomorphism.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Set Function Bundle Metric
open scoped Manifold ContDiff

namespace TauCeti

variable {V E H M F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [I.Boundaryless] {n : ℕ∞} [IsManifold I (n + 1) M] {f : M → V}

/-- Radial compression followed by fibrewise rescaling identifies the whole smooth normal
bundle with its open ball bundle of positive `C^n` radius `r`. -/
def normalBundleRadialPartialDiffeomorphOfRadius
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {r : M → ℝ} (hr : ContMDiff I 𝓘(ℝ) n r) (hrpos : ∀ x, 0 < r x) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    PartialDiffeomorph (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F))
      (TotalSpace F (fun x => normalSubspace I f x))
      (TotalSpace F (fun x => normalSubspace I f x)) n := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  exact (normalBundleRadialPartialDiffeomorph hf himm hdim zero_lt_one).trans
    (vectorBundleScalarDiffeomorph r hr (fun x => (hrpos x).ne')).toPartialDiffeomorph

variable (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
  (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
  (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
  {r : M → ℝ} (hr : ContMDiff I 𝓘(ℝ) n r) (hrpos : ∀ x, 0 < r x)

private theorem normalBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    letI := normalVectorBundle (hf.of_le le_add_self) himm hdim
    (normalBundleRadialPartialDiffeomorphOfRadius hf himm hdim hr hrpos).toPartialEquiv =
      (normalBundleRadialPartialDiffeomorph hf himm hdim zero_lt_one).toPartialEquiv.trans
        (vectorBundleScalarDiffeomorph r hr (fun x => (hrpos x).ne')).toEquiv.toPartialEquiv := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  unfold normalBundleRadialPartialDiffeomorphOfRadius
  rw [PartialDiffeomorph.trans_toPartialEquiv]
  exact congrArg
    ((normalBundleRadialPartialDiffeomorph hf himm hdim zero_lt_one).toPartialEquiv.trans)
    (Diffeomorph.toPartialDiffeomorph_toPartialEquiv _)

/-- Variable-radius radial coordinates are defined on the entire normal bundle. -/
@[simp] theorem normalBundleRadialPartialDiffeomorphOfRadius_source :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    (normalBundleRadialPartialDiffeomorphOfRadius hf himm hdim hr hrpos).source = univ := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  rw [normalBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv]
  simp [PartialEquiv.trans_source]

/-- The target consists exactly of normal vectors shorter than the radius at their base. -/
@[simp] theorem normalBundleRadialPartialDiffeomorphOfRadius_target :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    (normalBundleRadialPartialDiffeomorphOfRadius hf himm hdim hr hrpos).target =
      {p | ‖(p.2 : V)‖ < r p.proj} := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  rw [normalBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv,
    PartialEquiv.trans_target'']
  simpa [fun x => Real.norm_of_nonneg (hrpos x).le] using
    (vectorBundleScalarDiffeomorph_image_setOf_norm_lt (F := F)
      (V := fun x => normalSubspace I f x) r hr (fun x => (hrpos x).ne') (fun _ => 1))

/-- Compression uses the fixed-radius fibre formula with the radius at the base point. -/
@[simp] theorem normalBundleRadialPartialDiffeomorphOfRadius_apply
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    normalBundleRadialPartialDiffeomorphOfRadius hf himm hdim hr hrpos p =
      normalBundleRadialMap f (r p.proj) p := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  rw [normalBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv,
    PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, Diffeomorph.coe_toEquiv,
    vectorBundleScalarDiffeomorph_apply]
  rw [normalBundleRadialPartialDiffeomorph_apply]
  -- Compare in the ambient product, avoiding dependent equality between normal fibres.
  apply (isEmbedding_totalSpace_normalSubspace (F := F) f).injective
  apply Prod.ext <;> simp

/-- The inverse expands using the radius at the same base point. -/
@[simp] theorem normalBundleRadialPartialDiffeomorphOfRadius_symm_apply
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    (normalBundleRadialPartialDiffeomorphOfRadius hf himm hdim hr hrpos).toPartialEquiv.symm p =
      normalBundleRadialInverse f (r p.proj) p := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  rw [normalBundleRadialPartialDiffeomorphOfRadius_toPartialEquiv,
    PartialEquiv.trans_symm_eq_symm_trans_symm]
  simp only [PartialEquiv.trans_apply, ← Equiv.symm_toPartialEquiv,
    Equiv.toPartialEquiv_apply, Diffeomorph.toEquiv_coe_symm,
    vectorBundleScalarDiffeomorph_symm, vectorBundleScalarDiffeomorph_apply]
  rw [normalBundleRadialPartialDiffeomorph_symm_apply]
  apply (isEmbedding_totalSpace_normalSubspace (F := F) f).injective
  apply Prod.ext <;> simp

end TauCeti
