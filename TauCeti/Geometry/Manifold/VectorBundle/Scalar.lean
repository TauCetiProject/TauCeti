/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth scalar rescaling of vector bundles

Multiplying a vector in a bundle by a smooth scalar preserves smoothness even when its base
point varies. A nowhere-zero scalar function on the base therefore defines a diffeomorphism
of the total space, with inverse given by reciprocal multiplication. This construction fixes
the zero section and preserves the projection, without a choice of global trivialization.

For normal bundles, positive rescaling converts unit-radius fibre coordinates to a radius
varying over the submanifold. It is the rescaling step in the variable-radius tubular
neighbourhood construction of J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
Theorem 6.24.
-/

public section

open Bundle Filter Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

/-- Multiplying a bundle-valued map by a scalar-valued map preserves `C^n` regularity within
a set at a point. The base point of the bundle-valued map may vary. -/
theorem ContMDiffWithinAt.smul_totalSpace {a : M → 𝕜} {g : M → TotalSpace F V}
    {s : Set M} {x : M} (ha : ContMDiffWithinAt J 𝓘(𝕜) n a s x)
    (hg : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F)) n g s x) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F)) n
      (fun y => (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace F V)) s x := by
  obtain ⟨hb, hv⟩ := Bundle.contMDiffWithinAt_totalSpace.mp hg
  refine Bundle.contMDiffWithinAt_totalSpace.mpr ⟨hb, ?_⟩
  let e := trivializationAt F V (g x).proj
  have he : ∀ᶠ y in 𝓝[s] x, (g y).proj ∈ e.baseSet :=
    hb.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V (g x).proj))
  refine (ha.smul hv).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [he] with y hy
    exact (e.linear 𝕜 hy).map_smul (a y) (g y).2
  · exact (e.linear 𝕜 (mem_baseSet_trivializationAt F V (g x).proj)).map_smul
      (a x) (g x).2

/-- Multiplying a bundle-valued map by a scalar-valued map preserves `C^n` regularity at
a point, with the base point of the vector allowed to vary. -/
theorem ContMDiffAt.smul_totalSpace {a : M → 𝕜} {g : M → TotalSpace F V} {x : M}
    (ha : ContMDiffAt J 𝓘(𝕜) n a x)
    (hg : ContMDiffAt J (I.prod 𝓘(𝕜, F)) n g x) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F)) n
      (fun y => (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace F V)) x := by
  rw [← contMDiffWithinAt_univ]
  exact ha.contMDiffWithinAt.smul_totalSpace hg.contMDiffWithinAt

/-- Multiplying a bundle-valued map by a scalar-valued map preserves `C^n` regularity
on a set. -/
theorem ContMDiffOn.smul_totalSpace {a : M → 𝕜} {g : M → TotalSpace F V} {s : Set M}
    (ha : ContMDiffOn J 𝓘(𝕜) n a s) (hg : ContMDiffOn J (I.prod 𝓘(𝕜, F)) n g s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F)) n
      (fun y => (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace F V)) s :=
  fun x hx => (ha x hx).smul_totalSpace (hg x hx)

/-- Multiplying a bundle-valued map by a scalar-valued map preserves `C^n` regularity. -/
theorem ContMDiff.smul_totalSpace {a : M → 𝕜} {g : M → TotalSpace F V}
    (ha : ContMDiff J 𝓘(𝕜) n a) (hg : ContMDiff J (I.prod 𝓘(𝕜, F)) n g) :
    ContMDiff J (I.prod 𝓘(𝕜, F)) n
      (fun y => (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace F V)) := by
  intro x
  rw [← contMDiffWithinAt_univ]
  exact (ha x).contMDiffWithinAt.smul_totalSpace (hg x).contMDiffWithinAt

namespace TauCeti

/-- A nowhere-zero `C^n` scalar function on the base rescales each fibre by a `C^n`
diffeomorphism of the total space. Its inverse multiplies by the reciprocal scalar. -/
def vectorBundleScalarDiffeomorph (a : B → 𝕜) (ha : ContMDiff I 𝓘(𝕜) n a)
    (ha0 : ∀ b, a b ≠ 0) :
    TotalSpace F V ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯ TotalSpace F V where
  toFun p := ⟨p.proj, a p.proj • p.2⟩
  invFun p := ⟨p.proj, (a p.proj)⁻¹ • p.2⟩
  left_inv p := by cases p; simp [smul_smul, ha0]
  right_inv p := by cases p; simp [smul_smul, ha0]
  contMDiff_toFun := (ha.comp (Bundle.contMDiff_proj V)).smul_totalSpace contMDiff_id
  contMDiff_invFun := ((ha.inv₀ ha0).comp (Bundle.contMDiff_proj V)).smul_totalSpace
    contMDiff_id

/-- Scalar rescaling acts fibrewise by the given scalar. -/
@[simp]
theorem vectorBundleScalarDiffeomorph_apply (a : B → 𝕜) (ha : ContMDiff I 𝓘(𝕜) n a)
    (ha0 : ∀ b, a b ≠ 0) (p : TotalSpace F V) :
    vectorBundleScalarDiffeomorph a ha ha0 p = ⟨p.proj, a p.proj • p.2⟩ := (rfl)

/-- Rescaling by the constant one function is the identity diffeomorphism. -/
@[simp]
theorem vectorBundleScalarDiffeomorph_one :
    vectorBundleScalarDiffeomorph (F := F) (V := V) (fun _ => (1 : 𝕜))
      (contMDiff_const (I := I) (n := n)) (fun _ => one_ne_zero) =
      Diffeomorph.refl (I.prod 𝓘(𝕜, F)) (TotalSpace F V) n := by
  apply Diffeomorph.ext
  rintro ⟨b, v⟩
  simp

/-- Successive fibre rescalings multiply the scalar functions on the base. -/
theorem vectorBundleScalarDiffeomorph_trans (a b : B → 𝕜)
    (ha : ContMDiff I 𝓘(𝕜) n a) (hb : ContMDiff I 𝓘(𝕜) n b)
    (ha0 : ∀ x, a x ≠ 0) (hb0 : ∀ x, b x ≠ 0) :
    (vectorBundleScalarDiffeomorph (F := F) (V := V) a ha ha0).trans
      (vectorBundleScalarDiffeomorph b hb hb0) =
      vectorBundleScalarDiffeomorph (fun x => b x * a x)
        ((hb.smul ha).congr fun x => smul_eq_mul (b x) (a x))
        (fun x => mul_ne_zero (hb0 x) (ha0 x)) := by
  apply Diffeomorph.ext
  intro p
  simp [Diffeomorph.coe_trans, smul_smul]

/-- The inverse rescaling is the rescaling associated to the reciprocal function. -/
@[simp]
theorem vectorBundleScalarDiffeomorph_symm (a : B → 𝕜)
    (ha : ContMDiff I 𝓘(𝕜) n a) (ha0 : ∀ b, a b ≠ 0) :
    (vectorBundleScalarDiffeomorph (F := F) (V := V) a ha ha0).symm =
      vectorBundleScalarDiffeomorph (fun b => (a b)⁻¹) (ha.inv₀ ha0)
        (fun b => inv_ne_zero (ha0 b)) := by
  exact Diffeomorph.ext fun _ => rfl

section Norm

variable [∀ b, Norm (V b)] [∀ b, NormSMulClass 𝕜 (V b)]

/-- Rescaling sends a variable-radius open ball bundle to the open ball bundle whose radii
are multiplied by the norms of the scalars. No positivity assumption on the old radii is needed. -/
theorem vectorBundleScalarDiffeomorph_image_setOf_norm_lt (a : B → 𝕜)
    (ha : ContMDiff I 𝓘(𝕜) n a) (ha0 : ∀ b, a b ≠ 0) (r : B → ℝ) :
    vectorBundleScalarDiffeomorph (F := F) (V := V) a ha ha0 ''
        {p : TotalSpace F V | ‖p.2‖ < r p.proj} =
      {p : TotalSpace F V | ‖p.2‖ < ‖a p.proj‖ * r p.proj} := by
  rw [Diffeomorph.image_eq_preimage_symm]
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, vectorBundleScalarDiffeomorph_symm,
    vectorBundleScalarDiffeomorph_apply,
    norm_smul, norm_inv]
  exact inv_mul_lt_iff₀ (norm_pos_iff.mpr (ha0 p.proj))

/-- Rescaling sends closed ball bundles to closed ball bundles with rescaled radii. -/
theorem vectorBundleScalarDiffeomorph_image_setOf_norm_le (a : B → 𝕜)
    (ha : ContMDiff I 𝓘(𝕜) n a) (ha0 : ∀ b, a b ≠ 0) (r : B → ℝ) :
    vectorBundleScalarDiffeomorph (F := F) (V := V) a ha ha0 ''
        {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} =
      {p : TotalSpace F V | ‖p.2‖ ≤ ‖a p.proj‖ * r p.proj} := by
  rw [Diffeomorph.image_eq_preimage_symm]
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, vectorBundleScalarDiffeomorph_symm,
    vectorBundleScalarDiffeomorph_apply,
    norm_smul, norm_inv]
  exact inv_mul_le_iff₀ (norm_pos_iff.mpr (ha0 p.proj))

/-- Rescaling sends sphere bundles to sphere bundles with rescaled radii. -/
theorem vectorBundleScalarDiffeomorph_image_setOf_norm_eq (a : B → 𝕜)
    (ha : ContMDiff I 𝓘(𝕜) n a) (ha0 : ∀ b, a b ≠ 0) (r : B → ℝ) :
    vectorBundleScalarDiffeomorph (F := F) (V := V) a ha ha0 ''
        {p : TotalSpace F V | ‖p.2‖ = r p.proj} =
      {p : TotalSpace F V | ‖p.2‖ = ‖a p.proj‖ * r p.proj} := by
  rw [Diffeomorph.image_eq_preimage_symm]
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, vectorBundleScalarDiffeomorph_symm,
    vectorBundleScalarDiffeomorph_apply,
    norm_smul, norm_inv]
  exact inv_mul_eq_iff_eq_mul₀ (norm_ne_zero_iff.mpr (ha0 p.proj))

end Norm

end TauCeti
