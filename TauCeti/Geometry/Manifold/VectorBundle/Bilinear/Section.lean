/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Symmetrization of smooth bilinear forms

The transpose of a bilinear form field is smooth. Consequently averaging a field with its
transpose defines a linear projection onto the symmetric smooth sections. This provides a
linear ambient space for smooth Riemannian metrics, without choosing an inner product on
the original bundle fibres.

The construction uses Mathlib's `ContMDiffSection` of the iterated hom bundle. In bundle
coordinates transposition is the fixed continuous linear isometry
`ContinuousLinearMap.flipₗᵢ`; in particular smoothness is valid in boundary charts as well.
No compactness or finite-dimensionality is needed. The fibres are topological vector spaces
isomorphic to the normed model fibre and need not carry chosen norms.
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold Topology

-- Use the normed structures consistently when applying the differentiability API.
attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

namespace TauCeti.Manifold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω}

/-- Smooth bilinear form fields on a real vector bundle. -/
abbrev BilinearSection :=
  Cₛ^n⟮IB; F →L[ℝ] F →L[ℝ] ℝ, fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ⟯

/-- Transposition as a linear involution on smooth bilinear form fields. -/
def transposeBilinearSection :
    BilinearSection (IB := IB) (F := F) (V := V) (n := n) →ₗ[ℝ]
      BilinearSection (IB := IB) (F := F) (V := V) (n := n) := by
  -- Transfer normability without changing the topology or choosing fibre norms.
  letI : ∀ x, IsNormableSpace ℝ (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  refine
    { toFun := fun b ↦ ⟨fun x ↦ (b x).flip, ?_⟩
      map_add' := fun b c ↦ by ext x v w; simp
      map_smul' := fun a b ↦ by ext x v w; simp }
  intro x
  have hb := b.contMDiff x
  rw [contMDiffAt_section] at hb ⊢
  -- The unbundled bound avoids identifying the normed and seminormed structures on hom spaces.
  have hflip : IsBoundedLinearMap ℝ (fun c : F →L[ℝ] F →L[ℝ] ℝ ↦ c.flip) :=
    { map_add := fun c d ↦ by ext v w; simp
      map_smul := fun a c ↦ by ext v w; simp
      bound := ⟨1, by norm_num, fun c ↦ by simp⟩ }
  have h := hflip.contDiff.comp_contMDiffAt hb
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F V x)] with y hy
  ext v w
  simp only [hom_trivializationAt_apply, Function.comp_apply, ContinuousLinearMap.flip_apply]
  rw [inCoordinates_apply_eq₂ hy hy (by simp),
    inCoordinates_apply_eq₂ hy hy (by simp)]
  simp

@[simp]
theorem transposeBilinearSection_apply
    (b : BilinearSection (IB := IB) (F := F) (V := V) (n := n))
    (x : B) (v w : V x) : transposeBilinearSection b x v w = b x w v := by
  have : IsNormableSpace ℝ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  exact ContinuousLinearMap.flip_apply (b x) w v

/-- Transposing a smooth bilinear field twice recovers the original field. -/
@[simp]
theorem transposeBilinearSection_transpose
    (b : BilinearSection (IB := IB) (F := F) (V := V) (n := n)) :
    transposeBilinearSection (transposeBilinearSection b) = b := by
  ext x v w
  simp

/-- The linear subspace of symmetric smooth bilinear forms. -/
def symmetricBilinearSections :
    Submodule ℝ (BilinearSection (IB := IB) (F := F) (V := V) (n := n)) :=
  LinearMap.ker (transposeBilinearSection - LinearMap.id)

@[simp]
theorem mem_symmetricBilinearSections
    (b : BilinearSection (IB := IB) (F := F) (V := V) (n := n)) :
    b ∈ symmetricBilinearSections ↔ ∀ x v w, b x v w = b x w v := by
  simp only [symmetricBilinearSections, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h x v w
    simpa using congrArg (fun c ↦ c x w v) h
  · intro h
    ext x v w
    simpa using h x w v

/-- The symmetrization projection `b ↦ (b + bᵀ) / 2` on smooth bilinear fields. -/
def symmetrizeBilinearSection :
    BilinearSection (IB := IB) (F := F) (V := V) (n := n) →ₗ[ℝ]
      BilinearSection (IB := IB) (F := F) (V := V) (n := n) :=
  (1 / 2 : ℝ) • (LinearMap.id + transposeBilinearSection)

@[simp]
theorem symmetrizeBilinearSection_apply
    (b : BilinearSection (IB := IB) (F := F) (V := V) (n := n))
    (x : B) (v w : V x) :
    symmetrizeBilinearSection b x v w = (b x v w + b x w v) / 2 := by
  simp [symmetrizeBilinearSection, div_eq_mul_inv, mul_comm]
  ring

/-- Symmetrization takes values in the symmetric sections. -/
@[simp↓]
theorem symmetrizeBilinearSection_mem
    (b : BilinearSection (IB := IB) (F := F) (V := V) (n := n)) :
    symmetrizeBilinearSection b ∈ symmetricBilinearSections := by
  simp [add_comm]

/-- The fixed points of symmetrization are exactly the symmetric sections. -/
@[simp]
theorem symmetrizeBilinearSection_eq_self_iff
    (b : BilinearSection (IB := IB) (F := F) (V := V) (n := n)) :
    symmetrizeBilinearSection b = b ↔ b ∈ symmetricBilinearSections := by
  constructor
  · intro h
    rw [← h]
    exact symmetrizeBilinearSection_mem b
  · intro h
    ext x v w
    rw [symmetrizeBilinearSection_apply, (mem_symmetricBilinearSections b).mp h x v w]
    ring

/-- Symmetrization is idempotent. -/
@[simp]
theorem symmetrizeBilinearSection_idem
    (b : BilinearSection (IB := IB) (F := F) (V := V) (n := n)) :
    symmetrizeBilinearSection (symmetrizeBilinearSection b) = symmetrizeBilinearSection b :=
  (symmetrizeBilinearSection_eq_self_iff _).mpr (symmetrizeBilinearSection_mem b)

/-- Every symmetric smooth field is the symmetrization of a smooth bilinear field. -/
theorem range_symmetrizeBilinearSection :
    LinearMap.range (symmetrizeBilinearSection (IB := IB) (F := F) (V := V) (n := n)) =
      symmetricBilinearSections := by
  ext b
  constructor
  · rintro ⟨c, rfl⟩
    exact symmetrizeBilinearSection_mem c
  · intro hb
    exact ⟨b, (symmetrizeBilinearSection_eq_self_iff b).mpr hb⟩

end TauCeti.Manifold
