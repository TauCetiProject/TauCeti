/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Projection

/-!
# Symmetrization of `C^n` bilinear fields

The transpose of a `C^n` bilinear field is `C^n`. When two is nonzero in the scalar field,
averaging a field with its transpose defines a linear projection onto the symmetric `C^n`
sections. Over the reals this provides a linear ambient space for `C^n` Riemannian metrics,
without choosing an inner product on the original bundle fibres.

The construction uses Mathlib's `ContMDiffSection` of the iterated hom bundle. In bundle
coordinates transposition is the fixed continuous linear isometry
`ContinuousLinearMap.flipₗᵢ`; in particular preservation of regularity is valid in boundary
charts as well.
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω}

variable (IB F V G n) in
/-- `C^n` bilinear fields with values in a normed space on a vector bundle. -/
abbrev BilinearSection :=
  Cₛ^n⟮IB; F →L[𝕜] F →L[𝕜] G, fun x : B ↦ V x →L[𝕜] V x →L[𝕜] G⟯

section Flip

variable [∀ x, IsNormableSpace 𝕜 (V x)]

/-- Fibrewise flip preserves `C^n` regularity at a point. -/
theorem contMDiffAt_flip_section
    {b : ∀ x : B, V x →L[𝕜] V x →L[𝕜] G} {x : B}
    (hb : ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) y (b y)) x) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) y (b y).flip) x := by
  rw [contMDiffAt_section] at hb ⊢
  -- The unbundled bound avoids identifying the normed and seminormed structures on hom spaces.
  have hflip : IsBoundedLinearMap 𝕜 (fun c : F →L[𝕜] F →L[𝕜] G ↦ c.flip) :=
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

/-- Fibrewise flip preserves `C^n` regularity of a bilinear section. -/
theorem contMDiff_flip_section
    {b : ∀ x : B, V x →L[𝕜] V x →L[𝕜] G}
    (hb : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) y (b y))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) x (b x).flip) :=
  fun x ↦ contMDiffAt_flip_section (hb x)

end Flip

/-- Transposition as a linear involution on `C^n` bilinear fields. -/
def transposeBilinearSection :
    BilinearSection IB F V G n →ₗ[𝕜]
      BilinearSection IB F V G n :=
  -- Transfer normability without changing the topology or choosing fibre norms.
  letI : ∀ x, IsNormableSpace 𝕜 (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).isNormableSpace
  { toFun b := ⟨fun x ↦ (b x).flip, contMDiff_flip_section b.contMDiff⟩
    map_add' b c := by ext x v w; simp
    map_smul' a b := by ext x v w; simp }

@[simp]
theorem transposeBilinearSection_apply
    (b : BilinearSection IB F V G n)
    (x : B) (v w : V x) : transposeBilinearSection b x v w = b x w v := by
  -- The term-mode definition evaluates to the fibrewise flip.
  rfl

/-- Transposing a `C^n` bilinear field twice recovers the original field. -/
@[simp]
theorem transposeBilinearSection_transposeBilinearSection
    (b : BilinearSection IB F V G n) :
    transposeBilinearSection (transposeBilinearSection b) = b := by
  ext x v w
  simp

/-- The linear subspace of symmetric `C^n` bilinear fields. -/
def symmetricBilinearSections :
    Submodule 𝕜 (BilinearSection IB F V G n) :=
  LinearMap.ker (transposeBilinearSection - LinearMap.id)

@[simp]
theorem mem_symmetricBilinearSections
    (b : BilinearSection IB F V G n) :
    b ∈ symmetricBilinearSections ↔ ∀ x v w, b x v w = b x w v := by
  simp only [symmetricBilinearSections, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h x v w
    simpa using congrArg (fun c ↦ c x w v) h
  · intro h
    ext x v w
    simpa using h x w v

/-- Transposition fixes every symmetric section. -/
@[simp]
theorem transposeBilinearSection_of_mem
    {b : BilinearSection IB F V G n}
    (hb : b ∈ symmetricBilinearSections) : transposeBilinearSection b = b := by
  simpa only [symmetricBilinearSections, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] using hb

/-- The symmetrization projection `b ↦ (b + bᵀ) / 2` on `C^n` bilinear fields. -/
def symmetrizeBilinearSection :
    BilinearSection IB F V G n →ₗ[𝕜]
      BilinearSection IB F V G n :=
  (2 : 𝕜)⁻¹ • (LinearMap.id + transposeBilinearSection)

@[simp]
theorem symmetrizeBilinearSection_apply
    (b : BilinearSection IB F V G n)
    (x : B) (v w : V x) :
    symmetrizeBilinearSection b x v w = (2 : 𝕜)⁻¹ • (b x v w + b x w v) := by
  simp [symmetrizeBilinearSection]

/-- Symmetrization takes values in the symmetric sections. -/
@[simp↓]
theorem symmetrizeBilinearSection_mem
    (b : BilinearSection IB F V G n) :
    symmetrizeBilinearSection b ∈ symmetricBilinearSections := by
  simp [add_comm]

variable [NeZero (2 : 𝕜)]

/-- The fixed points of symmetrization are exactly the symmetric sections. -/
@[simp]
theorem symmetrizeBilinearSection_eq_self_iff
    (b : BilinearSection IB F V G n) :
    symmetrizeBilinearSection b = b ↔ b ∈ symmetricBilinearSections := by
  constructor
  · intro h
    rw [← h]
    exact symmetrizeBilinearSection_mem b
  · intro h
    ext x v w
    rw [symmetrizeBilinearSection_apply, (mem_symmetricBilinearSections b).mp h x v w]
    rw [← two_smul 𝕜, inv_smul_smul₀ (NeZero.ne (2 : 𝕜))]

/-- Symmetrization fixes every symmetric section. -/
@[simp]
theorem symmetrizeBilinearSection_of_mem
    {b : BilinearSection IB F V G n}
    (hb : b ∈ symmetricBilinearSections) : symmetrizeBilinearSection b = b :=
  (symmetrizeBilinearSection_eq_self_iff b).mpr hb

/-- Symmetrization is a projection onto the submodule of symmetric sections. -/
theorem isProj_symmetrizeBilinearSection :
    LinearMap.IsProj symmetricBilinearSections
      (symmetrizeBilinearSection (IB := IB) (F := F) (V := V) (G := G) (n := n)) where
  map_mem := symmetrizeBilinearSection_mem
  map_id _ hb := symmetrizeBilinearSection_of_mem hb

/-- Every symmetric `C^n` field is the symmetrization of a `C^n` bilinear field. -/
theorem range_symmetrizeBilinearSection :
    LinearMap.range (symmetrizeBilinearSection (IB := IB) (F := F) (V := V) (G := G) (n := n)) =
      symmetricBilinearSections := by
  ext b
  constructor
  · rintro ⟨c, rfl⟩
    exact symmetrizeBilinearSection_mem c
  · intro hb
    exact ⟨b, (symmetrizeBilinearSection_eq_self_iff b).mpr hb⟩

end TauCeti.Manifold
