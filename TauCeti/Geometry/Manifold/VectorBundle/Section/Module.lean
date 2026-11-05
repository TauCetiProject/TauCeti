/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# The smooth-function module of bundle sections

The native `ContMDiffSection` carrier is a module over scalar-valued `ContMDiffMap`s,
with pointwise multiplication. This extends its vector-space structure: constant functions
act by the original scalar action, and the two actions form a scalar tower and commute.
These structures allow function-linear maps on sections, in particular tensorial bundle
operators, to be expressed using the usual `LinearMap` API.

Pullback along a `C^n` map takes values in the pullback bundle. It is linear over the
ground field and intertwines multiplication with composition of scalar functions.
Restriction to an open subset is pullback along its inclusion. No finite-dimensionality,
compactness, or boundary assumption is needed, and the construction works at every
differentiability order.
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

section Module

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- Sections form a module over the ring of scalar-valued functions of the same regularity. -/
instance instModuleContMDiffMap : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_add f s t := by ext x; simp [smul_add]
  add_smul f g s := by ext x; simp [add_smul]
  mul_smul f g s := by ext x; simp [mul_smul]
  one_smul s := by ext x; simp
  zero_smul s := by ext x; simp
  smul_zero f := by ext x; simp

/-- Ground-field scalars and smooth scalar functions form a tower on sections. -/
instance instIsScalarTowerContMDiffMap : IsScalarTower 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_assoc c f s := by ext x; simp [mul_smul]

/-- Ground-field multiplication commutes with smooth-function multiplication on sections. -/
instance instSMulCommClassContMDiffMap : SMulCommClass 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_comm c f s := by ext x; simp [smul_comm c (f x)]

end Module

section Pullback

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

section

variable [∀ x, Nonempty (V x)]

-- Smoothness is checked using `Bundle.Pullback.contMDiff_iff`.
/-- Pull a section back along a `C^n` map, with values in the pullback bundle. -/
def pullback (s : Cₛ^n⟮I; F, V⟯) (g : C^n⟮I', N; I, M⟯) :
    Cₛ^n⟮I'; F, (g : C(N, M)) *ᵖ V⟯ where
  toFun x := s (g x)
  contMDiff_toFun :=
    (Pullback.contMDiff_iff (g : C(N, M)) g.contMDiff).2
      ⟨contMDiff_id, s.contMDiff.comp g.contMDiff⟩

/-- Pullback evaluates the original section at the image point. -/
-- Normalize the continuous-map coercion in the implicit pullback-fibre type.
@[simp]
theorem pullback_apply (s : Cₛ^n⟮I; F, V⟯) (g : C^n⟮I', N; I, M⟯) (x : N) :
    dsimp% only [ContinuousMap.coe_ofClass] (s.pullback g x = s (g x)) := (rfl)

end

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

@[simp]
theorem pullback_zero (g : C^n⟮I', N; I, M⟯) : (0 : Cₛ^n⟮I; F, V⟯).pullback g = 0 := by
  ext x
  exact rfl

@[simp]
theorem pullback_add (s t : Cₛ^n⟮I; F, V⟯) (g : C^n⟮I', N; I, M⟯) :
    (s + t).pullback g = s.pullback g + t.pullback g := by
  ext x
  exact rfl

@[simp]
theorem pullback_smul (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) (g : C^n⟮I', N; I, M⟯) :
    (c • s).pullback g = c • s.pullback g := by
  ext x
  exact rfl

/-- Pullback intertwines smooth-function multiplication with composition of functions. -/
@[simp]
theorem pullback_smul_function (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯)
    (g : C^n⟮I', N; I, M⟯) :
    (f • s).pullback g = f.comp g • s.pullback g := by
  ext x
  simp only [ContinuousMap.coe_ofClass, pullback_apply, smul_apply, ContMDiffMap.comp_apply]
  exact rfl

variable (I F n V) in
/-- Pullback of sections along a `C^n` map as a ground-field linear map. -/
def pullbackLinearMap (g : C^n⟮I', N; I, M⟯) :
    Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] Cₛ^n⟮I'; F, (g : C(N, M)) *ᵖ V⟯ where
  toFun s := s.pullback g
  map_add' s t := pullback_add s t g
  map_smul' c s := pullback_smul c s g

-- As for `pullback_apply`, normalize the implicit pullback-bundle type.
@[simp]
theorem pullbackLinearMap_apply (g : C^n⟮I', N; I, M⟯) (s : Cₛ^n⟮I; F, V⟯) :
    dsimp% only [ContinuousMap.coe_ofClass]
      (pullbackLinearMap I F n V g s = s.pullback g) := (rfl)

end Pullback

section Restriction

variable [∀ x, Nonempty (V x)]

/-- Restriction of a section to an open subset, in the pullback bundle along its inclusion. -/
def restrict (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ :=
  s.pullback (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯)

/-- Restriction keeps the value at each point of the open subset. -/
-- Normalize the bundled inclusion in the implicit pullback-fibre type for simplification.
@[simp]
theorem restrict_apply (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (s.restrict U x = s x) := (rfl)

end Restriction

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

@[simp]
theorem restrict_zero (U : Opens M) : (0 : Cₛ^n⟮I; F, V⟯).restrict U = 0 := by
  exact pullback_zero _

@[simp]
theorem restrict_add (s t : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    (s + t).restrict U = s.restrict U + t.restrict U :=
  pullback_add s t _

@[simp]
theorem restrict_smul (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    (c • s).restrict U = c • s.restrict U :=
  pullback_smul c s _

/-- Restriction intertwines smooth-function multiplication with restriction of functions. -/
@[simp]
theorem restrict_smul_function (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    (f • s).restrict U =
      f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯) • s.restrict U :=
  pullback_smul_function f s _

variable (I F n V) in
/-- Restriction of sections to an open subset as a ground-field linear map. -/
def restrictLinearMap (U : Opens M) :
    Cₛ^n⟮I; F, V⟯ →ₗ[𝕜]
      Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ :=
  pullbackLinearMap I F n V (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯)

-- As for `restrict_apply`, normalize the inclusion in the implicit pullback-bundle type.
@[simp]
theorem restrictLinearMap_apply (U : Opens M) (s : Cₛ^n⟮I; F, V⟯) :
    dsimp% only [ContinuousMap.coe_mk]
      (restrictLinearMap I F n V U s = s.restrict U) := (rfl)

end ContMDiffSection
