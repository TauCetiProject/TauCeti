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

Restriction to an open subset takes values in the pullback bundle along the inclusion.
It is linear over the ground field and intertwines multiplication with restriction of
scalar functions. No finite-dimensionality, compactness, or boundary assumption is needed,
and the construction works at every differentiability order.

Multiplication reuses `ContMDiffSection.smulLinearMap`; smoothness of restriction uses
`Bundle.Pullback.contMDiff_iff`.
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

/-- Scalar-valued `C^n` functions act on `C^n` sections by pointwise multiplication. -/
instance instSMulContMDiffMap : SMul C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s ↦ smulLinearMap f s⟩

/-- Evaluation of smooth-function multiplication is fibrewise scalar multiplication. -/
@[simp]
theorem smul_apply (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    (f • s) x = f x • s x := smulLinearMap_apply f s x

/-- The smooth-function action agrees with the existing scalar-localization linear map. -/
theorem smulLinearMap_eq_smul (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    smulLinearMap f s = f • s := (rfl)

/-- Sections form a module over the ring of scalar-valued functions of the same regularity. -/
instance instModuleContMDiffMap : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_add f s t := by ext x; simp [smul_add]
  add_smul f g s := by ext x; simp [add_smul]
  mul_smul f g s := by ext x; simp [mul_smul]
  one_smul s := by ext x; simp
  zero_smul s := by ext x; simp
  smul_zero f := by ext x; simp

/-- Constant scalar functions recover the native ground-field action on sections. -/
@[simp]
theorem const_smul (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) :
    (ContMDiffMap.const (I := I) (I' := 𝓘(𝕜)) (M := M) (n := n) c) • s = c • s := by
  ext x
  exact smul_apply _ s x

/-- Ground-field scalars and smooth scalar functions form a tower on sections. -/
instance instIsScalarTowerContMDiffMap : IsScalarTower 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_assoc c f s := by ext x; simp [mul_smul]

/-- Ground-field multiplication commutes with smooth-function multiplication on sections. -/
instance instSMulCommClassContMDiffMap : SMulCommClass 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_comm c f s := by ext x; simp [smul_comm c (f x)]

end Module

section Restriction

variable [∀ x, Nonempty (V x)]

/-- Restriction of a section to an open subset, in the pullback bundle along its inclusion. -/
def restrict (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ where
  toFun x := s x
  contMDiff_toFun :=
    (Pullback.contMDiff_iff (I' := I)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) contMDiff_subtype_val).2
      ⟨contMDiff_id, s.contMDiff.comp contMDiff_subtype_val⟩

/-- Restriction keeps the value at each point of the open subset. -/
-- Normalize the bundled inclusion in the implicit pullback-fibre type for simplification.
@[simp]
theorem restrict_apply (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (s.restrict U x = s x) := (rfl)

end Restriction

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

@[simp]
theorem restrict_zero (U : Opens M) : (0 : Cₛ^n⟮I; F, V⟯).restrict U = 0 := by
  ext x
  exact rfl

@[simp]
theorem restrict_add (s t : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    (s + t).restrict U = s.restrict U + t.restrict U := by
  ext x
  exact rfl

@[simp]
theorem restrict_smul (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    (c • s).restrict U = c • s.restrict U := by
  ext x
  exact rfl

/-- Restriction intertwines smooth-function multiplication with restriction of functions. -/
@[simp]
theorem restrict_smul_function (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    (f • s).restrict U =
      f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯) • s.restrict U := by
  ext x
  simp only [ContinuousMap.coe_mk, restrict_apply, smul_apply]
  exact congrArg (fun c : 𝕜 ↦ c • s (x : M))
    (ContMDiffMap.comp_apply f
      (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯) x).symm

variable (I F n V) in
/-- Restriction of sections to an open subset as a ground-field linear map. -/
def restrictLinearMap (U : Opens M) :
    Cₛ^n⟮I; F, V⟯ →ₗ[𝕜]
      Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ where
  toFun s := s.restrict U
  map_add' s t := restrict_add s t U
  map_smul' c s := restrict_smul c s U

-- As for `restrict_apply`, normalize the inclusion in the implicit pullback-bundle type.
@[simp]
theorem restrictLinearMap_apply (U : Opens M) (s : Cₛ^n⟮I; F, V⟯) :
    dsimp% only [ContinuousMap.coe_mk]
      (restrictLinearMap I F n V U s = s.restrict U) := (rfl)

end ContMDiffSection
