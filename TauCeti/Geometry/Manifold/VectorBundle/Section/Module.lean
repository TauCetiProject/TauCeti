/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
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

More generally, for a normed field extension `𝕜 ⊆ 𝕜'`, the sections of a `𝕜'`-vector bundle over
a `𝕜`-manifold form a module over the `𝕜'`-valued functions
(`ContMDiffSection.instModuleContMDiffMapOfNormedAlgebra`). This action extends the `𝕜`-valued
function action and the `𝕜'`-scalar action through constant functions, and commutes with pullback
and restriction. For `𝕜 = ℝ` and `𝕜' = ℂ` it makes the sections of a complex bundle over a real
manifold a module over the complex-valued functions.
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

variable (I F n V) in
/-- Evaluation of sections at a point as a ground-field linear map. -/
def evalLinearMap (x : M) : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] V x where
  toFun s := s x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalLinearMap_apply (x : M) (s : Cₛ^n⟮I; F, V⟯) : evalLinearMap I F n V x s = s x :=
  (rfl)

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

/-! ### Functions with values in a normed algebra -/

section NormedAlgebra

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {n : ℕ∞ω} {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜' (V x)] [VectorBundle 𝕜' F V]

/-- Functions with values in a normed algebra `𝕜'` act by pointwise multiplication on the
sections of a `𝕜'`-vector bundle over a `𝕜`-manifold. When `𝕜' = 𝕜`,
`ContMDiffSection.instSMulContMDiffMap` takes precedence; both actions are pointwise. -/
instance (priority := low) instSMulContMDiffMapOfNormedAlgebra :
    SMul C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s ↦ ⟨fun x ↦ f x • s x, f.contMDiff.smul_totalSpace s.contMDiff⟩⟩

/-- Evaluation of the `𝕜'`-valued function action is fibrewise scalar multiplication. -/
@[simp]
theorem smul_apply_of_normedAlgebra (f : C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯) (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    (f • s) x = f x • s x := (rfl)

/-- Constant `𝕜'`-scalars commute with `𝕜'`-valued functions acting on sections. -/
instance instSMulCommClassContMDiffMapOfNormedAlgebra :
    SMulCommClass 𝕜' C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯ Cₛ^n⟮I; F, V⟯ where
  smul_comm c f s := by ext x; simp [smul_comm c (f x)]

/-- A constant `𝕜'`-valued function acts on sections by its value. -/
@[simp]
theorem const_smul_of_normedAlgebra (c : 𝕜') (s : Cₛ^n⟮I; F, V⟯) :
    (ContMDiffMap.const c : C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯) • s = c • s :=
  ext fun _ ↦ (rfl)

section Pullback

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Pullback intertwines the `𝕜'`-valued function action with composition of functions. -/
@[simp]
theorem pullback_smul_function_of_normedAlgebra (f : C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯)
    (s : Cₛ^n⟮I; F, V⟯) (g : C^n⟮I', N; I, M⟯) :
    (f • s).pullback g = f.comp g • s.pullback g := by
  ext x
  simp only [ContinuousMap.coe_ofClass, pullback_apply, smul_apply_of_normedAlgebra,
    ContMDiffMap.comp_apply]
  exact rfl

/-- Restriction intertwines the `𝕜'`-valued function action with restriction of functions. -/
@[simp]
theorem restrict_smul_function_of_normedAlgebra (f : C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯)
    (s : Cₛ^n⟮I; F, V⟯) (U : Opens M) :
    (f • s).restrict U =
      f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯) • s.restrict U :=
  pullback_smul_function_of_normedAlgebra f s _

end Pullback

variable [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- The sections of a `𝕜'`-vector bundle over a `𝕜`-manifold form a module over the ring of
`𝕜'`-valued functions of the same regularity. -/
instance (priority := low) instModuleContMDiffMapOfNormedAlgebra [ContMDiffRing 𝓘(𝕜, 𝕜') n 𝕜'] :
    Module C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯ Cₛ^n⟮I; F, V⟯ where
  one_smul s := by ext x; simp
  mul_smul f g s := by ext x; simp [mul_smul]
  smul_zero f := by ext x; simp
  smul_add f s t := by ext x; simp [smul_add]
  add_smul f g s := by ext x; simp [add_smul]
  zero_smul s := by ext x; simp

/-- Ground-field scalars, acting on `𝕜'`-valued functions, and these functions form a tower on
sections. -/
instance instIsScalarTowerContMDiffMapOfNormedAlgebra [ContMDiffRing 𝓘(𝕜, 𝕜') n 𝕜']
    [∀ x, IsScalarTower 𝕜 𝕜' (V x)] :
    IsScalarTower 𝕜 C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯ Cₛ^n⟮I; F, V⟯ where
  smul_assoc c f s := by ext x; simp

/-- `𝕜`-valued functions, acting on `𝕜'`-valued functions by `ContMDiffMap.instSMul'`, and
`𝕜'`-valued functions form a tower on sections. -/
instance instIsScalarTowerContMDiffMapContMDiffMapOfNormedAlgebra
    [∀ x, IsScalarTower 𝕜 𝕜' (V x)] :
    IsScalarTower C^n⟮I, M; 𝕜⟯ C^n⟮I, M; 𝓘(𝕜, 𝕜'), 𝕜'⟯ Cₛ^n⟮I; F, V⟯ where
  smul_assoc f g s := by
    ext x
    rw [smul_apply_of_normedAlgebra, smul_apply, smul_apply_of_normedAlgebra]
    exact smul_assoc (f x) (g x) (s x)

end NormedAlgebra

end ContMDiffSection
