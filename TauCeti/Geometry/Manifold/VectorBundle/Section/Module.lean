/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.ContMDiffMap.Opens
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Smooth sections as a module over smooth functions

The `C^n` sections `Cₛ^n⟮I; F, V⟯` of a `C^n` vector bundle `V → M` form a module over the ring
`C^n⟮I, M; 𝕜⟯` of `C^n` scalar functions, acting by pointwise multiplication
`(f • s) x = f x • s x`. Tensorial operations on sections are linear over this ring, and
differential operators are characterised by their commutators with multiplication by functions.

The action is compatible with the native `𝕜`-module structure of sections: the scalar tower
`𝕜 → C^n⟮I, M; 𝕜⟯ → Cₛ^n⟮I; F, V⟯` commutes, the two actions commute, and a constant function
acts as the corresponding scalar.

Sections pull back along `C^n` maps `g : M' → M` to sections of the pullback bundle `g *ᵖ V`.
Pullback is `𝕜`-linear and sends `f • s` to `(f ∘ g) • (s ∘ g)`. Along the inclusion
`ContMDiffMap.subtypeVal U` of an open set it is the restriction of sections to `U`, which
therefore respects the function-module structure.

## Main definitions

* `ContMDiffSection.module'`: the `C^n⟮I, M; 𝕜⟯`-module structure on `Cₛ^n⟮I; F, V⟯`.
* `ContMDiffSection.pullback`: the pullback of a section along a `C^n` map, as a `𝕜`-linear map;
  along `ContMDiffMap.subtypeVal U` it restricts sections to the open set `U`.
-/

public section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

section Module

/-- `C^n` scalar functions act on `C^n` sections by pointwise multiplication. -/
instance instSMul' : SMul C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s ↦ ⟨fun x ↦ f x • s x, f.contMDiff.smul_section s.contMDiff⟩⟩

/-- Coercion to a function for a scalar function multiplying a section (as opposed to
`ContMDiffSection.coe_smul`, which is multiplication by a constant scalar). -/
@[simp]
theorem coe_smul' (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) : ⇑(f • s) = ⇑f • ⇑s :=
  rfl

/-- Evaluation of a scalar function multiplying a section (as opposed to
`ContMDiffSection.coe_smul`, which is multiplication by a constant scalar). -/
theorem smul_apply' (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) (x : M) : (f • s) x = f x • s x :=
  rfl

/-- The `C^n` sections of a `C^n` vector bundle form a module over the `C^n` scalar functions. -/
instance module' : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_add f s t := by ext x; exact smul_add (f x) (s x) (t x)
  add_smul f g s := by ext x; exact add_smul (f x) (g x) (s x)
  mul_smul f g s := by ext x; exact mul_smul (f x) (g x) (s x)
  one_smul s := by ext x; exact one_smul 𝕜 (s x)
  zero_smul s := by ext x; exact zero_smul 𝕜 (s x)
  smul_zero f := by ext x; exact smul_zero (f x)

instance : IsScalarTower 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_assoc c f s := by ext x; exact smul_assoc c (f x) (s x)

instance : SMulCommClass 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_comm c f s := by ext x; exact smul_comm c (f x) (s x)

instance : SMulCommClass C^n⟮I, M; 𝕜⟯ 𝕜 Cₛ^n⟮I; F, V⟯ :=
  .symm _ _ _

/-- A constant function acts on sections as the corresponding scalar. -/
@[simp]
theorem contMDiffMap_const_smul (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) :
    (ContMDiffMap.const c : C^n⟮I, M; 𝕜⟯) • s = c • s :=
  rfl

end Module

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- The pullback of a `C^n` section `s` of `V` along a `C^n` map `g : M' → M`: the `C^n` section
`y ↦ s (g y)` of the pullback bundle `g *ᵖ V`. -/
def pullback (g : C^n⟮I', M'; I, M⟯) :
    Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] Cₛ^n⟮I'; F, (g : M' → M) *ᵖ V⟯ where
  toFun s := ⟨fun y ↦ s (g y),
    (Pullback.contMDiff_iff g g.contMDiff).2 ⟨contMDiff_id, s.contMDiff.comp g.contMDiff⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pullback_apply (g : C^n⟮I', M'; I, M⟯) (s : Cₛ^n⟮I; F, V⟯) (y : M') :
    pullback g s y = s (g y) :=
  (rfl)

/-- Pulling back the product of a scalar function and a section gives the product of the
pulled-back function and the pulled-back section. -/
@[simp]
theorem pullback_smul' (g : C^n⟮I', M'; I, M⟯) (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    pullback g (f • s) = f.comp g • pullback g s :=
  (rfl)

/-- The restriction of a section to an open set `U`, its pullback along the inclusion
`ContMDiffMap.subtypeVal U`, takes the value of the section at each point of `U`. -/
theorem pullback_subtypeVal_apply (U : Opens M) (s : Cₛ^n⟮I; F, V⟯) (x : U) :
    pullback (ContMDiffMap.subtypeVal U : C^n⟮I, U; I, M⟯) s x = s x :=
  (rfl)

end Pullback

end ContMDiffSection
