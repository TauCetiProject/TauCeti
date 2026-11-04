/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.ContMDiffMap.Opens
public import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Sections of a vector bundle as a module over smooth functions

The `C^n` sections `Cₛ^n⟮I; F, V⟯` of a vector bundle `V → M` form a module over the ring
`C^n⟮I, M; 𝕜⟯` of `C^n` scalar functions, acting by pointwise multiplication
`(f • s) x = f x • s x`. This is the module of sections on which differential operators, jets and
derivations of vector bundles are built. Mathlib provides only the `𝕜`-module structure on
`Cₛ^n⟮I; F, V⟯` and the `C^n⟮I, M; 𝕜⟯`-module structure on vector-valued functions
`C^n⟮I, M; 𝓘(𝕜, V), V⟯` (`ContMDiffMap.module'`); this file supplies the corresponding structure
for sections of an arbitrary vector bundle.

Constant functions act through the native `𝕜`-scalar action, so `𝕜`, `C^n⟮I, M; 𝕜⟯` and the
sections form a scalar tower, and the two actions commute.

Sections pull back along `C^n` maps: a section `s` of `V` and a `C^n` map `f : M' → M` give the
section `y ↦ s (f y)` of the pullback bundle `f *ᵖ V`. Pullback is `𝕜`-linear and carries the
action of a function `g` to the action of `g ∘ f`. Pulling back along the inclusion
`ContMDiffMap.subtypeVal I n U` of an open subset `U` restricts sections to `U`
(`ContMDiffSection.pullback_subtypeVal_apply`), and the restriction of `g • s` is the restriction of
`g` acting on the restriction of `s`.

## Main declarations

* `ContMDiffSection.instModule'`: `Cₛ^n⟮I; F, V⟯` is a `C^n⟮I, M; 𝕜⟯`-module.
* `ContMDiffSection.smul_apply'`: the evaluation formula `(f • s) x = f x • s x`.
* `ContMDiffSection.const_smul_eq_smul`: constant functions act through the `𝕜`-scalar action.
* `ContMDiffSection.pullback`: pullback of sections along a `C^n` map, as a `𝕜`-linear map.
* `ContMDiffSection.pullback_smul'`: pullback carries `g • s` to `(g ∘ f) • (pullback f s)`.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- `C^n` scalar functions act on `C^n` sections by pointwise multiplication. -/
instance instSMul' : SMul C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s ↦ ⟨fun x ↦ f x • s x, f.contMDiff.smul_section s.contMDiff⟩⟩

@[simp]
theorem coe_smul' (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) : ⇑(f • s) = ⇑f • ⇑s :=
  rfl

theorem smul_apply' (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    (f • s) x = f x • s x :=
  rfl

/-- The `C^n` sections of a vector bundle form a module over the `C^n` scalar functions. -/
instance instModule' : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  one_smul s := ext fun x ↦ one_smul 𝕜 (s x)
  mul_smul f g s := ext fun x ↦ mul_smul (f x) (g x) (s x)
  smul_zero f := ext fun x ↦ smul_zero (f x)
  smul_add f s t := ext fun x ↦ smul_add (f x) (s x) (t x)
  add_smul f g s := ext fun x ↦ add_smul (f x) (g x) (s x)
  zero_smul s := ext fun x ↦ zero_smul 𝕜 (s x)

/-- A constant function acts on sections through the `𝕜`-scalar action. -/
@[simp]
theorem const_smul_eq_smul (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) :
    (ContMDiffMap.const c : C^n⟮I, M; 𝕜⟯) • s = c • s :=
  rfl

/-- The `𝕜`-scalar action factors through the constant functions. -/
instance instIsScalarTower : IsScalarTower 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_assoc c f s := ext fun x ↦ smul_assoc c (f x) (s x)

/-- The `𝕜`-scalar action commutes with the action of functions. -/
instance instSMulCommClass : SMulCommClass 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  smul_comm c f s := ext fun x ↦ smul_comm c (f x) (s x)

/-- The action of functions commutes with the `𝕜`-scalar action. -/
instance instSMulCommClass' : SMulCommClass C^n⟮I, M; 𝕜⟯ 𝕜 Cₛ^n⟮I; F, V⟯ :=
  .symm _ _ _

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- The pullback of a `C^n` section `s` of `V` along a `C^n` map `f`: the section `y ↦ s (f y)`
of the pullback bundle `f *ᵖ V`. -/
def pullback (f : C^n⟮I', M'; I, M⟯) :
    Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] Cₛ^n⟮I'; F, (f : M' → M) *ᵖ V⟯ where
  toFun s :=
    ⟨fun y ↦ s (f y), (Pullback.contMDiff_iff f f.contMDiff).2
      ⟨contMDiff_id, s.contMDiff.comp f.contMDiff⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pullback_apply (f : C^n⟮I', M'; I, M⟯) (s : Cₛ^n⟮I; F, V⟯) (y : M') :
    pullback f s y = s (f y) :=
  (rfl)

/-- Pulling back along `f` carries the action of a function `g` to the action of `g ∘ f`. -/
@[simp]
theorem pullback_smul' (f : C^n⟮I', M'; I, M⟯) (g : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    pullback f (g • s) = g.comp f • pullback f s :=
  ext fun _ ↦ (rfl)

/-- Pulling back along the inclusion of an open subset restricts a section to that subset. -/
-- Higher priority than `pullback_apply`, whose output `s (subtypeVal I n U x)` sits in a dependent
-- position where `ContMDiffMap.coe_subtypeVal` cannot rewrite it to `s x`.
@[simp high]
theorem pullback_subtypeVal_apply (U : TopologicalSpace.Opens M) (s : Cₛ^n⟮I; F, V⟯) (x : U) :
    pullback (ContMDiffMap.subtypeVal I n U) s x = s x :=
  (rfl)

end Pullback

end ContMDiffSection
