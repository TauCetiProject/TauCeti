/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Smooth monoid morphisms

Identity, composition, and their laws for bundled smooth multiplicative and additive monoid
morphisms. It also characterizes smooth group homomorphisms by their regularity at the identity.
-/

public section

open Function Manifold
open scoped ContDiff Manifold

namespace ContMDiffMonoidMorphism

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Monoid G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G']

/-- The identity smooth monoid morphism. -/
@[to_additive /-- The identity smooth additive monoid morphism. -/]
def id : ContMDiffMonoidMorphism I I n G G where
  toMonoidHom := MonoidHom.id G
  contMDiff_toFun := contMDiff_id

@[to_additive (attr := simp)]
theorem coe_id : ⇑(id (n := n) (I := I) (G := G)) = _root_.id := (rfl)

/-- Composition of smooth monoid morphisms. -/
@[to_additive /-- Composition of smooth additive monoid morphisms. -/]
def comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Monoid G'']
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'')
    (φ : ContMDiffMonoidMorphism I I' n G G') :
    ContMDiffMonoidMorphism I I'' n G G'' where
  toMonoidHom := ψ.toMonoidHom.comp φ.toMonoidHom
  contMDiff_toFun := ψ.contMDiff_toFun.comp φ.contMDiff_toFun

@[to_additive (attr := simp)]
theorem coe_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Monoid G'']
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'')
    (φ : ContMDiffMonoidMorphism I I' n G G') :
    ⇑(ψ.comp φ) = ⇑ψ ∘ ⇑φ := (rfl)

/-- The identity smooth monoid morphism is a left unit for composition. -/
@[to_additive (attr := simp)
  /-- The identity smooth additive monoid morphism is a left unit for composition. -/]
theorem id_comp (φ : ContMDiffMonoidMorphism I I' n G G') :
    (id (I := I') (G := G')).comp φ = φ := by
  apply DFunLike.coe_injective
  rfl

/-- The identity smooth monoid morphism is a right unit for composition. -/
@[to_additive (attr := simp)
  /-- The identity smooth additive monoid morphism is a right unit for composition. -/]
theorem comp_id (φ : ContMDiffMonoidMorphism I I' n G G') :
    φ.comp (id (I := I) (G := G)) = φ := by
  apply DFunLike.coe_injective
  rfl

/-- Composition of smooth monoid morphisms is associative. -/
@[to_additive (attr := simp) /-- Composition of smooth additive monoid morphisms is associative. -/]
theorem comp_assoc
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Monoid G'']
    {E''' : Type*} [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
    {H''' : Type*} [TopologicalSpace H'''] {I''' : ModelWithCorners 𝕜 E''' H'''}
    {G''' : Type*} [TopologicalSpace G'''] [ChartedSpace H''' G'''] [Monoid G''']
    (χ : ContMDiffMonoidMorphism I'' I''' n G'' G''')
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'')
    (φ : ContMDiffMonoidMorphism I I' n G G') :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by
  apply DFunLike.coe_injective
  rfl

end ContMDiffMonoidMorphism

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G']
  {F : Type*} [FunLike F G G'] [MonoidHomClass F G G']
  {n : ℕ∞ω} [ContMDiffMul I n G] [ContMDiffMul I' n G']

/-- A group homomorphism that is `C^n` at the identity is `C^n` everywhere.

This only requires smooth multiplication: inverses occur at fixed group elements, so the
inversion operation itself need not be smooth. -/
@[to_additive
  /-- An additive group homomorphism that is `C^n` at zero is `C^n` everywhere. -/]
theorem contMDiff_of_contMDiffAt_one (f : F)
    (hf : ContMDiffAt I I' n f 1) : ContMDiff I I' n f := by
  intro x
  have htranslate : ContMDiffAt I I n (fun y : G ↦ x⁻¹ * y) x :=
    contMDiffAt_const.mul contMDiffAt_id
  have hcomp : ContMDiffAt I I' n (fun y : G ↦ f (x⁻¹ * y)) x := by
    -- `comp_of_eq` exposes its composition explicitly, unlike the displayed translated germ.
    change ContMDiffAt I I' n (f ∘ fun y : G ↦ x⁻¹ * y) x
    exact hf.comp_of_eq htranslate (by simp)
  have hmul : ContMDiffAt I I' n (fun y : G ↦ f x * f (x⁻¹ * y)) x :=
    contMDiffAt_const.mul hcomp
  convert hmul using 1
  funext y
  rw [← map_mul]
  simp

end TauCeti
