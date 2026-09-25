/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SMul

/-!
# Smooth monoid morphisms

Identity, composition, and their laws for bundled smooth multiplicative and additive monoid
morphisms. It also propagates the regularity of multiplicative and additive maps from a group
at any one point to the whole group.
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
  {G' : Type*} [Mul G'] [TopologicalSpace G'] [ChartedSpace H' G']
  {F : Type*} [FunLike F G G'] [MulHomClass F G G']
  {n : ℕ∞ω} [ContMDiffConstSMul I n G G] [ContMDiffConstSMul I' n G' G']

/-- A multiplicative map from a group that is `C^n` at one point is `C^n` everywhere.

This is a smooth generalization of Mathlib's `continuous_of_continuousAt_one`, with regularity
assumed at an arbitrary basepoint.

The map need not preserve an identity. Only the individual left translations on the source
and target must be `C^n`, as expressed by `ContMDiffConstSMul` for multiplication acting on
itself. In particular, smooth multiplication suffices; smooth inversion is not required. -/
@[to_additive
  /-- An additive map from an additive group that is `C^n` at one point is `C^n` everywhere.

  This is a smooth generalization of Mathlib's `continuous_of_continuousAt_zero`, with regularity
  assumed at an arbitrary basepoint.

  The map need not preserve a zero. Only the individual left translations on the source
  and target must be `C^n`, as expressed by `ContMDiffConstVAdd` for addition acting on
  itself. In particular, smooth addition suffices; smooth negation is not required. -/]
theorem contMDiff_of_contMDiffAt_mulHom (f : F) {a : G}
    (hf : ContMDiffAt I I' n f a) : ContMDiff I I' n f := by
  intro x
  have hcomp := hf.comp_of_eq ((contMDiff_const_smul (a * x⁻¹)).contMDiffAt (x := x))
    (by simp [mul_assoc])
  have hmul := hcomp.const_smul (f (x * a⁻¹))
  convert hmul using 1
  funext y
  simp [Function.comp_def, smul_eq_mul, ← map_mul, mul_assoc]

end TauCeti
