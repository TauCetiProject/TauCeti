/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import TauCeti.Geometry.Manifold.Algebra.SMul

/-!
# Smooth monoid morphisms

Identity, composition, product projections, and their laws for bundled smooth multiplicative and
additive monoid morphisms. It also propagates the regularity of multiplicative and additive maps
from a group at any one point to the whole group.

The projections `ContMDiffMonoidMorphism.fst` and `ContMDiffMonoidMorphism.snd` have coercion
formulas `ContMDiffMonoidMorphism.coe_fst` and `ContMDiffMonoidMorphism.coe_snd`, and underlying
monoid homomorphisms `MonoidHom.fst` and `MonoidHom.snd`
(`ContMDiffMonoidMorphism.toMonoidHom_fst`, `ContMDiffMonoidMorphism.toMonoidHom_snd`). The
corresponding additive declarations are `ContMDiffAddMonoidMorphism.fst`,
`ContMDiffAddMonoidMorphism.snd`, `ContMDiffAddMonoidMorphism.coe_fst`,
`ContMDiffAddMonoidMorphism.coe_snd`, `ContMDiffAddMonoidMorphism.toAddMonoidHom_fst`, and
`ContMDiffAddMonoidMorphism.toAddMonoidHom_snd`.

The inclusions `ContMDiffMonoidMorphism.inl` and `ContMDiffMonoidMorphism.inr` of the two factors
are smooth monoid morphisms into the product. Two smooth monoid morphisms with commuting images
multiply to a smooth monoid morphism out of the product, `ContMDiffMonoidMorphism.noncommCoprod`,
which restricts to them along the inclusions.
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

@[to_additive (attr := simp)]
theorem coe_one : ⇑(1 : ContMDiffMonoidMorphism I I' n G G') = fun _ ↦ 1 := (rfl)

/-- The first projection as a smooth monoid morphism. -/
@[to_additive /-- The first projection as a smooth additive monoid morphism. -/]
def fst : ContMDiffMonoidMorphism (I.prod I') I n (G × G') G where
  toMonoidHom := MonoidHom.fst G G'
  contMDiff_toFun := contMDiff_fst

@[to_additive (attr := simp)]
theorem coe_fst : ⇑(fst (I := I) (I' := I') (n := n) (G := G) (G' := G')) = Prod.fst := by
  rfl

@[to_additive (attr := simp)]
theorem toMonoidHom_fst :
    (fst (I := I) (I' := I') (n := n) (G := G) (G' := G')).toMonoidHom = MonoidHom.fst G G' := by
  rfl

/-- The second projection as a smooth monoid morphism. -/
@[to_additive /-- The second projection as a smooth additive monoid morphism. -/]
def snd : ContMDiffMonoidMorphism (I.prod I') I' n (G × G') G' where
  toMonoidHom := MonoidHom.snd G G'
  contMDiff_toFun := contMDiff_snd

@[to_additive (attr := simp)]
theorem coe_snd : ⇑(snd (I := I) (I' := I') (n := n) (G := G) (G' := G')) = Prod.snd := by
  rfl

@[to_additive (attr := simp)]
theorem toMonoidHom_snd :
    (snd (I := I) (I' := I') (n := n) (G := G) (G' := G')).toMonoidHom = MonoidHom.snd G G' := by
  rfl

/-- The first inclusion `g ↦ (g, 1)` as a smooth monoid morphism. -/
@[to_additive /-- The first inclusion `g ↦ (g, 0)` as a smooth additive monoid morphism. -/]
def inl : ContMDiffMonoidMorphism I (I.prod I') n G (G × G') where
  toMonoidHom := MonoidHom.inl G G'
  contMDiff_toFun := contMDiff_id.prodMk contMDiff_const

@[to_additive (attr := simp)]
theorem coe_inl : ⇑(inl (I := I) (I' := I') (n := n) (G := G) (G' := G')) = fun g ↦ (g, 1) :=
  (rfl)

/-- The second inclusion `g' ↦ (1, g')` as a smooth monoid morphism. -/
@[to_additive /-- The second inclusion `g' ↦ (0, g')` as a smooth additive monoid morphism. -/]
def inr : ContMDiffMonoidMorphism I' (I.prod I') n G' (G × G') where
  toMonoidHom := MonoidHom.inr G G'
  contMDiff_toFun := contMDiff_const.prodMk contMDiff_id

@[to_additive (attr := simp)]
theorem coe_inr : ⇑(inr (I := I) (I' := I') (n := n) (G := G) (G' := G')) = fun g' ↦ (1, g') :=
  (rfl)

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

@[to_additive (attr := simp)]
theorem fst_comp_inl :
    (fst (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inl = id :=
  (rfl)

@[to_additive (attr := simp)]
theorem fst_comp_inr :
    (fst (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inr = 1 :=
  (rfl)

@[to_additive (attr := simp)]
theorem snd_comp_inl :
    (snd (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inl = 1 :=
  (rfl)

@[to_additive (attr := simp)]
theorem snd_comp_inr :
    (snd (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inr = id :=
  (rfl)

section NoncommCoprod

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Monoid G''] [ContMDiffMul I'' n G'']

/-- The product `(g, g') ↦ φ g * ψ g'` of two smooth monoid morphisms with commuting images, as a
smooth monoid morphism out of the product: the smooth form of `MonoidHom.noncommCoprod`. -/
@[to_additive /-- The sum `(g, g') ↦ φ g + ψ g'` of two smooth additive monoid morphisms with
commuting images, as a smooth additive monoid morphism out of the product: the smooth form of
`AddMonoidHom.noncommCoprod`. -/]
def noncommCoprod (φ : ContMDiffMonoidMorphism I I'' n G G'')
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'') (h : ∀ g g', Commute (φ g) (ψ g')) :
    ContMDiffMonoidMorphism (I.prod I') I'' n (G × G') G'' where
  toMonoidHom := φ.toMonoidHom.noncommCoprod ψ.toMonoidHom h
  contMDiff_toFun :=
    (φ.contMDiff_toFun.comp contMDiff_fst).mul (ψ.contMDiff_toFun.comp contMDiff_snd)

@[to_additive (attr := simp)]
theorem noncommCoprod_apply (φ : ContMDiffMonoidMorphism I I'' n G G'')
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'') (h : ∀ g g', Commute (φ g) (ψ g'))
    (p : G × G') : φ.noncommCoprod ψ h p = φ p.1 * ψ p.2 :=
  (rfl)

@[to_additive (attr := simp)]
theorem noncommCoprod_comp_inl (φ : ContMDiffMonoidMorphism I I'' n G G'')
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'') (h : ∀ g g', Commute (φ g) (ψ g')) :
    (φ.noncommCoprod ψ h).comp inl = φ :=
  DFunLike.ext _ _ fun g ↦ by
    simp only [coe_comp, Function.comp_apply, coe_inl, noncommCoprod_apply, map_one, mul_one]

@[to_additive (attr := simp)]
theorem noncommCoprod_comp_inr (φ : ContMDiffMonoidMorphism I I'' n G G'')
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'') (h : ∀ g g', Commute (φ g) (ψ g')) :
    (φ.noncommCoprod ψ h).comp inr = ψ :=
  DFunLike.ext _ _ fun g' ↦ by
    simp only [coe_comp, Function.comp_apply, coe_inr, noncommCoprod_apply, map_one, one_mul]

end NoncommCoprod

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
