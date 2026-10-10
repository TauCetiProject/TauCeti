/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Sequence
public import TauCeti.CategoryTheory.Preadditive.Radical.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Almost-split sequences and irreducible morphism spaces

For an almost-split sequence `0 → A → B → C → 0`, composition with `B → C` identifies
`Hom(X, B) / rad(X, B)` with `Irr(X, C)`. Dually, composition with `A → B` identifies
`Hom(B, X) / rad(B, X)` with `Irr(A, X)`. These identifications compute the dimensions of
irreducible morphism spaces from the middle term of an almost-split sequence.

The results require local endomorphism rings at the two ends, as in a Krull–Schmidt category.
The tested object `X` need not be indecomposable. No finiteness or field assumption is needed
for the linear equivalences.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), V.5 and VII.1.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

namespace CategoryTheory.ShortComplex.IsAlmostSplit

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
  {S : ShortComplex C}
  [IsLocalRing (End S.X₁)] [IsLocalRing (End S.X₃)]

/-- In an almost-split sequence, composition with its final map lies in the square of the
radical exactly when the original morphism into the middle term is radical. -/
theorem comp_g_mem_jacobsonRadicalSq_iff (hS : S.IsAlmostSplit) {X : C} (a : X ⟶ S.X₂) :
    a ≫ S.g ∈ jacobsonRadicalSq X S.X₃ ↔ a ∈ jacobsonRadical X S.X₂ := by
  have hf := mem_jacobsonRadical_iff_not_isSplitMono.mpr hS.isLeftAlmostSplit_f.not_isSplitMono
  have hg := mem_jacobsonRadical_iff_not_isSplitEpi.mpr hS.isRightAlmostSplit_g.not_isSplitEpi
  refine ⟨fun ha ↦ ?_, fun ha ↦ comp_mem_jacobsonRadicalSq ha hg⟩
  let F := Preadditive.rightComp X S.g
  have hle : jacobsonRadicalSq X S.X₃ ≤ (jacobsonRadical X S.X₂).map F := by
    apply jacobsonRadicalSq_le_iff.mpr
    intro Y b c hb hc
    obtain ⟨d, hd⟩ := hS.isRightAlmostSplit_g.factors Y c
      (mem_jacobsonRadical_iff_not_isSplitEpi.mp hc)
    exact ⟨b ≫ d, comp_mem_jacobsonRadical_right hb d, by simp [F, Preadditive.rightComp, hd]⟩
  obtain ⟨b, hb, heq⟩ := AddSubgroup.mem_map.mp (hle ha)
  have hz : (a - b) ≫ S.g = 0 := by
    simp only [F, Preadditive.rightComp, AddMonoidHom.mk'_apply, Preadditive.sub_comp] at heq ⊢
    exact sub_eq_zero.mpr heq.symm
  have := hS.shortExact.mono_f
  obtain ⟨e, he⟩ := hS.shortExact.exact.lift' (a - b) hz
  have hrad := comp_mem_jacobsonRadical_left e hf
  rw [he] at hrad
  simpa only [sub_add_cancel] using add_mem hrad hb

/-- In an almost-split sequence, precomposition with its initial map lies in the square of
the radical exactly when the original morphism out of the middle term is radical. -/
theorem f_comp_mem_jacobsonRadicalSq_iff (hS : S.IsAlmostSplit) {X : C} (a : S.X₂ ⟶ X) :
    S.f ≫ a ∈ jacobsonRadicalSq S.X₁ X ↔ a ∈ jacobsonRadical S.X₂ X := by
  have hf := mem_jacobsonRadical_iff_not_isSplitMono.mpr hS.isLeftAlmostSplit_f.not_isSplitMono
  have hg := mem_jacobsonRadical_iff_not_isSplitEpi.mpr hS.isRightAlmostSplit_g.not_isSplitEpi
  refine ⟨fun ha ↦ ?_, fun ha ↦ comp_mem_jacobsonRadicalSq hf ha⟩
  let F := Preadditive.leftComp X S.f
  have hle : jacobsonRadicalSq S.X₁ X ≤ (jacobsonRadical S.X₂ X).map F := by
    apply jacobsonRadicalSq_le_iff.mpr
    intro Y b c hb hc
    obtain ⟨d, hd⟩ := hS.isLeftAlmostSplit_f.factors Y b
      (mem_jacobsonRadical_iff_not_isSplitMono.mp hb)
    exact ⟨d ≫ c, comp_mem_jacobsonRadical_left d hc, by
      simp [F, Preadditive.leftComp, ← Category.assoc, hd]⟩
  obtain ⟨b, hb, heq⟩ := AddSubgroup.mem_map.mp (hle ha)
  have hz : S.f ≫ (a - b) = 0 := by
    simp only [F, Preadditive.leftComp, AddMonoidHom.mk'_apply, Preadditive.comp_sub] at heq ⊢
    exact sub_eq_zero.mpr heq.symm
  have := hS.shortExact.epi_g
  obtain ⟨e, he⟩ := hS.shortExact.exact.desc' (a - b) hz
  have hrad := comp_mem_jacobsonRadical_right hg e
  rw [he] at hrad
  simpa only [sub_add_cancel] using add_mem hrad hb

variable (k : Type*) [Ring k] [Linear k C]

private def rightRadicalMap (hS : S.IsAlmostSplit) (X : C) :
    (X ⟶ S.X₂) →ₗ[k] irreducibleMorphismSpace k X S.X₃ :=
  irreducibleMorphismMk k X S.X₃ ∘ₗ
    (Linear.rightComp k X S.g).codRestrict (jacobsonRadicalSubmodule k X S.X₃)
      (fun a ↦ mem_jacobsonRadicalSubmodule.mpr (comp_mem_jacobsonRadical_left a
        (mem_jacobsonRadical_iff_not_isSplitEpi.mpr hS.isRightAlmostSplit_g.not_isSplitEpi)))

private theorem rightRadicalMap_ker (hS : S.IsAlmostSplit) (X : C) :
    LinearMap.ker (rightRadicalMap k hS X) = jacobsonRadicalSubmodule k X S.X₂ := by
  ext a
  simp only [LinearMap.mem_ker, rightRadicalMap, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.codRestrict_apply, Linear.rightComp_apply, irreducibleMorphismMk_eq_zero_iff,
    hS.comp_g_mem_jacobsonRadicalSq_iff, mem_jacobsonRadicalSubmodule]

omit [Balanced C] [IsLocalRing (End S.X₁)] in
private theorem rightRadicalMap_surjective (hS : S.IsAlmostSplit) (X : C) :
    Function.Surjective (rightRadicalMap k hS X) := by
  intro x
  obtain ⟨a, rfl⟩ := irreducibleMorphismMk_surjective x
  obtain ⟨b, hb⟩ := hS.isRightAlmostSplit_g.factors X a
    (mem_jacobsonRadical_iff_not_isSplitEpi.mp (mem_jacobsonRadicalSubmodule.mp a.2))
  exact ⟨b, congrArg (irreducibleMorphismMk k X S.X₃) (Subtype.ext hb)⟩

/-- Composition with the final map of an almost-split sequence identifies morphisms into its
middle term modulo the radical with irreducible morphisms into its final term. -/
noncomputable def rightRadicalQuotientEquiv (hS : S.IsAlmostSplit) (X : C) :
    ((X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) ≃ₗ[k]
      irreducibleMorphismSpace k X S.X₃ :=
  (Submodule.quotEquivOfEq _ _ (rightRadicalMap_ker k hS X).symm).trans
    ((rightRadicalMap k hS X).quotKerEquivOfSurjective (rightRadicalMap_surjective k hS X))

/-- The equivalence induced by the final map is computed by composition on representatives. -/
@[simp]
theorem rightRadicalQuotientEquiv_mk (hS : S.IsAlmostSplit) (X : C) (a : X ⟶ S.X₂) :
    hS.rightRadicalQuotientEquiv k X (Submodule.Quotient.mk a) =
      irreducibleMorphismMk k X S.X₃ ⟨a ≫ S.g, mem_jacobsonRadicalSubmodule.mpr
        (comp_mem_jacobsonRadical_left a (mem_jacobsonRadical_iff_not_isSplitEpi.mpr
          hS.isRightAlmostSplit_g.not_isSplitEpi))⟩ := by
  rw [rightRadicalQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- A radical map into the final term can be lifted to the middle term to compute the inverse
equivalence. The resulting class is independent of the chosen lift. -/
theorem rightRadicalQuotientEquiv_symm_mk (hS : S.IsAlmostSplit) (X : C)
    (a : jacobsonRadicalSubmodule k X S.X₃) (b : X ⟶ S.X₂) (hb : b ≫ S.g = a) :
    (hS.rightRadicalQuotientEquiv k X).symm (irreducibleMorphismMk k X S.X₃ a) =
      Submodule.Quotient.mk b := by
  apply (hS.rightRadicalQuotientEquiv k X).injective
  simp only [LinearEquiv.apply_symm_apply, rightRadicalQuotientEquiv_mk]
  exact congrArg (irreducibleMorphismMk k X S.X₃) (Subtype.ext hb.symm)

private def leftRadicalMap (hS : S.IsAlmostSplit) (X : C) :
    (S.X₂ ⟶ X) →ₗ[k] irreducibleMorphismSpace k S.X₁ X :=
  irreducibleMorphismMk k S.X₁ X ∘ₗ
    (Linear.leftComp k X S.f).codRestrict (jacobsonRadicalSubmodule k S.X₁ X)
      (fun a ↦ mem_jacobsonRadicalSubmodule.mpr (comp_mem_jacobsonRadical_right
        (mem_jacobsonRadical_iff_not_isSplitMono.mpr hS.isLeftAlmostSplit_f.not_isSplitMono) a))

private theorem leftRadicalMap_ker (hS : S.IsAlmostSplit) (X : C) :
    LinearMap.ker (leftRadicalMap k hS X) = jacobsonRadicalSubmodule k S.X₂ X := by
  ext a
  simp only [LinearMap.mem_ker, leftRadicalMap, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.codRestrict_apply, Linear.leftComp_apply, irreducibleMorphismMk_eq_zero_iff,
    hS.f_comp_mem_jacobsonRadicalSq_iff, mem_jacobsonRadicalSubmodule]

omit [Balanced C] [IsLocalRing (End S.X₃)] in
private theorem leftRadicalMap_surjective (hS : S.IsAlmostSplit) (X : C) :
    Function.Surjective (leftRadicalMap k hS X) := by
  intro x
  obtain ⟨a, rfl⟩ := irreducibleMorphismMk_surjective x
  obtain ⟨b, hb⟩ := hS.isLeftAlmostSplit_f.factors X a
    (mem_jacobsonRadical_iff_not_isSplitMono.mp (mem_jacobsonRadicalSubmodule.mp a.2))
  exact ⟨b, congrArg (irreducibleMorphismMk k S.X₁ X) (Subtype.ext hb)⟩

/-- Precomposition with the initial map of an almost-split sequence identifies morphisms out of its
middle term modulo the radical with irreducible morphisms out of its initial term. -/
noncomputable def leftRadicalQuotientEquiv (hS : S.IsAlmostSplit) (X : C) :
    ((S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X) ≃ₗ[k]
      irreducibleMorphismSpace k S.X₁ X :=
  (Submodule.quotEquivOfEq _ _ (leftRadicalMap_ker k hS X).symm).trans
    ((leftRadicalMap k hS X).quotKerEquivOfSurjective (leftRadicalMap_surjective k hS X))

/-- The equivalence induced by the initial map is computed by precomposition on representatives. -/
@[simp]
theorem leftRadicalQuotientEquiv_mk (hS : S.IsAlmostSplit) (X : C) (a : S.X₂ ⟶ X) :
    hS.leftRadicalQuotientEquiv k X (Submodule.Quotient.mk a) =
      irreducibleMorphismMk k S.X₁ X ⟨S.f ≫ a, mem_jacobsonRadicalSubmodule.mpr
        (comp_mem_jacobsonRadical_right (mem_jacobsonRadical_iff_not_isSplitMono.mpr
          hS.isLeftAlmostSplit_f.not_isSplitMono) a)⟩ := by
  rw [leftRadicalQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- A radical map out of the initial term can be extended from the middle term to compute the
inverse equivalence. The resulting class is independent of the chosen extension. -/
theorem leftRadicalQuotientEquiv_symm_mk (hS : S.IsAlmostSplit) (X : C)
    (a : jacobsonRadicalSubmodule k S.X₁ X) (b : S.X₂ ⟶ X) (hb : S.f ≫ b = a) :
    (hS.leftRadicalQuotientEquiv k X).symm (irreducibleMorphismMk k S.X₁ X a) =
      Submodule.Quotient.mk b := by
  apply (hS.leftRadicalQuotientEquiv k X).injective
  simp only [LinearEquiv.apply_symm_apply, leftRadicalQuotientEquiv_mk]
  exact congrArg (irreducibleMorphismMk k S.X₁ X) (Subtype.ext hb.symm)

end CategoryTheory.ShortComplex.IsAlmostSplit
