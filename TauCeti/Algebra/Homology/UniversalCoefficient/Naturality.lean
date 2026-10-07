/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.UniversalCoefficient.Basic

/-!
# Naturality of the universal coefficient sequence

The inclusion of `Ext¹(Hⱼ(X), Y)` into the cohomology of `Hom(X, Y)` commutes with
pullback along chain maps and pushforward along coefficient morphisms. Together with
naturality of the Kronecker map, this makes both arrows of the universal coefficient
sequence natural in both variables.
No compatibility of chosen cycle retractions is needed.

The argument uses Mathlib's `ShortComplex.ShortExact.extClass_naturality` on the
canonical sequence of boundaries, cycles, and homology, and the characterization
`TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀` of the inclusion.

Reference: Hatcher, *Algebraic Topology*, Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian

universe w

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C]
  {α : Type*} [AddRightCancelSemigroup α] [One α]
  {k : Type*} [CommRing k] [Linear k C] [HasExt.{w} C]
  {X X' : ChainComplex C α} {Y : C}

/-- Pulling back an extension of homology and then including it in cohomology is
including it first and pulling back the resulting cohomology class. This holds in
particular in the universal coefficient degree `i = j + 1`. -/
lemma extToHomology_naturality (f : X' ⟶ X) (i j : α)
    [Projective (X.cycles j)] [IsSplitMono (X.iCycles j)]
    [Projective (X'.cycles j)] [IsSplitMono (X'.iCycles j)]
    (e : Ext.{w} (X.homology j) Y 1) :
    extToHomology k X' Y i j ((Ext.mk₀ (homologyMap f j)).comp e (zero_add 1)) =
      homologyMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
        ((linearYonedaFunctor k Y).map f.op) i (extToHomology k X Y i j e) := by
  -- State the kernel sequences with explicit terms so that their projective middle
  -- objects and extension-class endpoints are available to instance search and rewriting.
  have hX : (ShortComplex.mk (kernel.ι (X.homologyπ j)) (X.homologyπ j)
      (kernel.condition _)).ShortExact := kernelSequence_shortExact _
  have hX' : (ShortComplex.mk (kernel.ι (X'.homologyπ j)) (X'.homologyπ j)
      (kernel.condition _)).ShortExact := kernelSequence_shortExact _
  let b := kernel.map (X'.homologyπ j) (X.homologyπ j)
    (cyclesMap f j) (homologyMap f j) (homologyπ_naturality f j)
  let s : ShortComplex.mk (kernel.ι (X'.homologyπ j)) (X'.homologyπ j) (kernel.condition _) ⟶
      ShortComplex.mk (kernel.ι (X.homologyπ j)) (X.homologyπ j) (kernel.condition _) :=
    { τ₁ := b
      τ₂ := cyclesMap f j
      τ₃ := homologyMap f j
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (homologyπ_naturality f j).symm }
  -- Every extension comes from a map out of the boundaries. Transport that map
  -- using the naturality square of the canonical short exact sequences.
  obtain ⟨β, rfl⟩ := homBoundary_surjective k hX Y e
  have hn := ShortComplex.ShortExact.extClass_naturality hX' hX s
  dsimp only [s] at hn
  have he : (Ext.mk₀ (homologyMap f j)).comp (homBoundary k hX Y β) (zero_add 1) =
      homBoundary k hX' Y (b ≫ β) := by
    rw [homBoundary_apply, homBoundary_apply,
      ← Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by omega),
      ← hn, Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 0) (by omega), Ext.mk₀_comp_mk₀]
  let a := kernel.lift (X.homologyπ j) (X.toCycles i j) (X.toCycles_comp_homologyπ i j)
  have ha : X.d ((ComplexShape.up α).next i) i ≫ a = 0 := by
    rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, X.d_toCycles, zero_comp]
  let φ := cocycleOfComp k Y a ha β
  have hφ : (X.linearYonedaObj k Y).iCycles i φ = a ≫ β :=
    iCycles_cocycleOfComp a ha β
  have hEval : extToHomology k X Y i j (homBoundary k hX Y β) =
      (X.linearYonedaObj k Y).homologyπ i φ :=
    (congrArg (extToHomology k X Y i j) (homBoundary_apply k hX Y β)).trans
      (extToHomology_extClass_comp_mk₀ i j β φ hφ)
  -- It remains to identify the pulled-back representative cocycle.
  rw [he, hEval, homologyMap_linearYonedaFunctor_map_homologyπ_apply]
  rw [homBoundary_apply]
  apply extToHomology_extClass_comp_mk₀
  rw [iCycles_cyclesMap_linearYonedaFunctor_map_apply, hφ]
  simp only [← Category.assoc]
  apply congrArg (· ≫ β)
  rw [← cancel_mono (kernel.ι (X.homologyπ j))]
  dsimp only [a, b]
  simp only [Category.assoc, kernel.lift_ι]
  rw [← cancel_mono (X.iCycles j)]
  simp only [Category.assoc, kernel.lift_ι_assoc, cyclesMap_i,
    X.toCycles_i, X'.toCycles_i_assoc]
  exact f.comm i j

/-- Pushing an extension forward along a coefficient morphism and then including it
in cohomology agrees with applying the induced coefficient map to its cohomology class. -/
lemma extToHomology_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i j : α)
    [Projective (X.cycles j)] [IsSplitMono (X.iCycles j)]
    (e : Ext.{w} (X.homology j) Y 1) :
    extToHomology k X Z i j (e.comp (Ext.mk₀ g) (add_zero 1)) =
      homologyMap (X.linearYonedaObjMap k g) i (extToHomology k X Y i j e) := by
  -- The explicit sequence exposes the middle object for projective instance search.
  have hX : (ShortComplex.mk (kernel.ι (X.homologyπ j)) (X.homologyπ j)
      (kernel.condition _)).ShortExact := kernelSequence_shortExact _
  obtain ⟨β, rfl⟩ := homBoundary_surjective k hX Y e
  have he : (homBoundary k hX Y β).comp (Ext.mk₀ g) (add_zero 1) =
      homBoundary k hX Z (β ≫ g) := by
    rw [homBoundary_apply, homBoundary_apply,
      Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 0) (by omega), Ext.mk₀_comp_mk₀]
  let a := kernel.lift (X.homologyπ j) (X.toCycles i j) (X.toCycles_comp_homologyπ i j)
  have ha : X.d ((ComplexShape.up α).next i) i ≫ a = 0 := by
    rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, X.d_toCycles, zero_comp]
  let φ := cocycleOfComp k Y a ha β
  have hφ : (X.linearYonedaObj k Y).iCycles i φ = a ≫ β :=
    iCycles_cocycleOfComp a ha β
  have hEval : extToHomology k X Y i j (homBoundary k hX Y β) =
      (X.linearYonedaObj k Y).homologyπ i φ := by
    exact (congrArg (extToHomology k X Y i j) (homBoundary_apply k hX Y β)).trans
      (extToHomology_extClass_comp_mk₀ i j β φ hφ)
  rw [he, hEval]
  have hπ := ConcreteCategory.congr_hom (homologyπ_naturality (X.linearYonedaObjMap k g) i) φ
  simp only [ModuleCat.comp_apply] at hπ
  rw [hπ, homBoundary_apply]
  apply extToHomology_extClass_comp_mk₀
  have hcyc := ConcreteCategory.congr_hom (cyclesMap_i (X.linearYonedaObjMap k g) i) φ
  simp only [ModuleCat.comp_apply] at hcyc
  exact hcyc.trans ((X.linearYonedaObjMap_f_hom_apply k g i _).trans
    ((congrArg (· ≫ g) hφ).trans (Category.assoc _ _ _)))

end TauCeti.ChainComplex
