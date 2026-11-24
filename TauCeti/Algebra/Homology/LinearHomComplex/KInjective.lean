/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.Algebra.Homology.LinearHomComplex.Cohomology

/-!
# The linear Hom complex into a K-injective complex

If `I` is a K-injective cochain complex, then the linear Hom complex `Hom^•(-, I)` sends
quasi-isomorphisms to quasi-isomorphisms (`TauCeti.quasiIso_linearHomComplexPrecomp`): in degree
`n` its cohomology is the group of morphisms `K ⟶ I⟦n⟧` in the homotopy category, which are the
morphisms `K ⟶ I⟦n⟧` in the derived category since `I⟦n⟧` is K-injective.
-/

public section

open CategoryTheory DerivedCategory

universe w v u

namespace TauCeti

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Precomposition with a quasi-isomorphism `s : K' ⟶ K` induces a quasi-isomorphism
`Hom^•(K, I) ⟶ Hom^•(K', I)` of linear Hom complexes into a K-injective complex `I`. -/
theorem quasiIso_linearHomComplexPrecomp {K' K : CochainComplex C ℤ} (s : K' ⟶ K) [QuasiIso s]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    QuasiIso (linearHomComplexPrecomp R s I) := by
  let := HasDerivedCategory.standard C
  rw [quasiIso_iff]
  intro n
  have : (I⟦n⟧).IsKInjective := (CochainComplex.isKInjective_shift_iff I n).2 inferInstance
  have hs : IsIso (Qh.map ((HomotopyCategory.quotient C _).map s)) := by
    rw [isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  -- Precomposition with the class of `s` in the homotopy category is bijective, as it becomes
  -- precomposition with an isomorphism in the derived category.
  have hpre : Function.Bijective fun f : (HomotopyCategory.quotient C _).obj K ⟶
      (HomotopyCategory.quotient C _).obj (I⟦n⟧) ↦ (HomotopyCategory.quotient C _).map s ≫ f := by
    rw [← (CochainComplex.IsKInjective.Qh_map_bijective _ _).of_comp_iff']
    have h : (Qh.map ∘ fun f : (HomotopyCategory.quotient C _).obj K ⟶
        (HomotopyCategory.quotient C _).obj (I⟦n⟧) ↦ (HomotopyCategory.quotient C _).map s ≫ f) =
        (fun g ↦ Qh.map ((HomotopyCategory.quotient C _).map s) ≫ g) ∘ Qh.map := by
      ext f
      simp
    rw [h]
    refine Function.Bijective.comp ⟨fun g g' hg ↦ (cancel_epi _).1 hg, fun g ↦
      ⟨inv (Qh.map ((HomotopyCategory.quotient C _).map s)) ≫ g, by simp⟩⟩
      (CochainComplex.IsKInjective.Qh_map_bijective _ _)
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  have h : ⇑(HomologicalComplex.homologyMap (linearHomComplexPrecomp R s I) n).hom =
      (linearHomComplexHomologyLinearEquiv R K' I n).symm ∘
        (fun f ↦ (HomotopyCategory.quotient C _).map s ≫ f) ∘
          linearHomComplexHomologyLinearEquiv R K I n := by
    ext z
    simp [← linearHomComplexHomologyLinearEquiv_homologyMap_precomp]
  rw [h]
  exact (linearHomComplexHomologyLinearEquiv R K' I n).symm.bijective.comp
    (hpre.comp (linearHomComplexHomologyLinearEquiv R K I n).bijective)

end TauCeti
