/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The triangle of mapping cones of two monomorphisms, up to quasi-isomorphism

For composable morphisms `a : X ⟶ Y` and `b : Y ⟶ Z` of cochain complexes in an abelian category,
Mathlib's triangle of mapping cones `cone a ⟶ cone (a ≫ b) ⟶ cone b ⟶ (cone a)⟦1⟧`
(`mappingConeCompTriangle a b`) is compared with the sequence of cokernels
`cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` through the canonical maps
`mappingCone.descShortComplex` from the mapping cones to the cokernels. When `b` is a
monomorphism, the latter sequence is short exact, and the map in cohomology induced by the third
morphism of the triangle is the connecting map of that short exact sequence
(`CochainComplex.mappingCone.shiftMap_mappingConeCompTriangle_mor₃`). This extends Mathlib's
`mappingCone.homologySequenceδ_triangleh`, which is the case `a = 0`.
-/

public section

open CategoryTheory Limits HomotopyCategory

namespace CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Abelian C] {X Y Z : CochainComplex C ℤ} (a : X ⟶ Y)
  (b : Y ⟶ Z) [Mono b]

/-- The map in cohomology induced by the third morphism `cone b ⟶ (cone a)⟦1⟧` of the triangle of
mapping cones of `a` and `b`, read through the canonical maps `cone a ⟶ cokernel a` and
`cone b ⟶ cokernel b` (the latter a quasi-isomorphism, as `b` is a monomorphism), is the
connecting map of the short exact sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b`. -/
lemma shiftMap_mappingConeCompTriangle_mor₃ (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (mappingConeCompTriangle a b).mor₃ n₀ n₁ h ≫
      HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence a)) n₁ =
    HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence b)) n₀ ≫
      (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact a b).δ n₀ n₁
        (by simp [← h, add_comm]) := by
  -- The connecting map of the triangle of `b` alone, through `homologySequenceδ_triangleh`.
  have hb := homologySequenceδ_triangleh (TauCeti.cokernelSequence_shortExact b) n₀ n₁ (by lia)
  rw [homologySequenceδ_quotient_mapTriangle_obj] at hb
  have hb' : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (triangle b).mor₃ n₀ n₁ h =
      HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence b)) n₀ ≫
        (TauCeti.cokernelSequence_shortExact b).δ n₀ n₁ (by simp [← h, add_comm]) := by
    have h₁ := (Iso.cancel_iso_hom_left
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₀).app (mappingCone b)) _ _).1 hb
    exact (Iso.cancel_iso_inv_right _ _
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₁).app Y)).1
        (h₁.trans (Category.assoc _ _ _).symm)
  -- The naturality of connecting maps along `(Y ⟶ Z ⟶ cokernel b) ⟶ (cokernel a ⟶ … )`.
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (TauCeti.cokernelSequenceToSnakeInputL₃ a b) (TauCeti.cokernelSequence_shortExact b)
    (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact a b) n₀ n₁
    (by simp [← h, add_comm])
  simp only [TauCeti.cokernelSequenceToSnakeInputL₃_τ₃,
    TauCeti.cokernelSequenceToSnakeInputL₃_τ₁] at hnat
  have hnat' := hnat.trans ((congrArg (· ≫ _) (HomologicalComplex.homologyMap_id _ n₀)).trans
    (Category.id_comp _))
  -- `Functor.shiftMap_comp`, applied to the third morphism `(triangle b).mor₃ ≫ (inr a)⟦1⟧'`;
  -- `(homologyFunctor 0).shift n₁` is `homologyFunctor n₁` by `homologyFunctor_shift`.
  have hcomp : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (mappingConeCompTriangle a b).mor₃ n₀ n₁ h =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (triangle b).mor₃ n₀ n₁ h ≫ HomologicalComplex.homologyMap (inr a) n₁ :=
    Functor.shiftMap_comp _ _ _ _ _ _
  have e₁ : HomologicalComplex.homologyMap (inr a) n₁ ≫
      HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence a)) n₁ =
      HomologicalComplex.homologyMap (cokernel.π a) n₁ :=
    (HomologicalComplex.homologyMap_comp _ _ n₁).symm.trans
      (congrArg (HomologicalComplex.homologyMap · n₁)
        (inr_descShortComplex (ShortComplex.cokernelSequence a)))
  rw [hcomp, hb']
  let A := HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence b)) n₀
  let D := (TauCeti.cokernelSequence_shortExact b).δ n₀ n₁ (by simp [← h, add_comm])
  exact (Category.assoc (A ≫ D) _ _).trans <|
    (congrArg (fun t => (A ≫ D) ≫ t) e₁).trans <|
    (Category.assoc A D _).trans (congrArg (fun t => A ≫ t) hnat')

end CochainComplex.mappingCone
