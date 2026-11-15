/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import TauCeti.AlgebraicTopology.CechNerve
public import TauCeti.AlgebraicTopology.SimplicialObject.Matching

/-!
# Hypercovers of the terminal object

A simplicial object `U` in a category with a terminal object, augmented to the terminal object, is
a *hypercover* if `U _⦋0⦌ ⟶ ⊤_ C` is an epimorphism and every matching map
`U _⦋n + 1⦌ ⟶ ((cosk n).obj U) _⦋n + 1⦌` is an epimorphism
(`CategoryTheory.SimplicialObject.IsHypercover`). In a topos this is the notion of hypercover used
for descent of sheaves and of complexes of sheaves.

The augmentation to the terminal object is unique, so it is not recorded. The coskeleton in the
definition is the coskeleton of augmented simplicial objects over `⊤_ C`. In degrees `n + 1` it
agrees with the coskeleton of `U`, since a limit over the faces of `⦋n + 1⦌` does not change when
the terminal object is added to the diagram; in degree `0` it is `⊤_ C`, which gives the first
condition.

We check the definition on three examples.

* The constant simplicial object at `⊤_ C` is a hypercover
  (`CategoryTheory.SimplicialObject.isHypercover_const_terminal`).
* The Čech nerve `⦋n⦌ ↦ Uⁿ⁺¹` of an epimorphism `U ⟶ ⊤_ C` is a hypercover
  (`CategoryTheory.SimplicialObject.isHypercover_cechNerveTerminalFrom`): its matching maps are
  split epimorphisms, since a simplex is given by its vertices.
* The constant simplicial set on a two-element set is not a hypercover
  (`CategoryTheory.SimplicialObject.not_isHypercover_const_bool`): its matching map in degree one
  is the diagonal of `Bool`, which is not surjective.

## References

* M. Artin, A. Grothendieck and J.-L. Verdier, *Théorie des topos et cohomologie étale des
  schémas* (SGA 4), Lecture Notes in Mathematics 270, Springer, 1972, Exposé V, §7.
* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015), 99–201,
  Proposition 3.3.6 and the notation following it.
-/

public section

open CategoryTheory Limits Opposite Functor SimplexCategory.Truncated

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section

variable [HasTerminal C] [∀ (n : ℕ) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/-- A simplicial object `U`, augmented to the terminal object, is a hypercover if
`U _⦋0⦌ ⟶ ⊤_ C` and all matching maps `U _⦋n + 1⦌ ⟶ ((cosk n).obj U) _⦋n + 1⦌` are
epimorphisms. -/
class IsHypercover (U : SimplicialObject C) : Prop where
  /-- The augmentation `U _⦋0⦌ ⟶ ⊤_ C` is an epimorphism. -/
  epi_terminal_from : Epi (terminal.from (U _⦋0⦌))
  /-- Every matching map `U _⦋n + 1⦌ ⟶ ((cosk n).obj U) _⦋n + 1⦌` is an epimorphism. -/
  epi_matchingMap (n : ℕ) : Epi (U.matchingMap n)

attribute [instance] IsHypercover.epi_terminal_from IsHypercover.epi_matchingMap

end

section

variable [HasTerminal C] [∀ (n : ℕ) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]

/-- The constant simplicial object at the terminal object is a hypercover. -/
instance isHypercover_const_terminal : ((const C).obj (⊤_ C)).IsHypercover where
  epi_terminal_from := by
    dsimp
    have : IsSplitEpi (terminal.from (⊤_ C)) := ⟨⟨𝟙 _, terminal.hom_ext _ _⟩⟩
    infer_instance
  epi_matchingMap n := by
    have : IsSplitEpi (((const C).obj (⊤_ C)).matchingMap n) :=
      ⟨⟨terminal.from _, cosk_obj_hom_ext fun _ ↦ terminal.hom_ext _ _⟩⟩
    infer_instance

end

section

variable [HasFiniteProducts C] [∀ (n : ℕ) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]

/-- The Čech nerve `⦋n⦌ ↦ Uⁿ⁺¹` of an epimorphism `U ⟶ ⊤_ C` is a hypercover. -/
instance isHypercover_cechNerveTerminalFrom (U : C) [Epi (terminal.from U)] :
    (cechNerveTerminalFrom U).IsHypercover where
  epi_terminal_from := by
    have w : (Pi.lift fun _ : Fin 1 ↦ 𝟙 U) ≫ terminal.from ((cechNerveTerminalFrom U) _⦋0⦌) =
      terminal.from U := terminal.hom_ext _ _
    exact epi_of_epi_fac w
  epi_matchingMap n := by
    let X := cechNerveTerminalFrom U
    -- The vertex `i` of `⦋n + 1⦌`, as an object of the indexing category of the matching cone.
    let v (i : Fin (n + 2)) :
        StructuredArrow (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op :=
      .mk (Y := op ⦋0⦌ₙ) (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ i).op
    -- The section of the matching map takes the simplex with the vertices of a boundary family.
    have : IsSplitEpi (X.matchingMap n) :=
      ⟨⟨cechNerveTerminalFrom.lift U fun i ↦ (X.matchingCone n).π.app (v i),
        cosk_obj_hom_ext fun f ↦ by
          rw [Category.assoc, matchingMap_π, Category.id_comp]
          refine cechNerveTerminalFrom.hom_ext U fun i ↦ ?_
          -- The inclusion of the `i`-th vertex of the face `f` is a morphism `f ⟶ v (f i)`.
          let g : f ⟶ v (f.hom.unop.toOrderHom i) :=
            StructuredArrow.homMk (.op (SimplexCategory.Truncated.Hom.tr
              (SimplexCategory.const _ _ i) (by simp) f.right.unop.property)) (by
                apply Quiver.Hom.unop_inj
                simp [v])
          have hf : f.hom ≫ (SimplexCategory.const ⦋0⦌ _ i).op =
              (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (f.hom.unop.toOrderHom i)).op :=
            Quiver.Hom.unop_inj (by simp)
          rw [Category.assoc, ← X.map_comp, hf, cechNerveTerminalFrom.lift_map_const]
          exact ((X.matchingCone n).w g).symm⟩⟩
    infer_instance

end

/-- The constant simplicial set on the two-element set `Bool` is not a hypercover: its matching
map in degree one is the diagonal `Bool ⟶ Bool × Bool`, which misses the pair `(false, true)`. -/
theorem not_isHypercover_const_bool : ¬ ((const Type).obj Bool).IsHypercover := by
  intro h
  -- The boundary family of `⦋1⦌` taking the value `false` at the vertex `0` and `true` at `1`.
  obtain ⟨u, hu⟩ := (epi_iff_surjective _).1 (h.epi_matchingMap 0)
    ((Types.isLimitEquivSections (((const Type).obj Bool).isLimitMatchingCone 0)).symm
      ⟨fun f ↦ decide (f.hom.unop.toOrderHom 0 = 1), fun {f f'} φ ↦ by
        have key : f'.hom.unop.toOrderHom 0 = f.hom.unop.toOrderHom 0 := by
          rw [← StructuredArrow.w φ]
          dsimp
          rw [OrderHom.comp_coe, Function.comp_apply]
          congr 1
          have := f.right.unop.property
          ext
          simp at this ⊢
          omega
        simp [key, truncation]⟩)
  have h0 := congrArg ((((const Type).obj Bool).matchingCone 0).π.app
    (.mk (Y := op ⦋0⦌₀) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op)) hu
  have h1 := congrArg ((((const Type).obj Bool).matchingCone 0).π.app
    (.mk (Y := op ⦋0⦌₀) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op)) hu
  rw [Types.isLimitEquivSections_symm_apply, ← ConcreteCategory.comp_apply, matchingMap_π]
    at h0 h1
  have e0 : u = false := by simpa using h0
  have e1 : u = true := by simpa using h1
  exact Bool.false_ne_true (e0.symm.trans e1)

end CategoryTheory.SimplicialObject
