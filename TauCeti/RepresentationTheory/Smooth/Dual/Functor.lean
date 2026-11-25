/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Category
public import TauCeti.RepresentationTheory.Smooth.Dual.Basic

/-!
# The smooth dual as a contravariant functor

Let `G` be a topological group and `A` a commutative ring. The smooth dual `V ↦ V^∨`
(`Representation.smoothDual`) and the transpose of intertwining maps
(`Representation.IntertwiningMap.smoothDualMap`) form a contravariant functor
`SmoothRep.smoothDualFunctor : SmoothRep A G ⥤ (SmoothRep A G)ᵒᵖ`. It is adjoint to its own
opposite: `Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)` naturally in `V` and `W`
(`Representation.smoothDualHomEquiv`, both sides being the `G`-invariant bilinear pairings
`V × W → A`), which is the adjunction `smoothDualFunctor ⊣ smoothDualFunctor.leftOp`. Its unit is
the natural evaluation map `V → V^∨∨` (`Representation.smoothDualEval`).

## Main definitions

* `TauCeti.SmoothRep.smoothDualFunctor`: the contravariant functor `V ↦ V^∨`.
* `TauCeti.SmoothRep.smoothDualAdjunction`: `smoothDualFunctor ⊣ smoothDualFunctor.leftOp`, the
  natural bijection `Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)`.

## Main results

* `TauCeti.SmoothRep.smoothDualAdjunction_homEquiv_apply_hom_hom`: the bijection of the adjunction
  is `Representation.smoothDualHomEquiv`.
* `TauCeti.SmoothRep.smoothDualAdjunction_unit_app_hom_hom`,
  `TauCeti.SmoothRep.smoothDualAdjunction_counit_app_unop_hom_hom`: the unit and the counit of the
  adjunction are the evaluation maps `V → V^∨∨`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.2, Definition 8, p. 14.
-/

public section

noncomputable section

open CategoryTheory Opposite Representation

universe w u v

namespace TauCeti.SmoothRep

variable {A : Type u} {G : Type v} [CommRing A] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

/-- The smooth dual `V^∨` of a smooth representation, as an object of `SmoothRep A G`. -/
abbrev smoothDualObj (V : SmoothRep.{max u w} A G) : SmoothRep.{max u w} A G :=
  of (V := V.obj.ρ.dual.smoothVectors.toSubmodule) V.obj.ρ.smoothDual

/-- The transpose `W^∨ ⟶ V^∨` of a morphism `V ⟶ W` of smooth representations. -/
abbrev smoothDualObjMap {V W : SmoothRep.{max u w} A G} (f : V ⟶ W) :
    smoothDualObj W ⟶ smoothDualObj V :=
  ObjectProperty.homMk (Rep.ofHom f.hom.hom.smoothDualMap)

variable (A G) in
/-- **The smooth dual functor** `SmoothRep A G ⥤ (SmoothRep A G)ᵒᵖ`: it sends `V` to its smooth dual
`V^∨` and an intertwining map `f : V → W` to its transpose `W^∨ → V^∨`. -/
-- An abbreviation, so that the objects are seen to be the smooth duals.
abbrev smoothDualFunctor : SmoothRep.{max u w} A G ⥤ (SmoothRep.{max u w} A G)ᵒᵖ where
  obj V := op (smoothDualObj V)
  map f := (smoothDualObjMap f).op
  map_id V := by
    apply Quiver.Hom.unop_inj
    ext
    simp
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext
    simp

variable (A G) in
/-- **The smooth dual is adjoint to its opposite**: `Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)` naturally in
`V` and `W` (`Representation.smoothDualHomEquiv`), both sides being the `G`-invariant bilinear
pairings `V × W → A`. -/
def smoothDualAdjunction :
    smoothDualFunctor.{w} A G ⊣ (smoothDualFunctor.{w} A G).leftOp :=
  Adjunction.mkOfHomEquiv
    { homEquiv V W :=
        { toFun φ := ObjectProperty.homMk <| Rep.ofHom <|
            smoothDualHomEquiv W.unop.obj.ρ V.obj.ρ φ.unop.hom.hom
          invFun ψ := (ObjectProperty.homMk <| Rep.ofHom <|
            smoothDualHomEquiv V.obj.ρ W.unop.obj.ρ ψ.hom.hom).op
          left_inv φ := Quiver.Hom.unop_inj <| by ext; simp
          right_inv ψ := by
            ext v
            apply Subtype.ext
            ext
            simp }
      homEquiv_naturality_left_symm f g := by
        apply Quiver.Hom.unop_inj
        ext : 2
        simp [smoothDualHomEquiv_comp]
      homEquiv_naturality_right f g := by
        ext : 2
        simp [smoothDualHomEquiv_comp] }

/-- The bijection of `smoothDualAdjunction` is `Representation.smoothDualHomEquiv`: a morphism
`V^∨ ⟶ W` of the opposite category, that is an intertwining map `f : W → V^∨`, goes to the
intertwining map `V → W^∨`, `v ↦ (w ↦ f w v)`. -/
@[simp]
theorem smoothDualAdjunction_homEquiv_apply_hom_hom (V : SmoothRep.{max u w} A G)
    (W : (SmoothRep.{max u w} A G)ᵒᵖ) (φ : (smoothDualFunctor.{w} A G).obj V ⟶ W) :
    dsimp% ((smoothDualAdjunction.{w} A G).homEquiv V W φ).hom.hom =
      smoothDualHomEquiv W.unop.obj.ρ V.obj.ρ φ.unop.hom.hom := by
  simp only [smoothDualAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  simp

/-- The inverse bijection of `smoothDualAdjunction` is also `Representation.smoothDualHomEquiv`. -/
@[simp]
theorem smoothDualAdjunction_homEquiv_symm_apply_unop_hom_hom (V : SmoothRep.{max u w} A G)
    (W : (SmoothRep.{max u w} A G)ᵒᵖ) (ψ : V ⟶ (smoothDualFunctor.{w} A G).leftOp.obj W) :
    dsimp% (((smoothDualAdjunction.{w} A G).homEquiv V W).symm ψ).unop.hom.hom =
      smoothDualHomEquiv V.obj.ρ W.unop.obj.ρ ψ.hom.hom := by
  simp only [smoothDualAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  simp

/-- **The unit of the smooth duality adjunction is the evaluation map** `V → V^∨∨`,
`v ↦ (λ ↦ λ v)`. -/
@[simp]
theorem smoothDualAdjunction_unit_app_hom_hom (V : SmoothRep.{max u w} A G) :
    ((smoothDualAdjunction.{w} A G).unit.app V).hom.hom = V.obj.ρ.smoothDualEval := by
  rw [← Adjunction.homEquiv_id, smoothDualAdjunction_homEquiv_apply_hom_hom]
  ext v f
  simp

/-- **The counit of the smooth duality adjunction is the evaluation map** `W → W^∨∨`, read in the
opposite category. -/
@[simp]
theorem smoothDualAdjunction_counit_app_unop_hom_hom (W : (SmoothRep.{max u w} A G)ᵒᵖ) :
    ((smoothDualAdjunction.{w} A G).counit.app W).unop.hom.hom = W.unop.obj.ρ.smoothDualEval := by
  -- After `rw [← Adjunction.homEquiv_symm_id]`, rewriting with the inverse-bijection lemma does
  -- not match the goal syntactically, so instantiate that lemma at the identity instead.
  have h := smoothDualAdjunction_homEquiv_symm_apply_unop_hom_hom.{w} _ W (𝟙 _)
  rw [Adjunction.homEquiv_symm_id] at h
  rw [h]
  ext v f
  simp

end TauCeti.SmoothRep
