/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Category
public import TauCeti.RepresentationTheory.Smooth.Dual

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

* `TauCeti.SmoothRep.smoothDualAdjunction_unit_app_hom_hom`: the unit of the adjunction is the
  evaluation map `V → V^∨∨`.

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
            apply ObjectProperty.hom_ext
            apply Rep.hom_ext
            change smoothDualHomEquiv _ _ (smoothDualHomEquiv _ _ ψ.hom.hom) = ψ.hom.hom
            rw [← smoothDualHomEquiv_symm, LinearEquiv.symm_apply_apply] }
      homEquiv_naturality_left_symm f g := by
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        exact smoothDualHomEquiv_comp _ _
      homEquiv_naturality_right f g := by
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        exact smoothDualHomEquiv_comp _ _ }

/-- **The unit of the smooth duality adjunction is the evaluation map** `V → V^∨∨`,
`v ↦ (λ ↦ λ v)`. -/
theorem smoothDualAdjunction_unit_app_hom_hom (V : SmoothRep.{max u w} A G) :
    ((smoothDualAdjunction.{w} A G).unit.app V).hom.hom = V.obj.ρ.smoothDualEval := by
  change smoothDualHomEquiv _ _ (IntertwiningMap.id _) = _
  exact IntertwiningMap.ext <| LinearMap.ext fun v ↦ Subtype.ext <| LinearMap.ext fun f ↦ by simp

end TauCeti.SmoothRep
