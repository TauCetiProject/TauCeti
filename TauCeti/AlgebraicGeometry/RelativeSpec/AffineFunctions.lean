/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Affine
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# The coordinate algebra of an affine scheme over a base

A scheme `p : V ⟶ X` over `X` has a commutative `𝒪ₓ`-algebra of regular functions, carried by
the actual pushforward `p_* 𝒪_V` (`AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra`),
and a morphism `g : V ⟶ W` over `X` pulls back regular functions
(`AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap`). When the structure morphism is
affine, the algebra of regular functions is quasi-coherent, so this defines the functor

`affineFunctions X : AffineSchemeOver X ⥤ (QuasicoherentAlgebra X)ᵒᵖ`

in the direction opposite to `TauCeti.AlgebraicGeometry.relativeSpec X`. These are the two
functors of the anti-equivalence between quasi-coherent commutative `𝒪ₓ`-algebras and affine
schemes over `X`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_pushforwardStructureAlgebra`: the function
  algebra of an affine morphism is quasi-coherent;
* `TauCeti.AlgebraicGeometry.affineFunctions X`: the coordinate-algebra functor from affine
  schemes over `X` to quasi-coherent commutative `𝒪ₓ`-algebras.

## References

* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative
  spectrum).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X V : Scheme.{u}}

/-- The function algebra `p_* 𝒪_V` of an affine morphism `p : V ⟶ X` is quasi-coherent. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isQuasicoherent_pushforwardStructureAlgebra
    (p : V ⟶ X) [IsAffineHom p] : p.pushforwardStructureAlgebra.X.IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pushforward p).obj (𝟙_ V.Modules)).IsQuasicoherent

namespace AlgebraicGeometry

/-- The coordinate-algebra functor: an affine scheme `p : V ⟶ X` over `X` goes to its
quasi-coherent algebra of regular functions `p_* 𝒪_V`, and a morphism over `X` goes to pullback
of regular functions along it. -/
@[expose]
def affineFunctions (X : Scheme.{u}) : AffineSchemeOver X ⥤ (QuasicoherentAlgebra X)ᵒᵖ where
  obj V := op ⟨V.hom.pushforwardStructureAlgebra,
    (inferInstance : V.hom.pushforwardStructureAlgebra.X.IsQuasicoherent)⟩
  map g := (ObjectProperty.homMk
    (Scheme.Hom.pushforwardStructureAlgebraMap g.left (MorphismProperty.Over.w g))).op
  map_id V := by
    apply Quiver.Hom.unop_inj
    exact ObjectProperty.hom_ext _ Scheme.Hom.pushforwardStructureAlgebraMap_id
  map_comp g g' := by
    apply Quiver.Hom.unop_inj
    exact ObjectProperty.hom_ext _ (Scheme.Hom.pushforwardStructureAlgebraMap_comp g.left g'.left
      (MorphismProperty.Over.w g) (MorphismProperty.Over.w g'))

/-- The coordinate algebra of `p : V ⟶ X` is the function algebra `p_* 𝒪_V`. -/
@[simp]
lemma affineFunctions_obj_unop_obj (V : AffineSchemeOver X) :
    ((affineFunctions X).obj V).unop.obj = V.hom.pushforwardStructureAlgebra :=
  (rfl)

/-- The coordinate-algebra functor sends a morphism over `X` to pullback of regular functions. -/
@[simp]
lemma affineFunctions_map_unop_hom {V W : AffineSchemeOver X} (g : V ⟶ W) :
    ((affineFunctions X).map g).unop.hom =
      Scheme.Hom.pushforwardStructureAlgebraMap g.left (MorphismProperty.Over.w g) :=
  (rfl)

end AlgebraicGeometry

end

end TauCeti
