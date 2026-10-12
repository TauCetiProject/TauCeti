/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Fibre products of flat surjective morphisms over a base

The cartesian monoidal structure of `Over S` is the fibre product over `S`, so for morphisms
`f : X ⟶ Y` and `g : X' ⟶ Y'` of schemes over `S`, the underlying morphism of `f ⊗ g` is
`X ×_S X' ⟶ Y ×_S Y'`. It is the composite of a base change of `f` and a base change of `g`, so it
is flat, respectively surjective, when `f` and `g` are. In particular `f ⊗ g` is then an
epimorphism of `Over S`.

This is the hypothesis under which a morphism of group schemes over `S` descended along a flat
surjective homomorphism `f` is again a homomorphism: the multiplications are compared after
precomposition with `f ⊗ f`.

## Main results

* `AlgebraicGeometry.flat_tensorHom_left` and `AlgebraicGeometry.surjective_tensorHom_left`:
  flatness and surjectivity of `X ×_S X' ⟶ Y ×_S Y'`.
* `AlgebraicGeometry.epi_tensorHom`: `f ⊗ g` is an epimorphism of `Over S` when `f` and `g` are
  flat and surjective.
-/

public section

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')

/-- The fibre product over `S` of two flat morphisms is flat. -/
instance flat_tensorHom_left [Flat f.left] [Flat g.left] : Flat (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @Flat.{u}) ‹_› ‹_› (Over.w f).symm (Over.w g).symm

/-- The fibre product over `S` of two surjective morphisms is surjective. -/
instance surjective_tensorHom_left [Surjective f.left] [Surjective g.left] :
    Surjective (f ⊗ₘ g).left := by
  -- Instance search does not reach composition-stability of `@Surjective` through Mathlib's
  -- `IsMultiplicative` instance, so it is supplied by hand.
  have : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @Surjective.{u}) ‹_› ‹_› (Over.w f).symm
    (Over.w g).symm

/-- The fibre product over `S` of two flat surjective morphisms is an epimorphism of `Over S`. -/
instance epi_tensorHom [Flat f.left] [Surjective f.left] [Flat g.left] [Surjective g.left] :
    Epi (f ⊗ₘ g) :=
  have := Flat.epi_of_flat_of_surjective (f ⊗ₘ g).left
  Over.epi_of_epi_left _

end AlgebraicGeometry
