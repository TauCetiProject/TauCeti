/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import TauCeti.CategoryTheory.Linear.FullyFaithful
public import TauCeti.RepresentationTheory.Quiver.Representation.AsModule
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic

/-!
# The vertex projective as a module over the path algebra

`TauCeti.indecProjRep` is the vertex projective `Pᵢ` in the category of representations of a
quiver, while constructions such as `Ext` live in the category `ModuleCat (kQ)` of modules over
the path algebra. This file carries `Pᵢ` across the equivalence `TauCeti.quiverRepFunctor`: it
names the module `TauCeti.indecProjModule` whose representation is `Pᵢ`, records that it is a
projective object, and transports the universal property `TauCeti.indecProjRepHomEquiv` of `Pᵢ` to
it. What comes out of the universal property is the dimension of the morphism space,

`dim_k Hom(Pᵢ, Y) = (dim Y)ᵢ`,

together with the finite-dimensionality of that space. The transport is `k`-linear, and not merely
a bijection, because `TauCeti.quiverRepFunctor` is a `k`-linear functor; that is what lets a
dimension computed for representations be read as one for `kQ`-modules.

As with `TauCeti.indecProjRep`, indecomposability of the vertex projective is not proved here; the
name follows that of the representation it carries.

## Main definitions

* `TauCeti.indecProjModule k Q i`: the `kQ`-module carrying the vertex projective `Pᵢ`, with
  `TauCeti.indecProjModuleIso` identifying its representation with `Pᵢ`.
* `TauCeti.indecProjModuleHomEquiv`: the universal property of `Pᵢ` in the module category, the
  `k`-linear isomorphism `(Pᵢ ⟶ Y) ≃ₗ[k] Yᵢ`.

## Main results

* `TauCeti.finrank_hom_indecProjModule`: `dim_k Hom(Pᵢ, Y)` is the `i`-th coordinate of the
  dimension vector of `Y`.
* `TauCeti.finiteDimensional_hom_indecProjModule`: `Hom(Pᵢ, Y)` is finite-dimensional as soon as
  the vertex space of `Y` at `i` is.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 2, for the vertex projective as the left ideal
  `kQ · eᵢ` and its Hom functor.
-/

public section

namespace TauCeti

open CategoryTheory

open scoped ModuleCat

universe u v w

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-- **The vertex projective `Pᵢ` as a module over the path algebra.** It is a preimage of the
representation `TauCeti.indecProjRep` under the equivalence `TauCeti.quiverRepFunctor`; under the
usual identification of representations with left modules it is the left ideal `kQ · eᵢ`. -/
noncomputable def indecProjModule (i : Q) : ModuleCat (pathAlgebra k Q) :=
  (quiverRepFunctor k Q).objPreimage (indecProjRep k Q i)

/-- The representation carried by `TauCeti.indecProjModule` is the vertex projective `Pᵢ`. -/
noncomputable def indecProjModuleIso (i : Q) :
    (quiverRepFunctor k Q).obj (indecProjModule k Q i) ≅ indecProjRep k Q i :=
  (quiverRepFunctor k Q).objObjPreimageIso _

instance (i : Q) : Projective ((quiverRepFunctor k Q).obj (indecProjModule k Q i)) :=
  Projective.of_iso (indecProjModuleIso k Q i).symm inferInstance

instance (i : Q) : Projective (indecProjModule k Q i) :=
  Projective.of_iso ((quiverRepFunctor k Q).asEquivalence.unitIso.app (indecProjModule k Q i)).symm
    ((quiverRepFunctor k Q).inv.projective_obj_of_projective
      (inferInstanceAs (Projective ((quiverRepFunctor k Q).obj (indecProjModule k Q i)))))

/-- **The universal property of the vertex projective in the module category**: a `kQ`-linear map
out of `TauCeti.indecProjModule` is, `k`-linearly in the map, an element of the `i`-th vertex space
of the target. `TauCeti.finrank_hom_indecProjModule` and
`TauCeti.finiteDimensional_hom_indecProjModule` below read the dimension and the
finite-dimensionality of `Hom(Pᵢ, Y)` off it. -/
noncomputable def indecProjModuleHomEquiv (i : Q) (Y : ModuleCat (pathAlgebra k Q)) :
    (indecProjModule k Q i ⟶ Y) ≃ₗ[k] ((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i) :=
  (((quiverRepFunctor k Q).homLinearEquiv k (indecProjModule k Q i) Y).trans
      (Linear.homCongr k (indecProjModuleIso k Q i) (Iso.refl _))).trans
    (indecProjRepHomEquiv i _)

/-- **The morphisms out of a vertex projective are its vertex space.** The dimension of
`Hom(Pᵢ, Y)` is the `i`-th coordinate of the dimension vector of the representation of `Y`. -/
@[simp]
theorem finrank_hom_indecProjModule (i : Q) (Y : ModuleCat (pathAlgebra k Q)) :
    Module.finrank k (indecProjModule k Q i ⟶ Y)
      = dimVector ((quiverRepFunctor k Q).obj Y) i :=
  (indecProjModuleHomEquiv k Q i Y).finrank_eq.trans (dimVector_apply _ _).symm

/-- **One vertex space suffices for `Hom`-finiteness**: the morphisms out of `Pᵢ` are the vertex
space of `Y` at `i`, so their finite-dimensionality asks nothing of the other vertex spaces. -/
theorem finiteDimensional_hom_indecProjModule (i : Q) (Y : ModuleCat (pathAlgebra k Q))
    (hY : FiniteDimensional k (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i))) :
    FiniteDimensional k (indecProjModule k Q i ⟶ Y) :=
  haveI := hY
  Module.Finite.equiv (indecProjModuleHomEquiv k Q i Y).symm

-- The instance is the whole-module case of `TauCeti.finiteDimensional_hom_indecProjModule`, not the
-- general statement: a vertex space of the associated representation is a `TauCeti.vertexComponent`
-- only after the functor is unfolded, so instance search cannot discharge the general hypothesis on
-- its own, and a target that is finite-dimensional overall is the case automation meets.
instance (i : Q) (Y : ModuleCat (pathAlgebra k Q)) [FiniteDimensional k Y] :
    FiniteDimensional k (indecProjModule k Q i ⟶ Y) :=
  finiteDimensional_hom_indecProjModule k Q i Y
    (inferInstanceAs (FiniteDimensional k (vertexComponent k (Y : Type _) i)))

end TauCeti
