/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.Limits
public import TauCeti.Topology.Sheaves.LocallyConstant.Basic

/-!
# The sheaf of algebras of locally constant functions

For a commutative ring `R` and a topological space `X`, the locally constant `R`-valued functions
form a sheaf of `R`-algebras on `X` (`TopCat.locallyConstantAlgCatPresheaf X R`), the constant sheaf
`R_X` regarded as a sheaf of `R`-algebras. Its algebra of sections over an open `U` is
`LocallyConstant U R`. It is the coefficient sheaf of the Čech cohomology with constant coefficients
`R`, and the algebra structure on sections is what the cup product of Čech cochains multiplies
(`TauCeti.CategoryTheory.cechCup`).

A continuous map `f : X ⟶ Y` pulls locally constant functions back: composing with `f` gives a
morphism from `R_Y` to the pushforward of `R_X` along `f`
(`TopCat.Hom.locallyConstantAlgCatComap f R`). This is the coefficient map of the pullback of Čech
cohomology with constant coefficients along `f`.

## Main definitions

* `TopCat.locallyConstantAlgCatPresheaf X R`: the presheaf of `R`-algebras of locally constant
  `R`-valued functions on `X`.
* `TopCat.Hom.locallyConstantAlgCatComap f R`: the morphism
  `R_Y ⟶ f_* R_X` composing locally constant functions with `f`.

## Main results

* `TopCat.isSheaf_locallyConstantAlgCatPresheaf`: locally constant functions glue.
* `TopCat.locallyConstantAlgCatPresheaf_comp_forget₂`: forgetting the algebra structure gives the
  presheaf of rings `TopCat.locallyConstantRingCatPresheaf X R`.
-/

public section

open CategoryTheory TopologicalSpace

universe u

noncomputable section

namespace TopCat

variable (X : TopCat.{u}) (R : Type u) [CommRing R]

/-- The presheaf of `R`-algebras of locally constant `R`-valued functions on `X`. -/
@[expose] def locallyConstantAlgCatPresheaf : X.Presheaf (AlgCat.{u} R) where
  obj U := AlgCat.of R (LocallyConstant U.unop R)
  map i := AlgCat.ofHom
    (LocallyConstant.comapₐ R ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩)

@[simp]
theorem locallyConstantAlgCatPresheaf_obj (U : (Opens X)ᵒᵖ) :
    (locallyConstantAlgCatPresheaf X R).obj U = AlgCat.of R (LocallyConstant U.unop R) :=
  (rfl)

variable {X R}

@[simp]
theorem locallyConstantAlgCatPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : LocallyConstant U.unop R) :
    (locallyConstantAlgCatPresheaf X R).map i f =
      f.comap ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩ := (rfl)

variable (X R)

/-- Forgetting the algebra structure, the presheaf of `R`-algebras of locally constant functions is
the presheaf of rings of locally constant functions. -/
theorem locallyConstantAlgCatPresheaf_comp_forget₂ :
    locallyConstantAlgCatPresheaf X R ⋙ forget₂ (AlgCat.{u} R) RingCat.{u} =
      locallyConstantRingCatPresheaf X R :=
  (rfl)

/-- Locally constant functions glue: the presheaf of `R`-algebras of locally constant `R`-valued
functions is a sheaf. -/
theorem isSheaf_locallyConstantAlgCatPresheaf : (locallyConstantAlgCatPresheaf X R).IsSheaf :=
  (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp _ _ (forget₂ (AlgCat.{u} R) RingCat.{u})).mpr
    ((locallyConstantAlgCatPresheaf_comp_forget₂ X R).symm ▸
      isSheaf_locallyConstantRingCatPresheaf X R)

variable {X} {Y : TopCat.{u}} (f : X ⟶ Y)

/-- Composition with a continuous map `f : X ⟶ Y`, as the morphism from the presheaf of `R`-algebras
of locally constant functions on `Y` to the pushforward along `f` of the presheaf of `R`-algebras of
locally constant functions on `X`: a locally constant function `g` on an open `U ⊆ Y` goes to
`g ∘ f` on `f⁻¹(U)`. -/
def Hom.locallyConstantAlgCatComap :
    locallyConstantAlgCatPresheaf Y R ⟶
      (Presheaf.pushforward (AlgCat.{u} R) f).obj (locallyConstantAlgCatPresheaf X R) where
  app U := AlgCat.ofHom (LocallyConstant.comapₐ R (f.hom.restrictPreimage U.unop))
  naturality _ _ _ := rfl

/-- The component of `f.locallyConstantAlgCatComap R` at `U` composes with the restriction of `f`
to `f⁻¹(U) ⟶ U`. -/
theorem Hom.locallyConstantAlgCatComap_app_apply (U : (Opens Y)ᵒᵖ)
    (g : LocallyConstant U.unop R) :
    (f.locallyConstantAlgCatComap R).app U g = g.comap (f.hom.restrictPreimage U.unop) :=
  (rfl)

end TopCat
