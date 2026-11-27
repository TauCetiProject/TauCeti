/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.CategoryTheory.Exact.YonedaExt.Abelian

import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.Ext.FiniteLength

/-!
# Degree-one extensions of finitely generated modules

Over a left Noetherian ring, the inclusion of finitely generated modules into all modules
induces a linear equivalence on Yoneda `Ext¹`. It commutes with base and cobase change, so
dualities expressed via ambient module extensions can be transported to the exact category of
finitely generated modules. In particular, over an Artin algebra its Yoneda `Ext¹` has finite
length over the base ring.

The comparison uses the linear identification of Yoneda extensions with derived `Ext¹` and
Mathlib's bijectivity theorem for a fully faithful exact functor preserving projectives.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Section IV.4, for the formulas relating module extensions to stable morphisms.
-/

public section

open CategoryTheory CategoryTheory.Abelian TauCeti TauCeti.ExactStructure
open scoped ModuleCat.Algebra

namespace FGModuleCat

universe u v w

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A] [Small.{w} A]

section Noetherian

variable [IsNoetherianRing A]

local instance : HasExt.{w} (FGModuleCat.{w} A) := hasExt_of_enoughProjectives _

local instance : (forget₂ (FGModuleCat.{w} A) (ModuleCat.{w} A)).Additive :=
  inferInstanceAs ((ModuleCat.isFG.{w} A).ι.Additive)

/-- The inclusion of finitely generated modules into all modules induces an equivalence on
Yoneda `Ext¹` for the abelian exact structures. The smallness hypothesis allows projective
presentations in the universe of the modules. -/
noncomputable def ext1LinearEquiv (M N : FGModuleCat.{w} A) :
    (ExactStructure.abelian _).Ext1 M N ≃ₗ[R]
      (ExactStructure.abelian _).Ext1 M.obj N.obj := by
  let F := forget₂ (FGModuleCat.{w} A) (ModuleCat.{w} A)
  letI : F.Linear R := inferInstanceAs ((ModuleCat.isFG.{w} A).ι.Linear R)
  letI : F.PreservesProjectiveObjects :=
    ⟨fun {X} hX ↦ (projective_obj_iff X).2 hX⟩
  let e := LinearEquiv.ofBijective (F.mapExtLinearMap R M N 1)
    (F.mapExt_bijective_of_preservesProjectiveObjects M N 1)
  exact (Ext1.abelianLinearEquiv R M N).trans
    (e.trans (Ext1.abelianLinearEquiv R M.obj N.obj).symm)

/-- On derived extension classes the comparison is the map induced by the inclusion. -/
private theorem toExt_ext1LinearEquiv {M N : FGModuleCat.{w} A}
    (ξ : (ExactStructure.abelian _).Ext1 M N) :
    (ext1LinearEquiv R M N ξ).toExt =
      ξ.toExt.mapExactFunctor (forget₂ (FGModuleCat.{w} A) (ModuleCat.{w} A)) := by
  simp only [ext1LinearEquiv, LinearEquiv.trans_apply, Ext1.toExt_abelianLinearEquiv_symm,
    Ext1.abelianLinearEquiv_apply]
  rfl

/-- On a representative the comparison takes the extension class of the same short exact
sequence in the ambient module category. -/
@[simp]
theorem toExt_ext1LinearEquiv_mk {M N : FGModuleCat.{w} A}
    (e : (ExactStructure.abelian _).Extension M N) :
    (ext1LinearEquiv R M N (Ext1.mk e)).toExt =
      (e.isKernelCokernelPair.shortExact.map_of_exact
        (forget₂ (FGModuleCat.{w} A) (ModuleCat.{w} A))).extClass := by
  simp only [toExt_ext1LinearEquiv, Ext1.toExt_mk, Ext.mapExactFunctor_extClass]

/-- The inclusion comparison commutes with base change in the first argument. -/
@[simp]
theorem ext1LinearEquiv_pullback {M M' N : FGModuleCat.{w} A} (f : M' ⟶ M)
    (ξ : (ExactStructure.abelian _).Ext1 M N) :
    ext1LinearEquiv R M' N (ξ.pullback f) = (ext1LinearEquiv R M N ξ).pullback f.hom := by
  apply Ext1.toExt_injective
  simp only [toExt_ext1LinearEquiv, Ext1.toExt_pullback, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, forget₂_map]

/-- The inclusion comparison commutes with cobase change in the second argument. -/
@[simp]
theorem ext1LinearEquiv_pushout {M N N' : FGModuleCat.{w} A} (g : N ⟶ N')
    (ξ : (ExactStructure.abelian _).Ext1 M N) :
    ext1LinearEquiv R M N' (ξ.pushout g) = (ext1LinearEquiv R M N ξ).pushout g.hom := by
  apply Ext1.toExt_injective
  simp only [toExt_ext1LinearEquiv, Ext1.toExt_pushout, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, forget₂_map]

end Noetherian

/-- Yoneda `Ext¹` in the category of finitely generated modules over an Artin algebra has finite
length over the base ring. -/
theorem isFiniteLength_ext1 [IsArtinianRing R] [Module.Finite R A] (M N : FGModuleCat.{w} A) :
    letI : IsArtinianRing A := IsArtinianRing.of_finite R A
    IsFiniteLength R ((ExactStructure.abelian _).Ext1 M N) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite R A
  exact (ext1LinearEquiv R M N).symm.isFiniteLength (ModuleCat.isFiniteLength_ext1 R M.obj N.obj)

end FGModuleCat
