/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Induced.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Cotensor induction as a right adjoint

For a coalgebra map `f : C →ₗc[R] D` with `C` flat over the commutative ring `R`,
cotensor induction is right adjoint to corestriction. The adjunction uses the existing
cotensor equalizer and Frobenius reciprocity. Its unit is the coaction with codomain
restricted to that equalizer, and its counit is evaluation by the counit of `C`.

Consequently induction preserves all existing limits, in particular finite limits and
kernels. There is no finiteness or flatness requirement on the coefficient comodules,
and `D` need not be flat. This is the left exactness used in algebraic induction of
rational representations.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.3.3–I.3.4.
* M. Takeuchi, *Morita theorems for categories of comodules*, J. Fac. Sci. Univ. Tokyo
  24 (1977).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ComoduleCat

universe u v w x y z

attribute [local instance] Comodule.cofree

variable {R : Type u} [CommRing R]
  {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
  {D : Type w} [AddCommMonoid D] [Module R D] [Coalgebra R D]
  (f : C →ₗc[R] D) [Module.Flat R C]

/-- Cotensor induction along a coalgebra map, on the existing induced comodules. -/
-- Keep the cotensor carrier reducible for the subtype coercions used by induction.
noncomputable abbrev inducedFunctor :
    ComoduleCat.{u, w, max v x} R D ⥤ ComoduleCat.{u, v, max v x} R C where
  obj M := of R C (Comodule.induced f M)
  map g := Comodule.inducedMap f g
  map_id _ := Comodule.inducedMap_id f
  map_comp g h := Comodule.inducedMap_comp f h g

/-- The objects of the induction functor are the existing cotensor equalizers. -/
@[simp]
theorem inducedFunctor_obj (M : ComoduleCat.{u, w, max v x} R D) :
    (inducedFunctor f).obj M = of R C (Comodule.induced f M) :=
  (rfl)

/-- Cotensor induction is additive on comodule morphisms. -/
instance : (inducedFunctor f).Additive where
  map_add := by
    intro M N g h
    dsimp only [inducedFunctor]
    apply Comodule.Hom.ext
    intro t
    apply Subtype.ext
    simp [LinearMap.rTensor_add]

/-- Corestriction is left adjoint to cotensor induction. -/
noncomputable def inducedAdjunction : corestrict f ⊣ inducedFunctor.{u, v, w, x} f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦ (Comodule.inducedEquiv (N := M) (M := N) f).toEquiv.symm
      homEquiv_naturality_left_symm := by
        intro M M' N g h
        exact Comodule.inducedEquiv_comp f h g
      homEquiv_naturality_right := by
        intro M N N' g h
        let _ := Comodule.Corestrict (M := M) f
        let g' : Comodule.Hom R D M N := g
        -- Unpack the categorical hom equivalence to use coefficient naturality of reciprocity.
        change (Comodule.inducedEquiv f).symm (Comodule.Hom.comp h g') =
          Comodule.Hom.comp (Comodule.inducedMap f h) ((Comodule.inducedEquiv f).symm g')
        apply (Comodule.inducedEquiv f).injective
        rw [Comodule.inducedEquiv_inducedMap_comp]
        simp only [LinearEquiv.apply_symm_apply] }

/-- The hom-set equivalence is precisely the inverse of Frobenius reciprocity. -/
@[simp]
theorem inducedAdjunction_homEquiv
    (M : ComoduleCat.{u, v, max v x} R C) (N : ComoduleCat.{u, w, max v x} R D) :
    (inducedAdjunction f).homEquiv M N =
      (Comodule.inducedEquiv (N := M) (M := N) f).toEquiv.symm := by
  rw [inducedAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The counit of induction is the existing evaluation morphism. -/
@[simp]
theorem inducedAdjunction_counit_app
    (M : ComoduleCat.{u, w, max v x} R D) :
    (inducedAdjunction f).counit.app M = Comodule.inducedEval f := by
  rw [← (inducedAdjunction f).homEquiv_symm_id M, inducedAdjunction_homEquiv]
  let _ := Comodule.Corestrict (M := Comodule.induced f M) f
  -- Remove the `toEquiv` wrapper before using the public evaluation formula.
  change Comodule.inducedEquiv f (Comodule.Hom.id R C _) = _
  rw [Comodule.inducedEquiv_apply, Comodule.corestrictHom_id, Comodule.Hom.comp_id]

/-- Cotensor induction preserves all existing limits, with no flatness assumption on `D`. -/
instance : PreservesLimitsOfSize.{y, z} (inducedFunctor.{u, v, w, x} f) :=
  (inducedAdjunction f).rightAdjoint_preservesLimits

end TauCeti.ComoduleCat
