/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.SourceSink
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Semiperfect

/-!
# Simple functors on finitely generated modules over an Artin algebra

Every simple additive contravariant functor on `mod A` is finitely presented, by the existence of
sink maps. The same holds for simple additive covariant functors, by the existence of source maps.
In both cases the functors take values in abelian groups.

## References

* H. Enomoto, *Classifications of exact structures and Cohen-Macaulay-finite algebras*,
  Adv. Math. **335** (2018), 838–877, Proposition A.2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Corollary V.1.17, for source and sink maps.
-/

public section

universe u v w

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits Opposite TauCeti
open scoped ModuleCat.Algebra

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A] [Small.{w} A]

include R

/-- Over an Artin algebra, every simple additive contravariant functor on finitely generated
modules is finitely presented. -/
theorem isFinitelyPresentedFunctor_of_simple (F : ModCat.{w} (FGModuleCat.{w} A))
    [Simple F] : IsFinitelyPresentedFunctor F.obj := by
  let : IsArtinianRing A := IsArtinianRing.of_finite R A
  refine forall_isFinitelyPresentedFunctor_of_simple_iff.mpr (fun Z hZ ↦ ?_) F inferInstance
  obtain ⟨Y, g, hg, -⟩ := exists_right_minimal_isRightAlmostSplit R hZ
  exact ⟨Y, g, hg⟩

/-- Over an Artin algebra, every simple additive covariant functor on finitely generated modules
is finitely presented. In `ModCat`, covariant functors are modules over the opposite category. -/
theorem isFinitelyPresentedFunctor_covariant_of_simple
    (F : ModCat.{w} (FGModuleCat.{w} A)ᵒᵖ) [Simple F] :
    IsFinitelyPresentedFunctor F.obj := by
  let : IsArtinianRing A := IsArtinianRing.of_finite R A
  let : HasFiniteBiproducts (FGModuleCat.{w} A)ᵒᵖ :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  -- The opposite category has the same finite endomorphism modules, with composition reversed.
  let (Z : (FGModuleCat.{w} A)ᵒᵖ) : Module.Finite R (Z ⟶ Z) :=
    Module.Finite.equiv
      ({ (opEquiv Z Z).symm with map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
        (Z.unop ⟶ Z.unop) ≃ₗ[R] (Z ⟶ Z))
  let : IsKrullSchmidt (FGModuleCat.{w} A)ᵒᵖ := isKrullSchmidt_of_module_finite R
  refine forall_isFinitelyPresentedFunctor_of_simple_iff.mpr (fun Z hZ ↦ ?_) F inferInstance
  have hZ' : Indecomposable Z.unop := by
    refine ⟨fun h ↦ hZ.1 h.op, fun Y W e ↦ ?_⟩
    exact (hZ.2 (op Y) (op W) (e.symm.op ≪≫ biprod.opIso Y W)).imp IsZero.unop IsZero.unop
  obtain ⟨Y, f, hf, -⟩ := exists_left_minimal_isLeftAlmostSplit R hZ'
  exact ⟨op Y, f.op, isRightAlmostSplit_op_iff.mpr hf⟩

end FGModuleCat
