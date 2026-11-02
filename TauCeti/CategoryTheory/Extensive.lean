/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Over
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Base change of finite coproducts in finitary pre-extensive categories

In a finitary pre-extensive category finite coproducts are universal: they are stable under
pullback. Phrased in over categories, base change `Over.pullback f : Over S ⥤ Over T` along any
morphism `f : T ⟶ S` preserves finite coproducts. This applies for instance to schemes, where
it says that the fibre product of a finite disjoint union with `T` over `S` is the disjoint
union of the fibre products.

## Main results

* `CategoryTheory.Over.preservesColimitsOfShape_discrete_pullback`: in a finitary pre-extensive
  category, `Over.pullback f` preserves finite coproducts.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {S T : C} (f : T ⟶ S) [HasPullbacksAlong f]

/-- In a finitary pre-extensive category, base change of objects over `S` along any `f : T ⟶ S`
preserves finite coproducts. -/
instance preservesColimitsOfShape_discrete_pullback [FinitaryPreExtensive C] (J : Type*)
    [Finite J] : PreservesColimitsOfShape (Discrete J) (Over.pullback f) where
  preservesColimit {K} := ⟨fun {c} hc ↦ ⟨by
    -- The forgetful functors create colimits, and the image under `Over.forget S` of the
    -- coproduct `c` is universal, so it suffices that the base change of each coproduct
    -- inclusion is a pullback of it.
    apply isColimitOfReflects (Over.forget T)
    refine (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (isColimitOfPreserves (Over.forget S) hc) _
      (Discrete.natTrans fun j ↦ pullback.fst (K.obj j).hom f) (pullback.fst c.pt.hom f) ?_
      (NatTrans.Equifibered.of_discrete _) fun j ↦ ?_).some
    · ext j
      simp
    · exact isPullback_pullback_map_left f (c.ι.app j)⟩⟩

/-- In a finitary pre-extensive category, base change of objects over `S` preserves finite
coproducts. -/
instance [FinitaryPreExtensive C] : PreservesFiniteCoproducts (Over.pullback f) :=
  ⟨fun _ ↦ inferInstance⟩

end CategoryTheory.Over
