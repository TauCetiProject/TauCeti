/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Action.FullSubcategory
public import TauCeti.CategoryTheory.Monoidal.Action.StrongTrans
public import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# Exactness of restricted actions

Let a monoidal category `C` act on the left on categories `D'` and `D`, and let `F : D' ⥤ D` be
left-linear (equivariant), so that `actionLeft D' c ⋙ F ≅ F ⋙ actionLeft D c`. If `F` preserves
the limit of a diagram `K`, reflects the limit of `K ⋙ actionLeft D' c`, and the action functor
`actionLeft D c` preserves the limit of `K ⋙ F`, then `actionLeft D' c` preserves the limit of
`K`. We record this for single diagrams, and for limits of a given shape and finite limits when
`F` preserves and reflects all such limits, and dually for colimits. The functor `F` can be the
inclusion of a full subcategory or an equivalence.

The main application is to a property `P : ObjectProperty D` stable under the action, through the
equivariant inclusion `P.ι` (`TauCeti.CategoryTheory.Monoidal.Action.FullSubcategory`):

* if `P` is closed under kernels, then the restricted action functors on `P.FullSubcategory`
  preserve the kernel of each morphism whose underlying morphism has a kernel in `D`, whenever
  the action functors on `D` preserve that kernel; dually for cokernels;
* if `D` is preadditive with a zero object and finite products, and `P` contains zero and is
  closed under finite products and kernels (cokernels), then the restricted action functors
  preserve finite limits (colimits) whenever the action functors on `D` do. For an abelian
  category `D` and `P` closed under kernels, cokernels and finite products, the restriction of an
  action by exact functors is thus an action by exact functors of the inherited abelian
  category `P.FullSubcategory`.

The comparison isomorphisms are `Functor.commActionLeftIso`, and the transfer of preservation
along a functor reflecting limits is Mathlib's `preservesLimit_of_reflects_of_preserves`.
-/

public section

namespace CategoryTheory

open Limits MonoidalCategory

namespace MonoidalCategory.MonoidalLeftAction

variable {C : Type*} [Category* C] [MonoidalCategory C] {D' D : Type*} [Category* D']
  [Category* D] [MonoidalLeftAction C D'] [MonoidalLeftAction C D] (c : C) (F : D' ⥤ D)
  [F.LeftLinear C] {J : Type*} [Category* J]

/-- If a left-linear functor `F` preserves the limit of `K` and reflects the limit of
`K ⋙ actionLeft D' c`, and the action of `c` on the target preserves the limit of `K ⋙ F`, then
the action of `c` on the source preserves the limit of `K`. -/
lemma preservesLimit_actionLeft_of_leftLinear (K : J ⥤ D') [PreservesLimit K F]
    [ReflectsLimit (K ⋙ actionLeft D' c) F] [PreservesLimit (K ⋙ F) (actionLeft D c)] :
    PreservesLimit K (actionLeft D' c) :=
  have := preservesLimit_of_natIso K (F.commActionLeftIso c).symm
  preservesLimit_of_reflects_of_preserves (actionLeft D' c) F

/-- If a left-linear functor `F` preserves the colimit of `K` and reflects the colimit of
`K ⋙ actionLeft D' c`, and the action of `c` on the target preserves the colimit of `K ⋙ F`,
then the action of `c` on the source preserves the colimit of `K`. -/
lemma preservesColimit_actionLeft_of_leftLinear (K : J ⥤ D') [PreservesColimit K F]
    [ReflectsColimit (K ⋙ actionLeft D' c) F] [PreservesColimit (K ⋙ F) (actionLeft D c)] :
    PreservesColimit K (actionLeft D' c) :=
  have := preservesColimit_of_natIso K (F.commActionLeftIso c).symm
  preservesColimit_of_reflects_of_preserves (actionLeft D' c) F

/-- If a left-linear functor `F` preserves and reflects limits of shape `J` and the action of `c`
on the target preserves them, so does the action of `c` on the source. -/
lemma preservesLimitsOfShape_actionLeft_of_leftLinear [PreservesLimitsOfShape J F]
    [ReflectsLimitsOfShape J F] [PreservesLimitsOfShape J (actionLeft D c)] :
    PreservesLimitsOfShape J (actionLeft D' c) where
  preservesLimit {K} := preservesLimit_actionLeft_of_leftLinear c F K

/-- If a left-linear functor `F` preserves and reflects colimits of shape `J` and the action of
`c` on the target preserves them, so does the action of `c` on the source. -/
lemma preservesColimitsOfShape_actionLeft_of_leftLinear [PreservesColimitsOfShape J F]
    [ReflectsColimitsOfShape J F] [PreservesColimitsOfShape J (actionLeft D c)] :
    PreservesColimitsOfShape J (actionLeft D' c) where
  preservesColimit {K} := preservesColimit_actionLeft_of_leftLinear c F K

/-- If a left-linear functor `F` preserves and reflects finite limits and the action of `c` on
the target preserves finite limits, so does the action of `c` on the source. -/
lemma preservesFiniteLimits_actionLeft_of_leftLinear [PreservesFiniteLimits F]
    [ReflectsFiniteLimits F] [PreservesFiniteLimits (actionLeft D c)] :
    PreservesFiniteLimits (actionLeft D' c) where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_actionLeft_of_leftLinear c F

/-- If a left-linear functor `F` preserves and reflects finite colimits and the action of `c` on
the target preserves finite colimits, so does the action of `c` on the source. -/
lemma preservesFiniteColimits_actionLeft_of_leftLinear [PreservesFiniteColimits F]
    [ReflectsFiniteColimits F] [PreservesFiniteColimits (actionLeft D c)] :
    PreservesFiniteColimits (actionLeft D' c) where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_actionLeft_of_leftLinear c F

end MonoidalCategory.MonoidalLeftAction

namespace ObjectProperty

open MonoidalLeftAction

variable {C : Type*} [Category* C] [MonoidalCategory C] {D : Type*} [Category* D]
  [MonoidalLeftAction C D] (P : ObjectProperty D) [P.IsStableUnderLeftAction C] (c : C)

section Kernels

variable [HasZeroMorphisms D] {X Y : P.FullSubcategory} (f : X ⟶ Y)

/-- If `P` is closed under kernels, the restricted action of `c` preserves the kernel of a
morphism `f` of `P.FullSubcategory` whose underlying morphism has a kernel in `D`, whenever the
action of `c` on `D` preserves that kernel. -/
instance preservesLimit_parallelPair_actionLeft [HasKernel f.hom] [P.IsClosedUnderKernels]
    [PreservesLimit (parallelPair f.hom 0) (actionLeft D c)] :
    PreservesLimit (parallelPair f 0) (actionLeft P.FullSubcategory c) :=
  have := P.createsKernels f
  have := P.hasLimit_parallelPair_comp_ι f
  have := preservesLimit_of_createsLimit_and_hasLimit (parallelPair f 0) P.ι
  have : PreservesLimit (parallelPair f 0 ⋙ P.ι) (actionLeft D c) :=
    preservesLimit_of_iso_diagram (K₁ := parallelPair f.hom 0) _
      (diagramIsoParallelPair (parallelPair f 0 ⋙ P.ι)).symm
  preservesLimit_actionLeft_of_leftLinear c P.ι _

/-- If `P` is closed under cokernels, the restricted action of `c` preserves the cokernel of a
morphism `f` of `P.FullSubcategory` whose underlying morphism has a cokernel in `D`, whenever
the action of `c` on `D` preserves that cokernel. -/
instance preservesColimit_parallelPair_actionLeft [HasCokernel f.hom]
    [P.IsClosedUnderCokernels] [PreservesColimit (parallelPair f.hom 0) (actionLeft D c)] :
    PreservesColimit (parallelPair f 0) (actionLeft P.FullSubcategory c) :=
  have := P.createsCokernels f
  have := P.hasColimit_parallelPair_comp_ι f
  have := preservesColimit_of_createsColimit_and_hasColimit (parallelPair f 0) P.ι
  have : PreservesColimit (parallelPair f 0 ⋙ P.ι) (actionLeft D c) :=
    preservesColimit_of_iso_diagram (K₁ := parallelPair f.hom 0) _
      (diagramIsoParallelPair (parallelPair f 0 ⋙ P.ι)).symm
  preservesColimit_actionLeft_of_leftLinear c P.ι _

end Kernels

section Exact

variable [Preadditive D] [HasZeroObject D] [HasFiniteProducts D] [P.ContainsZero]
  [P.IsClosedUnderFiniteProducts]

/-- If `P` contains zero and is closed under finite products and kernels, the restricted action
of `c` preserves finite limits whenever the action of `c` on `D` does. -/
instance preservesFiniteLimits_actionLeft [HasKernels D] [P.IsClosedUnderKernels]
    [PreservesFiniteLimits (actionLeft D c)] :
    PreservesFiniteLimits (actionLeft P.FullSubcategory c) :=
  preservesFiniteLimits_actionLeft_of_leftLinear c P.ι

/-- If `P` contains zero and is closed under finite products and cokernels, the restricted
action of `c` preserves finite colimits whenever the action of `c` on `D` does. -/
instance preservesFiniteColimits_actionLeft [HasCokernels D] [P.IsClosedUnderCokernels]
    [PreservesFiniteColimits (actionLeft D c)] :
    PreservesFiniteColimits (actionLeft P.FullSubcategory c) :=
  preservesFiniteColimits_actionLeft_of_leftLinear c P.ι

end Exact

end ObjectProperty

end CategoryTheory
