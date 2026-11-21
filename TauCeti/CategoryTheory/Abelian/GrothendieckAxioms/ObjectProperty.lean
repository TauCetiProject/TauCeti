/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels and cokernels of colimits of morphisms

Let `C` be an abelian category in which colimits of shape `J` are exact, and let `P` be a property
of objects of `C` closed under isomorphisms and under colimits of shape `J`. For a natural
transformation `α : F ⟶ G` of `J`-shaped diagrams, the functor `colim` preserves kernels and
cokernels, so the kernel of the induced map `colimMap α` of colimits is the colimit of the kernels
of the components `α.app j`, and likewise for cokernels. Hence the kernel (or cokernel) of
`colimMap α` satisfies `P` as soon as the kernel (or cokernel) of every component does
(`CategoryTheory.ObjectProperty.prop_kernel_colimMap`,
`CategoryTheory.ObjectProperty.prop_cokernel_colimMap`).

For discrete `J`, these are statements about sums of morphisms `Sigma.map f`
(`CategoryTheory.ObjectProperty.prop_kernel_sigmaMap`,
`CategoryTheory.ObjectProperty.prop_cokernel_sigmaMap`). With `P` a Serre class closed under
coproducts, they say that a sum of isomorphisms modulo `P` is one; for instance in a category of
modules, where coproducts are exact, the kernel and the cokernel of a sum of maps whose kernels and
cokernels are killed by an integer `e` are killed by `e`. The zero objects are closed under all
colimits (`TauCeti.CategoryTheory.ObjectProperty.ColimitsOfShape`), so for `P` the zero objects
these say that a colimit of isomorphisms is an isomorphism.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]

section Colim

variable {J : Type*} [Category* J] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
  [P.IsClosedUnderColimitsOfShape J] {F G : J ⥤ C} (α : F ⟶ G)

/-- If colimits of shape `J` are exact, the kernel of the map of colimits induced by a natural
transformation `α` of `J`-shaped diagrams satisfies a property closed under isomorphisms and
colimits of shape `J` as soon as the kernels of all components of `α` do. -/
lemma prop_kernel_colimMap (h : ∀ j, P (kernel (α.app j))) : P (kernel (colimMap α)) :=
  -- `colim` preserves kernels, and kernels in the functor category are computed pointwise.
  P.prop_of_iso (PreservesKernel.iso colim α) <| P.prop_colimit _ fun j ↦
    P.prop_of_iso (PreservesKernel.iso ((evaluation J C).obj j) α).symm (h j)

omit [HasExactColimitsOfShape J C] in
/-- If colimits of shape `J` are exact, the cokernel of the map of colimits induced by a natural
transformation `α` of `J`-shaped diagrams satisfies a property closed under isomorphisms and
colimits of shape `J` as soon as the cokernels of all components of `α` do. -/
lemma prop_cokernel_colimMap (h : ∀ j, P (cokernel (α.app j))) : P (cokernel (colimMap α)) :=
  -- `colim` preserves cokernels, and cokernels in the functor category are computed pointwise.
  P.prop_of_iso (PreservesCokernel.iso colim α) <| P.prop_colimit _ fun j ↦
    P.prop_of_iso (PreservesCokernel.iso ((evaluation J C).obj j) α).symm (h j)

end Colim

section Sigma

variable {β : Type*} [HasColimitsOfShape (Discrete β) C] [HasExactColimitsOfShape (Discrete β) C]
  [P.IsClosedUnderColimitsOfShape (Discrete β)] {X Y : β → C} (f : ∀ b, X b ⟶ Y b)

/-- If coproducts indexed by `β` are exact, the kernel of a sum of morphisms `∐ X ⟶ ∐ Y` satisfies
a property closed under isomorphisms and `β`-indexed coproducts as soon as the kernels of all
summands do. -/
lemma prop_kernel_sigmaMap (h : ∀ b, P (kernel (f b))) : P (kernel (Limits.Sigma.map f)) :=
  P.prop_kernel_colimMap (F := Discrete.functor X) (G := Discrete.functor Y)
    (Discrete.natTrans fun b ↦ f b.as) fun b ↦ h b.as

omit [HasExactColimitsOfShape (Discrete β) C] in
/-- If coproducts indexed by `β` are exact, the cokernel of a sum of morphisms `∐ X ⟶ ∐ Y`
satisfies a property closed under isomorphisms and `β`-indexed coproducts as soon as the cokernels
of all summands do. -/
lemma prop_cokernel_sigmaMap (h : ∀ b, P (cokernel (f b))) : P (cokernel (Limits.Sigma.map f)) :=
  P.prop_cokernel_colimMap (F := Discrete.functor X) (G := Discrete.functor Y)
    (Discrete.natTrans fun b ↦ f b.as) fun b ↦ h b.as

end Sigma

end CategoryTheory.ObjectProperty
