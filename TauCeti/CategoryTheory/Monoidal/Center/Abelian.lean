/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import TauCeti.CategoryTheory.Monoidal.Center.Limits
public import TauCeti.CategoryTheory.Monoidal.Center.Preadditive

/-!
# The Drinfeld centre of an abelian monoidal category with exact tensor products

Let `C` be an abelian monoidal category in which tensoring on either side with any object is
additive and exact. Then the Drinfeld centre `Center C` is abelian: its additive structure is the
one induced from `C`, and its finite limits and colimits, in particular kernels and cokernels,
are computed in `C`, since the forgetful functor `Center.forget C` creates them. As the forgetful
functor preserves kernels and cokernels and reflects isomorphisms, the coimage-image comparison
of a morphism of the centre is an isomorphism because it is one in `C`.

The hypotheses hold in a rigid monoidal category, where tensoring with any object on either side
has adjoints on both sides (`TauCeti.isRightAdjoint_tensorLeft` and its relatives), so they are
found by instance search. So the centre of a rigid abelian monoidal category with additive
tensor products is abelian and `Center.forget C` is exact; this is the abelian structure on the
centre of a fusion category.

## Main declarations

* `CategoryTheory.Center.instAbelian`: the centre of an abelian monoidal category with additive
  and exact tensor products is abelian, with the preadditive structure
  `CategoryTheory.Center.instPreadditive` induced from `C`; the finite limits and colimits are
  computed in `C` by `CategoryTheory.Center.preservesFiniteLimits_forget` and
  `CategoryTheory.Center.preservesFiniteColimits_forget`.

The proof follows Sophie Morel's abelian instance on `FGModuleCat` in Mathlib
(`Mathlib/Algebra/Category/FGModuleCat/Abelian.lean`): a functor preserving kernels and cokernels
and reflecting isomorphisms transfers the coimage-image criterion.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

universe v u

namespace CategoryTheory.Center

open MonoidalCategory Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [∀ U : C, PreservesFiniteLimits (tensorLeft U)] [∀ U : C, PreservesFiniteLimits (tensorRight U)]
  [∀ U : C, PreservesFiniteColimits (tensorLeft U)]
  [∀ U : C, PreservesFiniteColimits (tensorRight U)]

/-- The Drinfeld centre of an abelian monoidal category in which tensoring on either side with any
object is additive and exact is abelian. Its preadditive structure is the one induced from `C`, and
kernels and cokernels are computed in `C`. -/
noncomputable instance instAbelian : Abelian (Center C) :=
  -- The forgetful functor preserves kernels and cokernels, so it carries the coimage-image
  -- comparison of `f` to that of `f.f`, which is an isomorphism; and it reflects isomorphisms.
  have (X Y : Center C) (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) :=
    have := IsIso.of_isIso_fac_right
      (Abelian.PreservesCoimage.hom_coimageImageComparison (forget C) f).symm
    isIso_of_reflects_iso _ (forget C)
  Abelian.ofCoimageImageComparisonIsIso

end CategoryTheory.Center
