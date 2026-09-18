/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal

/-!
# The closed monoidal category of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. This file makes sheaves of `R`-modules
into a closed symmetric monoidal category. Consequently, tensoring on the left has the internal
Hom functor as a right adjoint; Mathlib's standard `ihom.adjunction`, `ihom.ev`, and `ihom.coev`
provide the tensor--Hom adjunction, evaluation, and coevaluation.

The construction has two stages. Tensoring presheaves of modules preserves small colimits, and
the free modules on representables form a small separating family. The special adjoint functor
theorem therefore gives a right adjoint to tensoring by each presheaf. Day's reflection theorem
then transports this closed structure across the reflective sheafification adjunction. Thus the
internal Hom of sheaves is the sheafification of the presheaf internal Hom.

## Main declarations

* `TauCeti.SheafOfModules.presheafMonoidalClosed` gives the closed structure on presheaves of
  modules over the ring presheaf underlying `R`;
* `TauCeti.SheafOfModules.monoidalClosed` gives the closed structure on sheaves of modules;
* `SheafOfModules.ihom_obj` identifies its internal Hom object with the sheafification of the
  presheaf internal Hom.

The use of the special adjoint functor theorem and Day reflection follows the construction of
closed monoidal structures on sheaf categories in Mathlib's
`CategoryTheory.Monoidal.Braided.Reflection` and `Condensed.Light.Monoidal`.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed PresheafOfModules

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

local notation "preservesTensorLeft" =>
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierTensorLeft

/-- The closed monoidal structure on presheaves of modules over the ring presheaf underlying `R`.
Its internal Hom is the right adjoint supplied by the special adjoint functor theorem. -/
instance presheafMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (ringCatSheaf R).obj) where
  closed M :=
    letI : MonoidalCategory (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
      PresheafOfModules.monoidalCategory (R := R.obj)
    letI : PreservesColimitsOfSize.{u, u} (tensorLeft M) := preservesTensorLeft M
    letI := isLeftAdjoint_of_preservesColimits_of_isSeparating.{u}
      (PresheafOfModules.freeYoneda.isSeparating (ringCatSheaf R).obj) (tensorLeft M)
    { rightAdj := (tensorLeft M).rightAdjoint
      adj := Adjunction.ofIsLeftAdjoint (tensorLeft M) }

/-- The closed symmetric monoidal structure on sheaves of `R`-modules. It is obtained from the
closed structure on presheaves of modules by Day's reflection theorem. -/
instance monoidalClosed : MonoidalClosed (SheafOfModules.{u} (ringCatSheaf R)) :=
  Monoidal.Reflective.monoidalClosed
    (PresheafOfModules.sheafificationAdjunction (R := ringCatSheaf R)
      (R₀ := (ringCatSheaf R).obj) (J := J) (𝟙 (ringCatSheaf R).obj))

variable {R}

/-- The internal Hom of sheaves of modules is the sheafification of the internal Hom of their
underlying presheaves of modules. -/
@[simp]
theorem _root_.SheafOfModules.ihom_obj
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (ihom M).obj N =
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((ihom M.val).obj N.val) := rfl

/-- On morphisms, the internal Hom of sheaves of modules is induced by sheafification from the
internal Hom of presheaves of modules. -/
@[simp]
theorem _root_.SheafOfModules.ihom_map
    (M : SheafOfModules.{u} (ringCatSheaf R)) {N P : SheafOfModules.{u} (ringCatSheaf R)}
    (f : N ⟶ P) :
    (ihom M).map f =
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        ((ihom M.val).map f.val) := rfl

end SheafOfModules

end

end TauCeti
