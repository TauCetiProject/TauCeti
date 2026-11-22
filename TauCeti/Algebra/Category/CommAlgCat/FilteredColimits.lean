/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Filtered colimits in commutative algebras

The forgetful functor from commutative algebras over a base ring to commutative rings preserves
filtered colimits: a colimit of the underlying diagram of rings carries the algebra structure
induced by any one of its legs, and is then a colimit of commutative algebras. This follows the
construction of filtered colimits of algebras in Mathlib
(`Mathlib/Algebra/Category/AlgCat/FilteredColimits.lean`). Consequently the forgetful functor
from commutative algebras to types preserves small filtered colimits, and, since the forgetful
functor from algebras to types reflects filtered colimits, so does the forgetful functor from
commutative algebras to algebras.
-/

public section

open CategoryTheory Limits

universe v u

namespace CommAlgCat

variable {Base : Type u} [CommRing Base]

section

variable {J : Type*} [Category* J] {F : J ⥤ CommAlgCat.{v} Base}
  {c : Cocone (F ⋙ forget₂ _ CommRingCat.{v})}

/-- (Implementation): The algebra structure on the cocone point of the underlying diagram of
rings induced by the `j`-th leg. When `J` is filtered, every choice of `j` gives the same
structure. -/
private abbrev algebraOfIsFiltered (j : J) : Algebra Base c.pt :=
  ((c.ι.app j).hom.comp (algebraMap Base (F.obj j))).toAlgebra

variable [IsFilteredOrEmpty J]

/-- The cocone of the underlying diagram of rings lifted to `CommAlgCat Base`, with the algebra
structure on the cocone point induced by the `j`-th leg. -/
private def coconeOfIsFiltered (j : J) : Cocone F where
  pt :=
    letI : Algebra Base c.pt := algebraOfIsFiltered j
    of Base c.pt
  ι.app k := by
    letI : Algebra Base c.pt := algebraOfIsFiltered j
    refine ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra, ← c.w (IsFiltered.leftToMax j k),
      ← c.w (IsFiltered.rightToMax j k)]
  ι.naturality k k' f := by
    ext
    exact c.ι.naturality_apply _ _

/-- The lifted cocone is colimiting. -/
private def isColimitCoconeOfIsFiltered (hc : IsColimit c) (j : J) :
    IsColimit (coconeOfIsFiltered (c := c) j) where
  desc s := by
    letI : Algebra Base c.pt := algebraOfIsFiltered j
    refine ofHom { __ := (hc.desc <| Functor.mapCocone _ s).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply]
  fac s k := by
    ext
    apply elementwise_of% hc.fac
  uniq s m hm := by
    ext
    congrm $(hc.uniq (Functor.mapCocone _ s) ((forget₂ _ _).map m) fun j ↦ ?_) _
    ext
    congrm $(hm _) _

end

/-- The forgetful functor from commutative algebras to commutative rings preserves filtered
colimits. -/
noncomputable instance forget₂CommRingCat_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{v} Base) CommRingCat.{v}) where
  preserves_filtered_colimits J _ _ := ⟨fun {F} ↦
    have hc := colimit.isColimit (F ⋙ forget₂ _ CommRingCat.{v})
    preservesColimit_of_preserves_colimit_cocone
      (isColimitCoconeOfIsFiltered hc (IsFiltered.nonempty (C := J)).some)
      -- The lifted cocone is mapped back to `c` itself.
      (hc.ofIsoColimit (Cocone.ext (Iso.refl _)))⟩

/-- The forgetful functor from commutative algebras to types preserves small filtered colimits. -/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget (CommAlgCat.{v} Base)) where
  preserves_filtered_colimits _ _ _ :=
    preservesColimitsOfShape_of_natIso
      (eqToIso (HasForget₂.forget_comp (C := CommAlgCat.{v} Base) (D := CommRingCat.{v})))

/-- The forgetful functor from commutative algebras to algebras preserves small filtered
colimits. -/
noncomputable instance forget₂AlgCat_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{v} Base) (AlgCat.{v} Base)) where
  preserves_filtered_colimits J _ _ :=
    have : PreservesColimitsOfShape J
        (forget₂ (CommAlgCat.{v} Base) (AlgCat.{v} Base) ⋙ forget (AlgCat.{v} Base)) :=
      preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
    have : ReflectsColimitsOfShape J (forget (AlgCat.{v} Base)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    preservesColimitsOfShape_of_reflects_of_preserves _ (forget (AlgCat.{v} Base))

end CommAlgCat
