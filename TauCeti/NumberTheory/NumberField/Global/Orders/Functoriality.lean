/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Hom
public import TauCeti.NumberTheory.NumberField.Global.Orders.NarrowPic
public import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Functoriality of Picard groups of orders

A morphism of orders `f : O → O'` extends fractional ideals: an `O`-fractional ideal `I` of `K`
goes to the `O'`-submodule of `L` spanned by `f '' I`. This is a ring homomorphism of
fractional-ideal semirings, so it maps invertible ideals to invertible ideals. It takes the
principal ideal `(x)` to `(f x)`, and `f x` is totally positive whenever `x` is. Consequently it
descends both to the wide Picard groups and to the narrow Picard groups, and the forgetful map
from narrow to wide Picard groups is natural. Each of these maps respects identities and
composition.

An order morphism `NumberFieldOrder.Hom` packages its ambient field map explicitly, and the
extension of fractional ideals is described through that map. This is no extra choice: the
localization of the ring homomorphism `f.toOrderHom` on fraction fields is exactly the ambient
field map (`NumberFieldOrder.Hom.isLocalization_map_toOrderHom`).

## Main definitions

* `NumberFieldOrder.Hom.mapFractionalIdeal`: extension of fractional ideals along an order
  morphism, a specialisation of Mathlib's `FractionalIdeal.extendedHom'`.
* `NumberFieldOrder.Hom.mapInvertible`: the induced map of invertible fractional ideals.
* `NumberFieldOrder.Hom.mapPic`: the induced map of wide Picard groups.
* `NumberFieldOrder.Hom.mapNarrowPic`: the induced map of narrow Picard groups.

## Main results

* `NumberFieldOrder.Hom.mapFractionalIdeal_spanSingleton`: principal ideals go to principal ideals.
* `NumberFieldOrder.Hom.mapPic_mkPic`, `NumberFieldOrder.Hom.mapNarrowPic_mk`: the maps on ideal
  classes.
* `NumberFieldOrder.Hom.mapPic_comp`, `NumberFieldOrder.Hom.mapNarrowPic_comp` and the identity
  lemmas: functoriality.
* `NumberFieldOrder.narrowToPic_natural`: the forgetful map `NarrowPic → Pic` is natural.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [NumberField L]
variable {M : Type*} [Field M] [NumberField M]
variable {O : NumberFieldOrder K} {O' : NumberFieldOrder L} {O'' : NumberFieldOrder M}

namespace Hom

/-- An order morphism carries nonzero divisors of the source order to nonzero divisors of the
target order. -/
theorem nonZeroDivisors_le_comap (f : Hom O O') :
    nonZeroDivisors O.toSubalgebra ≤
      (nonZeroDivisors O'.toSubalgebra).comap f.toOrderHom :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ f.toOrderHom_injective

/-- On fraction fields, the localization of `f.toOrderHom` is the ambient field map of `f`. -/
@[simp]
theorem isLocalization_map_toOrderHom (f : Hom O O') :
    IsLocalization.map L f.toOrderHom f.nonZeroDivisors_le_comap = f.fieldHom :=
  IsFractionRing.ringHom_ext (A := O.toSubalgebra) fun x => by
    rw [IsLocalization.map_eq]
    exact f.toOrderHom_apply x

/-- Extension of fractional ideals along a morphism of orders: `I` goes to the `O'`-submodule of
`L` spanned by its image. -/
def mapFractionalIdeal (f : Hom O O') :
    FractionalIdeal (nonZeroDivisors O.toSubalgebra) K →+*
      FractionalIdeal (nonZeroDivisors O'.toSubalgebra) L :=
  FractionalIdeal.extendedHom' L f.nonZeroDivisors_le_comap

/-- The extension of a fractional ideal is the `O'`-span of its image under the field map. -/
theorem coe_mapFractionalIdeal (f : Hom O O')
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
    (f.mapFractionalIdeal I : Submodule O'.toSubalgebra L) =
      Submodule.span O'.toSubalgebra (f '' I) := by
  rw [mapFractionalIdeal, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.coe_extended_eq_span, isLocalization_map_toOrderHom]

/-- An element of the extension is an `O'`-linear combination of images of elements of `I`. -/
theorem mem_mapFractionalIdeal_iff (f : Hom O O')
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (y : L) :
    y ∈ f.mapFractionalIdeal I ↔ y ∈ Submodule.span O'.toSubalgebra (f '' I) := by
  rw [← coe_mapFractionalIdeal, FractionalIdeal.mem_coe]

/-- The image of an element of a fractional ideal lies in the extended ideal. -/
theorem map_mem_mapFractionalIdeal (f : Hom O O')
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} {x : K} (hx : x ∈ I) :
    f x ∈ f.mapFractionalIdeal I :=
  (f.mem_mapFractionalIdeal_iff I (f x)).mpr (Submodule.subset_span ⟨x, hx, rfl⟩)

/-- The extension of the principal fractional ideal `(x)` is the principal ideal `(f x)`. -/
@[simp]
theorem mapFractionalIdeal_spanSingleton (f : Hom O O') (x : K) :
    f.mapFractionalIdeal (FractionalIdeal.spanSingleton _ x) =
      FractionalIdeal.spanSingleton _ (f x) := by
  rw [mapFractionalIdeal, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_spanSingleton, isLocalization_map_toOrderHom]

/-- Extension along the identity morphism is the identity. -/
@[simp]
theorem mapFractionalIdeal_id (O : NumberFieldOrder K) :
    (Hom.id O).mapFractionalIdeal = RingHom.id _ := by
  ext I : 1
  rw [← FractionalIdeal.coeToSubmodule_inj, coe_mapFractionalIdeal]
  simp only [id_apply, Set.image_id']
  exact Submodule.span_eq (I : Submodule O.toSubalgebra K)

/-- Extension of fractional ideals respects composition of order morphisms. -/
theorem mapFractionalIdeal_comp (g : Hom O' O'') (f : Hom O O') :
    (g.comp f).mapFractionalIdeal = g.mapFractionalIdeal.comp f.mapFractionalIdeal := by
  ext I : 1
  simp only [mapFractionalIdeal, RingHom.comp_apply, FractionalIdeal.extendedHom'_apply]
  rw [FractionalIdeal.extended_extended]
  simp only [toOrderHom_comp]

/-- Extension of invertible fractional ideals along a morphism of orders. -/
def mapInvertible (f : Hom O O') :
    O.invertibleProperFractionalIdeals →* O'.invertibleProperFractionalIdeals :=
  Units.map f.mapFractionalIdeal.toMonoidHom

/-- The underlying fractional ideal of `f.mapInvertible I` is the extension of `I`. -/
@[simp]
theorem coe_mapInvertible (f : Hom O O') (I : O.invertibleProperFractionalIdeals) :
    (f.mapInvertible I : FractionalIdeal (nonZeroDivisors O'.toSubalgebra) L) =
      f.mapFractionalIdeal I := by
  simp [mapInvertible]

/-- The extension of a nonzero principal fractional ideal is generated by the image of its
generator. -/
@[simp]
theorem mapInvertible_toPrincipalIdeal (f : Hom O O') (x : Kˣ) :
    f.mapInvertible (toPrincipalIdeal O.toSubalgebra K x) =
      toPrincipalIdeal O'.toSubalgebra L (Units.map f.fieldHom x) := by
  ext : 1
  simp [coe_toPrincipalIdeal]

/-- Extension of invertible ideals along the identity morphism is the identity. -/
@[simp]
theorem mapInvertible_id (O : NumberFieldOrder K) :
    (Hom.id O).mapInvertible = MonoidHom.id _ := by
  ext I : 2
  simp

/-- Extension of invertible ideals respects composition of order morphisms. -/
theorem mapInvertible_comp (g : Hom O' O'') (f : Hom O O') :
    (g.comp f).mapInvertible = g.mapInvertible.comp f.mapInvertible := by
  ext I : 2
  simp [mapFractionalIdeal_comp]

/-- The extension of an ideal with a totally positive generator again has a totally positive
generator. -/
theorem mapInvertible_mem_narrowPrincipal (f : Hom O O')
    {I : O.invertibleProperFractionalIdeals} (hI : I ∈ O.narrowPrincipal) :
    f.mapInvertible I ∈ O'.narrowPrincipal := by
  obtain ⟨x, hx, rfl⟩ := O.mem_narrowPrincipal_iff.mp hI
  exact O'.mem_narrowPrincipal_iff.mpr
    ⟨Units.map f.fieldHom x, by simpa using f.isTotallyPositive_map hx,
      (f.mapInvertible_toPrincipalIdeal x).symm⟩

/-- The map of wide Picard groups induced by a morphism of orders: the class of `I` goes to the
class of its extension. -/
def mapPic (f : Hom O O') : Pic O →* Pic O' :=
  O.mkPic.liftOfSurjective O.mkPic_surjective
    ⟨O'.mkPic.comp f.mapInvertible, fun I hI => by
      obtain ⟨x, rfl⟩ := ClassGroup.mk_eq_one_iff_exists.mp (MonoidHom.mem_ker.mp hI)
      simp⟩

/-- On the class of an invertible ideal, `mapPic` gives the class of its extension. -/
@[simp]
theorem mapPic_mkPic (f : Hom O O') (I : O.invertibleProperFractionalIdeals) :
    f.mapPic (O.mkPic I) = O'.mkPic (f.mapInvertible I) :=
  O.mkPic.liftOfRightInverse_comp_apply _ _ _ I

/-- The map of narrow Picard groups induced by a morphism of orders: the narrow class of `I` goes
to the narrow class of its extension. This is well defined because the image of a totally positive
generator is totally positive. -/
def mapNarrowPic (f : Hom O O') : NarrowPic O →* NarrowPic O' :=
  NarrowPic.lift O ((NarrowPic.mk O').comp f.mapInvertible) fun I hI => by
    simpa using f.mapInvertible_mem_narrowPrincipal hI

/-- On the narrow class of an invertible ideal, `mapNarrowPic` gives the narrow class of its
extension. -/
@[simp]
theorem mapNarrowPic_mk (f : Hom O O') (I : O.invertibleProperFractionalIdeals) :
    f.mapNarrowPic (NarrowPic.mk O I) = NarrowPic.mk O' (f.mapInvertible I) :=
  NarrowPic.lift_mk _ _ _ I

/-- The identity morphism induces the identity on the wide Picard group. -/
@[simp]
theorem mapPic_id (O : NumberFieldOrder K) : (Hom.id O).mapPic = MonoidHom.id _ :=
  (MonoidHom.cancel_right O.mkPic_surjective).mp <| MonoidHom.ext fun I => by simp

/-- The maps on wide Picard groups respect composition of order morphisms. -/
theorem mapPic_comp (g : Hom O' O'') (f : Hom O O') :
    (g.comp f).mapPic = g.mapPic.comp f.mapPic :=
  (MonoidHom.cancel_right O.mkPic_surjective).mp <| MonoidHom.ext fun I => by
    simp [mapInvertible_comp]

/-- The identity morphism induces the identity on the narrow Picard group. -/
@[simp]
theorem mapNarrowPic_id (O : NumberFieldOrder K) :
    (Hom.id O).mapNarrowPic = MonoidHom.id _ :=
  (MonoidHom.cancel_right (NarrowPic.mk_surjective O)).mp <| MonoidHom.ext fun I => by simp

/-- The maps on narrow Picard groups respect composition of order morphisms. -/
theorem mapNarrowPic_comp (g : Hom O' O'') (f : Hom O O') :
    (g.comp f).mapNarrowPic = g.mapNarrowPic.comp f.mapNarrowPic :=
  (MonoidHom.cancel_right (NarrowPic.mk_surjective O)).mp <| MonoidHom.ext fun I => by
    simp [mapInvertible_comp]

end Hom

/-- Forgetting positivity commutes with the maps induced by a morphism of orders. -/
@[simp]
theorem narrowToPic_mapNarrowPic (f : Hom O O') (c : NarrowPic O) :
    O'.narrowToPic (f.mapNarrowPic c) = f.mapPic (O.narrowToPic c) := by
  obtain ⟨I, rfl⟩ := NarrowPic.mk_surjective O c
  simp

/-- **Naturality of the forgetful map.** For a morphism of orders `f : O → O'`, the square formed
by `narrowToPic` and the maps induced by `f` on narrow and wide Picard groups commutes. -/
theorem narrowToPic_natural (f : Hom O O') :
    O'.narrowToPic.comp f.mapNarrowPic = f.mapPic.comp O.narrowToPic :=
  MonoidHom.ext (narrowToPic_mapNarrowPic f)

end NumberFieldOrder

end TauCeti.GlobalNumberFields
