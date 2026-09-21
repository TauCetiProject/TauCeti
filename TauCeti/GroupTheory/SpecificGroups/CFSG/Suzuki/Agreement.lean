/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.SpecialIsogeny
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.Agreement

/-!
# The Suzuki special isogeny in the pinned symplectic model

This file extends the shared rank-two `B₂` carrier comparison with the data specific to a
`TauCeti.SuzukiLieIndex`. On the standard symplectic matrix group it uses the existing
characteristic-two special isogeny, defines its odd power, and transports both maps independently
to the pinned `Sp₄/ℤ` scheme points. It then proves that the shared carrier equivalence intertwines
both maps.

The pinned half-Frobenius is the matrix special isogeny `TauCeti.specialIsogeny`, rather than a
map transported from the explicit carrier. Its odd power is therefore an independently built
pinned Steinberg map. The square relation and the numbered simple-root equations below verify that
this pinned map has the expected half-Frobenius behavior.

## Main definitions

* `TauCeti.SuzukiLieIndex.symplecticSteinberg`: the odd power of the imported special isogeny on
  the standard symplectic matrix group.
* `TauCeti.SuzukiLieIndex.pinnedHalfFrobenius` and
  `TauCeti.SuzukiLieIndex.pinnedSteinberg`: the corresponding independently defined maps on the
  pinned scheme points.

## Main results

* `TauCeti.SuzukiLieIndex.carrierEquivPinned_halfFrobenius` and
  `TauCeti.SuzukiLieIndex.carrierEquivPinned_steinberg`: the carrier equivalence intertwines the
  Suzuki maps.
* `TauCeti.SuzukiLieIndex.pinnedHalfFrobenius_pinnedHalfFrobenius`: the pinned special isogeny
  squares to prime-field Frobenius.
* `TauCeti.SuzukiLieIndex.pinnedHalfFrobenius_pinnedSimpleRootSubgroup`: its action on the
  numbered simple-root subgroups has the expected exponents.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.SuzukiLieIndex

variable (d : SuzukiLieIndex)

/-! ## The special isogeny and the Steinberg map on the symplectic side -/

/-- **The Steinberg map of a Suzuki index on the standard symplectic matrix group**: the odd power
`τ ^ (2m+1)` of the special isogeny, for `2m+1` the field exponent the index records. -/
noncomputable def symplecticSteinberg :
    d.toRankTwoBLieIndex.StandardGroup →* d.toRankTwoBLieIndex.StandardGroup :=
  HPow.hPow (α := Monoid.End d.toRankTwoBLieIndex.StandardGroup)
    (TauCeti.specialIsogeny (R := d.1.Closure)) d.1.fieldExponent

/-- The special isogeny on the pinned symplectic scheme points. -/
noncomputable def pinnedHalfFrobenius :
    d.toRankTwoBLieIndex.PinnedGroup →* d.toRankTwoBLieIndex.PinnedGroup :=
  d.toRankTwoBLieIndex.pinnedEquivSymplectic.symm.toMonoidHom.comp
    ((TauCeti.specialIsogeny (R := d.1.Closure)).comp
      d.toRankTwoBLieIndex.pinnedEquivSymplectic.toMonoidHom)

/-- **The independently defined Steinberg map on the pinned symplectic scheme points**: the odd
power `τ ^ (2m+1)` of the pinned special isogeny. -/
noncomputable def pinnedSteinberg :
    d.toRankTwoBLieIndex.PinnedGroup →* d.toRankTwoBLieIndex.PinnedGroup :=
  HPow.hPow (α := Monoid.End d.toRankTwoBLieIndex.PinnedGroup) d.pinnedHalfFrobenius
    d.1.fieldExponent

/-- The canonical matrix realization intertwines the pinned and matrix special isogenies. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedHalfFrobenius (g : d.toRankTwoBLieIndex.PinnedGroup) :
    d.toRankTwoBLieIndex.pinnedEquivSymplectic (d.pinnedHalfFrobenius g) =
      TauCeti.specialIsogeny (d.toRankTwoBLieIndex.pinnedEquivSymplectic g) := by
  rw [pinnedHalfFrobenius, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

/-- The canonical matrix realization intertwines the pinned and matrix Steinberg maps. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedSteinberg (g : d.toRankTwoBLieIndex.PinnedGroup) :
    d.toRankTwoBLieIndex.pinnedEquivSymplectic (d.pinnedSteinberg g) =
      d.symplecticSteinberg (d.toRankTwoBLieIndex.pinnedEquivSymplectic g) := by
  have hpinned : ⇑d.pinnedSteinberg = (⇑d.pinnedHalfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.PinnedGroup) d.pinnedHalfFrobenius
      d.1.fieldExponent
  have hstandard : ⇑d.symplecticSteinberg =
      (⇑(TauCeti.specialIsogeny (R := d.1.Closure)))^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.StandardGroup)
      (TauCeti.specialIsogeny (R := d.1.Closure)) d.1.fieldExponent
  have hsemi : Function.Semiconj d.toRankTwoBLieIndex.pinnedEquivSymplectic d.pinnedHalfFrobenius
      (TauCeti.specialIsogeny (R := d.1.Closure)) :=
    d.pinnedEquivSymplectic_pinnedHalfFrobenius
  have hiter := hsemi.iterate_right d.1.fieldExponent g
  rwa [← hpinned, ← hstandard] at hiter

/-! ## The comparison on a Suzuki index -/

/-- **The carrier equivalence intertwines the two special isogenies.** -/
@[simp]
theorem carrierEquivSymplectic_halfFrobenius (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivSymplectic (d.halfFrobenius g) =
      TauCeti.specialIsogeny (d.toRankTwoBLieIndex.carrierEquivSymplectic g) := by
  rw [RankTwoBLieIndex.carrierEquivSymplectic_apply,
    RankTwoBLieIndex.carrierEquivSymplectic_apply, halfFrobenius_def,
    SpStd.pointsMulEquivGLSymplecticFin_specialIsogeny]

/-- **The carrier equivalence intertwines the two Steinberg maps.** Both sides are the same odd
power of their own special isogeny. -/
@[simp]
theorem carrierEquivSymplectic_steinberg (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivSymplectic (d.steinberg g) =
      d.symplecticSteinberg (d.toRankTwoBLieIndex.carrierEquivSymplectic g) := by
  have hcarrier : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] := by
    rw [steinberg_def]
    exact Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.AmbientGroup) d.halfFrobenius
      d.1.fieldExponent
  have hstandard : ⇑d.symplecticSteinberg =
      (⇑(TauCeti.specialIsogeny (R := d.1.Closure)))^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.StandardGroup)
      (TauCeti.specialIsogeny (R := d.1.Closure)) d.1.fieldExponent
  have hsemi : Function.Semiconj d.toRankTwoBLieIndex.carrierEquivSymplectic d.halfFrobenius
      (TauCeti.specialIsogeny (R := d.1.Closure)) := d.carrierEquivSymplectic_halfFrobenius
  have hiter := hsemi.iterate_right d.1.fieldExponent g
  rwa [← hcarrier, ← hstandard] at hiter

/-- The carrier-to-pinned equivalence intertwines the two special isogenies. -/
@[simp]
theorem carrierEquivPinned_halfFrobenius (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivPinned (d.halfFrobenius g) =
      d.pinnedHalfFrobenius (d.toRankTwoBLieIndex.carrierEquivPinned g) := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned,
    carrierEquivSymplectic_halfFrobenius, pinnedEquivSymplectic_pinnedHalfFrobenius,
    RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned]

/-- **The explicit carrier's Steinberg map agrees with the independently defined Steinberg map on
the pinned symplectic scheme points.** -/
@[simp]
theorem carrierEquivPinned_steinberg (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivPinned (d.steinberg g) =
      d.pinnedSteinberg (d.toRankTwoBLieIndex.carrierEquivPinned g) := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned, carrierEquivSymplectic_steinberg,
    pinnedEquivSymplectic_pinnedSteinberg,
    RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned]

/-! ## The pinned half-Frobenius is a half-Frobenius -/

/-- **The square of the special isogeny on the standard symplectic matrix group is the prime-field
Frobenius**, that is `τ ^ 2 = Frob_p` at the defining characteristic `p = 2`. -/
theorem symplecticHalfFrobenius_symplecticHalfFrobenius (g : d.toRankTwoBLieIndex.StandardGroup) :
    TauCeti.specialIsogeny (TauCeti.specialIsogeny g) =
      d.toRankTwoBLieIndex.symplecticPrimeFrobenius g := by
  obtain ⟨g, rfl⟩ := d.toRankTwoBLieIndex.carrierEquivSymplectic.surjective g
  rw [← carrierEquivSymplectic_halfFrobenius,
    ← carrierEquivSymplectic_halfFrobenius, halfFrobenius_halfFrobenius,
    RankTwoBLieIndex.carrierEquivSymplectic_primeFrobenius]

/-- **The square of the special isogeny on the pinned symplectic scheme points is the prime-field
Frobenius.** Together with the simple-root equation below this is what makes the pinned map a
half-Frobenius in the sense the Suzuki family's Steinberg map is built from. -/
@[simp]
theorem pinnedHalfFrobenius_pinnedHalfFrobenius (g : d.toRankTwoBLieIndex.PinnedGroup) :
    d.pinnedHalfFrobenius (d.pinnedHalfFrobenius g) =
      d.toRankTwoBLieIndex.pinnedPrimeFrobenius g := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [pinnedEquivSymplectic_pinnedHalfFrobenius, pinnedEquivSymplectic_pinnedHalfFrobenius,
    RankTwoBLieIndex.pinnedEquivSymplectic_pinnedPrimeFrobenius,
    symplecticHalfFrobenius_symplecticHalfFrobenius]

/-- **The special isogeny exchanges the two numbered simple root subgroups of the standard
symplectic matrix group**, raising the parameter to the index's exponent at that root, which is one
at the long simple root and the defining characteristic at the short one. -/
@[simp]
theorem symplecticHalfFrobenius_symplecticSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    TauCeti.specialIsogeny (d.toRankTwoBLieIndex.symplecticSimpleRootSubgroup i u) =
      d.toRankTwoBLieIndex.symplecticSimpleRootSubgroup
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  rw [← RankTwoBLieIndex.carrierEquivSymplectic_simpleRootSubgroup,
    ← carrierEquivSymplectic_halfFrobenius, halfFrobenius_simpleRootSubgroup,
    RankTwoBLieIndex.carrierEquivSymplectic_simpleRootSubgroup]

/-- **The special isogeny exchanges the two numbered simple root subgroups of the pinned symplectic
scheme points**, with the same exponents. -/
@[simp]
theorem pinnedHalfFrobenius_pinnedSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.pinnedHalfFrobenius (d.toRankTwoBLieIndex.pinnedSimpleRootSubgroup i u) =
      d.toRankTwoBLieIndex.pinnedSimpleRootSubgroup
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [pinnedEquivSymplectic_pinnedHalfFrobenius,
    RankTwoBLieIndex.pinnedEquivSymplectic_pinnedSimpleRootSubgroup,
    RankTwoBLieIndex.pinnedEquivSymplectic_pinnedSimpleRootSubgroup,
    symplecticHalfFrobenius_symplecticSimpleRootSubgroup]

end TauCeti.SuzukiLieIndex
