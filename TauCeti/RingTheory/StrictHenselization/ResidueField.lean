/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.ResidueField.Quotient
public import TauCeti.RingTheory.StrictHenselization.Henselian
public import TauCeti.RingTheory.Henselian.Strict
public import TauCeti.FieldTheory.IsSepClosed
public import TauCeti.RingTheory.StrictHenselization.Etale

/-!
# The residue field of the strict henselization

Let `algebra R Ω` be the colimit of the pointed étale neighbourhoods of `(R, Ω)` and
`toTarget : algebra R Ω →ₐ[R] Ω` the map induced by their pointings. For a local ring `R` and a
separable algebraic extension `Ω` of its residue field, `toTarget` is surjective
(`toTarget_surjective`) and its kernel is the maximal ideal (`ker_toTarget_eq_maximalIdeal`), so
`toTarget` identifies the residue field of `algebra R Ω` with `Ω` (`residueFieldEquiv`). This is
property (3) of Stacks, Tag 04GP: the residue field of the strict henselization of `R` with
respect to a separable closure `Ω` of its residue field is `Ω`. In particular the strict
henselization is strictly henselian (`isSepClosed_residueField`,
`isStrictlyHenselianLocalRing_algebra`): it is a henselian local ring (`henselianLocalRing`) with
separably closed residue field.

## Main results

* `TauCeti.StrictHenselization.residueFieldEquiv`: the residue field of `algebra R Ω` is `Ω`.
* `TauCeti.StrictHenselization.isSepClosed_residueField` and
  `TauCeti.StrictHenselization.isSepClosed_residueField_strictHenselization`: if `Ω` is moreover
  separably closed (in particular a separable closure of `ResidueField R`), then so is the residue
  field of `algebra R Ω`.
* `TauCeti.StrictHenselization.isStrictlyHenselianLocalRing_algebra`: when `Ω` is a separable
  closure of `ResidueField R`, `algebra R Ω` is strictly henselian.

## References

* [Stacks Project, Lemma 10.155.2](https://stacks.math.columbia.edu/tag/04GP), property (3).
-/

public section

open _root_.IsLocalRing

universe u

namespace TauCeti.StrictHenselization

section ResidueField

variable (R Ω : Type u) [CommRing R] [_root_.IsLocalRing R] [Field Ω] [Algebra R Ω]
  [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω]

/-- The residue field of the colimit of pointed étale neighbourhoods is `Ω`, through the map
induced by `toTarget`. For a separable closure `Ω` of the residue field of `R`, this identifies
the residue field of the strict henselization of `R` with `Ω`. -/
@[stacks 04GP "(3)"]
noncomputable def residueFieldEquiv : ResidueField (algebra R Ω) ≃ₐ[R] Ω :=
  residueFieldAlgEquivOfSurjective (toTarget_surjective R Ω)

/-- `residueFieldEquiv R Ω` is `residueFieldAlgEquivOfSurjective` applied to
`toTarget_surjective R Ω`. -/
theorem residueFieldEquiv_def :
    residueFieldEquiv R Ω = residueFieldAlgEquivOfSurjective (toTarget_surjective R Ω) :=
  (rfl)

/-- `residueFieldEquiv` sends the residue of `x` to `toTarget x`. -/
@[simp]
theorem residueFieldEquiv_residue (x : algebra R Ω) :
    residueFieldEquiv R Ω (residue (algebra R Ω) x) = toTarget R Ω x :=
  residueFieldAlgEquivOfSurjective_residue (toTarget_surjective R Ω) x

/-- The inverse of `residueFieldEquiv` sends `toTarget x` to the residue of `x`. -/
@[simp]
theorem residueFieldEquiv_symm_toTarget (x : algebra R Ω) :
    (residueFieldEquiv R Ω).symm (toTarget R Ω x) = residue (algebra R Ω) x :=
  residueFieldAlgEquivOfSurjective_symm_apply (toTarget_surjective R Ω) x

/-- If `Ω` is separably closed, so is the residue field of the colimit of pointed étale
neighbourhoods. Together with `henselianLocalRing`, this says that the strict henselization of a
local ring with respect to a separable closure of its residue field is strictly henselian. -/
@[stacks 04GP "(3)"]
instance isSepClosed_residueField [IsSepClosed Ω] :
    IsSepClosed (ResidueField (algebra R Ω)) :=
  .of_ringEquiv (residueFieldEquiv R Ω).symm.toRingEquiv

end ResidueField

section SepClosure

variable (R Ω : Type u) [CommRing R] [_root_.IsLocalRing R] [Field Ω] [Algebra R Ω]
  [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [IsSepClosure (ResidueField R) Ω]

/-- The residue field of the strict henselization of a local ring `R` with respect to a separable
closure `Ω` of `ResidueField R` is separably closed. Because Mathlib's `IsSepClosure.sep_closed` is
not an instance, this supplies `IsSepClosed (ResidueField (algebra R Ω))` directly from
`[IsSepClosure (ResidueField R) Ω]`. -/
@[stacks 04GP "(3)"]
instance isSepClosed_residueField_strictHenselization :
    IsSepClosed (ResidueField (algebra R Ω)) :=
  have : IsSepClosed Ω := IsSepClosure.sep_closed (ResidueField R)
  inferInstance

/-- The strict henselization of a local ring with respect to a separable closure `Ω` of its residue
field is strictly henselian. -/
@[stacks 04GP "(2)"]
instance isStrictlyHenselianLocalRing_algebra :
    IsStrictlyHenselianLocalRing (algebra R Ω) :=
  inferInstance

end SepClosure

end TauCeti.StrictHenselization
