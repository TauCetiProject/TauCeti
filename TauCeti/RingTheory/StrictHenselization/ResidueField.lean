/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local
public import TauCeti.FieldTheory.IsSepClosed
import TauCeti.RingTheory.StrictHenselization.Etale

/-!
# The residue field of the strict henselization

Let `algebra R Ω` be the colimit of the pointed étale neighbourhoods of `(R, Ω)` and
`toTarget : algebra R Ω →ₐ[R] Ω` the map induced by their pointings. For a local ring `R` and a
separable algebraic extension `Ω` of its residue field, `toTarget` is surjective
(`toTarget_surjective`) and its kernel is the maximal ideal (`ker_toTarget_eq_maximalIdeal`), so
`toTarget` identifies the residue field of `algebra R Ω` with `Ω` (`residueFieldEquiv`). This is
property (3) of Stacks, Tag 04GP: the residue field of the strict henselization of `R` with
respect to a separable closure `Ω` of its residue field is `Ω`. In particular the strict
henselization is strictly henselian (`isSepClosed_residueField`): it is a henselian local ring
(`henselianLocalRing`) with separably closed residue field.

## Main results

* `TauCeti.StrictHenselization.residueFieldEquiv`: the residue field of `algebra R Ω` is `Ω`.
* `TauCeti.StrictHenselization.isSepClosed_residueField`: if `Ω` is moreover separably closed,
  then so is the residue field of `algebra R Ω`.

## References

* [Stacks Project, Lemma 10.155.2](https://stacks.math.columbia.edu/tag/04GP), property (3).
-/

public section

open IsLocalRing

universe u

namespace TauCeti.StrictHenselization

section ResidueField

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
  [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω]

/-- The residue field of the colimit of pointed étale neighbourhoods is `Ω`, through the map
induced by `toTarget`. For a separable closure `Ω` of the residue field of `R`, this identifies
the residue field of the strict henselization of `R` with `Ω`. -/
@[stacks 04GP "(3)"]
noncomputable def residueFieldEquiv : ResidueField (algebra R Ω) ≃ₐ[R] Ω :=
  (Ideal.quotientEquivAlgOfEq R (ker_toTarget_eq_maximalIdeal R Ω).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toTarget_surjective R Ω))

/-- `residueFieldEquiv` sends the residue of `x` to `toTarget x`. -/
@[simp]
theorem residueFieldEquiv_residue (x : algebra R Ω) :
    residueFieldEquiv R Ω (residue (algebra R Ω) x) = toTarget R Ω x := by
  have h : maximalIdeal (algebra R Ω) = RingHom.ker (toTarget R Ω) :=
    (ker_toTarget_eq_maximalIdeal R Ω).symm
  -- `ResidueField` is by definition the quotient by the maximal ideal, with `residue` its
  -- quotient map (`residue_def`). Rewriting with `residue_def` would change the type of the
  -- argument, so state the unfolded form directly.
  change Ideal.quotientKerAlgEquivOfSurjective (toTarget_surjective R Ω)
    (Ideal.quotientEquivAlgOfEq R h (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The inverse of `residueFieldEquiv` sends `toTarget x` to the residue of `x`. -/
@[simp]
theorem residueFieldEquiv_symm_toTarget (x : algebra R Ω) :
    (residueFieldEquiv R Ω).symm (toTarget R Ω x) = residue (algebra R Ω) x :=
  (residueFieldEquiv R Ω).symm_apply_eq.mpr (residueFieldEquiv_residue R Ω x).symm

/-- If `Ω` is separably closed, so is the residue field of the colimit of pointed étale
neighbourhoods. Together with `henselianLocalRing`, this says that the strict henselization of a
local ring with respect to a separable closure of its residue field is strictly henselian. -/
@[stacks 04GP "(3)"]
instance isSepClosed_residueField [IsSepClosed Ω] :
    IsSepClosed (ResidueField (algebra R Ω)) :=
  .of_ringEquiv (residueFieldEquiv R Ω).symm.toRingEquiv

end ResidueField

end TauCeti.StrictHenselization
