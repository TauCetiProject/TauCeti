/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.Blowup.Restriction
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
public import TauCeti.AlgebraicGeometry.Fibers.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Blowups of flat schemes over a Bezout domain

Let `R` be a Bezout domain, for instance a discrete valuation ring, and let `X` be a flat scheme
over `R`. The blowup `Bl_I X` of `X` along an arbitrary ideal sheaf `I` is again flat over `R`.

Indeed, the exceptional divisor of `Bl_I X` is an effective Cartier divisor, so its open
complement is scheme-theoretically dense in `Bl_I X`. That complement is isomorphic to the open
`X ∖ V(I)` of `X`, which is flat over `R`. Over a Bezout domain, flatness passes from a
scheme-theoretically dense open to the whole scheme
(`TauCeti.flat_of_isSchemeTheoreticallyDominant_of_flat_comp`). No hypothesis on `I` is needed: no
finite type condition, and no condition on where its support lies.

Over a discrete valuation ring this is what lets blowups of models in centres of the special
fibre remain flat models.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.flat_blowupToBase_comp`: the blowup of a flat scheme
  over a Bezout domain is flat over it.

## References

* [The Stacks Project, Section *Blowing up*](https://stacks.math.columbia.edu/tag/01OF).
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002,
  Proposition 4.3.9, for flatness over Dedekind schemes.
-/

public section

noncomputable section

open CategoryTheory TauCeti

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The blowup of a flat scheme over a Bezout domain is flat.** If `X` is flat over a Bezout
domain `R`, then so is the blowup `Bl_I X` of `X` along any ideal sheaf `I`. -/
theorem flat_blowupToBase_comp {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
    (toBase : X ⟶ Spec (.of R)) [Flat toBase] : Flat (I.blowupToBase ≫ toBase) := by
  -- The complement of the exceptional divisor is dense, and it is `X ∖ V(I)`.
  have := I.isEffectiveCartier_comap_blowupToBase.isSchemeTheoreticallyDominant_support_compl_ι
  rw [compl_support_comap] at this
  have : Flat ((I.blowupToBase ⁻¹ᵁ I.support.compl).ι ≫ I.blowupToBase ≫ toBase) := by
    rw [← Category.assoc, ← morphismRestrict_ι]
    infer_instance
  exact flat_of_isSchemeTheoreticallyDominant_of_flat_comp
    (I.blowupToBase ⁻¹ᵁ I.support.compl).ι _

end AlgebraicGeometry.Scheme.IdealSheafData
