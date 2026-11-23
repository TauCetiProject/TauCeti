/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.FinitePresentation

/-!
# Finite presentation of effective Cartier divisors

The closed immersion of an effective Cartier divisor is locally of finite presentation: its
local principal equations give finitely generated defining ideals. Consequently, on a scheme
locally of finite presentation over a base, the divisor is also locally of finite presentation
over that base. No noetherian hypothesis is needed.

In particular, for a relative effective Cartier divisor on a smooth relative curve, this supplies
the finite-presentation condition required in addition to finiteness and flatness for a finite
locally free structure morphism.

## References

* Stacks Project, *Divisors*, Effective Cartier divisors, Tag 01WQ.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti

variable {X S : Scheme.{u}} {I : X.IdealSheafData}

/-- The inclusion of an effective Cartier divisor is locally of finite presentation over
an arbitrary ambient scheme. -/
theorem locallyOfFinitePresentation_subschemeι_of_isEffectiveCartier (hI : I.IsEffectiveCartier) :
    LocallyOfFinitePresentation I.subschemeι := by
  apply I.locallyOfFinitePresentation_subschemeι_of_locallyPrincipal
  intro x
  obtain ⟨U, hx, a, -, hUa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff I).mp hI x
  exact ⟨U, hx, a, hUa⟩

/-- An effective Cartier divisor on a scheme locally of finite presentation over `S` is
locally of finite presentation over `S`. -/
theorem locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier
    (hI : I.IsEffectiveCartier) {f : X ⟶ S} [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (I.subschemeι ≫ f) := by
  have := locallyOfFinitePresentation_subschemeι_of_isEffectiveCartier hI
  infer_instance

end TauCeti


namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {E : X.IdealSheafData}

/-- An effective Cartier ideal has finitely generated section ideals on every affine open. -/
theorem IsEffectiveCartier.fg_ideal (hE : E.IsEffectiveCartier) (U : X.affineOpens) :
    (E.ideal U).FG := by
  have := TauCeti.locallyOfFinitePresentation_subschemeι_of_isEffectiveCartier hE
  exact E.fg_ideal U

end AlgebraicGeometry.Scheme.IdealSheafData
