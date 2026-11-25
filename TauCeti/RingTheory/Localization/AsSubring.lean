/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Dedekind localizations inside fraction fields

The localization of a Dedekind domain at nonzero denominators, realized inside its fraction
field by `Localization.subalgebra.ofField`, is again a Dedekind domain.
-/

public section

namespace Localization.subalgebra

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  (S : Submonoid A) (hS : S ≤ A⁰)

/-- The localization of a Dedekind domain at a submonoid of nonzero elements, realized inside its
fraction field, is a Dedekind domain. -/
instance isDedekindDomain_ofField [IsDedekindDomain A] : IsDedekindDomain (ofField K S hS) :=
  IsLocalization.isDedekindDomain A hS _

end Localization.subalgebra
