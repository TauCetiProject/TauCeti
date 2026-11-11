/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
public import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Blowing up the singular subscheme of a relative curve

For a syntomic relative curve over an arbitrary commutative ring, blowing up the singular
subscheme is an isomorphism over the smooth locus. Thus modifications obtained by blowing up
the singular subscheme preserve the smooth part of the curve.

## References

* The Stacks Project, Lemma 31.32.4, Tag 02OG (blowups away from their centre).
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Blowing up the singular subscheme of a syntomic relative curve changes nothing over its
smooth locus. -/
theorem isIso_blowupToBase_singularLocus_restrict_smoothLocus
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    IsIso ((X.singularLocus R).blowupToBase ∣_ (X ↘ Spec (.of R)).smoothLocus) := by
  apply IdealSheafData.isIso_blowupToBase_restrict_of_disjoint_support
  rw [X.support_singularLocus_eq_compl_smoothLocus]
  exact disjoint_compl_right

end AlgebraicGeometry.Scheme
