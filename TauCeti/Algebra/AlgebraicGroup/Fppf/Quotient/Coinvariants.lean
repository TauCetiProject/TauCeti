/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.ShortExact

/-!
# Representing normal fppf quotients by coinvariants

Let `G` be a geometrically reduced affine group of finite type over a field, and let
`N` be a normal closed subgroup. The fppf quotient `G/N` is represented by the affine
group whose coordinate Hopf algebra consists of the `N`-coinvariant functions on `G`.
The subgroup `N` may be nonreduced, and the field need not be perfect.

The isomorphism `coinvariantsFppfQuotientIso` identifies the sheaf quotient projection
with the morphism induced by the inclusion of coinvariants. The coordinate maps form
a short exact sequence, recorded by `isShortExact_coinvariantsι_mkQuotient`.

This combines `faithfullyFlat_coinvariantsι`, `kernelHopfIdeal_coinvariantsι_eq`,
and the fppf first isomorphism theorem `kernelFppfQuotientIso`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H]
  {I : HopfIdeal k H}

/-- The fppf quotient by a normal closed subgroup of a geometrically reduced finite-type
affine group is represented by its coinvariant Hopf algebra. -/
def coinvariantsFppfQuotientIso (hI : I.IsNormal) :
    fppfQuotientSheaf H I hI ≅ pointsFppfGroupObject (coinvariants hI) :=
  eqToIso (by simp only [kernelHopfIdeal_coinvariantsι_eq hI]) ≪≫
    kernelFppfQuotientIso (coinvariantsι hI) (faithfullyFlat_coinvariantsι hI)
      (finitePresentation_coinvariantsι hI)

/-- The representing isomorphism carries the fppf quotient projection to the affine
group morphism defined by the inclusion of coinvariants. -/
@[reassoc (attr := simp), simp]
theorem fppfQuotientProjection_comp_coinvariantsFppfQuotientIso_hom
    (hI : I.IsNormal) :
    fppfQuotientProjection H I hI ≫ (coinvariantsFppfQuotientIso hI).hom =
      pointsFppfGroupObjectMap (coinvariantsι hI) := by
  rw [coinvariantsFppfQuotientIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc]
  have transport (J : HopfIdeal k H) (hJ : J.IsNormal) (h : J = I)
      (e : fppfQuotientSheaf H I hI = fppfQuotientSheaf H J hJ) :
      fppfQuotientProjection H I hI ≫ eqToHom e = fppfQuotientProjection H J hJ := by
    subst J
    simp
  rw [transport _ _ (kernelHopfIdeal_coinvariantsι_eq hI), kernelFppfQuotientIso_hom]
  exact fppfQuotientProjection_comp_kernelFppfQuotientHom (coinvariantsι hI)

end

end TauCeti.CommHopfAlgCat
