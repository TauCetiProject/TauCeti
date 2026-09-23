/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Low-degree group cohomology

For a trivial representation `A` of a group `G`, Mathlib identifies `H¹(G, A)` with the group of
additive homomorphisms `G →+ A`. This file records the consequence that `H¹(G, A)` vanishes when
`G` is finite and `A` has no additive torsion, since a homomorphism from a finite group into a
torsion-free group is zero.

## Main statements

* `TauCeti.groupCohomology.isZero_H1_of_isTrivial`: `H¹(G, A) = 0` for a trivial representation `A`
  of a finite group `G` without additive torsion.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- `H¹(G, A) = 0` for a trivial representation `A` of a finite group `G` whose underlying module
has no additive torsion. -/
theorem isZero_H1_of_isTrivial [Finite G] (A : Rep k G) [A.IsTrivial] [IsAddTorsionFree A] :
    IsZero (groupCohomology A 1) :=
  -- `H¹(G, A)` is `Hom(G, A)`, and a homomorphism from a finite group to a torsion-free group
  -- vanishes
  have : Subsingleton (Additive G →+ A) := subsingleton_of_forall_eq 0 fun f ↦
    AddMonoidHom.ext fun g ↦ (f.isOfFinAddOrder (isOfFinAddOrder_of_finite g)).eq_zero'
  (ModuleCat.isZero_of_subsingleton (ModuleCat.of k (Additive G →+ A))).of_iso <|
    H1IsoOfIsTrivial A

end TauCeti.groupCohomology
