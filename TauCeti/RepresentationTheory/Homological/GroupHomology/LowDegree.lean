/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Group homology in degree zero

Complements to Mathlib's `Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree`, which
identifies `H₀(G, A)` with the coinvariants of `A`.

## Main results

* `TauCeti.groupHomology.H0π_eq_iff`: two elements of `A` have the same class in `H₀(G, A)`
  exactly when their difference lies in the augmentation submodule
  `Representation.Coinvariants.ker A.ρ`.
-/

public section

universe u

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- Two elements of `A` have the same class in `H₀(G, A)` exactly when their difference lies in
the augmentation submodule `Representation.Coinvariants.ker A.ρ`, the kernel of the projection to
the coinvariants. -/
theorem H0π_eq_iff {x y : A.V} :
    H0π A x = H0π A y ↔ x - y ∈ Representation.Coinvariants.ker A.ρ := by
  rw [← coinvariantsMk_comp_H0Iso_inv_apply, ← coinvariantsMk_comp_H0Iso_inv_apply]
  exact (H0Iso A).toLinearEquiv.symm.injective.eq_iff.trans
    (Representation.Coinvariants.mk_eq_iff _)

end TauCeti.groupHomology
