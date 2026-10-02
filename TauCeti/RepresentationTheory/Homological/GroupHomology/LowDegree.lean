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
* `TauCeti.groupHomology.pOpcycles_comp_isoHomologyι₀_inv`: the projection of chains of degree
  zero onto the opcycles, read in homology, is the projection `H0π` to `H₀(G, A)`.
-/

public section

universe u

namespace TauCeti.groupHomology

open CategoryTheory _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- Two elements of `A` have the same class in `H₀(G, A)` exactly when their difference lies in
the augmentation submodule `Representation.Coinvariants.ker A.ρ`, the kernel of the projection to
the coinvariants. -/
theorem H0π_eq_iff {x y : A.V} :
    H0π A x = H0π A y ↔ x - y ∈ Representation.Coinvariants.ker A.ρ := by
  rw [← coinvariantsMk_comp_H0Iso_inv_apply, ← coinvariantsMk_comp_H0Iso_inv_apply]
  exact (H0Iso A).toLinearEquiv.symm.injective.eq_iff.trans
    (Representation.Coinvariants.mk_eq_iff _)

/-- In degree zero the cokernel of the differential of inhomogeneous chains is `H₀(G, A)`: the
projection of chains onto the opcycles, read in homology through `isoHomologyι₀`, is the
projection `H0π` of `A` to `H₀(G, A)`. -/
@[reassoc]
theorem pOpcycles_comp_isoHomologyι₀_inv :
    (inhomogeneousChains A).pOpcycles 0 ≫ (inhomogeneousChains A).isoHomologyι₀.inv =
      (chainsIso₀ A).hom ≫ H0π A := by
  rw [← coinvariantsMk_comp_H0Iso_inv, ← Category.assoc, ← pOpcycles_comp_opcyclesIso_hom,
    Category.assoc]
  -- `H0Iso` is `isoHomologyι₀` followed by `opcyclesIso₀`.
  exact congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc (opcyclesIso₀ A) _).symm

end TauCeti.groupHomology
