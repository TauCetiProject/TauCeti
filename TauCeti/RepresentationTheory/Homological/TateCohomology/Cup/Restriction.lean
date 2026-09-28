/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees

/-!
# Restriction of the Tate cup product

The restriction law for the Tate cup product starts in bidegree `(0, 0)`: the class of
an invariant pure tensor restricts to the class of the same tensor for a subgroup. This
is the degree-zero base case for the all-degree restriction law used in Tate's theorem.

The product and restriction are those of the existing Tate cohomology API. See
Artin and Tate, *Class Field Theory*, Preliminaries, §2, and Brown,
*Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Rep
open scoped MonoidalCategory

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- Restriction preserves the product of two Tate classes of degree zero. -/
theorem res_cup_zero_zero (M N : Rep k G) (H : Subgroup G)
    (x : tateCohomology M 0) (y : tateCohomology N 0) :
    H0Res (M ⊗ N) H (cup M N 0 0 0 (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) 0 0 0 (by omega)
        (H0Res M H x) (H0Res N H y) := by
  rw [cup_zero_right, cup_zero_right]
  induction x using H0_induction_on with
  | h x =>
    induction y using H0_induction_on with
    | h y =>
      rw [cupH0_H0π_H0π, H0π_comp_H0Res_apply,
        H0π_comp_H0Res_apply, H0π_comp_H0Res_apply,
        cupH0_H0π_H0π]
      rfl

end TauCeti.TateCohomology
