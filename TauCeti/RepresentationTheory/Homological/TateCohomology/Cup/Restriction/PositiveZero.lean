/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Restriction.Basic

/-!
# Restricting a Tate cup product with a degree-zero class

For a positive-degree Tate class and a degree-zero Tate class, restriction of their cup product
is the cup product of their restrictions. The degree-zero class is represented by an invariant
vector. The compatibility is stated in its `cupH0` normal form.

This is the `(n + 1, 0)` case of the restriction law for the all-degree Tate cup product.
The restriction convention follows Artin and Tate, *Class Field Theory*, Preliminaries §2,
and Brown, *Cohomology of Groups*, Chapter VI §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G]

attribute [local instance] Subgroup.fintypeOfFinite

variable [Fintype G]

/-- Restriction commutes with `cupH0` in positive degree. This form matches the normal form of a
cup product with a degree-zero right factor. -/
-- The displayed degree and target make the left-hand side match the form seen by `simp`.
@[simp]
theorem cupH0_posRes_zero_right (M N : Rep k G) (H : Subgroup G) (n : ℕ)
    (x : tateCohomology M ((n + 1 : ℕ) : ℤ)) (y : tateCohomology N 0) :
    (show tateCohomology (M ⊗ N) ((n : ℤ) + 1) ⟶
        tateCohomology (Rep.res H.subtype (M ⊗ N)) ((n : ℤ) + 1) from
      posRes (M ⊗ N) H n) (cupH0 M N ((n : ℤ) + 1) x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) ((n : ℤ) + 1)
        (posRes M H n x) (H0Res N H y) := by
  simpa only [cup_zero_right, Int.natCast_add, Int.cast_ofNat_Int, res_ofNat_succ] using
    cup_res_zero_right M N H ((n + 1 : ℕ) : ℤ) x y

end TauCeti.TateCohomology
