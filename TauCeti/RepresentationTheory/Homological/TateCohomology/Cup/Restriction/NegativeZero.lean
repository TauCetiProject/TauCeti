/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Restriction.Basic

/-!
# Restricting negative Tate cups with a degree-zero class

For a negative-degree Tate class and a degree-zero Tate class, restriction of their cup product
is the cup product of their restrictions (`cup_res_zero_right`). The degree-zero class is
represented by an invariant vector, so the result follows from naturality of restriction in the
coefficient representation (`res_natural`).

The lemmas expose the negative-degree restriction law in the `cupH0` normal form used by `simp`.
The restriction convention follows Artin and Tate, *Class Field Theory*, Preliminaries
§2, and Brown, *Cohomology of Groups*, Chapter VI §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- Restriction commutes with `cupH0` in degree `-1`. This form matches the normal form of a cup
product with a degree-zero right factor. -/
@[simp]
theorem cupH0_HNegOneRes_zero_right (M N : Rep k G) (H : Subgroup G)
    (x : tateCohomology M (-1)) (y : tateCohomology N 0) :
    HNegOneRes (M ⊗ N) H (cupH0 M N (-1) x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) (-1)
        (HNegOneRes M H x) (H0Res N H y) := by
  simpa only [cup_zero_right, res_neg_one] using
    cup_res_zero_right M N H (-1) x y

/-- Restriction commutes with `cupH0` in degree at most `-2`. This form matches the normal form
of a cup product with a degree-zero right factor. -/
@[simp]
theorem cupH0_negSuccRes_zero_right (M N : Rep k G) (H : Subgroup G) (n : ℕ) [NeZero n]
    (x : tateCohomology M (Int.negSucc n)) (y : tateCohomology N 0) :
    negSuccRes (M ⊗ N) H n (cupH0 M N (Int.negSucc n) x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) (Int.negSucc n)
        (negSuccRes M H n x) (H0Res N H y) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simpa only [cup_zero_right, res_negSucc_succ] using
    cup_res_zero_right M N H (Int.negSucc (n + 1)) x y

end TauCeti.TateCohomology
