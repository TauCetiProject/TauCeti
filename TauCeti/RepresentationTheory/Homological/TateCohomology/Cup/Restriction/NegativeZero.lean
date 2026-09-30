/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees

/-!
# Restricting negative Tate cups with a degree-zero class

For a negative-degree Tate class and a degree-zero Tate class, restriction of their cup product
is the cup product of their restrictions (`cup_res_zero_right_of_neg`). The degree-zero class is
represented by an invariant vector, so the result follows from naturality of restriction in the
coefficient representation (`res_natural_of_neg`).

This supplies the negative-degree base edge for the restriction law of the all-degree Tate cup
product. The restriction convention follows Artin and Tate, *Class Field Theory*, Preliminaries
§2, and Brown, *Cohomology of Groups*, Chapter VI §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- **Restriction preserves the Tate cup product in bidegree `(r, 0)` for `r < 0`.** For a subgroup
`H` of a finite group `G`, a class `x` of negative degree `r` and a class `y` of degree zero, the
restriction of `x ∪ y` to `H` is the cup product of the restrictions of `x` and `y`. -/
theorem cup_res_zero_right_of_neg (M N : Rep k G) (H : Subgroup G) {r : ℤ} (hr : r < 0)
    (x : tateCohomology M r) (y : tateCohomology N 0) :
    res (M ⊗ N) H r (cup M N r 0 r (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) r 0 r (by omega)
        (res M H r x) (H0Res N H y) := by
  rw [cup_zero_right, cup_zero_right]
  induction y using H0_induction_on with
  | h y =>
    rw [cupH0_H0π, H0π_comp_H0Res_apply, cupH0_H0π]
    -- `(Rep.resFunctor H.subtype).map` is `Rep.resMap H.subtype` by definition.
    have hnat : (tateCohomologyFunctor r).map (Rep.tensorInvariant M y) ≫ res (M ⊗ N) H r =
        res M H r ≫ (tateCohomologyFunctor r).map
          (Rep.resMap H.subtype (Rep.tensorInvariant M y)) :=
      res_natural_of_neg (Rep.tensorInvariant M y) H hr
    rw [Rep.resMap_tensorInvariant M N H y] at hnat
    -- The goal is `hnat` applied to `x`, with the target read in
    -- `Rep.res H.subtype M ⊗ Rep.res H.subtype N`, which is `Rep.res H.subtype (M ⊗ N)` by
    -- definition (the same identification made in the statement).
    exact ConcreteCategory.congr_hom hnat x

/-- Restriction commutes with `cupH0` in degree `-1`. This form matches the normal form of a cup
product with a degree-zero right factor. -/
@[simp]
theorem cupH0_HNegOneRes_zero_right (M N : Rep k G) (H : Subgroup G)
    (x : tateCohomology M (-1)) (y : tateCohomology N 0) :
    HNegOneRes (M ⊗ N) H (cupH0 M N (-1) x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) (-1)
        (HNegOneRes M H x) (H0Res N H y) := by
  simpa only [cup_zero_right, res_neg_one] using
    cup_res_zero_right_of_neg M N H (by omega) x y

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
    cup_res_zero_right_of_neg M N H (Int.negSucc_lt_zero n.succ) x y

end TauCeti.TateCohomology
