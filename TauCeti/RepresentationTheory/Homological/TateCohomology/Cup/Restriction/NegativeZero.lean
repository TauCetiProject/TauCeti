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
is the cup product of their restrictions. The degree-zero class is represented by an invariant
vector, so the result follows from naturality of relative or homological transfer in the
coefficient representation.

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

/-- Restriction commutes with the Tate cup product in bidegree `(-1, 0)`. This form applies to
the all-degree `cup` operation. -/
theorem cup_HNegOneRes_zero_right (M N : Rep k G) (H : Subgroup G)
    (x : tateCohomology M (-1)) (y : tateCohomology N 0) :
    HNegOneRes (M ⊗ N) H (cup M N (-1) 0 (-1) (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) (-1) 0 (-1) (by omega)
        (HNegOneRes M H x) (H0Res N H y) := by
  rw [cup_zero_right, cup_zero_right]
  induction y using H0_induction_on with
  | h y =>
    rw [cupH0_H0π, H0π_comp_H0Res_apply, cupH0_H0π]
    have hnat := HNegOneRes_natural (Rep.tensorInvariant M y) H
    have hnat' :
        (tateCohomologyFunctor (-1)).map (Rep.tensorInvariant M y) ≫
          HNegOneRes (M ⊗ N) H =
        HNegOneRes M H ≫ (tateCohomologyFunctor (-1)).map
          (Rep.resMap H.subtype (Rep.tensorInvariant M y)) := hnat
    rw [Rep.resMap_tensorInvariant M N H y] at hnat'
    convert congrArg (fun f ↦ f x) hnat' using 1
    simp only [ModuleCat.comp_apply]
    simp only [tensor_V, tensor_ρ]
    rfl

/-- Restriction commutes with `cupH0` in degree `-1`. This form matches the normal form of a cup
product with a degree-zero right factor. -/
@[simp]
theorem cupH0_HNegOneRes_zero_right (M N : Rep k G) (H : Subgroup G)
    (x : tateCohomology M (-1)) (y : tateCohomology N 0) :
    HNegOneRes (M ⊗ N) H (cupH0 M N (-1) x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) (-1)
        (HNegOneRes M H x) (H0Res N H y) := by
  simpa only [cup_zero_right] using cup_HNegOneRes_zero_right M N H x y

/-- Restriction commutes with the Tate cup product in bidegree `(-(n + 1), 0)` for `n > 0`.
This form applies to the all-degree `cup` operation. -/
theorem cup_negSuccRes_zero_right (M N : Rep k G) (H : Subgroup G) (n : ℕ) [NeZero n]
    (x : tateCohomology M (Int.negSucc n)) (y : tateCohomology N 0) :
    negSuccRes (M ⊗ N) H n
        (cup M N (Int.negSucc n) 0 (Int.negSucc n) (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N)
        (Int.negSucc n) 0 (Int.negSucc n) (by omega)
        (negSuccRes M H n x) (H0Res N H y) := by
  rw [cup_zero_right, cup_zero_right]
  induction y using H0_induction_on with
  | h y =>
    rw [cupH0_H0π, H0π_comp_H0Res_apply, cupH0_H0π]
    have hnat := negSuccRes_natural (Rep.tensorInvariant M y) H n
    have hnat' :
        (tateCohomologyFunctor (Int.negSucc n)).map (Rep.tensorInvariant M y) ≫
          negSuccRes (M ⊗ N) H n =
        negSuccRes M H n ≫ (tateCohomologyFunctor (Int.negSucc n)).map
          (Rep.resMap H.subtype (Rep.tensorInvariant M y)) := hnat
    rw [Rep.resMap_tensorInvariant M N H y] at hnat'
    convert congrArg (fun f ↦ f x) hnat' using 1
    simp only [ModuleCat.comp_apply]
    simp only [tensor_V, tensor_ρ]
    rfl

/-- Restriction commutes with `cupH0` in degree at most `-2`. This form matches the normal form
of a cup product with a degree-zero right factor. -/
@[simp]
theorem cupH0_negSuccRes_zero_right (M N : Rep k G) (H : Subgroup G) (n : ℕ) [NeZero n]
    (x : tateCohomology M (Int.negSucc n)) (y : tateCohomology N 0) :
    negSuccRes (M ⊗ N) H n (cupH0 M N (Int.negSucc n) x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) (Int.negSucc n)
        (negSuccRes M H n x) (H0Res N H y) := by
  simpa only [cup_zero_right] using cup_negSuccRes_zero_right M N H n x y

end TauCeti.TateCohomology
