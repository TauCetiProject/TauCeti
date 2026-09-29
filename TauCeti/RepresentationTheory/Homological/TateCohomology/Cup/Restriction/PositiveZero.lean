/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Positive

/-!
# Restricting a Tate cup product with a degree-zero class

For a positive-degree Tate class and a degree-zero Tate class, restriction of their cup product
is the cup product of their restrictions. The degree-zero class is represented by an invariant
vector. The compatibility is stated for both the all-degree cup product and its `cupH0` form.

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

/-- Restriction commutes with the Tate cup product in bidegree `(n + 1, 0)`: the
restriction of the cup equals the cup of the restricted classes. This form applies to the
all-degree `cup` operation. -/
theorem cup_posRes_zero_right (M N : Rep k G) (H : Subgroup G) (n : ℕ)
    (x : tateCohomology M ((n + 1 : ℕ) : ℤ)) (y : tateCohomology N 0) :
    posRes (M ⊗ N) H n
        (cup M N ((n + 1 : ℕ) : ℤ) 0 ((n + 1 : ℕ) : ℤ) (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N)
        ((n + 1 : ℕ) : ℤ) 0 ((n + 1 : ℕ) : ℤ) (by omega)
        (posRes M H n x) (H0Res N H y) := by
  rw [cup_zero_right, cup_zero_right]
  induction y using H0_induction_on with
  | h y =>
    rw [cupH0_H0π, H0π_comp_H0Res_apply, cupH0_H0π]
    have hnat := posRes_natural M H (Rep.tensorInvariant M y) n
    have hnat' :
        (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map (Rep.tensorInvariant M y) ≫
          posRes (M ⊗ N) H n =
        posRes M H n ≫ (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map
          (Rep.resMap H.subtype (Rep.tensorInvariant M y)) := hnat
    rw [Rep.resMap_tensorInvariant M N H y] at hnat'
    -- The two cup expressions reduce to the same composite. `convert` aligns the
    -- integer degree casts and restricted tensor representation in that composite.
    convert congrArg (fun f => f x) hnat' using 1
    simp only [ModuleCat.comp_apply]
    simp only [Int.natCast_add, Int.cast_ofNat_Int, tensor_V, tensor_ρ]
    rfl

/-- Restriction commutes with `cupH0` in positive degree. This form matches the normal form of a
cup product with a degree-zero right factor. -/
theorem cupH0_posRes_zero_right (M N : Rep k G) (H : Subgroup G) (n : ℕ)
    (x : tateCohomology M ((n + 1 : ℕ) : ℤ)) (y : tateCohomology N 0) :
    posRes (M ⊗ N) H n (cupH0 M N ((n + 1 : ℕ) : ℤ) x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) ((n + 1 : ℕ) : ℤ)
        (posRes M H n x) (H0Res N H y) := by
  simpa only [cup_zero_right] using
    cup_posRes_zero_right M N H n x y

end TauCeti.TateCohomology
