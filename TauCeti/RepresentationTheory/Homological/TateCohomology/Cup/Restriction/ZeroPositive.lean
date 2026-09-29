/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees

/-!
# Restricting a Tate cup product with a degree-zero first factor

For a degree-zero Tate class and a positive-degree Tate class, restriction of their cup product
is the cup product of their restrictions. A degree-zero class is represented by an invariant
vector. Cupping with it is induced by tensoring with that vector and applying the tensor symmetry,
so the result follows from naturality of positive-degree Tate restriction in the coefficients.

This is the `(0, n + 1)` case of the restriction law for the all-degree Tate cup product. The
restriction convention follows Artin and Tate, *Class Field Theory*, Preliminaries §2, and Brown,
*Cohomology of Groups*, Chapter VI §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G]

attribute [local instance] Subgroup.fintypeOfFinite

variable [Fintype G]

/-- Restriction commutes with the Tate cup product in bidegree `(0, n + 1)`. -/
theorem cup_res_zero_positive (M N : Rep k G) (H : Subgroup G) (n : ℕ)
    (x : tateCohomology M 0) (y : tateCohomology N ((n : ℤ) + 1)) :
    res (M ⊗ N) H ((n : ℤ) + 1) (cup M N 0 ((n : ℤ) + 1) ((n : ℤ) + 1) (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) 0 ((n : ℤ) + 1) ((n : ℤ) + 1) (by omega)
        (res M H 0 x) (res N H ((n : ℤ) + 1) y) := by
  rw [res_zero, res_ofNat_succ, res_ofNat_succ, cup_zero_left, cup_zero_left]
  induction x using H0_induction_on with
  | h x =>
    rw [cup0H_H0π, H0π_comp_H0Res_apply, cup0H_H0π]
    have hnat := posRes_natural N H (Rep.tensorInvariant N x ≫ (β_ N M).hom) n
    have hnat' :
        (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map
            (Rep.tensorInvariant N x ≫ (β_ N M).hom) ≫ posRes (M ⊗ N) H n =
          posRes N H n ≫ (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map
            (Rep.resMap H.subtype (Rep.tensorInvariant N x ≫ (β_ N M).hom)) := hnat
    rw [TauCeti.Rep.resMap_tensorInvariant_braiding N H.subtype x
      ((Submodule.inclusion
        (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H))) x)
      (Submodule.coe_inclusion _ x)] at hnat'
    convert congrArg (fun g => g y) hnat' using 1
    simp only [ModuleCat.comp_apply, Int.natCast_add, Int.cast_ofNat_Int, tensor_V, tensor_ρ]
    rfl

end TauCeti.TateCohomology
