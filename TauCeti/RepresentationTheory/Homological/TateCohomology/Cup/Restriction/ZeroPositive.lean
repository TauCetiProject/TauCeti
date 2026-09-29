/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Positive

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
theorem cup_zero_left_posRes (M N : Rep k G) (H : Subgroup G) (n : ℕ)
    (x : tateCohomology M 0) (y : tateCohomology N ((n + 1 : ℕ) : ℤ)) :
    posRes (M ⊗ N) H n
        (cup M N 0 ((n + 1 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ) (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N)
        0 ((n + 1 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)
        (H0Res M H x) (posRes N H n y) := by
  rw [cup_zero_left, cup_zero_left]
  induction x using H0_induction_on with
  | h x =>
    rw [cup0H_H0π, H0π_comp_H0Res_apply, cup0H_H0π]
    let f : N ⟶ M ⊗ N := Rep.tensorInvariant N x ≫ (β_ N M).hom
    have hnat := posRes_natural N H f n
    have hnat' :
        (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map f ≫ posRes (M ⊗ N) H n =
          posRes N H n ≫ (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map
            (Rep.resMap H.subtype f) := hnat
    have hmap : Rep.resMap H.subtype f =
        Rep.tensorInvariant (Rep.res H.subtype N)
            ((Submodule.inclusion
              (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H))) x) ≫
          (β_ (Rep.res H.subtype N) (Rep.res H.subtype M)).hom := by
      ext z
      -- Restriction retains the underlying module and linear map; spelling out evaluation avoids
      -- elaborating the two definitionally equal restricted tensor representations separately.
      change f.hom z =
        ((Rep.tensorInvariant (Rep.res H.subtype N)
            ((Submodule.inclusion
              (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H))) x) ≫
          (β_ (Rep.res H.subtype N) (Rep.res H.subtype M)).hom).hom z)
      dsimp only [f]
      simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
      let xH : (Rep.res H.subtype M).ρ.invariants :=
        (Submodule.inclusion
          (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H))) x
      calc
        ((β_ N M).hom.hom ((Rep.tensorInvariant N x).hom z)) =
            (x : M.V) ⊗ₜ[k] z := TauCeti.Rep.tensorInvariant_braiding_hom_apply x z
        _ = (xH : M.V) ⊗ₜ[k] z := rfl
        _ = ((β_ (Rep.res H.subtype N) (Rep.res H.subtype M)).hom.hom
            ((Rep.tensorInvariant (Rep.res H.subtype N) xH).hom z)) :=
          (TauCeti.Rep.tensorInvariant_braiding_hom_apply xH z).symm
    rw [hmap] at hnat'
    convert congrArg (fun g => g y) hnat' using 1
    simp only [ModuleCat.comp_apply, Int.natCast_add, Int.cast_ofNat_Int, tensor_V, tensor_ρ]
    rfl

end TauCeti.TateCohomology
