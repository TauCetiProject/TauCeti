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

Restriction preserves the Tate cup product with a degree-zero right factor in every integer
degree (`cup_res_zero_right`). An invariant vector represents the right factor, so coefficient
naturality gives this base case of the all-degree restriction law used in Tate's theorem. In
bidegree `(0, 0)`, restriction carries an invariant pure tensor to the tensor of its restrictions.

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

-- Subgroup restriction includes an invariant pure tensor as the tensor of the included factors.
omit [Fintype G] in
private theorem restrict_invariant_pure_tensor (M N : Rep k G) (H : Subgroup G)
    (x : M.ρ.invariants) (y : N.ρ.invariants) :
    ((Submodule.inclusion
      (Representation.invariants_le_invariants_comp_subtype (ρ := (M ⊗ N).ρ) (H := H)))
      (⟨(x : M.V) ⊗ₜ[k] (y : N.V), fun g ↦ by
        simp [Representation.tprod_apply, x.2 g, y.2 g]⟩ : (M ⊗ N).ρ.invariants) :
        (Rep.res H.subtype (M ⊗ N)).ρ.invariants).1 =
      (((Submodule.inclusion
        (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H))) x :
          (Rep.res H.subtype M).ρ.invariants).1 ⊗ₜ[k]
        ((Submodule.inclusion
          (Representation.invariants_le_invariants_comp_subtype (ρ := N.ρ) (H := H))) y :
            (Rep.res H.subtype N).ρ.invariants).1) := by
  rfl

/-- Restriction commutes with the degree-zero cup product in its `cupH0` normal form.
This is the form used by `simp` after reducing `cup` and `res` in degree zero. -/
@[simp]
theorem cupH0_H0Res (M N : Rep k G) (H : Subgroup G)
    (x : tateCohomology M 0) (y : tateCohomology N 0) :
    H0Res (M ⊗ N) H (cupH0 M N 0 x y) =
      cupH0 (Rep.res H.subtype M) (Rep.res H.subtype N) 0
        (H0Res M H x) (H0Res N H y) := by
  induction x using H0_induction_on with
  | h x =>
    induction y using H0_induction_on with
    | h y =>
      rw [cupH0_H0π_H0π, H0π_comp_H0Res_apply,
        H0π_comp_H0Res_apply, H0π_comp_H0Res_apply,
        cupH0_H0π_H0π]
      exact congrArg (H0π (Rep.res H.subtype (M ⊗ N)))
        (Subtype.ext (restrict_invariant_pure_tensor M N H x y))

/-- Restriction preserves the Tate cup product with a degree-zero right factor, in every
integer degree. -/
theorem cup_res_zero_right (M N : Rep k G) (H : Subgroup G) (r : ℤ)
    (x : tateCohomology M r) (y : tateCohomology N 0) :
    res (M ⊗ N) H r (cup M N r 0 r (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) r 0 r (by omega)
        (res M H r x) (H0Res N H y) := by
  rw [cup_zero_right, cup_zero_right]
  induction y using H0_induction_on with
  | h y =>
    rw [cupH0_H0π, H0π_comp_H0Res_apply, cupH0_H0π]
    have hnat : (tateCohomologyFunctor r).map (Rep.tensorInvariant M y) ≫ res (M ⊗ N) H r =
        res M H r ≫ (tateCohomologyFunctor r).map
          (Rep.resMap H.subtype (Rep.tensorInvariant M y)) :=
      res_natural (Rep.tensorInvariant M y) H r
    rw [Rep.resMap_tensorInvariant M N H y] at hnat
    -- The goal is `hnat` applied to `x`, with the target read in
    -- `Rep.res H.subtype M ⊗ Rep.res H.subtype N`, which is `Rep.res H.subtype (M ⊗ N)` by
    -- definition (the same identification made in the statement).
    exact ConcreteCategory.congr_hom hnat x

end TauCeti.TateCohomology
