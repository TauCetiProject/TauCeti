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

/-- Restriction preserves the product of two Tate classes of degree zero. -/
theorem cup_res_zero_zero (M N : Rep k G) (H : Subgroup G)
    (x : tateCohomology M 0) (y : tateCohomology N 0) :
    res (M ⊗ N) H 0 (cup M N 0 0 0 (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) 0 0 0 (by omega)
        (res M H 0 x) (res N H 0 y) := by
  simpa only [res_zero, cup_zero_right] using cupH0_H0Res M N H x y

end TauCeti.TateCohomology
