/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Pi

/-!
# Orthogonal sums with one summand

Evaluation identifies an orthogonal sum indexed by a unique type with its sole summand.
The induced map on discriminant groups is the corresponding coordinate projection. These
identifications let single-component glue constructions use the same orthogonal-sum API as
reducible ones.
-/

public section

namespace TauCeti.IntegralLattice

namespace Isometry

variable {ι : Type*} [Fintype ι] [Unique ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]

/-- Evaluation is an isometry from a one-summand orthogonal sum to its sole summand. -/
def piUnique (L : ∀ i, IntegralLattice (V i)) : Isometry (IntegralLattice.pi L) (L default) where
  toIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.piUnique ℚ V
      map_app' x y := by simp [pi_form, piForm_apply] }
  map_carrier := by
    ext y
    rw [Submodule.mem_map_equiv, mem_pi_carrier_iff]
    constructor
    · intro h
      exact h default
    · intro h i
      obtain rfl := Unique.eq_default i
      exact h

/-- The one-summand isometry evaluates at the unique index. -/
@[simp]
theorem piUnique_apply (L : ∀ i, IntegralLattice (V i)) (x : ∀ i, V i) :
    piUnique L x = x default := (rfl)

/-- The inverse one-summand isometry places a vector in the unique coordinate. -/
@[simp]
theorem piUnique_symm_apply (L : ∀ i, IntegralLattice (V i)) (y : V default) :
    (piUnique L).symm y = (LinearEquiv.piUnique ℚ V).symm y := by
  refine EquivLike.injective (piUnique L) ?_
  rw [apply_symm_apply, piUnique_apply]
  exact ((LinearEquiv.piUnique ℚ V).apply_symm_apply y).symm

/-- The unique coordinate of the inverse one-summand isometry is the original vector. -/
@[simp]
theorem piUnique_symm_apply_default (L : ∀ i, IntegralLattice (V i)) (y : V default) :
    (piUnique L).symm y default = y := by
  rw [piUnique_symm_apply]
  exact (LinearEquiv.piUnique ℚ V).apply_symm_apply y

/-- On discriminant groups the one-summand isometry extracts the unique component. -/
@[simp]
theorem discriminantGroupEquiv_piUnique (L : ∀ i, IntegralLattice (V i))
    (c : (IntegralLattice.pi L).DiscriminantGroup) :
    (piUnique L).discriminantGroupEquiv c = discriminantGroupPiEquiv L c default := by
  induction c using Submodule.Quotient.induction_on with
  | _ x =>
    rw [discriminantGroupEquiv_mk, discriminantGroupPiEquiv_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    simpa only [coe_dualCarrierEquiv_apply, coe_piDualCarrierEquiv_apply] using piUnique_apply L x

end Isometry

end TauCeti.IntegralLattice
