/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Semilinear transport of monoid algebra actions

A semilinear map commuting with the monoid action intertwines the monoid algebra actions
provided that the coefficients are transported through the scalar ring homomorphism.
This applies to the action of a group algebra projector under a change of complex embedding.
-/

public section

namespace LinearMap

/-- A semilinear intertwiner transports the action of a monoid algebra element to the action
of the coefficientwise image of that element. -/
theorem map_asAlgebraHom_apply_of_intertwines
    {R S G V W : Type*} [CommSemiring R] [CommSemiring S] [Monoid G]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module S W]
    {σ : R →+* S} (f : V →ₛₗ[σ] W) {ρ : Representation R G V} {τ : Representation S G W}
    (hf : ∀ g v, f (ρ g v) = τ g (f v)) (a : MonoidAlgebra R G) (v : V) :
    f (ρ.asAlgebraHom a v) = τ.asAlgebraHom (MonoidAlgebra.mapRingHom G σ a) (f v) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g r => simp [Representation.asAlgebraHom_single, hf]

end LinearMap
