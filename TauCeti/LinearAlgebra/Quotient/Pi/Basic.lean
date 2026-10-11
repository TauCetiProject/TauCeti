/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Dimensions of quotients in product coordinates

When a linear equivalence identifies a submodule with componentwise submodules of a finite
product, the dimension of its quotient is the sum of the component quotient dimensions.
`TauCeti.finrank_quotient_eq_sum_of_equiv_pi` applies over rings with the strong rank condition,
assuming the component quotients are finite free modules. In particular, it applies over
division rings without requiring commutativity or finiteness of the original modules.
-/

public section

namespace TauCeti

/-- In finite product coordinates, a quotient by a componentwise submodule has dimension equal
to the sum of the dimensions of the component quotients, provided those quotients are finite
free modules. -/
theorem finrank_quotient_eq_sum_of_equiv_pi (R : Type*) [Ring R] [StrongRankCondition R]
    {M : Type*} [AddCommGroup M] [Module R M] {J : Type*} [Fintype J]
    {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (e : M ≃ₗ[R] ∀ j, N j) (S : Submodule R M) (T : ∀ j, Submodule R (N j))
    [∀ j, Module.Free R (N j ⧸ T j)] [∀ j, Module.Finite R (N j ⧸ T j)]
    (h : ∀ x, x ∈ S ↔ ∀ j, e x j ∈ T j) :
    Module.finrank R (M ⧸ S) = ∑ j, Module.finrank R (N j ⧸ T j) := by
  let φ := (LinearMap.piMap fun j ↦ (T j).mkQ) ∘ₗ e.toLinearMap
  have hsurj : Function.Surjective φ :=
    (Function.Surjective.piMap fun j ↦ (T j).mkQ_surjective).comp e.surjective
  have hker : LinearMap.ker φ = S := by
    ext x
    simp [φ, funext_iff, h x]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (φ.quotKerEquivOfSurjective hsurj)).finrank_eq.trans (Module.finrank_pi_fintype R)

end TauCeti
