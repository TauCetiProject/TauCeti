/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Elementary linear-equivalence transport

Transport of submodule stability through an intertwining semilinear equivalence.
Symmetry of a linear automorphism agrees with inversion in its group structure.
-/

public section

namespace LinearEquiv

/-- Symmetry of a linear automorphism is its group inverse. -/
theorem symm_eq_inv {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (e : V ≃ₗ[R] V) : e.symm = e⁻¹ := rfl

/-- Transport stability of a mapped submodule through an intertwining semilinear
equivalence. -/
theorem mem_of_preserves_map
    {R S V W : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module S W]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : V ≃ₛₗ[σ] W) (p : Submodule R V) (q : Submodule S W)
    (hmap : p.map (e : V →ₛₗ[σ] W) = q) (f : V → V) (g : W → W)
    (hcomm : ∀ x, e (f x) = g (e x))
    (hstable : ∀ {y}, y ∈ q → g y ∈ q)
    {x : V} (hx : x ∈ p) : f x ∈ p := by
  subst hmap
  simpa [← hcomm] using hstable (Submodule.mem_map_of_mem hx)

end LinearEquiv
