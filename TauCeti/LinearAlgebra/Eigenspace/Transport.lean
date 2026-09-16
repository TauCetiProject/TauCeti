/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Transporting eigenspaces along linear equivalences

If a linear equivalence `e : U ≃ₗ[R] W` intertwines endomorphisms `f` of `U` and `g` of `W`,
then every eigenspace of `f` is the preimage under `e` of the corresponding eigenspace of `g`.
Mathlib's `Module.End.map_genEigenspace_le` gives only the inclusion of the image; this file
records the equality available for an equivalence.

## Main results

* `LinearEquiv.eigenspace_eq_comap_of_intertwine`: an intertwining linear equivalence identifies the
  eigenspaces of the two endomorphisms.
-/

public section

namespace LinearEquiv

variable {R U W : Type*} [CommRing R] [AddCommGroup U] [Module R U] [AddCommGroup W]
  [Module R W]

/-- An intertwining linear equivalence identifies the eigenspaces of the two endomorphisms. -/
theorem eigenspace_eq_comap_of_intertwine (e : U ≃ₗ[R] W) (f : U →ₗ[R] U) (g : W →ₗ[R] W)
    (h : ∀ x, e (f x) = g (e x)) (μ : R) :
    Module.End.eigenspace f μ = (Module.End.eigenspace g μ).comap e.toLinearMap := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap]
  constructor
  · intro hx
    calc
      g (e x) = e (f x) := (h x).symm
      _ = e (μ • x) := congrArg e hx
      _ = μ • e x := map_smul e μ x
  · intro hx
    apply e.injective
    calc
      e (f x) = g (e x) := h x
      _ = μ • e x := hx
      _ = e (μ • x) := (map_smul e μ x).symm

end LinearEquiv
