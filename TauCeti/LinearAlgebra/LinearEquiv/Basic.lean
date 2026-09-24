/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map

/-!
# Elementary linear-equivalence transport

Evaluation of composed equivalences and transport of submodule stability.
-/

public section

namespace LinearEquiv

/-- Transport stability of a mapped submodule through an intertwining linear equivalence. -/
theorem mem_of_preserves_map
    {R V W : Type*} [CommSemiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (e : V ≃ₗ[R] W) (p : Submodule R V) (q : Submodule R W)
    (hmap : p.map e.toLinearMap = q) (f : V → V) (g : W → W)
    (hcomm : ∀ x, e (f x) = g (e x))
    (hstable : ∀ {y}, y ∈ q → g y ∈ q)
    {x : V} (hx : x ∈ p) : f x ∈ p := by
  have hex : e x ∈ q := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  have hfx := hstable hex
  rw [← hcomm x, ← hmap] at hfx
  simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hfx

/-- An equivalence followed by an inverse coordinate change evaluates as the first map. -/
theorem apply_trans_symm
    {R U V W : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (f : U ≃ₗ[R] V) (e : W ≃ₗ[R] V) (x : U) :
    e (f.trans e.symm x) = f x := by
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

end LinearEquiv
