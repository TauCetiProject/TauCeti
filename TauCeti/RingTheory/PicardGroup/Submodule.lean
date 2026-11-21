/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Freeness and principality of invertible submodules

A submodule whose underlying module is invertible is free exactly when it is principal.
This identifies trivial invertible-module classes with principal submodules, over any
commutative semiring.
-/

public section

namespace Submodule

variable {R P : Type*} [CommSemiring R] [AddCommMonoid P] [Module R P]

/-- An invertible submodule is free exactly when it is principal. -/
theorem free_iff_isPrincipal (I : Submodule R P) [Module.Invertible R I] :
    Module.Free R I ↔ I.IsPrincipal := by
  rw [Module.Invertible.free_iff_linearEquiv]
  constructor
  · rintro ⟨f⟩
    exact ⟨_, Submodule.eq_span_singleton_of_surjective f.symm.surjective⟩
  · rintro ⟨x, hx⟩
    -- Multiplication by the generator maps `R` onto `I`, hence isomorphically.
    let f : R →ₗ[R] I :=
      (LinearMap.toSpanSingleton R P x).codRestrict I fun a ↦ by
        rw [hx]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hx ▸ hy : y ∈ Submodule.span R {x})
      exact ⟨a, rfl⟩
    exact ⟨(LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hf)).symm⟩

end Submodule
