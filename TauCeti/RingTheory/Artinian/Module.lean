/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian modules embed into finite powers of a separating module

If the linear maps from an Artinian module `M` to a module `E` separate the points of `M`, then
finitely many of them already do: `M` embeds into a finite power `Eⁿ`. The descending chain
condition provides a family of maps whose common kernel is minimal among the common kernels of
finite families, and a nonzero element of that kernel would be detected by one more map.

For an injective cogenerator `E`, for instance the injective hull of the residue field of a local
ring, this embedding of an Artinian module into a finite sum of copies of `E` is the first step of
Matlis duality for Artinian modules.

## References

* The Stacks Project, Lemma 47.7.6, Tag 08Z7.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

variable {R : Type*} [Ring R] {M E : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup E] [Module R E]

/-- **An Artinian module embeds into a finite power of a module separating its points.** If every
nonzero element of an Artinian module `M` is detected by a linear map to `E`, then there is an
injective linear map `M → Eⁿ` for some `n`. -/
theorem IsArtinian.exists_injective_linearMap_pi [IsArtinian R M]
    (h : ∀ m : M, m ≠ 0 → ∃ f : M →ₗ[R] E, f m ≠ 0) :
    ∃ (n : ℕ) (g : M →ₗ[R] Fin n → E), Function.Injective g := by
  -- A finite family of maps whose common kernel is minimal.
  obtain ⟨_, ⟨⟨n, f⟩, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal
    (Set.range fun f : Σ n, Fin n → M →ₗ[R] E ↦ LinearMap.ker (LinearMap.pi f.2))
    ⟨_, ⟨⟨0, Fin.elim0⟩, rfl⟩⟩
  refine ⟨n, LinearMap.pi f, LinearMap.ker_eq_bot.mp ?_⟩
  by_contra hne
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨φ, hφ⟩ := h m hm0
  -- Adjoining a map detecting `m` would shrink the common kernel.
  refine hmin _ ⟨⟨n + 1, Fin.cons φ f⟩, rfl⟩ (lt_of_le_of_ne (fun x hx ↦ ?_) fun heq ↦ hφ ?_)
  · ext i
    simpa using congr_fun (LinearMap.mem_ker.mp hx) i.succ
  · beta_reduce at heq
    rw [← heq] at hm
    simpa using congr_fun (LinearMap.mem_ker.mp hm) 0
