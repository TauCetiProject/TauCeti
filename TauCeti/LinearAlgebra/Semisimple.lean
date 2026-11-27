/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple

/-!
# Semisimple endomorphisms: transport along an injection, kernel and range

`LinearEquiv.isSemisimple_iff` transports semisimplicity between two endomorphisms intertwined by
a linear equivalence. For one of the two directions an injection is enough: an endomorphism that
embeds equivariantly into a semisimple one is semisimple, just as a submodule of a semisimple
module is semisimple.

Applying the invariant-complement characterisation of semisimplicity to the kernel and to
submodules containing the range shows that a semisimple endomorphism splits its module as the
internal direct sum of its kernel and its range.

## Main results

* `Module.End.IsSemisimple.of_injective`: semisimplicity passes to an endomorphism that
  admits an injective intertwiner into a semisimple one.
* `Module.End.IsSemisimple.isCompl_ker_range`: the kernel and the range of a semisimple
  endomorphism are complementary submodules.
-/

public section

open Polynomial

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Semisimplicity descends along an injective intertwiner.** If `i` is injective and carries
`f` to `g`, and `g` is semisimple, then so is `f`. -/
theorem IsSemisimple.of_injective {f : End R M} {g : End R N} (hg : g.IsSemisimple)
    (i : M →ₗ[R] N) (hi : Function.Injective i) (hcomm : i ∘ₗ f = g ∘ₗ i) :
    f.IsSemisimple :=
  have : IsSemisimpleModule R[X] (AEval' g) := hg
  -- `i` is `R[X]`-linear for the two `AEval'` structures precisely because it intertwines the
  -- endomorphisms, so it embeds `AEval' f` into the semisimple module `AEval' g`.
  IsSemisimpleModule.of_injective
    (LinearMap.ofAEval _ ((AEval'.of g).toLinearMap ∘ₗ i) fun x ↦ by
      simpa [AEval'.X_smul_of] using congr(AEval'.of g ($hcomm x)))
    -- By definition of `LinearMap.ofAEval`, this embedding is `i` conjugated by `AEval'.of`.
    ((AEval'.of g).injective.comp hi |>.comp (AEval'.of f).symm.injective)

/-- The kernel and the range of a semisimple endomorphism are complementary submodules. No
finiteness assumption is needed. -/
theorem IsSemisimple.isCompl_ker_range {g : End R M} (hg : g.IsSemisimple) :
    IsCompl (LinearMap.ker g) (LinearMap.range g) := by
  have hker : LinearMap.ker g ∈ g.invtSubmodule := by
    rw [mem_invtSubmodule]
    intro x hx
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker.mp hx, map_zero]
  have hrange (p : Submodule R M) : LinearMap.range g ≤ p → p ∈ g.invtSubmodule := by
    intro hp
    rw [mem_invtSubmodule]
    exact fun x _ ↦ hp (LinearMap.mem_range_self g x)
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · -- `x = g y` with `g x = 0`; decompose `y` along an invariant complement `q` of `ker g`.
    obtain ⟨q, hq, hkq⟩ := isSemisimple_iff.mp hg _ hker
    rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    obtain ⟨k, z, hk, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hkq.codisjoint y
    have hgz : g (k + z) = g z := by simp [LinearMap.mem_ker.mp hk]
    rw [hgz] at hx ⊢
    exact Submodule.disjoint_def.mp hkq.disjoint _ hx ((mem_invtSubmodule g).mp hq hz)
  · -- An invariant complement `q` of `ker g ⊔ range g` satisfies `g q = 0`, so `q = 0`.
    obtain ⟨q, hq, hpq⟩ :=
      isSemisimple_iff.mp hg _ (hrange (LinearMap.ker g ⊔ LinearMap.range g) le_sup_right)
    have hq_bot : q = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hgz : g z = 0 := Submodule.disjoint_def.mp hpq.disjoint _
        (Submodule.mem_sup_right (LinearMap.mem_range_self g z)) ((mem_invtSubmodule g).mp hq hz)
      exact Submodule.disjoint_def.mp hpq.disjoint _ (Submodule.mem_sup_left hgz) hz
    rw [codisjoint_iff, ← hpq.sup_eq_top, hq_bot, sup_bot_eq]

end Module.End
