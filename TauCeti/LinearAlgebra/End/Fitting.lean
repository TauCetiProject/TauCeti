/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
import TauCeti.LinearAlgebra.End.RangePow

/-!
# The two parts of the Fitting decomposition

For an endomorphism `f` of a module of finite length, Mathlib's Fitting decomposition
(`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`) splits the module as the direct sum of the
generalized kernel `⨆ n, ker (f ^ n)` and the stable range `⨅ n, range (f ^ n)`. Both summands are
`f`-invariant (`LinearMap.mapsTo_iSup_ker_pow`, `LinearMap.mapsTo_iInf_range_pow`, for every
module). On a Noetherian module, `f` restricts to a nilpotent endomorphism of the first
(`LinearMap.isNilpotent_restrict_iSup_ker_pow`); if the module is also Artinian, `f` restricts to
a bijection of the second (`LinearMap.bijective_restrict_iInf_range_pow`). Both apply to every
finite-dimensional vector space.

The same statements at a fixed power `n` at which both chains have stopped, without any finiteness
assumption, are in `TauCeti.LinearAlgebra.End.RangePow`.
-/

public section

namespace LinearMap

section Module

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f : M →ₗ[R] M)

/-- The generalized kernel `⨆ n, ker (f ^ n)` of an endomorphism `f` is `f`-invariant. -/
theorem mapsTo_iSup_ker_pow :
    Set.MapsTo f ↑(⨆ n, ker (f ^ n) : Submodule R M) ↑(⨆ n, ker (f ^ n) : Submodule R M) :=
  fun _ hx ↦ by
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ f.iterateKer.monotone.directed_le).1 hx
  exact Submodule.mem_iSup_of_mem n (mapsTo_ker_pow f n hn)

/-- The stable range `⨅ n, range (f ^ n)` of an endomorphism `f` is `f`-invariant. -/
theorem mapsTo_iInf_range_pow :
    Set.MapsTo f ↑(⨅ n, range (f ^ n) : Submodule R M) ↑(⨅ n, range (f ^ n) : Submodule R M) :=
  fun _ hx ↦ Submodule.mem_iInf _ |>.2 fun n ↦
    mapsTo_range_pow f n (Submodule.mem_iInf _ |>.1 hx n)

/-- **An endomorphism is nilpotent on its generalized kernel.** On a Noetherian module, the
restriction of `f` to `⨆ n, ker (f ^ n)` is nilpotent: the nilpotent part of the Fitting
decomposition. -/
theorem isNilpotent_restrict_iSup_ker_pow [IsNoetherian R M]
    (h : ∀ x ∈ ⨆ n, ker (f ^ n), f x ∈ ⨆ n, ker (f ^ n) := f.mapsTo_iSup_ker_pow) :
    IsNilpotent (f.restrict h) := by
  obtain ⟨n, hn⟩ := f.eventually_iSup_ker_pow_eq.exists
  exact Module.End.isNilpotent_restrict_of_le hn.le ⟨n, f.pow_restrict_ker_pow_eq_zero n⟩

end Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsArtinian R M] [IsNoetherian R M]
  (f : M →ₗ[R] M)

/-- **An endomorphism is invertible on its stable range.** On an Artinian and Noetherian module,
`f` restricts to a bijection of `⨅ n, range (f ^ n)`, the invertible part of the Fitting
decomposition. -/
theorem bijective_restrict_iInf_range_pow
    (h : ∀ x ∈ ⨅ n, range (f ^ n), f x ∈ ⨅ n, range (f ^ n) := f.mapsTo_iInf_range_pow) :
    Function.Bijective (f.restrict h) := by
  have hinj : Function.Injective (f.restrict h) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext ?_
    have hker : (x : M) ∈ ⨆ n, ker (f ^ n) :=
      Submodule.mem_iSup_of_mem 1 (mem_ker.2 (by rw [pow_one]; exact congrArg Subtype.val hx))
    have := Submodule.mem_inf.2 ⟨hker, x.property⟩
    rwa [(isCompl_iSup_ker_pow_iInf_range_pow f).inf_eq_bot, Submodule.mem_bot] at this
  exact ⟨hinj, IsArtinian.surjective_of_injective_endomorphism _ hinj⟩

end LinearMap
