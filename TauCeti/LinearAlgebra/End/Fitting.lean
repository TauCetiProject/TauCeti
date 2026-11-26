/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Module
import TauCeti.LinearAlgebra.End.RangePow

/-!
# The two parts of the Fitting decomposition

For an endomorphism `f` of a module of finite length, Mathlib's Fitting decomposition
(`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`) splits the module as the direct sum of the
generalized kernel `⨆ n, ker (f ^ n)` and the stable range `⨅ n, range (f ^ n)`. Both summands are
`f`-invariant (`LinearMap.mapsTo_iSup_ker_pow`, `LinearMap.mapsTo_iInf_range_pow`, for every
module). On a finite-dimensional vector space, `f` restricts to a nilpotent endomorphism of the
first (`LinearMap.isNilpotent_restrict_iSup_ker_pow`) and to a bijection of the second
(`LinearMap.bijective_restrict_iInf_range_pow`).

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

end Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (f : V →ₗ[K] V)

/-- **An endomorphism is invertible on its stable range.** On a finite-dimensional vector space,
`f` restricts to a bijection of `⨅ n, range (f ^ n)`, the invertible part of the Fitting
decomposition. -/
theorem bijective_restrict_iInf_range_pow
    (h : ∀ x ∈ ⨅ n, range (f ^ n), f x ∈ ⨅ n, range (f ^ n) := f.mapsTo_iInf_range_pow) :
    Function.Bijective (f.restrict h) := by
  have hinj : Function.Injective (f.restrict h) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext ?_
    have hker : (x : V) ∈ ⨆ n, ker (f ^ n) :=
      Submodule.mem_iSup_of_mem 1 (mem_ker.2 (by rw [pow_one]; exact congrArg Subtype.val hx))
    have := Submodule.mem_inf.2 ⟨hker, x.property⟩
    rwa [(isCompl_iSup_ker_pow_iInf_range_pow f).inf_eq_bot, Submodule.mem_bot] at this
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- **An endomorphism is nilpotent on its generalized kernel.** On a finite-dimensional vector
space, the restriction of `f` to `⨆ n, ker (f ^ n)` is nilpotent: the nilpotent part of the Fitting
decomposition. -/
theorem isNilpotent_restrict_iSup_ker_pow
    (h : ∀ x ∈ ⨆ n, ker (f ^ n), f x ∈ ⨆ n, ker (f ^ n) := f.mapsTo_iSup_ker_pow) :
    IsNilpotent (f.restrict h) := by
  obtain ⟨n, hn⟩ := f.eventually_iSup_ker_pow_eq.exists
  refine ⟨n, LinearMap.ext fun x ↦ Subtype.ext ?_⟩
  rw [Module.End.pow_restrict n]
  have hx : (x : V) ∈ ker (f ^ n) := by
    rw [← hn]
    exact x.property
  exact mem_ker.1 hx

end LinearMap
