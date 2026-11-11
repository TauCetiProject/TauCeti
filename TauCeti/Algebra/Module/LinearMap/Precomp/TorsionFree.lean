/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.Algebra.Module.LinearMap.Precomp
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Torsion-freeness for the precomposition action

For an algebraic extension of domains, the precomposition module of linear maps to a
torsion-free coefficient module is torsion-free over the extension ring. The action is on the
argument of the map; the usual scalar action on values does not give this statement.
-/

public section

namespace TauCeti.Algebra.PrecompLinearMap

/-- Precomposition duals of algebraic domain extensions inherit torsion-freeness from the
coefficient module. This scalar action is on the argument, rather than on the values. -/
instance {R B M : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] [Algebra.IsAlgebraic R B] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] : Module.IsTorsionFree B (PrecompLinearMap R B M) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro x φ h
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  have hne := Ideal.under_ne_bot_of_algebraic_mem hx (Ideal.mem_span_singleton_self x)
    (Algebra.IsAlgebraic.isAlgebraic (R := R) x)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hr)
  apply PrecompLinearMap.ext
  intro c
  rw [PrecompLinearMap.zero_apply]
  have he : r • φ c = 0 := by
    have hz := congrArg (fun ψ : PrecompLinearMap R B M ↦ ψ (y • c)) h
    have hr : r • φ c = φ ((x * y) • c) := by
      rw [mul_comm x y, hy, algebraMap_smul, φ.linearMap.map_smul]
    rw [hr]
    simpa only [PrecompLinearMap.smul_apply, PrecompLinearMap.zero_apply,
      smul_smul] using hz
  exact (smul_eq_zero.mp he).resolve_left hr0

end TauCeti.Algebra.PrecompLinearMap
