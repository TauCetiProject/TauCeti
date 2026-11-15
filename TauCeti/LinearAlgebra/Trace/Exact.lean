/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import TauCeti.LinearAlgebra.Trace.Prod

/-!
# The trace of an endomorphism of a short exact sequence

An endomorphism of a short exact sequence `0 → N → M → Q → 0` over a commutative ring,
with `M` finite and `N`, `Q` free, has `trace f = trace fN + trace fQ`. The freeness of `Q`
splits the sequence; the splitting makes `M` free and the two outer modules finite.
In particular this applies to every short exact sequence of finite-dimensional vector spaces.

The typical use is a filtration whose graded pieces are known: iterating the identity along
`M ⊇ M₁ ⊇ ⋯` expresses `trace f` as the sum of the traces on the successive quotients.  That is how
`Algebra.trace_quotient_pow_mk` computes the trace of `B ⧸ P ^ n` from the trace of `B ⧸ P`.

## Main results

* `LinearMap.trace_eq_add_of_exact`: the trace of the middle endomorphism of a short exact sequence
  is the sum of the traces of the outer ones.
-/

public section

open Module

namespace LinearMap

variable {R M N Q : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]

/-- **The trace is additive along a short exact sequence.** If `0 → N --i--> M --π--> Q → 0` is
exact and the endomorphisms `fN`, `f`, `fQ` commute with `i` and `π`, then
`trace f = trace fN + trace fQ`. The middle module is finite and the outer modules are free;
the quotient's projectivity supplies a section. -/
theorem trace_eq_add_of_exact [Module.Finite R M] [Module.Free R N] [Module.Free R Q]
    {i : N →ₗ[R] M} {π : M →ₗ[R] Q}
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : Function.Exact i π)
    {f : M →ₗ[R] M} {fN : N →ₗ[R] N} {fQ : Q →ₗ[R] Q}
    (hN : f ∘ₗ i = i ∘ₗ fN) (hQ : π ∘ₗ f = fQ ∘ₗ π) :
    trace R M f = trace R N fN + trace R Q fQ := by
  -- The free quotient is projective, so the sequence splits over any commutative ring.
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (range_eq_top.mpr hπ)
  obtain ⟨E, hiE, hπE⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  have _ : Module.Free R M := Module.Free.of_equiv E.symm
  have _ : Module.Finite R N := Module.Finite.of_surjective
    ((fst R N Q).comp E.toLinearMap) (by
      intro n
      exact ⟨E.symm (n, 0), by simp⟩)
  have _ : Module.Finite R Q := Module.Finite.of_surjective π hπ
  have hi_apply (n : N) : E.symm (n, 0) = i n := by
    simpa using congr($hiE n).symm
  -- transport `f` to `N × Q`; it is block upper triangular there
  set F : (N × Q) →ₗ[R] N × Q := E.conj f with hF
  have hFapply (x : N × Q) : F x = E (f (E.symm x)) := by
    simp [hF, LinearEquiv.conj_apply]
  have hsnd (m : M) : (E m).2 = π m := by
    simpa using congr($hπE m).symm
  have hinl : F ∘ₗ (inl R N Q) = (inl R N Q) ∘ₗ fN := by
    refine ext fun n ↦ E.symm.injective ?_
    have hfi : f (i n) = i (fN n) := congr($hN n)
    simp only [comp_apply, inl_apply, hFapply, E.symm_apply_apply, hi_apply]
    exact hfi
  have hsnd' : (snd R N Q) ∘ₗ F = fQ ∘ₗ (snd R N Q) := by
    refine ext fun x ↦ ?_
    have h₃ : π (f (E.symm x)) = fQ (π (E.symm x)) := congr($hQ (E.symm x))
    simp only [comp_apply, snd_apply, hFapply, hsnd, h₃]
    rw [← hsnd (E.symm x), E.apply_symm_apply]
  rw [← LinearMap.trace_conj' f E, ← hF,
    eq_prodMap_add_inl_comp_snd (fA := fN) (fC := fQ) F hinl hsnd',
    trace_prodMap_add_inl_comp_snd]

end LinearMap
