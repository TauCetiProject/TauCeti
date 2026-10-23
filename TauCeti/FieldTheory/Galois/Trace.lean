/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Sums of Galois automorphisms and the trace

Mathlib's `trace_eq_sum_automorphisms` writes the trace of a finite Galois extension as the sum of
its automorphisms. This file records two consequences for a tower `K ⊆ L ⊆ M`.

## Main results

* `MonoidHom.sum_fiber_apply_eq_algebraMap_trace`: for `f : Gal(M/K) → Gal(L/K)` compatible with the
  inclusion `L ⊆ M`, the automorphisms in the fibre of `f` over `σ` sum to `σ ∘ Tr_{M/L}`, because
  that fibre is a coset of `Gal(M/L)`.
* `Module.Basis.sum_traceDual_mul_apply`: for an `L`-basis `m` of a finite Galois extension `M/L`
  with trace-dual basis `m*`, `∑ᵢ m*ᵢ · g(mᵢ)` is `1` if `g = 1` and `0` for every other
  `g ∈ Gal(M/L)`, by Dedekind's independence of characters.
-/

public section

open Module

namespace MonoidHom

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- For a finite Galois extension `M/K`, an intermediate field `L` and a homomorphism
`f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the automorphisms in the fibre of
`f` over `σ` sum to `σ` composed with the trace of `M/L`. -/
theorem sum_fiber_apply_eq_algebraMap_trace [FiniteDimensional K M] [IsGalois K M]
    [DecidableEq Gal(L/K)] (f : Gal(M/K) →* Gal(L/K))
    (hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x)) (σ : Gal(L/K)) (z : M) :
    ∑ g ∈ Finset.univ.filter (fun g ↦ f g = σ), g z =
      algebraMap L M (σ (Algebra.trace L M z)) := by
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  set g₀ := σ.liftNormal M
  have hg₀ : f g₀ = σ := AlgEquiv.ext fun x ↦
    (algebraMap L M).injective ((hf g₀ x).trans (σ.liftNormal_commutes M x))
  -- `f` is trivial exactly on the automorphisms fixing `L`
  have hker (g : Gal(M/K)) : f g = 1 ↔ ∀ x, g (algebraMap L M x) = algebraMap L M x := by
    refine ⟨fun h x ↦ by rw [← hf, h, AlgEquiv.one_apply], fun h ↦ AlgEquiv.ext fun x ↦
      (algebraMap L M).injective ?_⟩
    rw [hf, h, AlgEquiv.one_apply]
  -- the kernel of `f` is `Gal(M/L)`, viewed inside `Gal(M/K)`
  let e : f.ker ≃ Gal(M/L) :=
    { toFun t := AlgEquiv.ofRingEquiv (f := (t : Gal(M/K)).toRingEquiv) ((hker _).1 t.2)
      invFun τ := ⟨τ.restrictScalars K, (hker _).2 τ.commutes⟩
      left_inv _ := Subtype.ext <| AlgEquiv.ext fun _ ↦ rfl
      right_inv _ := AlgEquiv.ext fun _ ↦ rfl }
  calc ∑ g ∈ Finset.univ.filter (fun g ↦ f g = σ), g z
      = ∑ g : {g : Gal(M/K) // f g = σ}, (g : Gal(M/K)) z :=
        Finset.sum_subtype _ (fun _ ↦ by simp) _
    _ = ∑ t : f.ker, (g₀ * t) z :=
        Fintype.sum_equiv (f.subtypeFiberEquivKer hg₀) _ _ fun _ ↦ by simp
    _ = ∑ τ : Gal(M/L), g₀ (τ z) := Fintype.sum_equiv e _ _ fun _ ↦ rfl
    _ = algebraMap L M (σ (Algebra.trace L M z)) := by
        rw [← map_sum, ← trace_eq_sum_automorphisms, ← hf, hg₀]

end MonoidHom

open Classical in
/-- For an `L`-basis `m` of a finite Galois extension `M/L` and `g ∈ Gal(M/L)`, the sum
`∑ᵢ m*ᵢ · g(mᵢ)` against the trace-dual basis is `1` if `g = 1` and `0` otherwise. This is
Dedekind's independence of characters applied to
`x = ∑ᵢ m*ᵢ · Tr(mᵢ x) = ∑_g (∑ᵢ m*ᵢ · g(mᵢ)) · g(x)`. -/
theorem Module.Basis.sum_traceDual_mul_apply {L M : Type*} [Field L] [Field M] [Algebra L M]
    [FiniteDimensional L M] [IsGalois L M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Basis ι L M) (g : Gal(M/L)) :
    ∑ i, m.traceDual i * g (m i) = if g = 1 then 1 else 0 := by
  classical
  set C : Gal(M/L) → M := fun g ↦ ∑ i, m.traceDual i * g (m i)
  have hC (x : M) : ∑ g, C g * g x = x := by
    calc ∑ g, C g * g x
        = ∑ i, m.traceDual i * ∑ g : Gal(M/L), g (m i * x) := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, map_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ i, Algebra.trace L M (x * m i) • m.traceDual i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← trace_eq_sum_automorphisms, Algebra.smul_def, mul_comm, mul_comm x]
      _ = x := by
          conv_rhs => rw [← m.traceDual.sum_repr x]
          simp [Algebra.traceForm_apply]
  have hli := (linearIndependent_monoidHom M M).comp (fun g : Gal(M/L) ↦ (g : M →* M))
    fun g g' h ↦ AlgEquiv.ext fun x ↦ by simpa using DFunLike.congr_fun h x
  have := Fintype.linearIndependent_iffₛ.1 hli C (fun g ↦ if g = 1 then 1 else 0) (by
    funext x
    simp [Finset.sum_apply, hC, ite_apply])
  simpa [C] using this g
