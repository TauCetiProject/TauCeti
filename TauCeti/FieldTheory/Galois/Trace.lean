/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsGaloisGroup.Defs
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Sums and products of Galois automorphisms: the trace and the norm

Mathlib's `trace_eq_sum_automorphisms` writes the trace of a finite Galois extension as the sum of
its automorphisms, and `Algebra.norm_eq_prod_automorphisms` writes the norm as their product. This
file states the first for an abstract finite Galois group and records consequences for a tower
`K ⊆ L ⊆ M`.

## Main results

* `IsGaloisGroup.algebraMap_trace_eq_sum`: for a finite Galois group `G` of `L/K`, the trace of
  `x` is the sum of the `g • x` over `g : G`.
* `MonoidHom.sum_fiber_apply_eq_algebraMap_trace`: for `f : Gal(M/K) → Gal(L/K)` compatible with the
  inclusion `L ⊆ M`, the automorphisms in the fibre of `f` over `σ` sum to `σ ∘ Tr_{M/L}`, because
  that fibre is a coset of `Gal(M/L)`.
* `MonoidHom.prod_fiber_apply_eq_algebraMap_norm`: in the same situation, the product of the
  conjugates `g z` over that fibre is `σ ∘ N_{M/L}`.
* `Module.Basis.sum_traceDual_mul_apply`: for an `L`-basis `m` of a finite Galois extension `M/L`
  with trace-dual basis `m*`, `∑ᵢ m*ᵢ · g(mᵢ)` is `1` if `g = 1` and `0` for every other
  `g ∈ Gal(M/L)`, by Dedekind's independence of characters.
-/

public section

open Module

namespace IsGaloisGroup

variable (G K : Type*) {L : Type*} [Group G] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [IsGaloisGroup G K L] [Fintype G]

/-- For a finite Galois group `G` of `L/K`, the trace of `x` is the sum of the `g • x` over
`g : G`. This is `trace_eq_sum_automorphisms` for an abstract Galois group. -/
theorem algebraMap_trace_eq_sum (x : L) :
    algebraMap K L (Algebra.trace K L x) = ∑ g : G, g • x := by
  have := finiteDimensional G K L
  have := isGalois G K L
  rw [trace_eq_sum_automorphisms]
  exact (Fintype.sum_equiv (mulEquivAlgEquiv G K L).toEquiv _ _ fun _ ↦ by simp).symm

end IsGaloisGroup

namespace MonoidHom

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- For `f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the fibre of `f` over
`σ` is the coset `g₀ Gal(M/L)` of the lift `g₀ = σ.liftNormal M`. -/
private theorem filter_eq_map_liftNormal_mul [FiniteDimensional K M] [FiniteDimensional L M]
    [Normal K M] [DecidableEq Gal(L/K)]
    (f : Gal(M/K) →* Gal(L/K)) (hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x))
    (σ : Gal(L/K)) :
    Finset.univ.filter (fun g ↦ f g = σ) = Finset.univ.map
      ⟨fun τ : Gal(M/L) ↦ σ.liftNormal M * τ.restrictScalars K,
        (mul_right_injective _).comp (AlgEquiv.restrictScalars_injective K)⟩ := by
  have hg₀ : f (σ.liftNormal M) = σ := AlgEquiv.ext fun x ↦
    (algebraMap L M).injective ((hf _ x).trans (σ.liftNormal_commutes M x))
  -- `f` is trivial exactly on the automorphisms fixing `L`
  have hker (g : Gal(M/K)) : f g = 1 ↔ ∀ x, g (algebraMap L M x) = algebraMap L M x := by
    refine ⟨fun h x ↦ by rw [← hf, h, AlgEquiv.one_apply], fun h ↦ AlgEquiv.ext fun x ↦
      (algebraMap L M).injective ?_⟩
    rw [hf, h, AlgEquiv.one_apply]
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have h1 : f ((σ.liftNormal M)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hg, hg₀, inv_mul_cancel]
    exact ⟨AlgEquiv.ofRingEquiv (f := ((σ.liftNormal M)⁻¹ * g).toRingEquiv) ((hker _).1 h1),
      AlgEquiv.ext fun x ↦ by simp⟩
  · rintro ⟨τ, rfl⟩
    rw [map_mul, (hker (τ.restrictScalars K)).2 τ.commutes, mul_one, hg₀]

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
  rw [filter_eq_map_liftNormal_mul f hf σ, ← σ.liftNormal_commutes M, trace_eq_sum_automorphisms,
    map_sum]
  simp

/-- For a finite Galois extension `M/K`, an intermediate field `L` and a homomorphism
`f : Gal(M/K) → Gal(L/K)` compatible with the inclusion `L ⊆ M`, the product of the conjugates
`g z` over the automorphisms `g` in the fibre of `f` over `σ` is `σ` applied to the norm of
`M/L`. For `σ = 1` this is `Algebra.norm_eq_prod_automorphisms`. -/
theorem prod_fiber_apply_eq_algebraMap_norm [FiniteDimensional K M] [IsGalois K M]
    [DecidableEq Gal(L/K)] (f : Gal(M/K) →* Gal(L/K))
    (hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x)) (σ : Gal(L/K)) (z : M) :
    ∏ g ∈ Finset.univ.filter (fun g ↦ f g = σ), g z =
      algebraMap L M (σ (Algebra.norm L z)) := by
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  rw [filter_eq_map_liftNormal_mul f hf σ, ← σ.liftNormal_commutes M,
    Algebra.norm_eq_prod_automorphisms, map_prod]
  simp

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
