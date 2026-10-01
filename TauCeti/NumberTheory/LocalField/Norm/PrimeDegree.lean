/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Basic
import TauCeti.Algebra.Ring.Action.PrimeOrder
import TauCeti.RingTheory.LocalRing.Pointwise

/-!
# The norm of `1 + x` in a Galois extension of prime degree

Let `L/K` be a Galois extension of nonarchimedean local fields of prime degree `ℓ`, so that its
Galois group is cyclic of order `ℓ`, and let `x ∈ 𝓂[L]^m`. Expanding the norm
`N_{L/K}(1 + x) = ∏_σ (1 + σ x)` gives the sum, over the subsets `S` of the Galois group, of the
products `∏_{σ ∈ S} σ x`. Because the group has prime order, it permutes the subsets with at least
two elements, other than the whole group, freely, so these terms collect into the trace of an
element `y` of `𝓂[L]^(2m)`, and

`N_{L/K}(1 + x) = 1 + Tr_{L/K}(x) + Tr_{L/K}(y) + N_{L/K}(x)`.

This is the shape in which the norm is computed on the unit filtration of such an extension: the
valuations of the two traces are read off from the behaviour of the trace on powers of the maximal
ideal, and `v_K(N_{L/K}(x)) = f(L/K) v_L(x)`, which is `v_L(x)` when the extension is totally
ramified and `ℓ v_L(x)` when it is unramified. It is Lemma 5 of Serre, *Local Fields*, Chapter V,
§3, stated for the integer rings.

## Main results

* `TauCeti.exists_norm_one_add_eq_of_mem_maximalIdeal_pow`: the expansion above.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §3, Lemma 5.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [IsGalois K L]

/-- **The norm of `1 + x` in a Galois extension of prime degree** (Serre, *Local Fields*, V §3,
Lemma 5). If `L/K` is a Galois extension of nonarchimedean local fields of prime degree and
`x ∈ 𝓂[L]^m`, then there is `y ∈ 𝓂[L]^(2m)` with

`N_{L/K}(1 + x) = 1 + Tr_{L/K}(x) + Tr_{L/K}(y) + N_{L/K}(x)`,

the norm and trace being those of `𝒪[L]` over `𝒪[K]`. -/
theorem exists_norm_one_add_eq_of_mem_maximalIdeal_pow (hℓ : (Module.finrank K L).Prime)
    {m : ℕ} {x : 𝒪[L]} (hx : x ∈ 𝓂[L] ^ m) :
    ∃ y ∈ 𝓂[L] ^ (2 * m), Algebra.norm 𝒪[K] (1 + x) =
      1 + Algebra.trace 𝒪[K] 𝒪[L] x + Algebra.trace 𝒪[K] 𝒪[L] y + Algebra.norm 𝒪[K] x := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hℓ.pos
  have hG : (Nat.card (L ≃ₐ[K] L)).Prime := by rwa [IsGalois.card_aut_eq_finrank]
  obtain ⟨y, hy, h⟩ :=
    MulSemiringAction.exists_prod_one_add_smul_eq_of_prime_card (L ≃ₐ[K] L) hG x
  refine ⟨y, ?_, ?_⟩
  · -- The orbit of `x` lies in `𝓂[L]^m`, so the square of the ideal it spans lies in `𝓂[L]^(2m)`.
    have hJ : Ideal.span (MulAction.orbit (L ≃ₐ[K] L) x) ≤ 𝓂[L] ^ m := by
      rw [Ideal.span_le]
      rintro _ ⟨σ, rfl⟩
      exact TauCeti.IsLocalRing.smul_mem_maximalIdeal_pow σ hx
    rw [sq] at hy
    rw [two_mul, pow_add]
    exact Ideal.mul_mono hJ hJ hy
  · -- Read the identity in `𝒪[L]`, where norm and trace are the product and sum of conjugates.
    apply FaithfulSMul.algebraMap_injective 𝒪[K] 𝒪[L]
    simp only [map_add, map_one, algebraMap_norm_integerRing_eq_prod_automorphisms,
      algebraMap_trace_integerRing_eq_sum_automorphisms]
    simpa only [smul_add, smul_one] using h

end TauCeti
