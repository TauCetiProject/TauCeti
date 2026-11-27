/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.LocalRing.HilbertSamuel

import TauCeti.RingTheory.AdicCompletion.Algebra

/-!
# Hilbert–Samuel functions of adic completions

A ring homomorphism `A → B` of local rings that induces isomorphisms
`A ⧸ 𝔪_A ^ (n + 1) ≃ B ⧸ 𝔪_B ^ (n + 1)` preserves the local quotient Hilbert–Samuel function
(`Ideal.localQuotientHilbertSamuel_map_of_surjective`). For a noetherian local ring `A` and its
`𝔪`-adic completion `Â`, the canonical map `A → Â` satisfies this jet isomorphism at every order,
so extending an ideal `I` to `Â` preserves `Ideal.localQuotientHilbertSamuel`
(`Ideal.localQuotientHilbertSamuel_map_algebraMap_adicCompletion`), and in particular `Â` has the
same intrinsic Hilbert–Samuel function at `⊥` as `A`
(`TauCeti.localQuotientHilbertSamuel_adicCompletion_bot`).

## Main results

* `Ideal.localQuotientHilbertSamuel_map_algebraMap_adicCompletion`: `𝔪`-adic completion preserves
  the Hilbert–Samuel function of every ideal of a noetherian local ring.
* `TauCeti.localQuotientHilbertSamuel_adicCompletion_bot`: the `𝔪`-adic completion of a noetherian
  local ring `A` has the same `Ideal.localQuotientHilbertSamuel` at `⊥` as `A`.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302, §1
  (Remarks 1.3, pp. 213–214), §3 (Corollary 3.20, p. 239), and §9 (p. 276).
* H. Matsumura, *Commutative Ring Theory*, §13.
-/

public section

namespace Ideal

open IsLocalRing

/-- **Completion preserves the Hilbert–Samuel function.** For an ideal `I` of a noetherian local
ring `A` with `𝔪`-adic completion `Â`, the Hilbert–Samuel function of the extended ideal `I Â`
agrees with that of `I`: both measure `A ⧸ (I + 𝔪 ^ (n + 1)) ≃ Â ⧸ (I Â + 𝔪_Â ^ (n + 1))`. -/
@[simp]
theorem localQuotientHilbertSamuel_map_algebraMap_adicCompletion {A : Type*} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).localQuotientHilbertSamuel n =
      I.localQuotientHilbertSamuel n := by
  have fg := (maximalIdeal A).fg_of_isNoetherianRing
  refine localQuotientHilbertSamuel_map_of_surjective _ (fun x ↦ ?_) ?_ I
  · obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow fg (n + 1) x
    rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map] at hy
    exact ⟨y, (Quotient.eq.mpr hy).symm⟩
  · ext a
    rw [mem_comap, AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
      AdicCompletion.algebraMap_mem_map_pow_iff]

end Ideal

namespace TauCeti

/-- The `𝔪`-adic completion of a Noetherian local ring `A` has the same Hilbert–Samuel function as
`A` at `⊥`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion_bot
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    (⊥ : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A)).localQuotientHilbertSamuel n =
      (⊥ : Ideal A).localQuotientHilbertSamuel n := by
  simpa using Ideal.localQuotientHilbertSamuel_map_algebraMap_adicCompletion (⊥ : Ideal A) n

end TauCeti
