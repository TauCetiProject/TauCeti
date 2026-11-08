/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic

/-!
# Valuations on finite products of rings

A point of the valuation spectrum of a finite product `∏ i, R i` of commutative rings is the
pullback of a point of some factor `Spv (R i)` along the projection `∏ i, R i → R i`
(`TauCeti.ValuationSpectrum.exists_comap_evalRingHom_eq`). Geometrically, `Spv (∏ i, R i)` is
covered by the images of the `Spv (R i)`, as `Spec (∏ i, R i)` is the disjoint union of the
`Spec (R i)`.

The proof uses the idempotents `eᵢ = Pi.single i 1`. A valuation `v` takes the value `0` or `1`
on an idempotent, and `∑ i, eᵢ = 1`, so `v(eᵢ) = 1` for some `i`. Then `v(1 - eᵢ) = 0`, because
`eᵢ (1 - eᵢ) = 0`, and every `f` vanishing at `i` equals `f (1 - eᵢ)`, so it lies in the support
of `v`. Hence `v` factors through the surjection onto `R i`
(`TauCeti.ValuationSpectrum.range_comap_of_surjective`).

Finiteness of the index set matters: on an infinite product, a valuation can factor through the
quotient by a nonprincipal ultrafilter and through no single factor.

This identifies the points of the fibre square of a finite étale torsor, which is a finite product
of copies of the torsor.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]

/-- **Points of the valuation spectrum of a finite product.** Every point of
`Spv (∏ i, R i)` is pulled back from a point of `Spv (R i)` along the projection to some factor
`R i`. -/
theorem exists_comap_evalRingHom_eq [Finite ι] (v : Spv (∀ i, R i)) :
    ∃ i, ∃ w : Spv (R i), comap (Pi.evalRingHom R i) w = v := by
  classical
  have := Fintype.ofFinite ι
  let e (i : ι) : ∀ j, R j := Pi.single i 1
  -- some idempotent `eᵢ` does not lie in the support, since the `eᵢ` sum to `1`
  obtain ⟨i, hi⟩ : ∃ i, v.valuation (e i) ≠ 0 := by
    by_contra! h
    have h1 : v.valuation (∑ i, e i) ≤ 0 := v.valuation.map_sum_le fun i _ ↦ (h i).le
    rw [Finset.univ_sum_single (fun _ ↦ 1), ← Pi.one_def, map_one] at h1
    simp at h1
  -- so the complementary idempotent `1 - eᵢ` does
  have hc : v.valuation (1 - e i) = 0 := by
    have h := congrArg v.valuation (show e i * (1 - e i) = 0 by
      ext j; by_cases hj : j = i
      · subst hj; simp [e]
      · simp [e, hj])
    rw [map_mul, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hi
  -- every function vanishing at `i` is a multiple of `1 - eᵢ`
  have hker : RingHom.ker (Pi.evalRingHom R i) ≤ v.supp := fun f hf ↦ by
    have hf' : f = f * (1 - e i) := by
      ext j
      by_cases hj : j = i
      · subst hj; simpa [e] using hf
      · simp [e, hj]
    rw [v.supp_eq_valuation_supp, Valuation.mem_supp_iff]
    rw [hf', map_mul, hc, mul_zero]
  have hsurj : Function.Surjective (Pi.evalRingHom R i) := fun r ↦ ⟨Pi.single i r, by simp⟩
  obtain ⟨w, hw⟩ : v ∈ Set.range (comap (Pi.evalRingHom R i)) := by
    rwa [range_comap_of_surjective hsurj]
  exact ⟨i, w, hw⟩

end TauCeti.ValuationSpectrum
