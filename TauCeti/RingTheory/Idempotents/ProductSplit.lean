/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Span

public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.LinearCombination

/-!
# Product decomposition of a commutative ring along an idempotent

Let e be an idempotent element of a commutative ring R, and let π : R →+* B and
ρ : R →+* E be surjective ring homomorphisms killing e and 1 - e respectively, with kernels
contained in Ideal.span {e} and Ideal.span {1 - e}. This file proves that x ↦ (π x, ρ x) is
bijective (hence a RingEquiv R ≃+* B × E) and that RingHom.ker π = Ideal.span {e}.

## Main results

* TauCeti.bijective_prod_of_isIdempotentElem: x ↦ (π x, ρ x) is bijective.
* TauCeti.ringEquivProdOfIsIdempotentElem: the resulting ring isomorphism R ≃+* B × E.
* TauCeti.ker_eq_span_of_isIdempotentElem: if π e = 0 and RingHom.ker π ≤ Ideal.span {e},
  then RingHom.ker π = Ideal.span {e}.

## References

* grh-lean, https://github.com/lsernau/grh-lean (commit
  72fead102f663d5c7a407964a13dc0cf9d977207), file
  src/Lib/Cohomology/Etale/DenseSubfunctors.lean (declaration
  New.Variety.bijective_map_prod_map_of_idempotent); Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

/-- If π : R →+* B kills e and has kernel contained in Ideal.span {e}, then its kernel is
equal to Ideal.span {e}. -/
theorem ker_eq_span_of_isIdempotentElem {R B : Type*} [CommRing R] [CommRing B]
    {e : R} {π : R →+* B} (hπ_kill : π e = 0) (hπ_ker : RingHom.ker π ≤ Ideal.span {e}) :
    RingHom.ker π = Ideal.span {e} :=
  le_antisymm hπ_ker (Ideal.span_singleton_le_iff_mem _ |>.mpr hπ_kill)

/-- Let e be an idempotent of a commutative ring R, and let π : R →+* B and ρ : R →+* E
be surjective ring homomorphisms killing e and 1 - e, with kernels contained in
Ideal.span {e} and Ideal.span {1 - e}. Then x ↦ (π x, ρ x) is bijective. -/
theorem bijective_prod_of_isIdempotentElem {R B E : Type*} [CommRing R] [CommRing B] [CommRing E]
    {e : R} (he : IsIdempotentElem e) {π : R →+* B} {ρ : R →+* E}
    (hπ_kill : π e = 0) (hπ_surj : Function.Surjective π)
    (hπ_ker : RingHom.ker π ≤ Ideal.span {e})
    (hρ_kill : ρ (1 - e) = 0) (hρ_surj : Function.Surjective ρ)
    (hρ_ker : RingHom.ker ρ ≤ Ideal.span {1 - e}) :
    Function.Bijective (fun x : R ↦ (π x, ρ x)) := by
  constructor
  · refine (injective_iff_map_eq_zero (π.prod ρ)).mpr fun x hx ↦ ?_
    have hx_π : π x = 0 := congrArg Prod.fst hx
    have hx_ρ : ρ x = 0 := congrArg Prod.snd hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hπ_ker hx_π)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hρ_ker hx_ρ)
    linear_combination (-(a + b)) * he.eq - e * hb - (1 - e) * ha
  · rintro ⟨y, z⟩
    obtain ⟨x₁, rfl⟩ := hπ_surj y
    obtain ⟨x₂, rfl⟩ := hρ_surj z
    refine ⟨x₁ + e * (x₂ - x₁), Prod.ext ?_ ?_⟩
    · simp [hπ_kill]
    · have hρ_e : ρ e = 1 := sub_eq_zero.mp (by simpa [map_sub, map_one] using hρ_kill) |>.symm
      simp [hρ_e]

/-- The ring isomorphism R ≃+* B × E induced by surjective ring homomorphisms π : R →+* B
and ρ : R →+* E killing complementary idempotents e and 1 - e with kernels bounded by
Ideal.span {e} and Ideal.span {1 - e}. -/
noncomputable def ringEquivProdOfIsIdempotentElem {R B E : Type*} [CommRing R] [CommRing B]
    [CommRing E] {e : R} (he : IsIdempotentElem e) {π : R →+* B} {ρ : R →+* E}
    (hπ_kill : π e = 0) (hπ_surj : Function.Surjective π)
    (hπ_ker : RingHom.ker π ≤ Ideal.span {e})
    (hρ_kill : ρ (1 - e) = 0) (hρ_surj : Function.Surjective ρ)
    (hρ_ker : RingHom.ker ρ ≤ Ideal.span {1 - e}) :
    R ≃+* B × E :=
  RingEquiv.ofBijective (π.prod ρ)
    (bijective_prod_of_isIdempotentElem he hπ_kill hπ_surj hπ_ker hρ_kill hρ_surj hρ_ker)

end TauCeti
