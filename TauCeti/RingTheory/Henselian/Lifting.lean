/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Transporting simple-root lifts along injective ring maps

A monic polynomial over a larger ring has a root congruent to a given approximate root
when its coefficients and the finite witnesses to simplicity come from a henselian subring.
This transports simple-root lifts from individual subrings to their directed unions.
-/

public section

open Polynomial

namespace TauCeti.HenselianRing

/-- Transport a simple-root lift along an injective ring map from a ring henselian along
`(π)`. The polynomial coefficients, approximate root, inverse derivative and both divisibility
witnesses must lie in the image; no henselianity of the target ring is assumed. -/
theorem exists_isRoot_of_injective {R S : Type*} [CommRing R] [CommRing S]
    {ι : R →+* S} (hinj : Function.Injective ι) {π : R}
    [HenselianRing R (Ideal.span {π})] {f : S[X]} (hf : f.Monic)
    (hlift : f ∈ Polynomial.lifts ι) {a b c d : S}
    (hfa : f.eval a = ι π * d) (hu : f.derivative.eval a * b - 1 = ι π * c)
    (ha : a ∈ Set.range ι) (hb : b ∈ Set.range ι)
    (hc : c ∈ Set.range ι) (hd : d ∈ Set.range ι) :
    ∃ x : S, f.IsRoot x ∧ x - a ∈ Ideal.span {ι π} := by
  obtain ⟨a₀, rfl⟩ := ha
  obtain ⟨b₀, rfl⟩ := hb
  obtain ⟨c₀, rfl⟩ := hc
  obtain ⟨d₀, rfl⟩ := hd
  obtain ⟨g, hg, -, hgmonic⟩ := lifts_and_natDegree_eq_and_monic hlift hf
  have heval (q : R[X]) : ι (q.eval a₀) = (q.map ι).eval (ι a₀) := by
    rw [eval_map_apply]
  have hderiv : ι (g.derivative.eval a₀) = f.derivative.eval (ι a₀) := by
    rw [heval, ← derivative_map, hg]
  -- Injectivity descends the two simple-root conditions using the chosen witnesses.
  have hga : g.eval a₀ ∈ Ideal.span {π} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨d₀, hinj ?_⟩
    simpa only [map_mul, heval, hg] using hfa
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {π}) (g.derivative.eval a₀)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk _ b₀, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq]
    rw [Ideal.mem_span_singleton]
    refine ⟨c₀, hinj ?_⟩
    simpa only [map_mul, map_sub, map_one, hderiv] using hu
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian g hgmonic a₀ hga hunit
  refine ⟨ι x, ?_, ?_⟩
  · simpa only [hg] using hx.map ι
  · rw [← map_sub]
    exact (Ideal.map_le_iff_le_comap.mpr (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      exact Ideal.mem_span_singleton_self (ι π))) (Ideal.mem_map_of_mem ι hxa)

end TauCeti.HenselianRing
