/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Transporting simple-root lifts along ring maps

A monic polynomial over a larger ring has a root congruent to a given approximate root
when its coefficients, the approximate root and an inverse of the derivative there come from a
subring that is henselian along the preimage of the ideal. This transports simple-root lifts
from individual subrings to their directed unions.
-/

public section

open Polynomial

namespace TauCeti.HenselianRing

/-- Transport a simple-root lift along a ring map `ι : R →+* S`, for an ideal `I` of `S` such
that `R` is henselian along `I.comap ι`. The polynomial coefficients, the approximate root and an
inverse of the derivative modulo `I` must lie in the image; no henselianity of `S` and no
injectivity of `ι` is assumed. -/
theorem exists_isRoot_of_lifts {R S : Type*} [CommRing R] [CommRing S] {ι : R →+* S}
    {I : Ideal S} [HenselianRing R (I.comap ι)] {f : S[X]} (hf : f.Monic)
    (hlift : f ∈ Polynomial.lifts ι) {a b : S} (hfa : f.eval a ∈ I)
    (hu : f.derivative.eval a * b - 1 ∈ I) (ha : a ∈ Set.range ι) (hb : b ∈ Set.range ι) :
    ∃ x : S, f.IsRoot x ∧ x - a ∈ I := by
  obtain ⟨a₀, rfl⟩ := ha
  obtain ⟨b₀, rfl⟩ := hb
  obtain ⟨g, hg, -, hgmonic⟩ := lifts_and_natDegree_eq_and_monic hlift hf
  have heval (q : R[X]) : ι (q.eval a₀) = (q.map ι).eval (ι a₀) := by
    rw [eval_map_apply]
  have hga : g.eval a₀ ∈ I.comap ι := by
    rwa [Ideal.mem_comap, heval, hg]
  have hunit : IsUnit (Ideal.Quotient.mk (I.comap ι) (g.derivative.eval a₀)) := by
    refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ b₀, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.comap ι)), Ideal.Quotient.eq, Ideal.mem_comap,
      map_sub, map_mul, map_one, heval, ← derivative_map, hg]
    exact hu
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian g hgmonic a₀ hga hunit
  refine ⟨ι x, ?_, ?_⟩
  · simpa only [hg] using hx.map ι
  · rw [← map_sub]
    exact hxa

end TauCeti.HenselianRing
