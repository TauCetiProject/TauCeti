/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Hecke.Trace
public import TauCeti.KnotTheory.Markov.Skein

/-!
# Skein characterization of normalized Hecke traces

The normalized braid trace `MarkovBraid.heckeTrace` and its Markov invariance are defined in
`TauCeti.KnotTheory.Hecke.Trace` for any Hecke Markov trace, together with its split-unknot
factor and skein relations. This file proves its characterization by the skein relation and
normalization.

After importing `TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace`, the canonical specialization
is obtained by taking `τ = ocneanuTrace R q z` and
`hτ = isMarkovTrace_ocneanuTrace z`. In this case the invariant is the braid-closure invariant
Jones constructs from the Ocneanu trace. Its comparison with the HOMFLY invariant built from
Jimbo representations is not made here. The skein relation itself needs only linearity of `τ`.

## Main results

* `TauCeti.MarkovBraid.eq_heckeTrace_of_skein`: the skein characterization.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti

open BraidGroup MarkovBraid InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} {l : Rˣ} {C : R}

/-- **The skein characterization of the normalized Hecke trace.** A Markov invariant `F`
satisfying the skein relation `l⁻¹ * F(σᵢ c) - l * F(σᵢ⁻¹ c) = (q - q⁻¹) * F(c)`, multiplied by
`C` when an uncrossed strand is added, and with value `1` on the unknot, is the normalized Hecke
trace. In particular this applies to the Ocneanu trace. -/
theorem MarkovBraid.eq_heckeTrace_of_skein (hτ : IsMarkovTrace z τ)
    (hpos : C * l * z = 1)
    (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1) {F : MarkovBraid → R}
    (hF : ∀ β γ, MarkovEquiv β γ → F β = F γ)
    (hs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      ↑l⁻¹ * F ⟨n, sigma (n := n + 1) i * c⟩ - l * F ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        ((q : R) - ↑q⁻¹) * F ⟨n, c⟩)
    (hι : ∀ n (b : BraidGroup (n + 1)), F ⟨n + 1, strandIncl b⟩ = C * F ⟨n, b⟩)
    (h₁ : F ⟨0, 1⟩ = 1) :
    F = fun β ↦ β.heckeTrace τ C l :=
  eq_of_skein l⁻¹ ((q : R) - ↑q⁻¹) C hF
    (fun _ _ h ↦ h.heckeTrace_eq hτ C l hpos hneg)
    (by simpa only [smul_eq_mul, inv_inv] using hs)
    (fun n c i ↦ by simpa only [smul_eq_mul, inv_inv, one_mul] using
      heckeTrace_skein (τ := τ) C l 1 c i)
    (by simpa only [smul_eq_mul] using hι)
    (fun n b ↦ by rw [smul_eq_mul, τ.heckeTrace_strandIncl])
    (by rw [h₁, heckeTrace_one_strand hτ.map_one])

end TauCeti
