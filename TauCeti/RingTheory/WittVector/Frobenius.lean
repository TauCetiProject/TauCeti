/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Teichmuller
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Witt-vector Frobenius on Teichmüller representatives and the `(p, [ϖ])`-adic topology

Let `R` be a ring of characteristic `p`. The Witt-vector Frobenius `φ` of `𝕎 R` sends the
Teichmüller representative `[r]` to `[r ^ p] = [r] ^ p`, and when `R` is perfect its inverse sends
`[r]` to `[r ^ (1 / p)]`. Consequently `φ` carries the ideal `(p, [ϖ])` into itself, and `φ⁻¹`
carries it into its radical, so both are continuous for the `(p, [ϖ])`-adic topology. For a perfect
ring of integers `𝒪_F` this is the continuity of Frobenius on `A_inf = W(𝒪_F)`, which lets
Frobenius act on its adic spectrum.

## Main results

* `WittVector.frobenius_teichmuller` : `φ [r] = [r] ^ p` in characteristic `p`.
* `WittVector.frobeniusEquiv_symm_teichmuller` : `φ⁻¹ [r] = [r ^ (1 / p)]` for perfect `R`.
* `TauCeti.WittVector.continuous_frobenius` : `φ` is continuous for the `(p, [ϖ])`-adic topology.
* `TauCeti.WittVector.continuous_frobeniusEquiv_symm` : so is `φ⁻¹`, for perfect `R`.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017, §3.1.
-/

public section

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

/-- In characteristic `p`, the Witt-vector Frobenius sends a Teichmüller representative `[r]` to
its `p`-th power `[r ^ p]`. -/
@[simp]
theorem frobenius_teichmuller (r : R) : frobenius (teichmuller p r) = teichmuller p r ^ p := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, map_pow]

/-- For a perfect ring of characteristic `p`, the inverse of the Witt-vector Frobenius sends a
Teichmüller representative `[r]` to the Teichmüller representative of the `p`-th root of `r`. -/
@[simp]
theorem frobeniusEquiv_symm_teichmuller [PerfectRing R p] (r : R) :
    (frobeniusEquiv p R).symm (teichmuller p r) =
      teichmuller p ((_root_.frobeniusEquiv R p).symm r) := by
  simp [frobeniusEquiv_symm_apply, map_teichmuller]

end WittVector

namespace TauCeti.WittVector

open _root_.WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
  [TopologicalSpace (WittVector p R)] {ϖ : R}

/-- The Witt-vector Frobenius is continuous for the `(p, [ϖ])`-adic topology: it fixes `p` and
sends `[ϖ]` to `[ϖ] ^ p`, so it carries the ideal `(p, [ϖ])` into itself. -/
theorem continuous_frobenius
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) :
    Continuous (frobenius : WittVector p R →+* WittVector p R) := by
  refine IsAdic.continuous_of_map_le_radical hI hI (Submodule.fg_span (by simp)) (le_trans ?_
    Ideal.le_radical)
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · simpa using Ideal.subset_span (by simp)
  · simpa using Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) p hp.out.pos

/-- For a perfect ring of characteristic `p`, the inverse of the Witt-vector Frobenius is
continuous for the `(p, [ϖ])`-adic topology: it fixes `p` and sends `[ϖ]` to a `p`-th root
`[ϖ ^ (1 / p)]` of `[ϖ]`, so it carries the ideal `(p, [ϖ])` into its radical. -/
theorem continuous_frobeniusEquiv_symm [PerfectRing R p]
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) :
    Continuous (frobeniusEquiv p R).symm := by
  refine IsAdic.continuous_of_map_le_radical hI hI (f := (frobeniusEquiv p R).symm.toRingHom)
    (Submodule.fg_span (by simp)) ?_
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  refine ⟨Ideal.le_radical ?_, Ideal.mem_radical_iff.mpr ⟨p, ?_⟩⟩
  · simpa using Ideal.subset_span (by simp)
  · -- the `p`-th power of `[ϖ ^ (1 / p)]` is `[ϖ ^ (1 / p) ^ p] = [ϖ]`
    have h : ((_root_.frobeniusEquiv R p).symm ϖ) ^ p = ϖ := by simp [← frobenius_def]
    simpa [← map_pow, h] using Ideal.subset_span (by simp)

end TauCeti.WittVector
