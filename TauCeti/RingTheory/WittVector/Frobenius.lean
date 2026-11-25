/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Teichmuller
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Witt-vector Frobenius: naturality, Teichmüller representatives and the `(p, [ϖ])`-adic topology

The Witt-vector Frobenius `φ` of `𝕎 R` commutes with `WittVector.map f` for every ring homomorphism
`f`, since the coordinates of `φ x` are given by universal integer polynomials in those of `x`.

Let `R` be a ring of characteristic `p`. The Witt-vector Frobenius `φ` of `𝕎 R` raises every
Witt coordinate to its `p`-th power, so its fixed points are the Witt vectors whose coordinates are
all fixed by the `p`-power map. It sends the Teichmüller representative `[r]` to
`[r ^ p] = [r] ^ p`, and when `R` is perfect its inverse sends `[r]` to `[r ^ (1 / p)]`.
Consequently `φ` carries the ideal `(p, [ϖ])` into itself, and `φ⁻¹`
carries it into its radical, so both are continuous for the `(p, [ϖ])`-adic topology. For a perfect
ring of integers `𝒪_F` this is the continuity of Frobenius on `A_inf = W(𝒪_F)`, which lets
Frobenius act on its adic spectrum.

## Main results

* `WittVector.map_frobenius` : `φ` is natural, `W(f) (φ x) = φ (W(f) x)` for every ring
  homomorphism `f`.
* `WittVector.frobenius_teichmuller` : `φ [r] = [r] ^ p` in characteristic `p`.
* `WittVector.frobenius_eq_self_iff_forall_coeff` : `φ x = x` iff every coordinate of `x` is fixed
  by the `p`-power map, in characteristic `p`.
* `WittVector.frobeniusEquiv_symm_teichmuller` : `φ⁻¹ [r] = [r ^ (1 / p)]` for perfect `R`.
* `WittVector.frobeniusEquiv_symm_frobenius`, `WittVector.frobenius_frobeniusEquiv_symm` :
  `φ⁻¹ (φ x) = x` and `φ (φ⁻¹ x) = x` for perfect `R`, with `φ` written as `WittVector.frobenius`.
* `TauCeti.WittVector.continuous_frobenius` : `φ` is continuous for the `(p, [ϖ])`-adic topology.
* `TauCeti.WittVector.continuous_frobeniusEquiv_symm` : so is `φ⁻¹`, for perfect `R`.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017, §3.1.
-/

public section

namespace WittVector

section Map

variable {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]

/-- The Witt-vector Frobenius is natural: `W(f) (φ x) = φ (W(f) x)` for every ring homomorphism
`f : R →+* S`. -/
@[simp]
theorem map_frobenius (f : R →+* S) (x : WittVector p R) :
    map f (frobenius x) = frobenius (map f x) := by
  ext n
  -- the `n`-th coordinate of `φ x` is the integer polynomial `frobeniusPoly p n` evaluated at the
  -- coordinates of `x`, and `f` commutes with evaluating integer polynomials
  simp only [map_coeff, coeff_frobenius, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

end Map

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

/-- In characteristic `p`, the Witt-vector Frobenius sends a Teichmüller representative `[r]` to
its `p`-th power `[r ^ p]`. -/
@[simp]
theorem frobenius_teichmuller (r : R) : frobenius (teichmuller p r) = teichmuller p r ^ p := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, map_pow]

/-- In characteristic `p`, a Witt vector is fixed by the Witt-vector Frobenius if and only if each
of its coordinates is fixed by the `p`-power map. -/
theorem frobenius_eq_self_iff_forall_coeff (x : WittVector p R) :
    frobenius x = x ↔ ∀ n, x.coeff n ^ p = x.coeff n := by
  simp [frobenius_eq_map_frobenius, WittVector.ext_iff, map_coeff, frobenius_def]

/-- For a perfect ring of characteristic `p`, the inverse of the Witt-vector Frobenius sends a
Teichmüller representative `[r]` to the Teichmüller representative of the `p`-th root of `r`. -/
@[simp]
theorem frobeniusEquiv_symm_teichmuller [PerfectRing R p] (r : R) :
    (frobeniusEquiv p R).symm (teichmuller p r) =
      teichmuller p ((_root_.frobeniusEquiv R p).symm r) := by
  simp [frobeniusEquiv_symm_apply, map_teichmuller]

-- The next two lemmas are not `@[simp]`: simp first rewrites `(frobeniusEquiv p R).symm` to
-- `map (_root_.frobeniusEquiv R p).symm` by `WittVector.frobeniusEquiv_symm_apply`.

/-- For a perfect ring of characteristic `p`, the inverse of the Witt-vector Frobenius undoes
`WittVector.frobenius`. -/
theorem frobeniusEquiv_symm_frobenius [PerfectRing R p] (x : WittVector p R) :
    (frobeniusEquiv p R).symm (frobenius x) = x :=
  (frobeniusEquiv p R).symm_apply_apply x

/-- For a perfect ring of characteristic `p`, `WittVector.frobenius` undoes the inverse of the
Witt-vector Frobenius. -/
theorem frobenius_frobeniusEquiv_symm [PerfectRing R p] (x : WittVector p R) :
    frobenius ((frobeniusEquiv p R).symm x) = x :=
  (frobeniusEquiv p R).apply_symm_apply x

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
