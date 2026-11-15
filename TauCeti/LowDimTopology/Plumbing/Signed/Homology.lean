/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.LowDimTopology.Plumbing.Signed.Differential

/-!
# Lattice homology over `R[U]`

This file packages the oriented plumbing-lattice differential with coefficients in `R[U]` as a
short complex and defines its homology, Némethi's lattice homology with coefficients in `R[U]`;
for `R = ℤ` it is lattice homology over `ℤ[U]`. For a plumbing graph `P` with linearly ordered
vertices and a characteristic covector `k`, the oriented differential occurs on both sides of the
short complex

`(PlumbingCube V →₀ R[U]) → (PlumbingCube V →₀ R[U]) → (PlumbingCube V →₀ R[U])`,

which is a short complex because the oriented differential squares to zero. Its homology is the
kernel of the differential modulo its range. As for the characteristic-two theory of
`TauCeti.LowDimTopology.Plumbing.Homology`, this is the ungraded total module obtained from all
cubical dimensions, and Mathlib's `ShortComplex` homology API applies to it directly.

## Main definitions

* `TauCeti.PlumbingGraph.signedLatticeShortComplex`: the short complex with the oriented lattice
  differential in both positions.
* `TauCeti.PlumbingGraph.signedLatticeHomology`: its homology, an `R[U]`-module.

## Main results

* `TauCeti.PlumbingGraph.signedLatticeShortComplex_exact_iff_range_eq_ker`: the short complex is
  exact exactly when the boundaries of the oriented lattice differential are all of its cycles.

## References

The oriented cubical complex and its homology over `ℤ[U]` are those of A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

open CategoryTheory Polynomial

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [LinearOrder V] [Fintype V] (R : Type*) [CommRing R]

/-- The short complex whose two maps are the oriented lattice differential over `R[U]`.

The three objects are the total plumbing-chain module on all cubical dimensions. The
short-complex condition is exactly `signedLatticeDifferential_comp_self`. -/
noncomputable def signedLatticeShortComplex
    (P : PlumbingGraph V) (k : P.characteristicVectors) : ShortComplex (ModuleCat R[X]) :=
  ShortComplex.moduleCatMk (P.signedLatticeDifferential R k) (P.signedLatticeDifferential R k)
    (P.signedLatticeDifferential_comp_self R k)

/-- The left object of the oriented lattice short complex is the plumbing-chain module. -/
@[simp]
theorem signedLatticeShortComplex_X₁ (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.signedLatticeShortComplex R k).X₁ = ModuleCat.of R[X] (PlumbingCube V →₀ R[X]) :=
  (rfl)

/-- The middle object of the oriented lattice short complex is the plumbing-chain module. -/
@[simp]
theorem signedLatticeShortComplex_X₂ (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.signedLatticeShortComplex R k).X₂ = ModuleCat.of R[X] (PlumbingCube V →₀ R[X]) :=
  (rfl)

/-- The right object of the oriented lattice short complex is the plumbing-chain module. -/
@[simp]
theorem signedLatticeShortComplex_X₃ (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.signedLatticeShortComplex R k).X₃ = ModuleCat.of R[X] (PlumbingCube V →₀ R[X]) :=
  (rfl)

/-- The left map of the oriented lattice short complex is the oriented lattice differential. -/
@[simp]
theorem signedLatticeShortComplex_f (P : PlumbingGraph V) (k : P.characteristicVectors) :
    HEq (P.signedLatticeShortComplex R k).f
      (ModuleCat.ofHom (P.signedLatticeDifferential R k)) :=
  (HEq.rfl)

/-- The right map of the oriented lattice short complex is the oriented lattice differential. -/
@[simp]
theorem signedLatticeShortComplex_g (P : PlumbingGraph V) (k : P.characteristicVectors) :
    HEq (P.signedLatticeShortComplex R k).g
      (ModuleCat.ofHom (P.signedLatticeDifferential R k)) :=
  (HEq.rfl)

/-- Exactness of the oriented lattice short complex says exactly that the boundaries of the
oriented lattice differential are all of its cycles. -/
theorem signedLatticeShortComplex_exact_iff_range_eq_ker (P : PlumbingGraph V)
    (k : P.characteristicVectors) :
    (P.signedLatticeShortComplex R k).Exact ↔
      LinearMap.range (P.signedLatticeDifferential R k) =
        LinearMap.ker (P.signedLatticeDifferential R k) :=
  ShortComplex.moduleCat_exact_iff_range_eq_ker _

/-- **Lattice homology over `R[U]`**: the homology of the oriented weighted plumbing-lattice
short complex. For `R = ℤ` this is Némethi's lattice homology over `ℤ[U]`.

This is Mathlib's canonical homology object, so the generic `ShortComplex.cycles`,
`ShortComplex.homologyπ`, and homology-map API can be used directly via
`signedLatticeHomology_def`. -/
noncomputable def signedLatticeHomology
    (P : PlumbingGraph V) (k : P.characteristicVectors) : ModuleCat R[X] :=
  (P.signedLatticeShortComplex R k).homology

/-- Lattice homology over `R[U]` is the canonical homology object of the oriented lattice short
complex. -/
@[simp]
theorem signedLatticeHomology_def (P : PlumbingGraph V) (k : P.characteristicVectors) :
    P.signedLatticeHomology R k = (P.signedLatticeShortComplex R k).homology :=
  (rfl)

end PlumbingGraph

end TauCeti
