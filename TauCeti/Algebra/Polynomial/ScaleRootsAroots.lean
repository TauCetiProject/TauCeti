/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Linear-factor products over roots of `Polynomial.scaleRoots`

Let `K` be an integral domain algebra over a commutative ring `F` with injective structure map
`algebraMap F K`, let `φ : K →* L` be a multiplicative map into a commutative ring `L`, and let
`u : F` map to a unit of `K`. Scaling the roots of `p : F[X]` by `u` multiplies every root in
`p.aroots K` by `algebraMap F K u`. Consequently, substituting `C (φ (algebraMap F K u)) * X` into
`∏ x ∈ (p.scaleRoots u).aroots K, (X - C (φ x))` yields
`C (φ (algebraMap F K u) ^ (p.aroots K).card) * ∏ x ∈ p.aroots K, (X - C (φ x))`, and in
particular the original linear-factor product divides the substituted product.

## Provenance

Extracted and generalized from `grh-lean`
(https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC),
file `src/New/Congruences/GaloisRepresentations/AttachedRepresentations.lean`
(`prod_aroots_dvd_prod_aroots_scaleRoots_comp`).
-/

public section

namespace TauCeti

open Polynomial

private lemma aroots_scaleRoots {F K : Type*} [CommRing F] [CommRing K] [IsDomain K] [Algebra F K]
    (h_inj : Function.Injective (algebraMap F K)) (p : F[X]) {u : F}
    (hu : IsUnit (algebraMap F K u)) :
    (p.scaleRoots u).aroots K = (p.aroots K).map fun x ↦ algebraMap F K u * x := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · have hlc : algebraMap F K p.leadingCoeff ≠ 0 :=
      (map_ne_zero_iff (algebraMap F K) h_inj).mpr (leadingCoeff_ne_zero.mpr hp)
    rw [aroots, map_scaleRoots p u (algebraMap F K) hlc, roots_scaleRoots _ hu, aroots]

/-- Substituting `C (φ (algebraMap F K u)) * X` into the linear-factor product over
`(p.scaleRoots u).aroots K` pulls out `C (φ (algebraMap F K u) ^ (p.aroots K).card)` times the
linear-factor product over `p.aroots K`. -/
theorem prod_aroots_scaleRoots_comp {F K L : Type*} [CommRing F] [CommRing K] [IsDomain K]
    [Algebra F K] [CommRing L] (h_inj : Function.Injective (algebraMap F K))
    (φ : K →* L) (p : F[X]) {u : F} (hu : IsUnit (algebraMap F K u)) :
    (((p.scaleRoots u).aroots K).map fun x ↦ X - C (φ x)).prod.comp
        (C (φ (algebraMap F K u)) * X) =
      C (φ (algebraMap F K u) ^ (p.aroots K).card) *
        ((p.aroots K).map fun x ↦ X - C (φ x)).prod := by
  rw [aroots_scaleRoots h_inj p hu, multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  have hfactor (x : K) :
      (X - C (φ (algebraMap F K u * x))).comp (C (φ (algebraMap F K u)) * X) =
        C (φ (algebraMap F K u)) * (X - C (φ x)) := by
    simp only [map_mul, sub_comp, mul_comp, X_comp, C_comp]
    ring
  calc
    ((p.aroots K).map fun x ↦
        (X - C (φ (algebraMap F K u * x))).comp (C (φ (algebraMap F K u)) * X)).prod
      = ((p.aroots K).map fun x ↦ C (φ (algebraMap F K u)) * (X - C (φ x))).prod := by
        congr 1
        exact Multiset.map_congr rfl fun x _ ↦ hfactor x
    _ = ((p.aroots K).map fun _ ↦ C (φ (algebraMap F K u))).prod *
          ((p.aroots K).map fun x ↦ X - C (φ x)).prod := Multiset.prod_map_mul
    _ = C (φ (algebraMap F K u) ^ (p.aroots K).card) *
          ((p.aroots K).map fun x ↦ X - C (φ x)).prod := by
        rw [Multiset.map_const', Multiset.prod_replicate, map_pow]

/-- The linear-factor product over `p.aroots K` divides the linear-factor product over
`(p.scaleRoots u).aroots K` evaluated at `C (φ (algebraMap F K u)) * X`. -/
theorem prod_aroots_dvd_prod_aroots_scaleRoots_comp {F K L : Type*} [CommRing F] [CommRing K]
    [IsDomain K] [Algebra F K] [CommRing L] (h_inj : Function.Injective (algebraMap F K))
    (φ : K →* L) (p : F[X]) {u : F} (hu : IsUnit (algebraMap F K u)) :
    ((p.aroots K).map fun x ↦ X - C (φ x)).prod ∣
      (((p.scaleRoots u).aroots K).map fun x ↦ X - C (φ x)).prod.comp
        (C (φ (algebraMap F K u)) * X) := by
  rw [prod_aroots_scaleRoots_comp h_inj φ p hu]
  exact dvd_mul_left _ _

end TauCeti
