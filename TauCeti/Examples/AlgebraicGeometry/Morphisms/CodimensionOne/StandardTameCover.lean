/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.CodimensionOne.StandardTameCover

import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Test: the square root cover of the punctured line over `ℤ[1/2]`

Let `A = ℤ[1/2][t]` be the coordinate ring of the affine line `𝔸¹_{ℤ[1/2]}`. The standard cover
`A[x]/(x² − t)` restricted to `D(t)` is `Spec ℤ[1/2][x, t, t⁻¹]/(x² − t) → Spec ℤ[1/2][t, t⁻¹]`.
It is tamely ramified over `𝔸¹_{ℤ[1/2]}` in codimension one, because `2` is invertible in `A`
(`TauCeti.AlgebraicGeometry.standardTameCover_isTamelyRamifiedInCodimOne`), but it is not
unramified there, because its ramification index along `t = 0` is `2`
(`TauCeti.AlgebraicGeometry.standardTameCover_isUnramifiedInCodimOne_iff`). So the two notions of
Stacks, Section 58.31 differ.

## References

* [Stacks Project, Section 58.31](https://stacks.math.columbia.edu/tag/0BSE).
* [Stacks Project, Example 58.31.4](https://stacks.math.columbia.edu/tag/0EYF).
-/

public section

open AlgebraicGeometry Polynomial

namespace TauCeti.Examples.CodimensionOne

/-- Over a nontrivial reduced Noetherian ring `R` in which `2` is invertible, the standard cover
`R[t][x]/(x² − t)` restricted to `D(t)` is tamely ramified over `𝔸¹_R` in codimension one and is
not unramified over it in codimension one. -/
private theorem square_root_tame (R : Type) [CommRing R] [Nontrivial R] [IsReduced R]
    [IsNoetherianRing R] (h2 : IsUnit (2 : R)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R[X] (standardTameCover R[X] X 2))) ∣_
      PrimeSpectrum.basicOpen X).IsTamelyRamifiedInCodimOne ∧
    ¬ (Spec.map (CommRingCat.ofHom (algebraMap R[X] (standardTameCover R[X] X 2))) ∣_
      PrimeSpectrum.basicOpen X).IsUnramifiedInCodimOne := by
  -- `(t)` is the kernel of `constantCoeff : R[t] → R`, so `R[t] ⧸ (t) ≅ R` is reduced.
  have : IsReduced (R[X] ⧸ Ideal.span {(X : R[X])}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← ker_constantCoeff]
    exact (RingHom.ker_isRadical_iff_reduced_of_surjective
      (constantCoeff_surjective (R := R))).mpr ‹_›
  have h2X : IsUnit ((2 : ℕ) : R[X]) := by
    simpa only [Nat.cast_ofNat, map_ofNat] using h2.map (C : R →+* R[X])
  -- The arguments are named explicitly: unifying them with the goal times out.
  refine ⟨AlgebraicGeometry.standardTameCover_isTamelyRamifiedInCodimOne (A := R[X]) (f := X)
    (e := 2) X_mem_nonZeroDivisors h2X, fun h ↦ ?_⟩
  have := (AlgebraicGeometry.standardTameCover_isUnramifiedInCodimOne_iff (A := R[X]) (f := X)
    (e := 2) X_mem_nonZeroDivisors not_isUnit_X two_ne_zero).mp h
  omega

/-- *test_square_root_tame*: over `ℤ[1/2]`, the cover
`Spec ℤ[1/2][x, t, t⁻¹]/(x² − t) → Spec ℤ[1/2][t, t⁻¹]`, the standard cover `A[x]/(x² − t)` of
`A = ℤ[1/2][t]` restricted to `D(t)`, is tamely ramified over `𝔸¹_{ℤ[1/2]} = Spec A` in
codimension one and is not unramified over it in codimension one. -/
theorem test_square_root_tame :
    (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (2 : ℤ))[X]
        (standardTameCover (Localization.Away (2 : ℤ))[X] X 2))) ∣_
      PrimeSpectrum.basicOpen X).IsTamelyRamifiedInCodimOne ∧
    ¬ (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (2 : ℤ))[X]
        (standardTameCover (Localization.Away (2 : ℤ))[X] X 2))) ∣_
      PrimeSpectrum.basicOpen X).IsUnramifiedInCodimOne :=
  have : Nontrivial (Localization.Away (2 : ℤ)) :=
    (IsLocalization.injective (M := Submonoid.powers (2 : ℤ)) (Localization.Away (2 : ℤ))
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero two_ne_zero))).nontrivial
  square_root_tame _ (by
    simpa only [map_ofNat] using IsLocalization.Away.algebraMap_isUnit (R := ℤ)
      (S := Localization.Away (2 : ℤ)) 2)

end TauCeti.Examples.CodimensionOne
