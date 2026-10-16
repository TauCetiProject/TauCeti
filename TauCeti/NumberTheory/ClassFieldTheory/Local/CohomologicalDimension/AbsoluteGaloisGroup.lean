/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.KummerCoeffProP
public import TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.RootsOfUnity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ContinuousMulEquiv
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.TrivialFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Existence

/-!
# The cohomological dimension of the absolute Galois group of a local field

For a nonarchimedean local field `K` and a prime `ℓ` invertible in `K`, this file proves

```text
cd_ℓ G_K = 2
```

(`cohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit`), and in particular
`cd_ℓ G_K = 2` for every prime `ℓ` when `K` has characteristic zero, that is when `K` is a finite
extension of some `ℚ_p` (`cohomologicalDimensionAt_absoluteGaloisGroup_eq_two`).

* **`cd_ℓ G_K ≤ 2`.** By the Sylow equality `TauCeti.IsProPSylow.cohomologicalDimensionAt_eq`, it
  suffices to bound a Sylow pro-`ℓ` subgroup `P` of `G_K`, and by the pro-`ℓ` test
  `TauCeti.IsProP.cohomologicalDimensionAt_le_iff_subsingleton_cohomFp` it suffices that
  `H³(P, ℤ/ℓ) = 0`. The group `P` acts trivially on `μ_ℓ`: its image under the cyclotomic
  character `G_K → (ℤ/ℓ)ˣ` is an `ℓ`-group in a group of order `ℓ - 1`
  (`TauCeti.smul_kummerCoeff_eq_self_of_isProP`). So `μ_ℓ` is a trivial `P`-module of order `ℓ`, and
  `H³(P, ℤ/ℓ) ≅ H³(P, μ_ℓ)`, which vanishes because `P` is closed
  (`TauCeti.ClassFieldTheory.subsingleton_h3_kummerCoeff_of_isClosed`).
* **`cd_ℓ G_K ≥ 2`.** The group `H²(G_K, μ_ℓ) ≅ ℤ/ℓ` is nonzero
  (`TauCeti.ClassFieldTheory.nontrivial_h2_kummerCoeff`), and `μ_ℓ` is `ℓ`-primary.

Both bounds are proved on Tau Ceti's `Gal(Kˢ/K)` and read on Mathlib's `Field.absoluteGaloisGroup K`
through `TauCeti.absoluteGaloisGroupRestrictEquiv` and `TauCeti.cohomologicalDimensionAt_congr`.

## Main results

* `TauCeti.ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_le_two`,
  `TauCeti.ClassFieldTheory.two_le_cohomologicalDimensionAt_absoluteGaloisGroup`: the two bounds
  on `Gal(Kˢ/K)`.
* `TauCeti.ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit`:
  `cd_ℓ G_K = 2` for `ℓ` invertible in `K`.
* `TauCeti.ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_eq_two`: **`cd_ℓ G_K = 2`**
  for a local field `K` of characteristic zero and every prime `ℓ`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.3, Prop. 12.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.1.8)(i).
-/

public section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`cd_ℓ Gal(Kˢ/K) ≤ 2`** for a prime `ℓ` invertible in `K`: a Sylow pro-`ℓ` subgroup `P` fixes
`μ_ℓ`, so `H³(P, ℤ/ℓ) ≅ H³(P, μ_ℓ) = 0`. -/
theorem cohomologicalDimensionAt_absoluteGaloisGroup_le_two (hℓ : IsUnit (ℓ : K)) :
    cohomologicalDimensionAt.{0} ℓ (AbsoluteGaloisGroup K) ≤ 2 := by
  obtain ⟨P, hP⟩ := exists_isProPSylow ℓ (AbsoluteGaloisGroup K)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.isClosed.isCompact
  rw [hP.cohomologicalDimensionAt_eq]
  refine (hP.isProP.cohomologicalDimensionAt_le_iff_subsingleton_cohomFp 2).2 ?_
  refine (subsingleton_continuousCohomology_iff_subsingleton_cohomFp_of_natCard_eq
    (KummerCoeff K ℓ) (natCard_kummerCoeff hℓ)
    (smul_kummerCoeff_eq_self_of_isProP hℓ hP.isProP) 3).1 ?_
  exact subsingleton_h3_kummerCoeff_of_isClosed hℓ P hP.isClosed

/-- **`cd_ℓ Gal(Kˢ/K) ≥ 2`** for a prime `ℓ` invertible in `K`: `H²(G_K, μ_ℓ) ≅ ℤ/ℓ` is nonzero. -/
theorem two_le_cohomologicalDimensionAt_absoluteGaloisGroup (hℓ : IsUnit (ℓ : K)) :
    2 ≤ cohomologicalDimensionAt.{0} ℓ (AbsoluteGaloisGroup K) := by
  by_contra h
  have h1 : cohomologicalDimensionAt.{0} ℓ (AbsoluteGaloisGroup K) ≤ (1 : ℕ) :=
    Order.le_of_lt_add_one (lt_of_not_ge h)
  have hM : IsPPrimaryTorsion ℓ (KummerCoeff K ℓ) :=
    isPPrimaryTorsion_of_natCard_eq_pow (k := 1) (by rw [pow_one, natCard_kummerCoeff hℓ])
  have := (cohomologicalDimensionLE_iff.1 ((cohomologicalDimensionAt_le_iff ℓ _ 1).1 h1))
    (KummerCoeff K ℓ) hM 2 one_lt_two
  have := nontrivial_h2_kummerCoeff hℓ (Fact.out : ℓ.Prime).one_lt
  exact not_subsingleton _ ‹Subsingleton _›

/-- **`cd_ℓ G_K = 2`** for a nonarchimedean local field `K` and a prime `ℓ` invertible in `K`. -/
theorem cohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit (hℓ : IsUnit (ℓ : K)) :
    cohomologicalDimensionAt.{0} ℓ (Field.absoluteGaloisGroup K) = 2 := by
  rw [cohomologicalDimensionAt_congr (absoluteGaloisGroupRestrictEquiv K)]
  exact (cohomologicalDimensionAt_absoluteGaloisGroup_le_two hℓ).antisymm
    (two_le_cohomologicalDimensionAt_absoluteGaloisGroup hℓ)

/-- **`cd_ℓ G_K = 2`** for every prime `ℓ` and every nonarchimedean local field `K` of
characteristic zero, that is every finite extension of some `ℚ_p` (NSW (7.1.8)(i); Serre,
*Galois Cohomology*, II §5.3): every prime is invertible in `K`. -/
theorem cohomologicalDimensionAt_absoluteGaloisGroup_eq_two [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] :
    cohomologicalDimensionAt.{0} ℓ (Field.absoluteGaloisGroup K) = 2 :=
  cohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit
    (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero).isUnit

end TauCeti.ClassFieldTheory
