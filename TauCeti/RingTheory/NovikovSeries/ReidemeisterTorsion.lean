/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.RestrictScalars
public import TauCeti.RingTheory.NovikovSeries.MinimalPrimes
import Mathlib.RingTheory.Localization.Module

/-!
# Torsion of Novikov complexes under a finite cover

Let `H` be a finitely generated abelian group with a period homomorphism `N : H →+ ℝ`, and let
`K ≤ H` be a subgroup of finite index, the deck group of a finite cover. The Novikov series
`Nov(R, H, N)` are finite free over `Nov(R, K, N|K)`, for instance on the coset monomials
`TauCeti.NovikovSeries.cosetBasis`. A based complex `C` over `Nov(R, H, N)` therefore restricts to a
based complex `D` over `Nov(R, K, N|K)`, based by the products of the basis vectors of `C` with a
basis `β` of `Nov(R, H, N)`: the complex of the cover, built from the lifts of the cells or critical
points to the cover.

The torsion of such complexes lives in the total rings of fractions `QA` of `Nov(R, K, N|K)` and
`QB` of `Nov(R, H, N)`, finite products of fields when they are reduced, and is taken
componentwise (`HomologicalComplex.componentwiseReidemeisterTorsion`). If `K` contains the torsion
subgroup of `H`, the componentwise torsion of `D` is the norm `Algebra.fractionNorm` of the
componentwise torsion of `C`
(`TauCeti.NovikovSeries.fractionNorm_componentwiseReidemeisterTorsion_of_torsion_le`). This keeps
track of partial acyclicity: a field component of the torsion of `D` vanishes exactly when the
component of the torsion of `C` above it does. Under this hypothesis each field component of `QA`
has a single field component of `QB` above it
(`TauCeti.NovikovSeries.comap_algebraMap_bijective_of_torsion_le`), and the formula is the norm
formula `HomologicalComplex.norm_componentwiseReidemeisterTorsion` for the restriction of scalars.

## Main results

* `TauCeti.NovikovSeries.fractionNorm_componentwiseReidemeisterTorsion_of_torsion_le`: under a
  finite cover whose deck group contains the torsion, the componentwise torsion of the restricted
  complex is the norm of the componentwise torsion.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 3.4, Lemma 3.5 and Proposition 3.6(b) (torsion under finite cyclic covers satisfying
  condition (3.8)).
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Chapter I.
-/

public section

namespace TauCeti

namespace NovikovSeries

variable (R : Type*) {H : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [AddCommGroup H]
  [AddGroup.FG H] (N : H →+ ℝ) {K : AddSubgroup H}
  [K.FiniteIndex] (QA QB : Type*) [CommRing QA] [CommRing QB]
  [Algebra (NovikovSeries R K (N.comp K.subtype)) QA]
  [IsFractionRing (NovikovSeries R K (N.comp K.subtype)) QA]
  [Algebra (NovikovSeries R H N) QB] [IsFractionRing (NovikovSeries R H N) QB]
  [Algebra QA QB] [Algebra (NovikovSeries R K (N.comp K.subtype)) QB]
  [IsScalarTower (NovikovSeries R K (N.comp K.subtype)) QA QB]
  [IsScalarTower (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) QB]
  [IsArtinianRing QA] [IsReduced QA] [IsArtinianRing QB] [IsReduced QB]

/-- **Torsion under a finite cover containing the torsion.** Let `K` be a subgroup of finite index
of `H` containing its torsion subgroup, and let `β` be an ordered basis of `Nov(R, H, N)` over
`Nov(R, K, N|K)`, such as the coset monomials `TauCeti.NovikovSeries.cosetBasis` reindexed along
an equivalence `H ⧸ K ≃ Fin m`. Let `(D, e)` be the restriction of scalars of a based complex
`(C, c)` over `Nov(R, H, N)` to `Nov(R, K, N|K)`, based by the vectors `β a • c i k` as in
`HomologicalComplex.norm_reidemeisterTorsion`. Then the componentwise torsion of `D` in the total
ring of fractions `QA` of `Nov(R, K, N|K)` is the norm of the componentwise torsion of `C` in the
total ring of fractions `QB` of `Nov(R, H, N)`. Both total rings of fractions are Artinian
(`TauCeti.NovikovSeries.isArtinianRing_of_isFractionRing`), and they are reduced over `R = ℤ`. -/
theorem fractionNorm_componentwiseReidemeisterTorsion_of_torsion_le
    (hK : AddCommGroup.torsion H ≤ K) {m : ℕ}
    (β : Module.Basis (Fin m) (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N))
    {C : ChainComplex (ModuleCat (NovikovSeries R H N)) ℤ} {n : ℤ → ℕ}
    {c : ∀ i, Module.Basis (Fin (n i)) (NovikovSeries R H N) (C.X i)}
    {D : ChainComplex (ModuleCat (NovikovSeries R K (N.comp K.subtype))) ℤ}
    {e : ∀ i, Module.Basis (Fin (n i * m)) (NovikovSeries R K (N.comp K.subtype)) (D.X i)}
    (hd : ∀ i, LinearMap.toMatrix (e (i + 1)) (e i) (D.d (i + 1) i).hom =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.comp _ _ _ _ _
        ((LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map
          (Algebra.leftMulMatrix β)))) :
    Algebra.fractionNorm (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N) QA QB
        (C.componentwiseReidemeisterTorsion c
          (algebraMap (NovikovSeries R H N) QB)) =
      D.componentwiseReidemeisterTorsion e (algebraMap _ QA) := by
  -- `QB` is the localization of `Nov(R, H, N)` at the non-zero-divisors of `Nov(R, K, N|K)`, so
  -- the image of `β` is a basis of `QB` over `QA`.
  have := (IsFractionRing.isLocalization_algebraMapSubmonoid_iff
    (NovikovSeries R K (N.comp K.subtype)) (S := NovikovSeries R H N) QB).2 inferInstance
  rw [Algebra.fractionNorm_eq_norm]
  exact HomologicalComplex.norm_componentwiseReidemeisterTorsion hd
    (β' := β.localizationLocalization QA
      (nonZeroDivisors (NovikovSeries R K (N.comp K.subtype))) QB)
    (fun a ↦ β.localizationLocalization_apply QA _ QB a)
    (comap_algebraMap_bijective_of_torsion_le R N QA QB hK).1

end NovikovSeries

end TauCeti
