/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.Algebra.Category.ModuleCat.ZModCoefficientSequence
import TauCeti.Algebra.Homology.Linear

/-!
# Singular homology and the mod-`m` coefficient sequence

The first map of the coefficient sequence `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/m ⟶ 0`
(`TauCeti.zmodCoefficientSequence`) is multiplication by `m`, so it induces multiplication by `m`
on integral singular homology `Hₙ(X; ℤ)`
(`TopCat.singularHomologyFunctor_map_zmodCoefficientSequence_f_app`). This identifies the maps
`Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ)` in the coefficient long exact sequence of
`TauCeti.AlgebraicTopology.Singular.Coefficients.Bockstein`; for `m = 2` see
`TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo`.
-/

public section

open CategoryTheory AlgebraicTopology

universe u

namespace TopCat

/-- The coefficient map `ℤ ⟶ ℤ` of the mod-`m` coefficient sequence induces multiplication by `m`
on integral singular homology. -/
theorem singularHomologyFunctor_map_zmodCoefficientSequence_f_app (X : TopCat.{u}) (m n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
        (TauCeti.zmodCoefficientSequence.{u} m).f).app X).hom =
      LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m := by
  -- Mathlib's `singularHomologyFunctor` is by definition singular chains followed by homology, and
  -- the first coefficient map is multiplication by `m` (`TauCeti.zmodCoefficientSequence_f`)
  change (HomologicalComplex.homologyMap (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map
    ((m : ℤ) • 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ)))).app X) n).hom =
      LinearMap.lsmul ℤ ((((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X).homology n) m
  ext x
  simp [HomologicalComplex.homologyMap_smul, Nat.cast_smul_eq_nsmul]

end TopCat
