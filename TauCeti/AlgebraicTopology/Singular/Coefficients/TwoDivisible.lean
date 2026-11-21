/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Basic
public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.Algebra.Category.ModuleCat.ZModCoefficientSequence
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence

/-!
# Mod-two vanishing and integral homology

If the mod-two homology of a space vanishes in degrees `n` and `n + 1`, multiplication by two on
its integral homology in degree `n` is bijective. This is the `m = 2` specialization of
`TopCat.bijective_zsmul_singularHomology_of_isZero_zmod`, phrased with
`TauCeti.IsUniquelyTwoDivisible`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.A, change of coefficients.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public noncomputable section

open CategoryTheory Limits

universe u

namespace TopCat

/-- Vanishing of mod-two singular homology in two adjacent degrees makes integral singular
homology in the lower degree uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two (X : TopCat.{u}) (n : ℕ)
    (hn : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X))
    (hn' : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X)) :
    TauCeti.IsUniquelyTwoDivisible
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) := by
  rw [TauCeti.isUniquelyTwoDivisible_iff]
  simpa only [Nat.cast_ofNat] using
    X.bijective_zsmul_singularHomology_of_isZero_zmod 2 n hn hn'

end TopCat
