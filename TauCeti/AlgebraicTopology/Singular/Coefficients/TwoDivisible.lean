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
import TauCeti.AlgebraicTopology.Singular.Coefficients.PrimeField

/-!
# Mod-two vanishing and integral homology

If the mod-two homology of a space vanishes in degrees n and n + 1, multiplication by two on
its integral homology in degree n is bijective. This is the algebraic step used with the Hurewicz
isomorphism to deduce unique two-divisibility of a first nonzero homotopy group.

This is the case m = 2 of two consequences of the long exact sequence of the coefficient
sequence ℤ → ℤ → ℤ/m: vanishing of mod-m homology in degree n + 1 makes multiplication by m
injective in degree n (`TopCat.injective_lsmul_singularHomology_of_isZero_zmod`), and vanishing
in degree n makes it onto (`TopCat.surjective_lsmul_singularHomology_of_isZero_zmod`). It
requires no connectivity or finite-generation assumptions. The coefficients are universe-lifted
so that the space can live in any universe. The reusable coefficient sequence and its exactness are
`TauCeti.zmodCoefficientSequence 2` and `TauCeti.zmodCoefficientSequence_shortExact`.

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
  -- Vanishing in degree `n + 1` makes two injective, and vanishing in degree `n` makes it onto.
  rw [TauCeti.isUniquelyTwoDivisible_iff]
  -- the integer action of the abelian group agrees with that of the integer module
  convert (show Function.Bijective _ from
    ⟨X.injective_lsmul_singularHomology_of_isZero_zmod 2 n hn',
      X.surjective_lsmul_singularHomology_of_isZero_zmod 2 n hn⟩) using 1
  ext x
  simp [two_smul, two_zsmul]

end TopCat
