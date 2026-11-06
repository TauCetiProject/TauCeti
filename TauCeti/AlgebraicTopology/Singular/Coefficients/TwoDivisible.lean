/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Basic
public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.Algebra.Category.ModuleCat.ModTwo
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo

/-!
# Mod-two vanishing and integral homology

If the mod-two homology of a space vanishes in degrees n and n + 1, multiplication by two on
its integral homology in degree n is bijective. This is the algebraic step used with the Hurewicz
isomorphism to deduce unique two-divisibility of a first nonzero homotopy group.

The proof uses the long exact sequence of the coefficient sequence ℤ → ℤ → ℤ/2, through the
reduction modulo two: its kernel is twice integral homology
(`TopCat.ker_singularHomologyReductionModTwo`), and it is onto in degree n + 1 exactly when
multiplication by two is injective in degree n
(`TopCat.surjective_singularHomologyReductionModTwo_succ_iff`). It requires no connectivity or
finite-generation assumptions. The coefficients are universe-lifted so that the space can live
in any universe. The reusable coefficient sequence and its exactness are
`TauCeti.modTwoCoefficientSequence` and `TauCeti.modTwoCoefficientSequence_shortExact`.

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
  -- Vanishing in degree `n + 1` makes the reduction onto, so two is injective in degree `n`.
  have hinj := (X.surjective_singularHomologyReductionModTwo_succ_iff n).1 fun y ↦
    ⟨0, (ModuleCat.isZero_iff_subsingleton.1 hn').elim _ _⟩
  -- Vanishing in degree `n` makes every class reduce to zero, hence twice a class.
  have hsurj := LinearMap.range_eq_top.1 ((X.ker_singularHomologyReductionModTwo n).symm.trans
    (LinearMap.ker_eq_top.2
      (LinearMap.ext fun _ ↦ (ModuleCat.isZero_iff_subsingleton.1 hn).elim _ _)))
  rw [TauCeti.isUniquelyTwoDivisible_iff]
  -- the integer action of the abelian group agrees with that of the integer module
  convert (show Function.Bijective _ from ⟨hinj, hsurj⟩) using 1
  ext x
  simp [two_smul, two_zsmul]

end TopCat
