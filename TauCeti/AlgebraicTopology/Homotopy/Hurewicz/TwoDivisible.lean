/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Singular.Coefficients.TwoDivisible
public import Mathlib.Algebra.Module.ULift

/-!
# Mod-two vanishing and the first possible homotopy group

For an `(n + 1)`-connected space, vanishing of mod-two homology in degrees `n + 2` and
`n + 3` implies unique two-divisibility of `πₙ₊₂`. In particular this homotopy group is a
module over `ℤ[1/2]`, and its tensor product with `ℤ/2` vanishes. Only the two adjacent
homology groups are needed; no finite-generation assumption is imposed.

This is the first step in constructing connected covers of a simply connected mod-two
acyclic space. The Hurewicz equivalence identifies the first possible homotopy group with
integral homology, on which the coefficient exact sequence makes multiplication by two
bijective. Both adjacent vanishing hypotheses matter: the lower one gives surjectivity,
and the higher one rules out two-torsion.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.A and 4.2.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public noncomputable section

open CategoryTheory AlgebraicTopology

namespace TauCeti

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

/-- If all lower homotopy groups vanish, vanishing of mod-two homology in two adjacent
higher degrees makes the first possible nonzero homotopy group uniquely two-divisible.
The group is written additively to use its canonical integer action. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hn : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of X)))
    (hn' : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 3)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of X))) :
    IsUniquelyTwoDivisible (Additive (HomotopyGroup (Fin (n + 2)) X x)) := by
  -- The coefficient exact sequence uses lifted coefficients; transport the two zero objects.
  have liftZero (k : ℕ)
      (hk : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of X))) :
      Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ (ULift.{0} (ZMod 2)))).obj (TopCat.of X)) :=
    hk.of_iso (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).mapIso
      (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).toModuleIso).app (TopCat.of X))
  have h := (TopCat.of X).isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two
    (n + 2) (liftZero _ hn) (liftZero _ hn')
  let e : (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of X)) ≃+
      ((singularChains ℤ).obj (TopCat.of X)).homology (n + 2) :=
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).mapIso
      (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ).toModuleIso).app
        (TopCat.of X)).toLinearEquiv.toAddEquiv
  exact (h.of_addEquiv e).of_addEquiv
    (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hX).symm

end TauCeti
