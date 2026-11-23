/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Singular.Coefficients.TwoDivisible
public import Mathlib.Algebra.Module.ULift
import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo

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

The hypotheses can be stated with coefficients in the integer module `ℤ/2`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two`) or in the field `𝔽₂`, given
as any ring isomorphic to `ZMod 2`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two`).
The space lies in an arbitrary universe `u`, with the coefficients lifted to it.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.A and 4.2.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public noncomputable section

open CategoryTheory AlgebraicTopology

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

/-- If all lower homotopy groups vanish, vanishing of mod-two homology in two adjacent
higher degrees makes the first possible nonzero homotopy group uniquely two-divisible.
The group is written additively to use its canonical integer action. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hn : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj (TopCat.of X)))
    (hn' : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 3)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj (TopCat.of X))) :
    IsUniquelyTwoDivisible (Additive (HomotopyGroup (Fin (n + 2)) X x)) :=
  ((TopCat.of X).isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two (n + 2) hn
    hn').of_addEquiv (HomotopyGroup.cubicalHurewiczSingularHomologyUliftAddEquiv hX).symm

/-- If all lower homotopy groups vanish, vanishing of homology with coefficients in the field `𝔽₂`,
or in any ring `k` isomorphic to it, in two adjacent higher degrees makes the first possible
nonzero homotopy group uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two {k : Type u} [CommRing k]
    (e : k ≃+* ZMod 2) (hX : ∀ j < n + 2, Subsingleton (HomotopyGroup (Fin j) X x))
    (hn : Subsingleton (((singularChains k).obj (TopCat.of X)).homology (n + 2)))
    (hn' : Subsingleton (((singularChains k).obj (TopCat.of X)).homology (n + 3))) :
    IsUniquelyTwoDivisible (Additive (HomotopyGroup (Fin (n + 2)) X x)) := by
  rw [← singularHomologyFunctor_obj_obj] at hn hn'
  exact isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two hX
    (((TopCat.of X).isZero_singularHomology_modTwo_iff_of_ringEquiv e _).2
      (ModuleCat.isZero_iff_subsingleton.2 hn))
    (((TopCat.of X).isZero_singularHomology_modTwo_iff_of_ringEquiv e _).2
      (ModuleCat.isZero_iff_subsingleton.2 hn'))

end TauCeti
