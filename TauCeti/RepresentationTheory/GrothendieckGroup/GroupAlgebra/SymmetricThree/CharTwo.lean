/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Augmentation
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.PrimePower
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.RepresentationTheory.Symmetric.Standard
public import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.RepresentationTheory.Induction.PointStabilizer

/-!
# Permutation classes of `S₃` in characteristic two

Write `S` for the standard two-dimensional representation. Over a field of characteristic two,
the three-point permutation module has class `1 + [S]`, the regular module has class
`2 • 1 + 2 • [S]`, and the permutation module on cosets of `A₃` has class `2 • 1`.
The induction formulas hold for every point stabilizer, so the same class calculations apply
to each of the three order-two subgroups.

All equalities are in the integral exact Grothendieck group, including the class of the
nonsplit two-point permutation module. They supply the permutation terms in modular Artin
induction. The three-point augmentation relation itself holds in every characteristic.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  §VII.3, (7.3.4).
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

variable (k : Type) [Field k]

/-- The natural permutation module of `S₃` has the standard module and the trivial line as
its Grothendieck constituents in every characteristic. -/
@[simp]
theorem permK0_fin_three_eq_one_add_standard :
    letI : Module.Finite k[Equiv.Perm (Fin 3)] (standardRepresentation k (Fin 3)).asModule :=
      Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
    permK0 k (Equiv.Perm (Fin 3)) (Fin 3) =
      1 + ExactK0.of (FGModuleCat.of k[Equiv.Perm (Fin 3)]
        (standardRepresentation k (Fin 3)).asModule) := by
  rw [permK0_eq_augmentation_add_trivial, toRepresentation_augmentationSubrepresentation,
    ← exactK0_one_eq_of_trivial, add_comm]

/-- Inducing the trivial line from any point stabilizer gives the three-point permutation
class, namely the trivial class plus the standard class. -/
@[simp]
theorem indK0_one_stabilizer_fin_three_eq_one_add_standard (a : Fin 3) :
    letI : Module.Finite k[Equiv.Perm (Fin 3)] (standardRepresentation k (Fin 3)).asModule :=
      Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
    indK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a) 1 =
      1 + ExactK0.of (FGModuleCat.of k[Equiv.Perm (Fin 3)]
        (standardRepresentation k (Fin 3)).asModule) := by
  rw [exactK0_one_eq_of_trivial, indK0_of_trivial,
    permK0_congr k (quotientStabilizerEquiv (Equiv.Perm (Fin 3)) a)
      (quotientStabilizerEquiv_smul (Equiv.Perm (Fin 3)) a),
    permK0_fin_three_eq_one_add_standard]

variable [CharP k 2]

/-- In characteristic two, the regular class is twice the class induced from any point
stabilizer. This removes the two-part of that cyclic subgroup in modular Artin induction. -/
theorem indK0_one_bot_eq_two_nsmul_stabilizer_fin_three (a : Fin 3) :
    indK0 k (⊥ : Subgroup (Equiv.Perm (Fin 3))) 1 =
      2 • indK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a) 1 := by
  have hpow : ∀ c ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
      ∃ n : ℕ, c ^ 2 ^ n ∈ (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by
    intro c hc
    refine ⟨1, ?_⟩
    have h := pow_card_eq_one' (x := (⟨c, hc⟩ :
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a))
    rw [card_stabilizer_perm_fin_three] at h
    exact congrArg Subtype.val h
  simpa only [← exactK0_one_eq_of_trivial, Subgroup.relIndex_bot_left,
    card_stabilizer_perm_fin_three] using
    indK0_of_trivial_eq_relIndex_nsmul (k := k) 2 bot_le hpow

/-- In characteristic two, the regular `S₃`-module has two trivial and two standard
composition factors in the exact Grothendieck group. -/
@[simp]
theorem permK0_regular_fin_three_eq_two_nsmul_one_add_standard :
    letI : Module.Finite k[Equiv.Perm (Fin 3)] (standardRepresentation k (Fin 3)).asModule :=
      Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
    permK0 k (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)) =
      2 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) +
      2 • ExactK0.of (FGModuleCat.of k[Equiv.Perm (Fin 3)]
        (standardRepresentation k (Fin 3)).asModule) := by
  rw [← permK0_congr k QuotientGroup.quotientBot.toEquiv quotientBot_equivariant,
    ← indK0_of_trivial, ← exactK0_one_eq_of_trivial,
    indK0_one_bot_eq_two_nsmul_stabilizer_fin_three k 0,
    indK0_one_stabilizer_fin_three_eq_one_add_standard, nsmul_add]

/-- The coset permutation module of `A₃` in characteristic two has two trivial
composition factors, without claiming that the extension splits. -/
@[simp]
theorem permK0_quotient_alternating_fin_three_eq_two_nsmul_one :
    permK0 k (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) =
        2 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) := by
  have hpow : ∀ g : Equiv.Perm (Fin 3), ∃ n : ℕ, g ^ 2 ^ n ∈ alternatingGroup (Fin 3) := by
    intro g
    refine ⟨1, ?_⟩
    simpa only [pow_one, alternatingGroup.index_eq_two] using
      (Subgroup.pow_index_mem (H := alternatingGroup (Fin 3)) g)
  simpa only [← permK0_def, ← exactK0_one_eq_of_trivial, alternatingGroup.index_eq_two] using
    exactK0_ofMulAction_quotient_eq_index_nsmul (k := k) 2 (alternatingGroup (Fin 3)) hpow

/-- Inducing the trivial line from `A₃` in characteristic two gives twice the trivial
class of `S₃`. -/
@[simp]
theorem indK0_one_alternating_fin_three_eq_two_nsmul_one :
    indK0 k (alternatingGroup (Fin 3)) 1 =
      2 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) := by
  rw [exactK0_one_eq_of_trivial, indK0_of_trivial,
    permK0_quotient_alternating_fin_three_eq_two_nsmul_one]

end TauCeti
