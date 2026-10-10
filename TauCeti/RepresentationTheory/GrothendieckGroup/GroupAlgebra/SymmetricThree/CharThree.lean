/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Modular.Three
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Projection
import TauCeti.RepresentationTheory.Induction.PointStabilizer

/-!
# Composition factors of the S₃ permutation module in characteristic three

The standard module has a trivial submodule with sign quotient. The augmentation sequence
then gives `[k³] = 2[k] + [sgn]` in the exact Grothendieck group. The permutation module is
induced from a point stabilizer, so this also evaluates induction of its trivial line.
All equalities below are in the integral Grothendieck group, rather than in field-valued traces.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

variable (k : Type) [Field k] [CharP k 3]

/-- The standard S₃ module has one trivial and one sign composition factor
in characteristic three. -/
theorem fdRepK0RingEquiv_of_standard_perm_fin_three_char_three :
    fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
      (ExactK0.of (FDRep.of (standardRepresentation k (Fin 3)))) =
      1 + fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
        (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)))) := by
  let : Module.Finite k[Equiv.Perm (Fin 3)]
      (standardRepresentation k (Fin 3)).asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  let : Module.Finite k[Equiv.Perm (Fin 3)]
      (Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  let : Module.Finite k[Equiv.Perm (Fin 3)]
      (Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))).asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  rw [FDRep.ofLinearCharacter_def, fdRepK0RingEquiv_of, fdRepK0RingEquiv_of,
    exactK0_one_eq_of_trivial]
  simp only [FDRep.of_ρ']
  have hS := standardThreeSequence_shortExact k
  let := hS.mono_f
  let := hS.epi_g
  apply (finiteModulesExactK0Equiv k[Equiv.Perm (Fin 3)]).injective
  simp only [map_add, finiteModulesExactK0Equiv_of]
  have h := ExactK0.of_conflation_fullSubcategory
    (isExtensionClosed_finiteModules k[Equiv.Perm (Fin 3)])
    ((ExactStructure.abelian_conflation _).2 (hS.map Rep.toModuleMonoidAlgebra))
    (by
      rw [ShortComplex.map_X₁, standardThreeSequence_X₁]
      exact (ModuleCat.isFG_iff (ModuleCat.of k[Equiv.Perm (Fin 3)]
        (Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule)).2 inferInstance)
    (by
      rw [ShortComplex.map_X₃, standardThreeSequence_X₃]
      exact (ModuleCat.isFG_iff (ModuleCat.of k[Equiv.Perm (Fin 3)]
        (Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))).asModule)).2
        inferInstance)
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃] at h
  simp only [standardThreeSequence_X₁, standardThreeSequence_X₂, standardThreeSequence_X₃] at h
  simpa only [Rep.toModuleMonoidAlgebra, Rep.of_ρ, Rep.trivial] using h

/-- The three-point permutation module of S₃ has two trivial factors and one sign factor. -/
theorem permK0_fin_three_char_three :
    permK0 k (Equiv.Perm (Fin 3)) (Fin 3) =
      2 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) +
        fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
          (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)))) := by
  have hS := permutationAugmentationSequence_shortExact k (Equiv.Perm (Fin 3)) (Fin 3)
  rw [permutationAugmentationSequence_def] at hS
  let := hS.mono_f
  let := hS.epi_g
  let : Module.Finite k[Equiv.Perm (Fin 3)]
      (Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  let : Module.Finite k[Equiv.Perm (Fin 3)]
      (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toRepresentation.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  have h := ExactK0.of_conflation_fullSubcategory
    (isExtensionClosed_finiteModules k[Equiv.Perm (Fin 3)])
    ((ExactStructure.abelian_conflation _).2 (hS.map Rep.toModuleMonoidAlgebra))
    (by exact (ModuleCat.isFG_iff (ModuleCat.of k[Equiv.Perm (Fin 3)]
      (augmentationSubrepresentation k (Equiv.Perm (Fin 3))
        (Fin 3)).toRepresentation.asModule)).2 inferInstance)
    (by exact (ModuleCat.isFG_iff (ModuleCat.of k[Equiv.Perm (Fin 3)]
      (Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule)).2 inferInstance)
  have hc : permK0 k (Equiv.Perm (Fin 3)) (Fin 3) =
      fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
        (ExactK0.of (FDRep.of (standardRepresentation k (Fin 3)))) + 1 := by
    rw [permK0_def, fdRepK0RingEquiv_of, FDRep.of_ρ', exactK0_one_eq_of_trivial]
    rw [← toRepresentation_augmentationSubrepresentation]
    apply (finiteModulesExactK0Equiv k[Equiv.Perm (Fin 3)]).injective
    simp only [map_add, finiteModulesExactK0Equiv_of]
    simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
      Rep.toModuleMonoidAlgebra, Rep.of_ρ, Rep.trivial] using h
  rw [hc, fdRepK0RingEquiv_of_standard_perm_fin_three_char_three]
  simp only [two_nsmul]
  abel

/-- Inducing the trivial line from any point stabilizer of S₃ gives two trivial factors
and one sign factor in characteristic three. -/
theorem indK0_one_stabilizer_perm_fin_three_char_three (a : Fin 3) :
    indK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a) 1 =
      2 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) +
        fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
          (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)))) := by
  rw [indK0_one, permK0_congr k (quotientStabilizerEquiv (Equiv.Perm (Fin 3)) a)
    (quotientStabilizerEquiv_smul (Equiv.Perm (Fin 3)) a)]
  exact permK0_fin_three_char_three k

end TauCeti
