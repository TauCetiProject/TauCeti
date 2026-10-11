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
  let ρ₁ := Representation.trivial k (Equiv.Perm (Fin 3)) k
  let ρ₂ := standardRepresentation k (Fin 3)
  let ρ₃ := Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))
  let : Module.Finite k[Equiv.Perm (Fin 3)] ρ₂.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  let : Module.Finite k[Equiv.Perm (Fin 3)] ρ₁.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  let : Module.Finite k[Equiv.Perm (Fin 3)] ρ₃.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  rw [FDRep.ofLinearCharacter_def, fdRepK0RingEquiv_of, fdRepK0RingEquiv_of,
    exactK0_one_eq_of_trivial]
  simp only [FDRep.of_ρ']
  -- These group-algebra maps preserve the underlying functions of the representation maps.
  let f : ρ₁.asModule →ₗ[k[Equiv.Perm (Fin 3)]] ρ₂.asModule := by
    exact _root_.Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (standardThreeTrivialInclusion k)
  let g : ρ₂.asModule →ₗ[k[Equiv.Perm (Fin 3)]] ρ₃.asModule := by
    exact _root_.Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (standardThreeSignQuotient k)
  have hfg : Function.Exact f g := by
    simpa only [f, g, Function.Exact, Set.mem_range,
      _root_.Representation.IntertwiningMap.equivLinearMapAsModule_apply]
      using! exact_standardThreeTrivialInclusion_standardThreeSignQuotient k
  have h := exactK0_of_eq_range_add_range k[Equiv.Perm (Fin 3)]
    (M := ρ₁.asModule) (N := ρ₂.asModule) (P := ρ₃.asModule) (f := f) (g := g) hfg
  rw [exactK0_of_range_of_injective k[Equiv.Perm (Fin 3)]
      (M := ρ₁.asModule) (N := ρ₂.asModule) (f := f) (by
      simpa only [f, Function.Injective,
        _root_.Representation.IntertwiningMap.equivLinearMapAsModule_apply]
        using! standardThreeTrivialInclusion_injective k),
    exactK0_of_range_of_surjective k[Equiv.Perm (Fin 3)]
      (M := ρ₂.asModule) (N := ρ₃.asModule) (f := g) (by
      simpa only [g, Function.Surjective,
        _root_.Representation.IntertwiningMap.equivLinearMapAsModule_apply]
        using! standardThreeSignQuotient_surjective k)] at h
  exact h

/-- The three-point permutation module of S₃ has two trivial factors and one sign factor. -/
theorem permK0_fin_three_char_three :
    permK0 k (Equiv.Perm (Fin 3)) (Fin 3) =
      2 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) +
        fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
          (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)))) := by
  let ρ₁ := (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toRepresentation
  let ρ₂ := Representation.ofMulAction k (Equiv.Perm (Fin 3)) (Fin 3)
  let ρ₃ := Representation.trivial k (Equiv.Perm (Fin 3)) k
  have hS := permutationAugmentationSequence_shortExact k (Equiv.Perm (Fin 3)) (Fin 3)
  rw [permutationAugmentationSequence_def] at hS
  let : Module.Finite k[Equiv.Perm (Fin 3)] ρ₃.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  let : Module.Finite k[Equiv.Perm (Fin 3)] ρ₁.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  let : Module.Finite k[Equiv.Perm (Fin 3)] ρ₂.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _
  -- These group-algebra maps preserve the underlying functions of the representation maps.
  let f : ρ₁.asModule →ₗ[k[Equiv.Perm (Fin 3)]] ρ₂.asModule := by
    exact _root_.Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).subtype
  let g : ρ₂.asModule →ₗ[k[Equiv.Perm (Fin 3)]] ρ₃.asModule := by
    exact _root_.Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (permutationAugmentation k (Equiv.Perm (Fin 3)) (Fin 3)).hom
  have hc : permK0 k (Equiv.Perm (Fin 3)) (Fin 3) =
      fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
        (ExactK0.of (FDRep.of (standardRepresentation k (Fin 3)))) + 1 := by
    rw [permK0_def, fdRepK0RingEquiv_of, FDRep.of_ρ', exactK0_one_eq_of_trivial]
    rw [← toRepresentation_augmentationSubrepresentation]
    have hfg : Function.Exact f g := by
      simpa only [f, g, Function.Exact, Set.mem_range,
        _root_.Representation.IntertwiningMap.equivLinearMapAsModule_apply, Rep.ofHom_hom]
        using! (Rep.exact_iff_function_exact _).1 hS.exact
    have h := exactK0_of_eq_range_add_range k[Equiv.Perm (Fin 3)]
      (M := ρ₁.asModule) (N := ρ₂.asModule) (P := ρ₃.asModule) (f := f) (g := g) hfg
    rw [exactK0_of_range_of_injective k[Equiv.Perm (Fin 3)]
        (M := ρ₁.asModule)
        (N := ρ₂.asModule) (f := f) (by
        simpa only [f, Function.Injective,
          _root_.Representation.IntertwiningMap.equivLinearMapAsModule_apply, Rep.ofHom_hom]
          using! (Rep.mono_iff_injective _).1 hS.mono_f),
      exactK0_of_range_of_surjective k[Equiv.Perm (Fin 3)]
        (M := ρ₂.asModule)
        (N := ρ₃.asModule) (f := g) (by
        simpa only [g, Function.Surjective,
          _root_.Representation.IntertwiningMap.equivLinearMapAsModule_apply, Rep.ofHom_hom]
          using! (Rep.epi_iff_surjective _).1 hS.epi_g)] at h
    exact h
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
