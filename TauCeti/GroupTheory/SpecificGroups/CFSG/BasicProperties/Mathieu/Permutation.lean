/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.List
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyThree

/-!
# Permutation representations of the five Mathieu presentations

The generator images recorded with the sporadic presentations satisfy the exact transcribed
relations of `M₁₁`, `M₁₂`, `M₂₂`, `M₂₃`, and `M₂₄`. This file constructs homomorphisms
from the presented groups. Their images contain two noncommuting permutations, so each presented
group is nontrivial and nonabelian.

The documented external calculations use right permutation actions. We invert their cycles to
obtain homomorphisms for Mathlib's multiplication, which composes functions from right to left.
The kernel checks every relator after this conversion.

These results supply the finite-model relation checks in milestone P1 of
`TauCetiRoadmap/CFSGBasicProperties/README.md`. They do not prove that the homomorphisms are
injective, identify their image orders, or establish finiteness or simplicity of the presentations.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- Images of the two generators in the documented degree-11 permutation action. -/
@[expose]
def m11GeneratorImages (i : Fin m11Presentation.generatorCount) :
    Equiv.Perm (Fin 11) :=
  if i.val = 0 then
    ([0, 2, 3, 10, 6, 1, 9, 8, 4, 7, 5] : List (Fin 11)).formPerm⁻¹
  else
    ([0, 4, 1, 5, 9, 8, 3, 6, 7, 10, 2] : List (Fin 11)).formPerm⁻¹

/-- Every defining relator of the exact `M11` presentation evaluates to the identity. -/
theorem m11_relators :
    ∀ r ∈ m11Presentation.relatorSet, FreeGroup.lift m11GeneratorImages r = 1 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := (GroupPresentation.mem_relatorSet_iff _ _).mp hr
  rw [m11Presentation_transcribed] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;>
    simp only [Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
      Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow,
      FreeGroup.lift_apply_of, m11GeneratorImages] <;> decide +kernel

/-- The permutation representation determined by the checked generator images. -/
def m11PermutationHom : m11Presentation.Group →* Equiv.Perm (Fin 11) :=
  PresentedGroup.toGroup m11_relators

@[simp]
theorem m11PermutationHom_of (i : Fin m11Presentation.generatorCount) :
    m11PermutationHom (PresentedGroup.of i) = m11GeneratorImages i :=
  PresentedGroup.toGroup.of m11_relators

/-- The presentation is nonabelian, as witnessed by two noncommuting generator images. -/
theorem m11_not_isMulCommutative : ¬ IsMulCommutative m11Presentation.Group := by
  intro h
  let a : Fin m11Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  let b : Fin m11Presentation.generatorCount := ⟨1, by simp [GroupPresentation.generatorCount]⟩
  have hc := congrArg m11PermutationHom
    (isMulCommutative_iff.mp h (PresentedGroup.of a) (PresentedGroup.of b))
  simp only [map_mul, m11PermutationHom_of] at hc
  have hn : m11GeneratorImages a * m11GeneratorImages b ≠
      m11GeneratorImages b * m11GeneratorImages a := by
    unfold m11GeneratorImages a b
    decide +kernel
  exact hn hc

/-- The first generator acts nontrivially in the permutation representation. -/
theorem m11_nontrivial : Nontrivial m11Presentation.Group := by
  let a : Fin m11Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  refine ⟨⟨PresentedGroup.of a, 1, ?_⟩⟩
  intro h
  have he := congrArg m11PermutationHom h
  simp only [m11PermutationHom_of, map_one] at he
  have hn : m11GeneratorImages a ≠ 1 := by
    unfold m11GeneratorImages a
    decide +kernel
  exact hn he

/-- Images of the two generators in the documented degree-12 permutation action. -/
def m12GeneratorImages (i : Fin m12Presentation.generatorCount) :
    Equiv.Perm (Fin 12) :=
  if i.val = 0 then
    ([0, 1, 2, 7, 4] : List (Fin 12)).formPerm⁻¹ *
      ([3, 8, 10, 5, 6] : List (Fin 12)).formPerm⁻¹
  else
    ([0, 8, 5] : List (Fin 12)).formPerm⁻¹ *
      ([1, 6] : List (Fin 12)).formPerm⁻¹ *
      ([2, 10, 7, 9, 11, 4] : List (Fin 12)).formPerm⁻¹

/-- Every defining relator of the exact `M12` presentation evaluates to the identity. -/
theorem m12_relators :
    ∀ r ∈ m12Presentation.relatorSet, FreeGroup.lift m12GeneratorImages r = 1 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := (GroupPresentation.mem_relatorSet_iff _ _).mp hr
  rw [m12Presentation_transcribed] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;>
    simp only [Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
      Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow,
      FreeGroup.lift_apply_of, m12GeneratorImages] <;> decide +kernel

/-- The permutation representation determined by the checked generator images. -/
def m12PermutationHom : m12Presentation.Group →* Equiv.Perm (Fin 12) :=
  PresentedGroup.toGroup m12_relators

@[simp]
theorem m12PermutationHom_of (i : Fin m12Presentation.generatorCount) :
    m12PermutationHom (PresentedGroup.of i) = m12GeneratorImages i :=
  PresentedGroup.toGroup.of m12_relators

/-- The presentation is nonabelian, as witnessed by two noncommuting generator images. -/
theorem m12_not_isMulCommutative : ¬ IsMulCommutative m12Presentation.Group := by
  intro h
  let a : Fin m12Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  let b : Fin m12Presentation.generatorCount := ⟨1, by simp [GroupPresentation.generatorCount]⟩
  have hc := congrArg m12PermutationHom
    (isMulCommutative_iff.mp h (PresentedGroup.of a) (PresentedGroup.of b))
  simp only [map_mul, m12PermutationHom_of] at hc
  have hn : m12GeneratorImages a * m12GeneratorImages b ≠
      m12GeneratorImages b * m12GeneratorImages a := by
    unfold m12GeneratorImages a b
    decide +kernel
  exact hn hc

/-- The first generator acts nontrivially in the permutation representation. -/
theorem m12_nontrivial : Nontrivial m12Presentation.Group := by
  let a : Fin m12Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  refine ⟨⟨PresentedGroup.of a, 1, ?_⟩⟩
  intro h
  have he := congrArg m12PermutationHom h
  simp only [m12PermutationHom_of, map_one] at he
  have hn : m12GeneratorImages a ≠ 1 := by
    unfold m12GeneratorImages a
    decide +kernel
  exact hn he

/-- Images of the two generators in the documented degree-22 permutation action. -/
def m22GeneratorImages (i : Fin m22Presentation.generatorCount) :
    Equiv.Perm (Fin 22) :=
  if i.val = 0 then
    ([0, 12, 11, 21, 10] : List (Fin 22)).formPerm⁻¹ *
      ([1, 14, 20, 13, 19] : List (Fin 22)).formPerm⁻¹ *
      ([3, 16, 7, 18, 4] : List (Fin 22)).formPerm⁻¹ *
      ([5, 17, 15, 6, 8] : List (Fin 22)).formPerm⁻¹
  else
    ([0, 20, 10, 9, 14, 16, 15, 4, 13, 19, 1] : List (Fin 22)).formPerm⁻¹ *
      ([2, 5, 6, 8, 18, 17, 11, 21, 3, 12, 7] : List (Fin 22)).formPerm⁻¹

/-- Every defining relator of the exact `M22` presentation evaluates to the identity. -/
theorem m22_relators :
    ∀ r ∈ m22Presentation.relatorSet, FreeGroup.lift m22GeneratorImages r = 1 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := (GroupPresentation.mem_relatorSet_iff _ _).mp hr
  rw [m22Presentation_transcribed] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;>
    simp only [Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
      Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow,
      FreeGroup.lift_apply_of, m22GeneratorImages] <;> decide +kernel

/-- The permutation representation determined by the checked generator images. -/
def m22PermutationHom : m22Presentation.Group →* Equiv.Perm (Fin 22) :=
  PresentedGroup.toGroup m22_relators

@[simp]
theorem m22PermutationHom_of (i : Fin m22Presentation.generatorCount) :
    m22PermutationHom (PresentedGroup.of i) = m22GeneratorImages i :=
  PresentedGroup.toGroup.of m22_relators

/-- The presentation is nonabelian, as witnessed by two noncommuting generator images. -/
theorem m22_not_isMulCommutative : ¬ IsMulCommutative m22Presentation.Group := by
  intro h
  let a : Fin m22Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  let b : Fin m22Presentation.generatorCount := ⟨1, by simp [GroupPresentation.generatorCount]⟩
  have hc := congrArg m22PermutationHom
    (isMulCommutative_iff.mp h (PresentedGroup.of a) (PresentedGroup.of b))
  simp only [map_mul, m22PermutationHom_of] at hc
  have hn : m22GeneratorImages a * m22GeneratorImages b ≠
      m22GeneratorImages b * m22GeneratorImages a := by
    unfold m22GeneratorImages a b
    decide +kernel
  exact hn hc

/-- The first generator acts nontrivially in the permutation representation. -/
theorem m22_nontrivial : Nontrivial m22Presentation.Group := by
  let a : Fin m22Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  refine ⟨⟨PresentedGroup.of a, 1, ?_⟩⟩
  intro h
  have he := congrArg m22PermutationHom h
  simp only [m22PermutationHom_of, map_one] at he
  have hn : m22GeneratorImages a ≠ 1 := by
    unfold m22GeneratorImages a
    decide +kernel
  exact hn he

/-- Images of the two generators in the documented degree-23 permutation action. -/
@[expose]
def m23GeneratorImages (i : Fin m23Presentation.generatorCount) :
    Equiv.Perm (Fin 23) :=
  if i.val = 0 then
    ([0, 5] : List (Fin 23)).formPerm⁻¹ *
      ([2, 7] : List (Fin 23)).formPerm⁻¹ *
      ([3, 20] : List (Fin 23)).formPerm⁻¹ *
      ([6, 14] : List (Fin 23)).formPerm⁻¹ *
      ([8, 9] : List (Fin 23)).formPerm⁻¹ *
      ([11, 17] : List (Fin 23)).formPerm⁻¹ *
      ([16, 19] : List (Fin 23)).formPerm⁻¹ *
      ([18, 21] : List (Fin 23)).formPerm⁻¹
  else
    ([0, 15, 6, 7] : List (Fin 23)).formPerm⁻¹ *
      ([1, 21, 14, 3] : List (Fin 23)).formPerm⁻¹ *
      ([4, 12, 5, 11] : List (Fin 23)).formPerm⁻¹ *
      ([9, 13, 18, 22] : List (Fin 23)).formPerm⁻¹ *
      ([10, 20] : List (Fin 23)).formPerm⁻¹ *
      ([17, 19] : List (Fin 23)).formPerm⁻¹

/-- Every defining relator of the exact `M23` presentation evaluates to the identity. -/
theorem m23_relators :
    ∀ r ∈ m23Presentation.relatorSet, FreeGroup.lift m23GeneratorImages r = 1 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := (GroupPresentation.mem_relatorSet_iff _ _).mp hr
  rw [m23Presentation_transcribed] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
      Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, Relator.toFreeGroup_comm,
      commutatorElement_def, map_mul, map_inv, map_pow,
      FreeGroup.lift_apply_of, m23GeneratorImages] <;> decide +kernel

/-- The permutation representation determined by the checked generator images. -/
def m23PermutationHom : m23Presentation.Group →* Equiv.Perm (Fin 23) :=
  PresentedGroup.toGroup m23_relators

@[simp]
theorem m23PermutationHom_of (i : Fin m23Presentation.generatorCount) :
    m23PermutationHom (PresentedGroup.of i) = m23GeneratorImages i :=
  PresentedGroup.toGroup.of m23_relators

/-- The presentation is nonabelian, as witnessed by two noncommuting generator images. -/
theorem m23_not_isMulCommutative : ¬ IsMulCommutative m23Presentation.Group := by
  intro h
  let a : Fin m23Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  let b : Fin m23Presentation.generatorCount := ⟨1, by simp [GroupPresentation.generatorCount]⟩
  have hc := congrArg m23PermutationHom
    (isMulCommutative_iff.mp h (PresentedGroup.of a) (PresentedGroup.of b))
  simp only [map_mul, m23PermutationHom_of] at hc
  have hn : m23GeneratorImages a * m23GeneratorImages b ≠
      m23GeneratorImages b * m23GeneratorImages a := by
    unfold m23GeneratorImages a b
    decide +kernel
  exact hn hc

/-- The first generator acts nontrivially in the permutation representation. -/
theorem m23_nontrivial : Nontrivial m23Presentation.Group := by
  let a : Fin m23Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  refine ⟨⟨PresentedGroup.of a, 1, ?_⟩⟩
  intro h
  have he := congrArg m23PermutationHom h
  simp only [m23PermutationHom_of, map_one] at he
  have hn : m23GeneratorImages a ≠ 1 := by
    unfold m23GeneratorImages a
    decide +kernel
  exact hn he

/-- Images of the two generators in the documented degree-24 permutation action. -/
@[expose]
def m24GeneratorImages (i : Fin m24Presentation.generatorCount) :
    Equiv.Perm (Fin 24) :=
  if i.val = 0 then
    ([0, 11] : List (Fin 24)).formPerm⁻¹ *
      ([1, 4] : List (Fin 24)).formPerm⁻¹ *
      ([2, 5] : List (Fin 24)).formPerm⁻¹ *
      ([3, 10] : List (Fin 24)).formPerm⁻¹ *
      ([6, 14] : List (Fin 24)).formPerm⁻¹ *
      ([7, 17] : List (Fin 24)).formPerm⁻¹ *
      ([8, 23] : List (Fin 24)).formPerm⁻¹ *
      ([9, 20] : List (Fin 24)).formPerm⁻¹ *
      ([12, 15] : List (Fin 24)).formPerm⁻¹ *
      ([13, 19] : List (Fin 24)).formPerm⁻¹ *
      ([16, 18] : List (Fin 24)).formPerm⁻¹ *
      ([21, 22] : List (Fin 24)).formPerm⁻¹
  else
    ([1, 21, 11] : List (Fin 24)).formPerm⁻¹ *
      ([3, 20, 16] : List (Fin 24)).formPerm⁻¹ *
      ([5, 22, 10] : List (Fin 24)).formPerm⁻¹ *
      ([6, 19, 14] : List (Fin 24)).formPerm⁻¹ *
      ([9, 13, 15] : List (Fin 24)).formPerm⁻¹ *
      ([17, 18, 23] : List (Fin 24)).formPerm⁻¹

/-- Every defining relator of the exact `M24` presentation evaluates to the identity. -/
theorem m24_relators :
    ∀ r ∈ m24Presentation.relatorSet, FreeGroup.lift m24GeneratorImages r = 1 := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := (GroupPresentation.mem_relatorSet_iff _ _).mp hr
  rw [m24Presentation_transcribed] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
      Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, Relator.toFreeGroup_comm,
      commutatorElement_def, map_mul, map_inv, map_pow,
      FreeGroup.lift_apply_of, m24GeneratorImages] <;> decide +kernel

/-- The permutation representation determined by the checked generator images. -/
def m24PermutationHom : m24Presentation.Group →* Equiv.Perm (Fin 24) :=
  PresentedGroup.toGroup m24_relators

@[simp]
theorem m24PermutationHom_of (i : Fin m24Presentation.generatorCount) :
    m24PermutationHom (PresentedGroup.of i) = m24GeneratorImages i :=
  PresentedGroup.toGroup.of m24_relators

/-- The presentation is nonabelian, as witnessed by two noncommuting generator images. -/
theorem m24_not_isMulCommutative : ¬ IsMulCommutative m24Presentation.Group := by
  intro h
  let a : Fin m24Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  let b : Fin m24Presentation.generatorCount := ⟨1, by simp [GroupPresentation.generatorCount]⟩
  have hc := congrArg m24PermutationHom
    (isMulCommutative_iff.mp h (PresentedGroup.of a) (PresentedGroup.of b))
  simp only [map_mul, m24PermutationHom_of] at hc
  have hn : m24GeneratorImages a * m24GeneratorImages b ≠
      m24GeneratorImages b * m24GeneratorImages a := by
    unfold m24GeneratorImages a b
    decide +kernel
  exact hn hc

/-- The first generator acts nontrivially in the permutation representation. -/
theorem m24_nontrivial : Nontrivial m24Presentation.Group := by
  let a : Fin m24Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  refine ⟨⟨PresentedGroup.of a, 1, ?_⟩⟩
  intro h
  have he := congrArg m24PermutationHom h
  simp only [m24PermutationHom_of, map_one] at he
  have hn : m24GeneratorImages a ≠ 1 := by
    unfold m24GeneratorImages a
    decide +kernel
  exact hn he

end TauCeti.Sporadic.Mathieu
