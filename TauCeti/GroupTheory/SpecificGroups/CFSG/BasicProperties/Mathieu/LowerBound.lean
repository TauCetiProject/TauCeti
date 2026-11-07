/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.Permutation
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# A lower bound for the M11 presentation

Short words give transversals at four levels of the degree-11 permutation action.
Their products define an injection from a type of size `11 * 10 * 9 * 8 = 7920`
into the exact presented group. Only the 38 transversal words are checked.

The cardinal bound assumes finiteness of the presentation separately.
-/

public section

namespace TauCeti.Sporadic.Mathieu

private def generatorA : Fin m11Presentation.generatorCount :=
  ⟨0, by simp [GroupPresentation.generatorCount]⟩

private def generatorB : Fin m11Presentation.generatorCount :=
  ⟨1, by simp [GroupPresentation.generatorCount]⟩

private def letter (i : Fin 4) : m11Presentation.Group :=
  if i.val = 0 then PresentedGroup.of generatorA
  else if i.val = 1 then PresentedGroup.of generatorB
  else if i.val = 2 then (PresentedGroup.of generatorA)⁻¹
  else (PresentedGroup.of generatorB)⁻¹

private def letterImage (i : Fin 4) : Equiv.Perm (Fin 11) :=
  if i.val = 0 then m11GeneratorImages generatorA
  else if i.val = 1 then m11GeneratorImages generatorB
  else if i.val = 2 then (m11GeneratorImages generatorA)⁻¹
  else (m11GeneratorImages generatorB)⁻¹

private def evalWord (w : List (Fin 4)) : m11Presentation.Group :=
  (w.map letter).prod

private theorem map_evalWord (w : List (Fin 4)) :
    m11PermutationHom (evalWord w) = (w.map letterImage).prod := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, letter, letterImage]
  split_ifs <;> simp only [m11PermutationHom_of, map_inv]

private def words0 : Vector (List (Fin 4)) 11 :=
  #v[
    [],
    [1, 0],
    [1],
    [2, 1],
    [3],
    [0],
    [1, 0, 0],
    [0, 0],
    [0, 3],
    [3, 0],
    [1, 1]]

private def transversal0 (i : Fin 11) : m11Presentation.Group :=
  evalWord words0[i]

private theorem transversal0_apply_0 (i : Fin 11) :
    m11PermutationHom (transversal0 i) 0 = i := by
  have h : ∀ j : Fin 11, (words0[j].map letterImage).prod 0 = j := by
    decide +kernel
  simpa only [transversal0, map_evalWord] using h i

private def words1 : Vector (List (Fin 4)) 10 :=
  #v[
    [],
    [1, 1, 0, 3, 0],
    [2, 2, 2, 3],
    [2, 3, 3, 3],
    [0, 3, 3, 0, 0],
    [0, 3, 2, 2, 2],
    [0, 0, 0, 3, 0, 0],
    [0, 1],
    [1, 1, 1, 0],
    [3, 0, 0, 1, 1]]

private def transversal1 (i : Fin 10) : m11Presentation.Group :=
  evalWord words1[i]

private theorem transversal1_apply_0 (i : Fin 10) :
    m11PermutationHom (transversal1 i) 0 = 0 := by
  have h : ∀ j : Fin 10, (words1[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

private theorem transversal1_apply_1 (i : Fin 10) :
    m11PermutationHom (transversal1 i) 1 = Fin.natAdd 1 i := by
  have h : ∀ j : Fin 10, (words1[j].map letterImage).prod 1 = Fin.natAdd 1 j := by
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

private def words2 : Vector (List (Fin 4)) 9 :=
  #v[
    [],
    [1, 2, 1, 1, 0, 1, 0],
    [1, 0, 3, 2, 1, 1],
    [3, 2, 3, 2],
    [0, 0, 1, 2, 3, 0, 0],
    [0, 3, 2, 2, 1],
    [3, 3, 0, 0, 1, 0],
    [0, 1, 0, 1],
    [1, 0, 1, 2, 2, 2]]

private def transversal2 (i : Fin 9) : m11Presentation.Group :=
  evalWord words2[i]

private theorem transversal2_apply_0 (i : Fin 9) :
    m11PermutationHom (transversal2 i) 0 = 0 := by
  have h : ∀ j : Fin 9, (words2[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_1 (i : Fin 9) :
    m11PermutationHom (transversal2 i) 1 = 1 := by
  have h : ∀ j : Fin 9, (words2[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_2 (i : Fin 9) :
    m11PermutationHom (transversal2 i) 2 = Fin.natAdd 2 i := by
  have h : ∀ j : Fin 9, (words2[j].map letterImage).prod 2 = Fin.natAdd 2 j := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private def words3 : Vector (List (Fin 4)) 8 :=
  #v[
    [],
    [0, 0, 0, 0, 1, 0, 0],
    [0, 3, 3, 0, 3, 2, 1, 0, 0],
    [2, 2, 1, 2, 3, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 1, 2],
    [0, 1, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 1, 0, 0, 3, 0],
    [2, 2, 2, 3, 3, 2]]

private def transversal3 (i : Fin 8) : m11Presentation.Group :=
  evalWord words3[i]

private theorem transversal3_apply_0 (i : Fin 8) :
    m11PermutationHom (transversal3 i) 0 = 0 := by
  have h : ∀ j : Fin 8, (words3[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_1 (i : Fin 8) :
    m11PermutationHom (transversal3 i) 1 = 1 := by
  have h : ∀ j : Fin 8, (words3[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_2 (i : Fin 8) :
    m11PermutationHom (transversal3 i) 2 = 2 := by
  have h : ∀ j : Fin 8, (words3[j].map letterImage).prod 2 = 2 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_3 (i : Fin 8) :
    m11PermutationHom (transversal3 i) 3 = Fin.natAdd 3 i := by
  have h : ∀ j : Fin 8, (words3[j].map letterImage).prod 3 = Fin.natAdd 3 j := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

/-- Products of four transversal words in the exact M11 presentation. -/
def m11TransversalProduct (i : Fin 11 × Fin 10 × Fin 9 × Fin 8) :
    m11Presentation.Group :=
  transversal0 i.1 * (transversal1 i.2.1 * (transversal2 i.2.2.1 * transversal3 i.2.2.2))

/-- The four successive point images distinguish the permutation images of the products. -/
theorem m11PermutationHom_transversalProduct_injective :
    Function.Injective (fun i ↦ m11PermutationHom (m11TransversalProduct i)) := by
  rintro ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩ h
  change m11PermutationHom
    (transversal0 i₀ * (transversal1 i₁ * (transversal2 i₂ * transversal3 i₃))) =
    m11PermutationHom
      (transversal0 j₀ * (transversal1 j₁ * (transversal2 j₂ * transversal3 j₃))) at h
  simp only [map_mul] at h
  have h₀ := congrArg (fun g : Equiv.Perm (Fin 11) ↦ g 0) h
  simp only [Equiv.Perm.mul_apply, transversal3_apply_0, transversal2_apply_0,
    transversal1_apply_0, transversal0_apply_0] at h₀
  subst j₀
  replace h := mul_left_cancel h
  have h₁ := congrArg (fun g : Equiv.Perm (Fin 11) ↦ g 1) h
  simp only [Equiv.Perm.mul_apply, transversal3_apply_1, transversal2_apply_1,
    transversal1_apply_1] at h₁
  have e₁ : i₁ = j₁ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₁))
  subst j₁
  replace h := mul_left_cancel h
  have h₂ := congrArg (fun g : Equiv.Perm (Fin 11) ↦ g 2) h
  simp only [Equiv.Perm.mul_apply, transversal3_apply_2, transversal2_apply_2] at h₂
  have e₂ : i₂ = j₂ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₂))
  subst j₂
  replace h := mul_left_cancel h
  have h₃ := congrArg (fun g : Equiv.Perm (Fin 11) ↦ g 3) h
  simp only [transversal3_apply_3] at h₃
  have e₃ : i₃ = j₃ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₃))
  subst j₃
  rfl

/-- The transversal products give distinct elements of the exact M11 presentation. -/
theorem m11TransversalProduct_injective : Function.Injective m11TransversalProduct :=
  fun _ _ h ↦ m11PermutationHom_transversalProduct_injective (congrArg _ h)

/-- The concrete permutation image contains at least 7920 elements. -/
theorem m11PermutationHom_range_natCard_ge : 7920 ≤ Nat.card m11PermutationHom.range := by
  have h : Function.Injective
      (fun i ↦ m11PermutationHom.rangeRestrict (m11TransversalProduct i)) := by
    intro i j hij
    apply m11PermutationHom_transversalProduct_injective
    exact congrArg Subtype.val hij
  have hcard := Nat.card_le_card_of_injective _ h
  simpa only [Nat.card_prod, Nat.card_fin] using hcard

/-- The exact M11 presentation has order at least 7920 whenever it is finite. -/
theorem m11_natCard_ge [Finite m11Presentation.Group] :
    7920 ≤ Nat.card m11Presentation.Group := by
  have h := Nat.card_le_card_of_injective m11TransversalProduct m11TransversalProduct_injective
  simpa only [Nat.card_prod, Nat.card_fin] using h

end TauCeti.Sporadic.Mathieu
