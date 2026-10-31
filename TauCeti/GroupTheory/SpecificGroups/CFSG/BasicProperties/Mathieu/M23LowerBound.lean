/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.Permutation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.Permutation

/-!
# A lower bound for the M23 permutation image

Short words in the two presented generators distinguish 23, 22, 21, 20, 16, and 3
successive point images. Each word fixes the earlier base points, and its current
point image is checked by kernel reduction. Recovering the six indices in order
proves that the products have distinct permutation images, giving 10200960 elements.

Letters 0 and 1 are the generators; 2 and 3 are their respective inverses. Products
act from right to left. No finiteness or faithfulness of the presentation is assumed.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- The index of the first generator in the transcribed presentation. -/
private def generatorA : Fin m23Presentation.generatorCount :=
  ⟨0, by simp [GroupPresentation.generatorCount]⟩

/-- The index of the second generator in the transcribed presentation. -/
private def generatorB : Fin m23Presentation.generatorCount :=
  ⟨1, by simp [GroupPresentation.generatorCount]⟩

/-- The two presented generators and their inverses, in that order. -/
private def letter (i : Fin 4) : m23Presentation.Group :=
  if i.val = 0 then PresentedGroup.of generatorA
  else if i.val = 1 then PresentedGroup.of generatorB
  else if i.val = 2 then (PresentedGroup.of generatorA)⁻¹
  else (PresentedGroup.of generatorB)⁻¹

/-- The permutation values of the four word letters. -/
private def letterImage (i : Fin 4) : Equiv.Perm (Fin 23) :=
  if i.val = 0 then m23GeneratorImages generatorA
  else if i.val = 1 then m23GeneratorImages generatorB
  else if i.val = 2 then (m23GeneratorImages generatorA)⁻¹
  else (m23GeneratorImages generatorB)⁻¹

/-- Evaluate a transversal word in the exact presented group. -/
private def evalWord (w : List (Fin 4)) : m23Presentation.Group :=
  (w.map letter).prod

private theorem map_evalWord (w : List (Fin 4)) :
    m23PermutationHom (evalWord w) = (w.map letterImage).prod := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, letter, letterImage]
  split_ifs <;> simp only [m23PermutationHom_of, map_inv]

/-- Words fixing earlier base points and distinguishing point 0. -/
private def words0 : Vector (List (Fin 4)) 23 :=
  #v[
    [],
    [3, 3, 2, 3, 3],
    [2, 1],
    [3, 2, 3, 3],
    [3, 3, 2],
    [2],
    [3, 3],
    [1],
    [2, 3, 3, 2, 1, 2, 3, 3],
    [3, 3, 2, 1, 2, 3, 3],
    [3, 2, 3, 2, 3, 3],
    [3, 2],
    [1, 2],
    [1, 2, 1, 2, 3, 3],
    [2, 3, 3],
    [3],
    [2, 3, 2, 3, 2],
    [2, 3, 2],
    [2, 1, 2, 3, 3],
    [3, 2, 3, 2],
    [2, 3, 2, 3, 3],
    [1, 2, 3, 3],
    [3, 2, 1, 2, 3, 3]]

/-- The presented-group values of the level-0 words. -/
private def transversal0 (i : Fin 23) : m23Presentation.Group :=
  evalWord words0[i]

private theorem transversal0_apply_0 (i : Fin 23) :
    m23PermutationHom (transversal0 i) 0 = i := by
  have h : ∀ j : Fin 23,
      (words0[j].map letterImage).prod 0 = j := by
    decide +kernel
  simpa only [transversal0, map_evalWord] using h i

/-- Words fixing earlier base points and distinguishing point 1. -/
private def words1 : Vector (List (Fin 4)) 22 :=
  #v[
    [],
    [0, 3, 2, 1, 2, 3, 0, 3, 2, 1],
    [3, 0, 1, 2, 1, 0, 3, 2, 1, 2, 3, 0, 3, 2, 1],
    [0, 1, 1, 2, 3, 3, 2, 1, 2, 3, 0, 3, 2, 1, 2],
    [0, 1, 1, 2, 3, 3, 2],
    [1, 2, 3, 0, 3, 2, 1, 2, 3, 0, 3, 2, 1],
    [3, 0, 1, 2, 1, 0, 3, 2, 1, 2],
    [0, 1, 1, 2, 3, 3, 2, 3, 0, 3, 2, 1],
    [0, 3, 2, 1, 2, 1, 2, 3],
    [0, 3, 2, 1, 2],
    [3, 0, 3, 2, 1, 0, 3, 2, 1, 2, 3, 0, 3, 2, 1],
    [3, 0, 1, 2, 1, 0, 1, 1, 2, 3, 3, 2],
    [1, 2, 3],
    [1, 2, 3, 0, 3, 2, 1, 2],
    [3, 0, 3, 2, 1, 0, 1, 1, 2, 3, 3, 2],
    [1, 1, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3, 3],
    [1, 2, 1, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3, 3],
    [3, 0, 1, 2, 1, 1, 2, 3, 0, 3, 2, 1, 2],
    [1, 2, 3, 0, 1, 1, 2, 3, 3, 2],
    [3, 0, 3, 2, 1],
    [3, 0, 3, 2, 1, 0, 3, 2, 1, 2],
    [0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2]]

/-- The presented-group values of the level-1 words. -/
private def transversal1 (i : Fin 22) : m23Presentation.Group :=
  evalWord words1[i]

private theorem transversal1_apply_0 (i : Fin 22) :
    m23PermutationHom (transversal1 i) 0 = 0 := by
  have h : ∀ j : Fin 22,
      (words1[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

private theorem transversal1_apply_1 (i : Fin 22) :
    m23PermutationHom (transversal1 i) 1 = Fin.natAdd 1 i := by
  have h : ∀ j : Fin 22,
      (words1[j].map letterImage).prod 1 = Fin.natAdd 1 j := by
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

/-- Words fixing earlier base points and distinguishing point 2. -/
private def words2 : Vector (List (Fin 4)) 21 :=
  #v[
    [],
    [1, 0, 3, 3, 0, 3, 2, 1, 1, 2, 3],
    [0, 1, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 3, 2, 3, 2, 3, 2],
    [3, 0, 1, 2, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 0, 3, 3, 2, 1],
    [3, 0, 3, 3, 2, 1],
    [3, 0, 3, 3, 2, 1, 1, 0, 3, 0, 3, 0, 1, 1, 0, 3, 3, 2, 3, 2],
    [0, 3, 0, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2],
    [0, 1, 0, 1, 0, 1, 2, 3, 3, 0, 3, 2, 3, 2, 3, 2, 3, 0, 3, 3, 2, 1],
    [3, 0, 3, 3, 2, 1, 0, 3, 0, 1, 1, 0, 3, 3, 2, 3, 2, 1, 2, 3],
    [1, 0, 3, 3, 0, 1, 2, 1, 1, 2, 3],
    [3, 0, 3, 3, 2, 1, 1, 0, 1, 0, 3, 0, 1, 2, 3, 2, 1, 2, 3, 3],
    [0, 1, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 3, 2, 3, 0, 3, 2, 1],
    [1, 1, 0, 3, 0, 1, 1, 0, 1, 2, 3, 3, 2, 1, 2, 3, 3],
    [1, 0, 1, 0, 3, 0, 1, 2, 3, 2, 1, 2, 3, 3],
    [1, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3, 3, 0, 3, 3, 2, 1],
    [1, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 3],
    [1, 1, 0, 3, 0, 1, 1, 0, 3, 2, 3, 3, 2, 1, 2, 3, 3],
    [3, 0, 1, 2, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 3, 2],
    [0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3],
    [1, 0, 3, 0, 3, 0, 1, 1, 0, 3, 3, 2, 3, 2],
    [0, 3, 0, 1, 1, 0, 3, 3, 2, 3, 2, 1, 2, 3]]

/-- The presented-group values of the level-2 words. -/
private def transversal2 (i : Fin 21) : m23Presentation.Group :=
  evalWord words2[i]

private theorem transversal2_apply_0 (i : Fin 21) :
    m23PermutationHom (transversal2 i) 0 = 0 := by
  have h : ∀ j : Fin 21,
      (words2[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_1 (i : Fin 21) :
    m23PermutationHom (transversal2 i) 1 = 1 := by
  have h : ∀ j : Fin 21,
      (words2[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_2 (i : Fin 21) :
    m23PermutationHom (transversal2 i) 2 = Fin.natAdd 2 i := by
  have h : ∀ j : Fin 21,
      (words2[j].map letterImage).prod 2 = Fin.natAdd 2 j := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

/-- Words fixing earlier base points and distinguishing point 3. -/
private def words3 : Vector (List (Fin 4)) 20 :=
  #v[
    [],
    [3, 0, 1, 1, 2, 1, 0, 3, 0, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3, 0, 3, 3, 2, 1],
    [1, 1, 0, 3, 0, 1, 0, 3, 2, 1, 2, 3, 3, 0, 1, 0, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2],
    [3, 0, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 0, 3, 3, 2, 1, 0, 3, 2, 1, 2],
    [1, 0, 3, 0, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 2, 1, 2, 3],
    [1, 0, 1, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3],
    [3, 0, 1, 2, 1, 0, 1, 1, 0, 3, 3, 3, 2, 1, 1, 1, 2, 3, 3, 2, 3, 0, 3, 2, 1],
    [1, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 3, 0, 1, 1, 2, 3, 3, 2, 1, 2, 3],
    [3, 0, 1, 2, 1, 1, 2, 3, 3, 0, 3, 2, 1],
    [3, 0, 1, 2, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2],
    [1, 1, 0, 1, 0, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3, 0, 1, 0, 3, 3, 2, 3, 2],
    [0, 1, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2],
    [0, 1, 0, 1, 1, 2, 3, 2, 1, 1, 0, 1, 0, 1, 2, 3, 3, 3, 2, 3, 2, 3, 3],
    [0, 1, 0, 1, 0, 1, 2, 3, 3, 0, 3, 2, 3, 2, 3, 2, 3, 0, 1, 2, 1, 1, 2, 3, 3, 0, 3, 2, 1],
    [0, 1, 1, 0, 3, 3, 2, 3, 0, 1, 2, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 0, 3, 2, 1],
    [1, 0, 3, 0, 1, 1, 2, 3, 3, 2, 1, 2, 3],
    [3, 0, 1, 2, 1, 1, 2, 3, 3, 0, 3, 2, 1, 1, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3],
    [1, 0, 3, 0, 1, 1, 2, 3, 3, 2, 1, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3],
    [0, 1, 1, 0, 3, 3, 2, 3, 0, 3, 3, 2, 1, 1, 2, 3, 0, 1, 1, 2, 3, 3, 2],
    [1, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3]]

/-- The presented-group values of the level-3 words. -/
private def transversal3 (i : Fin 20) : m23Presentation.Group :=
  evalWord words3[i]

private theorem transversal3_apply_0 (i : Fin 20) :
    m23PermutationHom (transversal3 i) 0 = 0 := by
  have h : ∀ j : Fin 20,
      (words3[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_1 (i : Fin 20) :
    m23PermutationHom (transversal3 i) 1 = 1 := by
  have h : ∀ j : Fin 20,
      (words3[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_2 (i : Fin 20) :
    m23PermutationHom (transversal3 i) 2 = 2 := by
  have h : ∀ j : Fin 20,
      (words3[j].map letterImage).prod 2 = 2 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_3 (i : Fin 20) :
    m23PermutationHom (transversal3 i) 3 = Fin.natAdd 3 i := by
  have h : ∀ j : Fin 20,
      (words3[j].map letterImage).prod 3 = Fin.natAdd 3 j := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

/-- Distinct images of base point 13 at level 4. -/
private def targets4 : Vector (Fin 23) 16 :=
  #v[13, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20]

private theorem targets4_injective :
    Function.Injective (fun i : Fin 16 ↦ targets4[i]) := by
  decide +kernel

/-- Words fixing earlier base points and distinguishing point 13. -/
private def words4 : Vector (List (Fin 4)) 16 :=
  #v[
    [],
    [1, 1, 0, 3, 0, 1, 1, 0, 3, 2, 3, 3, 2, 1, 2, 3, 0, 3, 3, 0, 1, 2, 1, 1, 1, 0, 3, 0, 1, 2, 3,
      2, 1, 2, 3, 3],
    [1, 1, 0, 3, 0, 1, 0, 3, 2, 1, 1, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 3, 3, 3, 0, 1, 2, 1,
      1, 2, 3, 3, 0, 3, 2, 1],
    [1, 1, 0, 3, 0, 1, 0, 3, 2, 1, 2, 3, 3, 3, 0, 3, 2, 1, 1, 2, 1, 0, 3, 0, 1, 1, 0, 1, 2, 3, 3,
      2, 1, 2, 3, 3],
    [3, 0, 1, 2, 1, 0, 3, 0, 1, 2, 3, 0, 3, 3, 2, 1, 1, 2, 3, 0, 3, 2, 1, 2, 3, 0, 3, 2, 1],
    [1, 0, 3, 0, 1, 0, 1, 1, 2, 3, 3, 2, 1, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 3, 0, 3, 2, 1, 2, 1,
      2, 3],
    [1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 3, 0, 3, 2, 1, 2, 1, 2, 3, 0, 3, 0, 1, 1, 0, 3, 3, 2, 3, 2, 1,
      2, 3],
    [1, 0, 3, 0, 1, 1, 0, 3, 3, 2, 1, 1, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3, 3, 0, 1, 1, 2, 3, 3, 2, 1,
      2, 3],
    [1, 1, 0, 3, 0, 1, 1, 0, 1, 2, 3, 3, 2, 1, 2, 3, 0, 1, 0, 3, 0, 1, 2, 1, 0, 3, 2, 3, 3, 2, 1,
      2, 3, 3],
    [3, 0, 1, 2, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 0, 1, 2, 1, 1, 2, 3, 3, 0, 3, 2, 1],
    [1, 0, 3, 3, 0, 1, 2, 1, 0, 3, 0, 1, 2, 1, 2, 3, 0, 3, 2, 1, 2, 3, 0, 3, 2, 1, 1, 2, 3],
    [1, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 3, 3, 0, 3, 2, 1, 0, 3, 0, 1, 2, 1, 1, 0, 1, 0, 1, 2, 3,
      2, 3, 2, 3, 3],
    [1, 0, 3, 0, 1, 1, 0, 3, 3, 2, 1, 2, 3, 0, 3, 0, 1, 2, 1, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 3,
      0, 1, 1, 2, 3, 3, 3, 2, 1, 2],
    [0, 1, 1, 0, 3, 3, 2, 1, 0, 3, 3, 0, 1, 2, 1, 0, 3, 2, 1, 2, 3, 0, 3, 2, 1, 1, 2, 3, 0, 1, 1,
      2, 3, 3, 2],
    [1, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 3, 0, 3, 2, 1, 2, 3, 0, 1, 2, 1, 1, 1, 0, 1, 0, 3, 3, 2,
      3, 2, 3, 2, 3],
    [0, 1, 1, 0, 3, 3, 2, 3, 0, 3, 2, 1, 0, 3, 2, 1, 2, 3, 0, 1, 2, 1, 0, 1, 1, 2, 3, 3, 2]]

/-- The presented-group values of the level-4 words. -/
private def transversal4 (i : Fin 16) : m23Presentation.Group :=
  evalWord words4[i]

private theorem transversal4_apply_0 (i : Fin 16) :
    m23PermutationHom (transversal4 i) 0 = 0 := by
  have h : ∀ j : Fin 16,
      (words4[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_1 (i : Fin 16) :
    m23PermutationHom (transversal4 i) 1 = 1 := by
  have h : ∀ j : Fin 16,
      (words4[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_2 (i : Fin 16) :
    m23PermutationHom (transversal4 i) 2 = 2 := by
  have h : ∀ j : Fin 16,
      (words4[j].map letterImage).prod 2 = 2 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_3 (i : Fin 16) :
    m23PermutationHom (transversal4 i) 3 = 3 := by
  have h : ∀ j : Fin 16,
      (words4[j].map letterImage).prod 3 = 3 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_13 (i : Fin 16) :
    m23PermutationHom (transversal4 i) 13 = targets4[i] := by
  have h : ∀ j : Fin 16,
      (words4[j].map letterImage).prod 13 = targets4[j] := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

/-- Distinct images of base point 4 at level 5. -/
private def targets5 : Vector (Fin 23) 3 :=
  #v[4, 21, 22]

private theorem targets5_injective :
    Function.Injective (fun i : Fin 3 ↦ targets5[i]) := by
  decide +kernel

/-- Words fixing earlier base points and distinguishing point 4. -/
private def words5 : Vector (List (Fin 4)) 3 :=
  #v[
    [],
    [3, 0, 1, 2, 1, 0, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0, 1, 0, 1, 2, 3, 3, 3, 2, 3, 2, 1, 1, 0,
      3, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3],
    [1, 0, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 3, 3, 0, 1, 0, 1, 1, 1, 0, 3, 2, 3, 2, 3, 2, 3, 0, 1, 2,
      1, 0, 3, 2, 1, 2, 3, 0, 3, 2, 1]]

/-- The presented-group values of the level-5 words. -/
private def transversal5 (i : Fin 3) : m23Presentation.Group :=
  evalWord words5[i]

private theorem transversal5_apply_0 (i : Fin 3) :
    m23PermutationHom (transversal5 i) 0 = 0 := by
  have h : ∀ j : Fin 3,
      (words5[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i

private theorem transversal5_apply_1 (i : Fin 3) :
    m23PermutationHom (transversal5 i) 1 = 1 := by
  have h : ∀ j : Fin 3,
      (words5[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i

private theorem transversal5_apply_2 (i : Fin 3) :
    m23PermutationHom (transversal5 i) 2 = 2 := by
  have h : ∀ j : Fin 3,
      (words5[j].map letterImage).prod 2 = 2 := by
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i

private theorem transversal5_apply_3 (i : Fin 3) :
    m23PermutationHom (transversal5 i) 3 = 3 := by
  have h : ∀ j : Fin 3,
      (words5[j].map letterImage).prod 3 = 3 := by
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i

private theorem transversal5_apply_13 (i : Fin 3) :
    m23PermutationHom (transversal5 i) 13 = 13 := by
  have h : ∀ j : Fin 3,
      (words5[j].map letterImage).prod 13 = 13 := by
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i

private theorem transversal5_apply_4 (i : Fin 3) :
    m23PermutationHom (transversal5 i) 4 = targets5[i] := by
  have h : ∀ j : Fin 3,
      (words5[j].map letterImage).prod 4 = targets5[j] := by
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i

/-- Products of the six successive representative words. -/
private def transversalProduct (i : Fin 23 × Fin 22 × Fin 21 × Fin 20 × Fin 16 × Fin 3) :
    m23Presentation.Group :=
  transversal0 i.1 * (transversal1 i.2.1 * (transversal2 i.2.2.1 * (transversal3 i.2.2.2.1 *
    (transversal4 i.2.2.2.2.1 * (transversal5 i.2.2.2.2.2)))))

private theorem image_product_injective :
    Function.Injective (fun i ↦ m23PermutationHom (transversalProduct i)) := by
  rintro ⟨i₀, i₁, i₂, i₃, i₄, i₅⟩ ⟨j₀, j₁, j₂, j₃, j₄, j₅⟩ h
  change m23PermutationHom (transversal0 i₀ * (transversal1 i₁ * (transversal2 i₂ * (transversal3
    i₃ * (transversal4 i₄ * (transversal5 i₅)))))) =
    m23PermutationHom (transversal0 j₀ * (transversal1 j₁ * (transversal2 j₂ * (transversal3 j₃ *
      (transversal4 j₄ * (transversal5 j₅)))))) at h
  simp only [map_mul] at h
  have h₀ := congrArg (fun g : Equiv.Perm (Fin 23) ↦ g 0) h
  simp only [Equiv.Perm.mul_apply, transversal5_apply_0, transversal4_apply_0,
    transversal3_apply_0, transversal2_apply_0, transversal1_apply_0, transversal0_apply_0] at h₀
  subst j₀
  replace h := mul_left_cancel h
  have h₁ := congrArg (fun g : Equiv.Perm (Fin 23) ↦ g 1) h
  simp only [Equiv.Perm.mul_apply, transversal5_apply_1, transversal4_apply_1,
    transversal3_apply_1, transversal2_apply_1, transversal1_apply_1] at h₁
  have e₁ : i₁ = j₁ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₁))
  subst j₁
  replace h := mul_left_cancel h
  have h₂ := congrArg (fun g : Equiv.Perm (Fin 23) ↦ g 2) h
  simp only [Equiv.Perm.mul_apply, transversal5_apply_2, transversal4_apply_2,
    transversal3_apply_2, transversal2_apply_2] at h₂
  have e₂ : i₂ = j₂ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₂))
  subst j₂
  replace h := mul_left_cancel h
  have h₃ := congrArg (fun g : Equiv.Perm (Fin 23) ↦ g 3) h
  simp only [Equiv.Perm.mul_apply, transversal5_apply_3, transversal4_apply_3,
    transversal3_apply_3] at h₃
  have e₃ : i₃ = j₃ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₃))
  subst j₃
  replace h := mul_left_cancel h
  have h₄ := congrArg (fun g : Equiv.Perm (Fin 23) ↦ g 13) h
  simp only [Equiv.Perm.mul_apply, transversal5_apply_13, transversal4_apply_13] at h₄
  have e₄ : i₄ = j₄ := targets4_injective h₄
  subst j₄
  replace h := mul_left_cancel h
  have h₅ := congrArg (fun g : Equiv.Perm (Fin 23) ↦ g 4) h
  simp only [transversal5_apply_4] at h₅
  have e₅ : i₅ = j₅ := targets5_injective h₅
  subst j₅
  rfl

/-- The exact degree-23 permutation image contains at least 10200960 elements. -/
theorem m23PermutationHom_range_natCard_ge :
    10200960 ≤ Nat.card m23PermutationHom.range := by
  have h : Function.Injective
      (fun i ↦ m23PermutationHom.rangeRestrict (transversalProduct i)) := by
    intro i j hij
    apply image_product_injective
    exact congrArg Subtype.val hij
  have hcard := Nat.card_le_card_of_injective _ h
  simpa only [Nat.card_prod, Nat.card_fin] using hcard

end TauCeti.Sporadic.Mathieu
