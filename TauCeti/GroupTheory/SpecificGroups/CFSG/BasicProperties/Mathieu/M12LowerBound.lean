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
# A lower bound for the M12 presentation

Fifty short words give transversals at five levels of the degree-12 permutation action.
At level `s`, the words fix all smaller points and send `s` to each of the remaining
`12 - s` points. The kernel checks these point images directly. Successively recovering
the five indices proves that the products have distinct permutation images.

The permutation image therefore contains at least `12 * 11 * 10 * 9 * 8 = 95040` elements.
The cardinal bound for the exact presented group assumes its finiteness separately.
Letters `0, 1, 2, 3` denote the two generators followed by their respective inverses;
permutation products act from right to left. The private implementation import permits
kernel reduction of the existing generator images without changing their public interface.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- The index of the first generator in the transcribed presentation. -/
private def generatorA : Fin m12Presentation.generatorCount :=
  ⟨0, by simp [GroupPresentation.generatorCount]⟩

/-- The index of the second generator in the transcribed presentation. -/
private def generatorB : Fin m12Presentation.generatorCount :=
  ⟨1, by simp [GroupPresentation.generatorCount]⟩

/-- The two presented generators and their inverses, in that order. -/
private def letter (i : Fin 4) : m12Presentation.Group :=
  if i.val = 0 then PresentedGroup.of generatorA
  else if i.val = 1 then PresentedGroup.of generatorB
  else if i.val = 2 then (PresentedGroup.of generatorA)⁻¹
  else (PresentedGroup.of generatorB)⁻¹

/-- The permutation values of the four word letters. -/
private def letterImage (i : Fin 4) : Equiv.Perm (Fin 12) :=
  if i.val = 0 then m12GeneratorImages generatorA
  else if i.val = 1 then m12GeneratorImages generatorB
  else if i.val = 2 then (m12GeneratorImages generatorA)⁻¹
  else (m12GeneratorImages generatorB)⁻¹

/-- Evaluate a transversal word in the exact presented group. -/
private def evalWord (w : List (Fin 4)) : m12Presentation.Group :=
  (w.map letter).prod

private theorem map_evalWord (w : List (Fin 4)) :
    m12PermutationHom (evalWord w) = (w.map letterImage).prod := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, letter, letterImage]
  split_ifs <;> simp only [m12PermutationHom_of, map_inv]

/-- Words fixing points below 0, indexed by the image of 0 minus 0. -/
private def words0 : Vector (List (Fin 4)) 12 :=
  #v[
    [],
    [2],
    [2, 2],
    [0, 3],
    [0],
    [1],
    [1, 2],
    [0, 0],
    [3],
    [1, 1, 0],
    [0, 1],
    [1, 0]]

/-- The presented-group values of the level-0 transversal words. -/
private def transversal0 (i : Fin 12) : m12Presentation.Group :=
  evalWord words0[i]

private theorem transversal0_apply_0 (i : Fin 12) :
    m12PermutationHom (transversal0 i) 0 = i := by
  have h : ∀ j : Fin 12, (words0[j].map letterImage).prod 0 = j := by
    decide +kernel
  simpa only [transversal0, map_evalWord] using h i

/-- Words fixing points below 1, indexed by the image of 1 minus 1. -/
private def words1 : Vector (List (Fin 4)) 11 :=
  #v[
    [],
    [0, 3, 3, 2],
    [0, 3, 2, 1, 0, 3, 3, 2],
    [2, 3, 0, 1, 0],
    [2, 1, 2, 2],
    [1, 1, 1],
    [0, 0, 3, 0, 1, 1, 1],
    [0, 3, 2, 1, 1, 1, 1],
    [3, 0, 1, 2],
    [1, 1, 1, 0, 1, 1, 2],
    [0, 1, 1, 2]]

/-- The presented-group values of the level-1 transversal words. -/
private def transversal1 (i : Fin 11) : m12Presentation.Group :=
  evalWord words1[i]

private theorem transversal1_apply_0 (i : Fin 11) :
    m12PermutationHom (transversal1 i) 0 = 0 := by
  have h : ∀ j : Fin 11, (words1[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

private theorem transversal1_apply_1 (i : Fin 11) :
    m12PermutationHom (transversal1 i) 1 = Fin.natAdd 1 i := by
  have h : ∀ j : Fin 11, (words1[j].map letterImage).prod 1 = Fin.natAdd 1 j := by
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

/-- Words fixing points below 2, indexed by the image of 2 minus 2. -/
private def words2 : Vector (List (Fin 4)) 10 :=
  #v[
    [],
    [3, 3, 3, 0, 3, 2, 1],
    [2, 1, 2, 2, 1, 1, 1],
    [0, 1, 1, 0, 1, 0, 0, 1, 2],
    [0, 1, 0, 0, 3],
    [1, 2, 2, 3, 2],
    [0, 1, 1, 2, 2, 2, 3, 0, 1],
    [0, 3, 2, 1, 1, 1, 1, 0, 3, 3, 2],
    [3, 0, 1, 2, 1, 1, 1],
    [3, 3, 3, 0, 0, 3, 0]]

/-- The presented-group values of the level-2 transversal words. -/
private def transversal2 (i : Fin 10) : m12Presentation.Group :=
  evalWord words2[i]

private theorem transversal2_apply_0 (i : Fin 10) :
    m12PermutationHom (transversal2 i) 0 = 0 := by
  have h : ∀ j : Fin 10, (words2[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_1 (i : Fin 10) :
    m12PermutationHom (transversal2 i) 1 = 1 := by
  have h : ∀ j : Fin 10, (words2[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_2 (i : Fin 10) :
    m12PermutationHom (transversal2 i) 2 = Fin.natAdd 2 i := by
  have h : ∀ j : Fin 10, (words2[j].map letterImage).prod 2 = Fin.natAdd 2 j := by
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

/-- Words fixing points below 3, indexed by the image of 3 minus 3. -/
private def words3 : Vector (List (Fin 4)) 9 :=
  #v[
    [],
    [2, 3, 2, 3, 3, 0, 0],
    [2, 2, 1, 1, 0, 1, 0],
    [0, 1, 0, 0, 3, 2, 1, 2, 3, 2, 1],
    [3, 0, 1, 0, 1, 0, 1],
    [2, 2, 3, 0, 1, 2, 3, 0, 1, 0],
    [2, 1, 2, 3, 2, 3, 3, 0, 3, 2, 1],
    [3, 2, 3, 2, 3, 2, 1],
    [3, 3, 3, 0, 3, 2, 2, 3, 3, 0]]

/-- The presented-group values of the level-3 transversal words. -/
private def transversal3 (i : Fin 9) : m12Presentation.Group :=
  evalWord words3[i]

private theorem transversal3_apply_0 (i : Fin 9) :
    m12PermutationHom (transversal3 i) 0 = 0 := by
  have h : ∀ j : Fin 9, (words3[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_1 (i : Fin 9) :
    m12PermutationHom (transversal3 i) 1 = 1 := by
  have h : ∀ j : Fin 9, (words3[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_2 (i : Fin 9) :
    m12PermutationHom (transversal3 i) 2 = 2 := by
  have h : ∀ j : Fin 9, (words3[j].map letterImage).prod 2 = 2 := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_3 (i : Fin 9) :
    m12PermutationHom (transversal3 i) 3 = Fin.natAdd 3 i := by
  have h : ∀ j : Fin 9, (words3[j].map letterImage).prod 3 = Fin.natAdd 3 j := by
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

/-- Words fixing points below 4, indexed by the image of 4 minus 4. -/
private def words4 : Vector (List (Fin 4)) 8 :=
  #v[
    [],
    [3, 2, 3, 3, 0, 1, 2, 2, 3, 2],
    [3, 2, 2, 3, 0, 3, 3, 2, 3, 3, 3, 0, 0, 1, 0, 1],
    [2, 1, 2, 3, 2, 3, 3, 0, 0, 1, 0, 1],
    [3, 2, 3, 2, 2, 1, 1, 0, 1, 0, 3, 0],
    [2, 2, 1, 1, 1, 0, 3, 2, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 0, 3, 2, 1, 1, 0, 1],
    [2, 3, 2, 3, 3, 3, 0, 1, 2, 3, 3, 3, 0, 0]]

/-- The presented-group values of the level-4 transversal words. -/
private def transversal4 (i : Fin 8) : m12Presentation.Group :=
  evalWord words4[i]

private theorem transversal4_apply_0 (i : Fin 8) :
    m12PermutationHom (transversal4 i) 0 = 0 := by
  have h : ∀ j : Fin 8, (words4[j].map letterImage).prod 0 = 0 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_1 (i : Fin 8) :
    m12PermutationHom (transversal4 i) 1 = 1 := by
  have h : ∀ j : Fin 8, (words4[j].map letterImage).prod 1 = 1 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_2 (i : Fin 8) :
    m12PermutationHom (transversal4 i) 2 = 2 := by
  have h : ∀ j : Fin 8, (words4[j].map letterImage).prod 2 = 2 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_3 (i : Fin 8) :
    m12PermutationHom (transversal4 i) 3 = 3 := by
  have h : ∀ j : Fin 8, (words4[j].map letterImage).prod 3 = 3 := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_4 (i : Fin 8) :
    m12PermutationHom (transversal4 i) 4 = Fin.natAdd 4 i := by
  have h : ∀ j : Fin 8, (words4[j].map letterImage).prod 4 = Fin.natAdd 4 j := by
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

/-- Products of five transversal words in the exact M12 presentation. -/
def m12TransversalProduct (i : Fin 12 × Fin 11 × Fin 10 × Fin 9 × Fin 8) :
    m12Presentation.Group :=
  transversal0 i.1 * (transversal1 i.2.1 *
    (transversal2 i.2.2.1 * (transversal3 i.2.2.2.1 * transversal4 i.2.2.2.2)))

/-- The five successive point images distinguish the permutation images of the products. -/
theorem m12PermutationHom_transversalProduct_injective :
    Function.Injective (fun i ↦ m12PermutationHom (m12TransversalProduct i)) := by
  rintro ⟨i₀, i₁, i₂, i₃, i₄⟩ ⟨j₀, j₁, j₂, j₃, j₄⟩ h
  change m12PermutationHom
    (transversal0 i₀ * (transversal1 i₁ * (transversal2 i₂ *
      (transversal3 i₃ * transversal4 i₄)))) =
    m12PermutationHom
      (transversal0 j₀ * (transversal1 j₁ * (transversal2 j₂ *
        (transversal3 j₃ * transversal4 j₄)))) at h
  simp only [map_mul] at h
  have h₀ := congrArg (fun g : Equiv.Perm (Fin 12) ↦ g 0) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_0, transversal3_apply_0,
    transversal2_apply_0, transversal1_apply_0, transversal0_apply_0] at h₀
  subst j₀
  replace h := mul_left_cancel h
  have h₁ := congrArg (fun g : Equiv.Perm (Fin 12) ↦ g 1) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_1, transversal3_apply_1,
    transversal2_apply_1, transversal1_apply_1] at h₁
  have e₁ : i₁ = j₁ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₁))
  subst j₁
  replace h := mul_left_cancel h
  have h₂ := congrArg (fun g : Equiv.Perm (Fin 12) ↦ g 2) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_2, transversal3_apply_2,
    transversal2_apply_2] at h₂
  have e₂ : i₂ = j₂ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₂))
  subst j₂
  replace h := mul_left_cancel h
  have h₃ := congrArg (fun g : Equiv.Perm (Fin 12) ↦ g 3) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_3, transversal3_apply_3] at h₃
  have e₃ : i₃ = j₃ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₃))
  subst j₃
  replace h := mul_left_cancel h
  have h₄ := congrArg (fun g : Equiv.Perm (Fin 12) ↦ g 4) h
  simp only [transversal4_apply_4] at h₄
  have e₄ : i₄ = j₄ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₄))
  subst j₄
  rfl

/-- The transversal products give distinct elements of the exact M12 presentation. -/
theorem m12TransversalProduct_injective : Function.Injective m12TransversalProduct :=
  fun _ _ h ↦ m12PermutationHom_transversalProduct_injective (congrArg _ h)

/-- The concrete permutation image contains at least 95040 elements. -/
theorem m12PermutationHom_range_natCard_ge : 95040 ≤ Nat.card m12PermutationHom.range := by
  have h : Function.Injective
      (fun i ↦ m12PermutationHom.rangeRestrict (m12TransversalProduct i)) := by
    intro i j hij
    apply m12PermutationHom_transversalProduct_injective
    exact congrArg Subtype.val hij
  have hcard := Nat.card_le_card_of_injective _ h
  simpa only [Nat.card_prod, Nat.card_fin] using hcard

/-- The exact M12 presentation has order at least 95040 whenever it is finite. -/
theorem m12_natCard_ge [Finite m12Presentation.Group] :
    95040 ≤ Nat.card m12Presentation.Group := by
  have h := Nat.card_le_card_of_injective m12TransversalProduct m12TransversalProduct_injective
  simpa only [Nat.card_prod, Nat.card_fin] using h

end TauCeti.Sporadic.Mathieu
