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
# A permutation-image lower bound for M22

Short words distinguish 22, 21, 20, 16, and 3 images of successive pivots
`0, 1, 2, 5, 3`. Each word fixes all earlier pivots. Cancelling the successive
factors therefore proves that their products have distinct permutation images.
Only the 82 transversal words, totalling 600 letters, need point-image checks.

The resulting lower bound is `22 * 21 * 20 * 16 * 3 = 443520` for the concrete
permutation image. The presentation cardinal bound assumes its finiteness
separately; these witnesses supply no upper bound for the presented group.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- Index of the first generator of the exact M22 presentation. -/
private def generatorA : Fin m22Presentation.generatorCount :=
  ⟨0, by simp [GroupPresentation.generatorCount]⟩

/-- Index of the second generator of the exact M22 presentation. -/
private def generatorB : Fin m22Presentation.generatorCount :=
  ⟨1, by simp [GroupPresentation.generatorCount]⟩

/-- Signed letters `0, 1, 2, 3` denote `a, b, a⁻¹, b⁻¹` in the presentation. -/
private def letter (i : Fin 4) : m22Presentation.Group :=
  if i.val = 0 then PresentedGroup.of generatorA
  else if i.val = 1 then PresentedGroup.of generatorB
  else if i.val = 2 then (PresentedGroup.of generatorA)⁻¹
  else (PresentedGroup.of generatorB)⁻¹

/-- The same signed letters in the already checked degree-22 representation. -/
private def letterImage (i : Fin 4) : Equiv.Perm (Fin 22) :=
  if i.val = 0 then m22GeneratorImages generatorA
  else if i.val = 1 then m22GeneratorImages generatorB
  else if i.val = 2 then (m22GeneratorImages generatorA)⁻¹
  else (m22GeneratorImages generatorB)⁻¹

/-- Evaluate a signed word in the exact presented group. -/
private def evalWord (w : List (Fin 4)) : m22Presentation.Group :=
  (w.map letter).prod

private theorem map_evalWord (w : List (Fin 4)) :
    m22PermutationHom (evalWord w) = (w.map letterImage).prod := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, letter, letterImage]
  split_ifs <;> simp only [m22PermutationHom_of, map_inv]

/-- The final three distinct images of pivot 3 after fixing pivots `0, 1, 2, 5`. -/
private def lastTargets : Vector (Fin 22) 3 := #v[3, 4, 21]

private theorem lastTargets_injective :
    Function.Injective (fun i : Fin 3 ↦ lastTargets[i]) := by
  decide +kernel

/-- Words sending pivot 0 to the 22 listed distinct images.
The entries are ordered by their pivot images: 0 through 21. -/
private def words0 : Vector (List (Fin 4)) 22 := #v[
  [],
  [1],
  [3, 3, 2],
  [1, 2],
  [0, 1, 2],
  [0, 1, 2, 2],
  [0, 1, 2, 3, 2],
  [3, 2],
  [1, 2, 3, 2],
  [3, 0],
  [0],
  [2, 2],
  [2],
  [2, 3],
  [0, 3],
  [1, 0, 1, 2],
  [0, 3, 2],
  [1, 2, 2],
  [2, 3, 2],
  [0, 1],
  [3],
  [0, 0]]

/-- The presentation element of a level-0 transversal word. -/
private def transversal0 (i : Fin 22) : m22Presentation.Group :=
  evalWord words0[i]

private theorem transversal0_apply_0 (i : Fin 22) :
    m22PermutationHom (transversal0 i) 0 = i := by
  have h : ∀ j : Fin 22, (words0[j].map letterImage).prod 0 =
      j := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal0, map_evalWord] using h i

/-- Words sending pivot 1 to the 21 listed distinct images while fixing `0`.
The entries are ordered by their pivot images: 1 through 21. -/
private def words1 : Vector (List (Fin 4)) 21 := #v[
  [],
  [0, 1, 1, 2, 3, 3, 2],
  [3, 0, 0, 3],
  [1, 1, 0],
  [0, 3, 2, 3, 2, 1, 2, 2],
  [1, 1, 0, 1, 1, 0],
  [0, 0, 1, 0, 0],
  [1, 0, 1, 0, 1],
  [1, 2, 2, 1],
  [3, 0, 0, 3, 2, 3, 3],
  [3, 3, 0, 1, 2, 3, 3],
  [2, 1, 1, 0, 3],
  [2, 3, 3],
  [2, 3, 3, 2, 3, 3],
  [1, 1, 0, 0, 3, 3, 0, 0],
  [1, 1, 0, 3, 0, 0, 3],
  [3, 2, 3, 2, 3],
  [2, 3, 3, 3, 0, 0, 3],
  [0, 3, 3, 0, 0],
  [0, 3, 0, 0, 3, 2],
  [0, 1, 2, 2, 1, 2]]

/-- The presentation element of a level-1 transversal word. -/
private def transversal1 (i : Fin 21) : m22Presentation.Group :=
  evalWord words1[i]

private theorem transversal1_apply_0 (i : Fin 21) :
    m22PermutationHom (transversal1 i) 0 = 0 := by
  have h : ∀ j : Fin 21, (words1[j].map letterImage).prod 0 =
      0 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

private theorem transversal1_apply_1 (i : Fin 21) :
    m22PermutationHom (transversal1 i) 1 = Fin.natAdd 1 i := by
  have h : ∀ j : Fin 21, (words1[j].map letterImage).prod 1 =
      Fin.natAdd 1 j := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

/-- Words sending pivot 2 to the 20 listed distinct images while fixing `0, 1`.
The entries are ordered by their pivot images: 2 through 21. -/
private def words2 : Vector (List (Fin 4)) 20 := #v[
  [],
  [2, 2, 3, 2, 3, 0, 0, 3, 0, 1, 0, 0],
  [3, 3, 0, 1],
  [0, 3, 3, 0, 1, 1, 0, 3],
  [0, 3, 2, 3, 0, 0, 1, 2, 3, 2],
  [0, 0, 3, 2, 3, 3, 3, 3, 3, 0, 0],
  [2, 3, 3, 2, 3, 2, 2, 1, 1, 1, 0],
  [2, 3, 2, 3, 3, 3, 3, 2, 3, 3],
  [1, 1, 0, 1, 1, 1, 1, 0, 1, 0],
  [1, 1, 1, 0, 3, 3, 3, 2, 3, 3],
  [2, 3, 3, 3, 0, 0, 1, 0, 1, 1, 0],
  [2, 3, 3, 2, 2, 1, 1, 2, 1, 0, 1, 0, 1],
  [1, 2, 2, 3, 0, 0, 0, 3],
  [1, 2, 2, 1, 2, 3, 3, 3, 0, 0, 1, 0],
  [1, 2, 2, 1, 1, 2, 3, 3, 0],
  [0, 0, 1, 0, 1, 1, 0, 3],
  [0, 1, 0, 3, 2, 2, 1, 0, 1, 2],
  [1, 1, 0, 1, 1, 1, 2, 3, 3, 3],
  [1, 2, 3, 3, 2, 3, 2, 2],
  [3, 2, 1, 1]]

/-- The presentation element of a level-2 transversal word. -/
private def transversal2 (i : Fin 20) : m22Presentation.Group :=
  evalWord words2[i]

private theorem transversal2_apply_0 (i : Fin 20) :
    m22PermutationHom (transversal2 i) 0 = 0 := by
  have h : ∀ j : Fin 20, (words2[j].map letterImage).prod 0 =
      0 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_1 (i : Fin 20) :
    m22PermutationHom (transversal2 i) 1 = 1 := by
  have h : ∀ j : Fin 20, (words2[j].map letterImage).prod 1 =
      1 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

private theorem transversal2_apply_2 (i : Fin 20) :
    m22PermutationHom (transversal2 i) 2 = Fin.natAdd 2 i := by
  have h : ∀ j : Fin 20, (words2[j].map letterImage).prod 2 =
      Fin.natAdd 2 j := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

/-- Words sending pivot 5 to the 16 listed distinct images while fixing `0, 1, 2`.
The entries are ordered by their pivot images: 5 through 20. -/
private def words3 : Vector (List (Fin 4)) 16 := #v[
  [],
  [3, 2, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0],
  [3, 0, 0, 3, 0, 1, 0, 1, 1, 2, 2, 1, 2, 2, 1],
  [1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 1],
  [0, 1, 2, 2, 3, 0, 0, 1, 0, 1, 1, 1],
  [0, 0, 1, 0, 1, 1, 0, 1, 0, 3, 3, 0, 1, 1, 0, 1, 0, 1],
  [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 0, 1],
  [0, 1, 1, 0, 3, 3, 2, 1, 2, 2, 1, 1, 0, 1, 1, 1],
  [0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 2, 3, 3, 0, 0],
  [1, 0, 1, 0, 1, 0, 1, 1, 2, 3, 3, 3, 3, 0, 0],
  [2, 2, 3, 2, 3, 0, 0, 3, 0, 1, 0, 0, 3, 2, 1, 1],
  [3, 3, 0, 1, 1, 2, 2, 1, 1, 0, 1, 0, 1, 1, 2, 2, 1],
  [2, 3, 3, 2, 1, 1, 0, 3, 3, 3, 0, 1, 2, 3, 3, 3, 3, 0, 1],
  [1, 0, 1, 0, 3, 0, 1, 1, 1, 0, 1, 1, 0, 3, 2, 1, 1],
  [3, 0, 0, 3, 3, 2, 3, 2, 3, 3, 0, 0, 3, 3, 2, 1, 1],
  [3, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3, 3]]

/-- The presentation element of a level-3 transversal word. -/
private def transversal3 (i : Fin 16) : m22Presentation.Group :=
  evalWord words3[i]

private theorem transversal3_apply_0 (i : Fin 16) :
    m22PermutationHom (transversal3 i) 0 = 0 := by
  have h : ∀ j : Fin 16, (words3[j].map letterImage).prod 0 =
      0 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_1 (i : Fin 16) :
    m22PermutationHom (transversal3 i) 1 = 1 := by
  have h : ∀ j : Fin 16, (words3[j].map letterImage).prod 1 =
      1 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_2 (i : Fin 16) :
    m22PermutationHom (transversal3 i) 2 = 2 := by
  have h : ∀ j : Fin 16, (words3[j].map letterImage).prod 2 =
      2 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

private theorem transversal3_apply_5 (i : Fin 16) :
    m22PermutationHom (transversal3 i) 5 = (Fin.natAdd 5 i).castSucc := by
  have h : ∀ j : Fin 16, (words3[j].map letterImage).prod 5 =
      (Fin.natAdd 5 j).castSucc := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

/-- Words sending pivot 3 to the 3 listed distinct images while fixing `0, 1, 2, 5`.
The entries are ordered by their pivot images: `3, 4, 21`. -/
private def words4 : Vector (List (Fin 4)) 3 := #v[
  [],
  [3, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 2, 3, 2, 3],
  [1, 0, 1, 0, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 1]]

/-- The presentation element of a level-4 transversal word. -/
private def transversal4 (i : Fin 3) : m22Presentation.Group :=
  evalWord words4[i]

private theorem transversal4_apply_0 (i : Fin 3) :
    m22PermutationHom (transversal4 i) 0 = 0 := by
  have h : ∀ j : Fin 3, (words4[j].map letterImage).prod 0 =
      0 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_1 (i : Fin 3) :
    m22PermutationHom (transversal4 i) 1 = 1 := by
  have h : ∀ j : Fin 3, (words4[j].map letterImage).prod 1 =
      1 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_2 (i : Fin 3) :
    m22PermutationHom (transversal4 i) 2 = 2 := by
  have h : ∀ j : Fin 3, (words4[j].map letterImage).prod 2 =
      2 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_5 (i : Fin 3) :
    m22PermutationHom (transversal4 i) 5 = 5 := by
  have h : ∀ j : Fin 3, (words4[j].map letterImage).prod 5 =
      5 := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

private theorem transversal4_apply_3 (i : Fin 3) :
    m22PermutationHom (transversal4 i) 3 = lastTargets[i] := by
  have h : ∀ j : Fin 3, (words4[j].map letterImage).prod 3 =
      lastTargets[j] := by
    unfold letterImage m22GeneratorImages
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

/-- Products of five transversal words in the exact M22 presentation. -/
def m22TransversalProduct (i : Fin 22 × Fin 21 × Fin 20 × Fin 16 × Fin 3) :
    m22Presentation.Group :=
  transversal0 i.1 * (transversal1 i.2.1 *
    (transversal2 i.2.2.1 * (transversal3 i.2.2.2.1 * transversal4 i.2.2.2.2)))

/-- Successive pivot images distinguish all 443520 transversal products. -/
theorem m22PermutationHom_transversalProduct_injective :
    Function.Injective (fun i ↦ m22PermutationHom (m22TransversalProduct i)) := by
  rintro ⟨i₀, i₁, i₂, i₃, i₄⟩ ⟨j₀, j₁, j₂, j₃, j₄⟩ h
  change m22PermutationHom
    (transversal0 i₀ * (transversal1 i₁ *
      (transversal2 i₂ * (transversal3 i₃ * transversal4 i₄)))) =
    m22PermutationHom
      (transversal0 j₀ * (transversal1 j₁ *
        (transversal2 j₂ * (transversal3 j₃ * transversal4 j₄)))) at h
  simp only [map_mul] at h
  have h₀ := congrArg (fun g : Equiv.Perm (Fin 22) ↦ g 0) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_0, transversal3_apply_0,
    transversal2_apply_0, transversal1_apply_0, transversal0_apply_0] at h₀
  subst j₀
  replace h := mul_left_cancel h
  have h₁ := congrArg (fun g : Equiv.Perm (Fin 22) ↦ g 1) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_1, transversal3_apply_1,
    transversal2_apply_1, transversal1_apply_1] at h₁
  have e₁ : i₁ = j₁ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₁))
  subst j₁
  replace h := mul_left_cancel h
  have h₂ := congrArg (fun g : Equiv.Perm (Fin 22) ↦ g 2) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_2, transversal3_apply_2,
    transversal2_apply_2] at h₂
  have e₂ : i₂ = j₂ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₂))
  subst j₂
  replace h := mul_left_cancel h
  have h₃ := congrArg (fun g : Equiv.Perm (Fin 22) ↦ g 5) h
  simp only [Equiv.Perm.mul_apply, transversal4_apply_5, transversal3_apply_5] at h₃
  have e₃ : i₃ = j₃ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₃))
  subst j₃
  replace h := mul_left_cancel h
  have h₄ := congrArg (fun g : Equiv.Perm (Fin 22) ↦ g 3) h
  simp only [transversal4_apply_3] at h₄
  have e₄ : i₄ = j₄ := lastTargets_injective h₄
  subst j₄
  rfl

/-- The transversal products are distinct already in the exact presentation. -/
theorem m22TransversalProduct_injective : Function.Injective m22TransversalProduct :=
  fun _ _ h ↦ m22PermutationHom_transversalProduct_injective (congrArg _ h)

/-- The concrete degree-22 permutation image contains at least 443520 elements. -/
theorem m22PermutationHom_range_natCard_ge :
    443520 ≤ Nat.card m22PermutationHom.range := by
  have h : Function.Injective
      (fun i ↦ m22PermutationHom.rangeRestrict (m22TransversalProduct i)) := by
    intro i j hij
    apply m22PermutationHom_transversalProduct_injective
    exact congrArg Subtype.val hij
  have hcard := Nat.card_le_card_of_injective _ h
  simpa only [Nat.card_prod, Nat.card_fin] using hcard

/-- A finite exact M22 presentation has at least 443520 elements. -/
theorem m22_natCard_ge [Finite m22Presentation.Group] :
    443520 ≤ Nat.card m22Presentation.Group := by
  have h := Nat.card_le_card_of_injective m22TransversalProduct
    m22TransversalProduct_injective
  simpa only [Nat.card_prod, Nat.card_fin] using h

end TauCeti.Sporadic.Mathieu
