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
# A permutation-image lower bound for M24

The 129 words below give distinct images of successive pivots `0, 1, 2, 3, 4, 5, 6`,
while fixing all earlier pivots. Their respective numbers are `24, 23, 22, 21, 20, 16, 3`.
Cancelling successive factors distinguishes all 244823040 products in the checked
permutation image. Only individual word actions on the seven pivots are checked.
This gives no finiteness, faithfulness, or simplicity assertion for the presentation.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- Index of the first generator of the exact M24 presentation. -/
private def generatorA : Fin m24Presentation.generatorCount :=
  ⟨0, by simp [GroupPresentation.generatorCount]⟩

/-- Index of the second generator of the exact M24 presentation. -/
private def generatorB : Fin m24Presentation.generatorCount :=
  ⟨1, by simp [GroupPresentation.generatorCount]⟩

/-- Signed letters `0, 1, 2, 3` denote `a, b, a⁻¹, b⁻¹` in the presentation. -/
private def letter (i : Fin 4) : m24Presentation.Group :=
  if i.val = 0 then PresentedGroup.of generatorA
  else if i.val = 1 then PresentedGroup.of generatorB
  else if i.val = 2 then (PresentedGroup.of generatorA)⁻¹
  else (PresentedGroup.of generatorB)⁻¹

/-- The signed letters in the already checked degree-24 representation. -/
private def letterImage (i : Fin 4) : Equiv.Perm (Fin 24) :=
  if i.val = 0 then m24GeneratorImages generatorA
  else if i.val = 1 then m24GeneratorImages generatorB
  else if i.val = 2 then (m24GeneratorImages generatorA)⁻¹
  else (m24GeneratorImages generatorB)⁻¹

/-- Evaluate a signed word in the exact presented group. -/
private def evalWord (w : List (Fin 4)) : m24Presentation.Group :=
  (w.map letter).prod

private theorem map_evalWord (w : List (Fin 4)) :
    m24PermutationHom (evalWord w) = (w.map letterImage).prod := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, letter, letterImage]
  split_ifs <;> simp only [m24PermutationHom_of, map_inv]

/-- Words fixing points below 0 and sending 0 to points 0 through 23, in order. -/
private def words0 : Vector (List (Fin 4)) 24 := #v[
  [],
  [3, 2],
  [2, 1, 2, 1, 2],
  [2, 3, 2, 1, 2],
  [2, 3, 2],
  [1, 2, 1, 2],
  [1, 2, 3, 2, 3, 2, 3, 2, 1, 2],
  [2, 1, 2, 1, 2, 3, 2, 1, 2],
  [2, 3, 2, 1, 2, 3, 2, 1, 2],
  [2, 3, 2, 3, 2, 1, 2],
  [3, 2, 1, 2],
  [2],
  [0, 1, 0, 3, 2, 3, 2, 1, 2],
  [3, 2, 3, 2, 3, 2, 1, 2],
  [3, 2, 3, 2, 3, 2, 3, 2, 1, 2],
  [1, 2, 3, 2, 3, 2, 1, 2],
  [1, 2, 3, 2, 1, 2],
  [1, 2, 1, 2, 3, 2, 1, 2],
  [2, 1, 2, 3, 2, 1, 2],
  [2, 3, 2, 3, 2, 3, 2, 1, 2],
  [3, 2, 3, 2, 1, 2],
  [1, 2],
  [2, 1, 2],
  [3, 2, 1, 2, 3, 2, 1, 2]]

/-- The presentation element represented by a level-0 word. -/
private def transversal0 (i : Fin 24) : m24Presentation.Group :=
  evalWord (getElem words0 i i.isLt)

private theorem transversal0_pivot (i : Fin 24) :
    m24PermutationHom (transversal0 i) 0 =
      (Fin.natAdd 0 i).castLE (by decide) := by
  have h : ∀ j : Fin 24, ((getElem words0 j j.isLt).map letterImage).prod 0 =
      (Fin.natAdd 0 j).castLE (by decide) := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal0, map_evalWord] using h i

/-- Words fixing points below 1 and sending 1 to points 1 through 23, in order. -/
private def words1 : Vector (List (Fin 4)) 23 := #v[
  [],
  [0, 1, 0, 3, 2, 3, 2],
  [0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2],
  [0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3],
  [3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [0, 1, 0, 1, 2, 3, 2, 3],
  [0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2],
  [3, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2, 3],
  [0, 1, 0, 1, 2, 3, 2, 3, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [1],
  [0, 1, 0, 3, 2, 3, 2, 3],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [3, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2, 3],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2],
  [0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1],
  [3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2],
  [3],
  [1, 0, 1, 0, 1, 2, 3, 2, 3, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1]]

/-- The presentation element represented by a level-1 word. -/
private def transversal1 (i : Fin 23) : m24Presentation.Group :=
  evalWord (getElem words1 i i.isLt)

private theorem transversal1_fixed (x : Fin 24) (hx : x.val < 1) (i : Fin 23) :
    m24PermutationHom (transversal1 i) x = x := by
  have h : ∀ (j : Fin 23) (y : Fin 24), y.val < 1 →
      ((getElem words1 j j.isLt).map letterImage).prod y = y := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i x hx

private theorem transversal1_pivot (i : Fin 23) :
    m24PermutationHom (transversal1 i) 1 =
      (Fin.natAdd 1 i).castLE (by decide) := by
  have h : ∀ j : Fin 23, ((getElem words1 j j.isLt).map letterImage).prod 1 =
      (Fin.natAdd 1 j).castLE (by decide) := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal1, map_evalWord] using h i

/-- Words fixing points below 2 and sending 2 to points 2 through 23, in order. -/
private def words2 : Vector (List (Fin 4)) 22 := #v[
  [],
  [3, 0, 1, 0, 1, 2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2],
  [3, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2,
    1, 2, 1],
  [0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2],
  [0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2],
  [0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1],
  [0, 1, 0, 3, 2, 3, 2, 1],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 1],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1],
  [1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 2, 3],
  [3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2],
  [1, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3],
  [1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2, 3],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1],
  [3, 0, 1, 0, 1, 2, 3, 2],
  [3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3],
  [3, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1]]

/-- The presentation element represented by a level-2 word. -/
private def transversal2 (i : Fin 22) : m24Presentation.Group :=
  evalWord (getElem words2 i i.isLt)

private theorem transversal2_fixed (x : Fin 24) (hx : x.val < 2) (i : Fin 22) :
    m24PermutationHom (transversal2 i) x = x := by
  have h : ∀ (j : Fin 22) (y : Fin 24), y.val < 2 →
      ((getElem words2 j j.isLt).map letterImage).prod y = y := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i x hx

private theorem transversal2_pivot (i : Fin 22) :
    m24PermutationHom (transversal2 i) 2 =
      (Fin.natAdd 2 i).castLE (by decide) := by
  have h : ∀ j : Fin 22, ((getElem words2 j j.isLt).map letterImage).prod 2 =
      (Fin.natAdd 2 j).castLE (by decide) := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal2, map_evalWord] using h i

/-- Words fixing points below 3 and sending 3 to points 3 through 23, in order. -/
private def words3 : Vector (List (Fin 4)) 21 := #v[
  [],
  [3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3],
  [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2],
  [3, 0, 1, 0, 1, 1, 2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 1, 2, 3, 2, 3],
  [1, 0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 3, 0, 1, 0, 1, 2, 3, 2],
  [1, 0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 1, 2,
    1],
  [3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2,
    1],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 3, 2, 3, 2, 1],
  [1, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1],
  [0, 1, 0, 3, 2, 3, 2, 1, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2, 3],
  [1, 0, 1, 0, 1, 2, 3, 3, 0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 3, 2,
    3, 2, 1],
  [3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2,
    3, 2, 1],
  [1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 1, 2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3],
  [3, 0, 1, 0, 1, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3],
  [1, 0, 1, 0, 3, 2, 3, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 3, 3, 2, 3, 2, 1],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2],
  [3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 1, 0, 3, 2,
    3, 2, 1]]

/-- The presentation element represented by a level-3 word. -/
private def transversal3 (i : Fin 21) : m24Presentation.Group :=
  evalWord (getElem words3 i i.isLt)

private theorem transversal3_fixed (x : Fin 24) (hx : x.val < 3) (i : Fin 21) :
    m24PermutationHom (transversal3 i) x = x := by
  have h : ∀ (j : Fin 21) (y : Fin 24), y.val < 3 →
      ((getElem words3 j j.isLt).map letterImage).prod y = y := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i x hx

private theorem transversal3_pivot (i : Fin 21) :
    m24PermutationHom (transversal3 i) 3 =
      (Fin.natAdd 3 i).castLE (by decide) := by
  have h : ∀ j : Fin 21, ((getElem words3 j j.isLt).map letterImage).prod 3 =
      (Fin.natAdd 3 j).castLE (by decide) := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal3, map_evalWord] using h i

/-- Words fixing points below 4 and sending 4 to points 4 through 23, in order. -/
private def words4 : Vector (List (Fin 4)) 20 := #v[
  [],
  [1, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 0, 1, 1, 2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 3,
    0, 1, 1, 2, 1, 2, 1, 1, 0, 1, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 1, 0, 1, 0,
    3, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1],
  [0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2, 3, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 1, 2, 3,
    0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 3, 0, 1, 0, 1, 2, 3, 2],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3, 3,
    0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3],
  [0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 3, 0, 1, 0,
    1, 2, 3, 2, 3, 3, 0, 1, 0, 1, 2, 3, 2],
  [0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2,
    3, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 1],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 3, 2, 3, 2, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3,
    3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 3, 2, 3, 2, 1],
  [1, 0, 1, 0, 3, 2, 3, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1,
    0, 1, 1, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 3, 2, 3, 2],
  [3, 0, 1, 0, 1, 2, 3, 3, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 1],
  [0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 3, 2,
    3, 2, 1, 0, 3, 2, 3, 2, 3],
  [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 1, 2, 3,
    3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3,
    2, 1, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3],
  [1, 0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3,
    0, 1, 0, 1, 2, 3, 2, 3, 2],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 1, 2, 1, 1, 0, 1, 2, 3, 2, 3, 3, 0, 1, 0, 1, 1,
    2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 1, 2, 3, 2, 3],
  [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 2, 3, 2, 1],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 2, 3, 0, 1, 0, 1, 2, 3, 3, 0, 1, 0, 3, 0,
    3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 1],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 1,
    0, 1, 2, 3, 2, 3, 2, 1, 1, 0, 3, 2, 3, 2, 1],
  [0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 3, 2, 1, 2, 1, 2, 3],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 1, 0, 1, 2, 3, 2]]

/-- The presentation element represented by a level-4 word. -/
private def transversal4 (i : Fin 20) : m24Presentation.Group :=
  evalWord (getElem words4 i i.isLt)

private theorem transversal4_fixed (x : Fin 24) (hx : x.val < 4) (i : Fin 20) :
    m24PermutationHom (transversal4 i) x = x := by
  have h : ∀ (j : Fin 20) (y : Fin 24), y.val < 4 →
      ((getElem words4 j j.isLt).map letterImage).prod y = y := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i x hx

private theorem transversal4_pivot (i : Fin 20) :
    m24PermutationHom (transversal4 i) 4 =
      (Fin.natAdd 4 i).castLE (by decide) := by
  have h : ∀ j : Fin 20, ((getElem words4 j j.isLt).map letterImage).prod 4 =
      (Fin.natAdd 4 j).castLE (by decide) := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal4, map_evalWord] using h i

/-- Words fixing points below 5 and sending 5 to points 5 through 20, in order. -/
private def words5 : Vector (List (Fin 4)) 16 := #v[
  [],
  [0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2,
    3, 3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 3, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 3, 0, 3, 0,
    1, 0, 1, 2, 3, 2, 1, 2, 1],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 3,
    0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1,
    0, 1, 2, 3, 2, 1, 2, 1],
  [3, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 2, 3, 2, 1, 0, 3, 0, 1, 0,
    3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 3,
    0, 3, 2, 1, 2, 1, 2, 3],
  [3, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 1, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 0, 3, 2, 3, 2, 1,
    1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 3,
    0, 1, 0, 1, 2, 3, 3, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 0, 1, 0, 1, 2, 3, 2],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 1, 0, 1, 1, 0, 3, 2,
    3, 2, 1, 0, 3, 2, 3, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 1, 0, 1, 1,
    0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2],
  [1, 0, 3, 0, 3, 0, 1, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 0, 3, 2, 1, 2, 1, 2, 3,
    0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0,
    3, 2, 1, 2, 1, 2, 3],
  [1, 0, 1, 0, 3, 2, 3, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 3, 3, 2, 3, 2, 1, 0, 1, 0, 1, 0, 3, 2,
    3, 2, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3, 3, 0, 3, 0, 3, 0,
    3, 2, 1, 2, 1, 2, 3],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 3, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 3, 0,
    3, 2, 1, 2, 1, 1, 0, 1, 2, 3, 3, 0, 3, 0, 1, 1, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3,
    2, 1, 1, 0, 1, 2, 3, 2],
  [0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 0, 3, 2, 3, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2,
    3, 2, 1, 1, 0, 1, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3,
    2, 1, 1, 0, 3, 2, 3, 2, 1],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 2,
    3, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1,
    2, 3, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 1],
  [1, 0, 1, 0, 3, 2, 3, 3, 0, 3, 0, 3, 3, 2, 1, 1, 0, 1, 0, 1, 0, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3,
    2, 3, 2, 1, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0,
    3, 2, 3, 2, 1, 0, 3, 2, 3, 2, 3],
  [0, 1, 0, 3, 2, 3, 3, 0, 3, 0, 3, 2, 1, 2, 1, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1],
  [0, 1, 0, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3,
    2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1, 0,
    3, 0, 3, 0, 3, 2, 1, 2, 1, 2],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 3, 3, 2, 3, 2, 1, 0, 1, 0, 3, 2, 3, 2, 2,
    1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 1, 0, 1, 2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 3,
    0, 3, 2, 1, 2, 1, 2, 3],
  [0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 3, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 1, 2, 1, 2, 1, 2, 3, 2,
    1, 2, 1, 0, 1, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 3, 2, 3, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3,
    2, 3, 3, 0, 3, 2, 1, 2, 1, 2, 3]]

/-- The presentation element represented by a level-5 word. -/
private def transversal5 (i : Fin 16) : m24Presentation.Group :=
  evalWord (getElem words5 i i.isLt)

private theorem transversal5_fixed (x : Fin 24) (hx : x.val < 5) (i : Fin 16) :
    m24PermutationHom (transversal5 i) x = x := by
  have h : ∀ (j : Fin 16) (y : Fin 24), y.val < 5 →
      ((getElem words5 j j.isLt).map letterImage).prod y = y := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i x hx

private theorem transversal5_pivot (i : Fin 16) :
    m24PermutationHom (transversal5 i) 5 =
      (Fin.natAdd 5 i).castLE (by decide) := by
  have h : ∀ j : Fin 16, ((getElem words5 j j.isLt).map letterImage).prod 5 =
      (Fin.natAdd 5 j).castLE (by decide) := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal5, map_evalWord] using h i

/-- Words fixing points below 6 and sending 6 to points 6 through 8, in order. -/
private def words6 : Vector (List (Fin 4)) 3 := #v[
  [],
  [3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 3, 0, 3, 0, 1, 2, 1, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 3,
    0, 3, 3, 2, 1, 2, 1, 1, 0, 3, 2, 3, 3, 0, 3, 0, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2,
    3, 2, 1, 1, 0, 3, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2],
  [0, 1, 0, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 3, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 3, 0,
    3, 2, 1, 2, 1, 1, 0, 1, 2, 3, 3, 0, 3, 0, 1, 1, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3,
    3, 0, 3, 2, 1, 2, 1, 2, 3, 0, 1, 0, 3, 2, 3, 2, 1]]

/-- The presentation element represented by a level-6 word. -/
private def transversal6 (i : Fin 3) : m24Presentation.Group :=
  evalWord (getElem words6 i i.isLt)

private theorem transversal6_fixed (x : Fin 24) (hx : x.val < 6) (i : Fin 3) :
    m24PermutationHom (transversal6 i) x = x := by
  have h : ∀ (j : Fin 3) (y : Fin 24), y.val < 6 →
      ((getElem words6 j j.isLt).map letterImage).prod y = y := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal6, map_evalWord] using h i x hx

private theorem transversal6_pivot (i : Fin 3) :
    m24PermutationHom (transversal6 i) 6 =
      (Fin.natAdd 6 i).castLE (by decide) := by
  have h : ∀ j : Fin 3, ((getElem words6 j j.isLt).map letterImage).prod 6 =
      (Fin.natAdd 6 j).castLE (by decide) := by
    unfold letterImage m24GeneratorImages
    decide +kernel
  simpa only [transversal6, map_evalWord] using h i

/-- Products of seven transversal words in the exact M24 presentation. -/
def m24TransversalProduct (i : Fin 24 × Fin 23 × Fin 22 × Fin 21 × Fin 20 × Fin 16 × Fin 3) :
    m24Presentation.Group :=
  transversal0 i.1 * (transversal1 i.2.1 * (transversal2 i.2.2.1 * (transversal3 i.2.2.2.1 *
    (transversal4 i.2.2.2.2.1 * (transversal5 i.2.2.2.2.2.1 * (transversal6 i.2.2.2.2.2.2))))))

/-- Successive pivot images distinguish all 244823040 transversal products. -/
theorem m24PermutationHom_transversalProduct_injective :
    Function.Injective (fun i ↦ m24PermutationHom (m24TransversalProduct i)) := by
  rintro ⟨i₀, i₁, i₂, i₃, i₄, i₅, i₆⟩ ⟨j₀, j₁, j₂, j₃, j₄, j₅, j₆⟩ h
  change m24PermutationHom
    (transversal0 i₀ * (transversal1 i₁ * (transversal2 i₂ * (transversal3 i₃ * (transversal4 i₄
      * (transversal5 i₅ * (transversal6 i₆))))))) =
    m24PermutationHom
      (transversal0 j₀ * (transversal1 j₁ * (transversal2 j₂ * (transversal3 j₃ * (transversal4
        j₄ * (transversal5 j₅ * (transversal6 j₆))))))) at h
  simp only [map_mul] at h
  have h₀ := congrArg (fun g : Equiv.Perm (Fin 24) ↦ g 0) h
  simp only [Equiv.Perm.mul_apply, transversal6_fixed 0 (by decide),
    transversal5_fixed 0 (by decide), transversal4_fixed 0 (by decide),
    transversal3_fixed 0 (by decide), transversal2_fixed 0 (by decide),
    transversal1_fixed 0 (by decide), transversal0_pivot] at h₀
  have e₀ : i₀ = j₀ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₀))
  subst j₀
  replace h := mul_left_cancel h
  have h₁ := congrArg (fun g : Equiv.Perm (Fin 24) ↦ g 1) h
  simp only [Equiv.Perm.mul_apply, transversal6_fixed 1 (by decide),
    transversal5_fixed 1 (by decide), transversal4_fixed 1 (by decide),
    transversal3_fixed 1 (by decide), transversal2_fixed 1 (by decide),
    transversal1_pivot] at h₁
  have e₁ : i₁ = j₁ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₁))
  subst j₁
  replace h := mul_left_cancel h
  have h₂ := congrArg (fun g : Equiv.Perm (Fin 24) ↦ g 2) h
  simp only [Equiv.Perm.mul_apply, transversal6_fixed 2 (by decide),
    transversal5_fixed 2 (by decide), transversal4_fixed 2 (by decide),
    transversal3_fixed 2 (by decide), transversal2_pivot] at h₂
  have e₂ : i₂ = j₂ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₂))
  subst j₂
  replace h := mul_left_cancel h
  have h₃ := congrArg (fun g : Equiv.Perm (Fin 24) ↦ g 3) h
  simp only [Equiv.Perm.mul_apply, transversal6_fixed 3 (by decide),
    transversal5_fixed 3 (by decide), transversal4_fixed 3 (by decide),
    transversal3_pivot] at h₃
  have e₃ : i₃ = j₃ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₃))
  subst j₃
  replace h := mul_left_cancel h
  have h₄ := congrArg (fun g : Equiv.Perm (Fin 24) ↦ g 4) h
  simp only [Equiv.Perm.mul_apply, transversal6_fixed 4 (by decide),
    transversal5_fixed 4 (by decide), transversal4_pivot] at h₄
  have e₄ : i₄ = j₄ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₄))
  subst j₄
  replace h := mul_left_cancel h
  have h₅ := congrArg (fun g : Equiv.Perm (Fin 24) ↦ g 5) h
  simp only [Equiv.Perm.mul_apply, transversal6_fixed 5 (by decide),
    transversal5_pivot] at h₅
  have e₅ : i₅ = j₅ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₅))
  subst j₅
  replace h := mul_left_cancel h
  have h₆ := congrArg (fun g : Equiv.Perm (Fin 24) ↦ g 6) h
  simp only [transversal6_pivot] at h₆
  have e₆ : i₆ = j₆ := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₆))
  subst j₆
  rfl

/-- The concrete degree-24 permutation image contains at least 244823040 elements. -/
theorem m24PermutationHom_range_natCard_ge :
    244823040 ≤ Nat.card m24PermutationHom.range := by
  have h : Function.Injective
      (fun i ↦ m24PermutationHom.rangeRestrict (m24TransversalProduct i)) := by
    intro i j hij
    apply m24PermutationHom_transversalProduct_injective
    exact congrArg Subtype.val hij
  have hcard := Nat.card_le_card_of_injective _ h
  simpa only [Nat.card_prod, Nat.card_fin] using hcard

end TauCeti.Sporadic.Mathieu
