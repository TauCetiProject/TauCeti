/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.LowerBound
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M12UpperBound
import all TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.Permutation

/-!
# The M11 permutation image as an M12 point stabilizer

An explicit relabeling extends the two M11 generator images to M12 words of lengths
10 and 11, fixing point 0. Kernel computation checks both permutation identities;
actual presentation words prove membership in the exact M12 image. Generation and
injectivity of permutation extension give an embedding of the exact M11 image.

Twelve short words certify the full M12 orbit. Orbit-stabilizer and the checked
M12 image order give stabilizer cardinality 7920. The independent M11 image lower
bound makes the embedding surjective. No presentation-finiteness or faithfulness
claim is used, and the large M11 finite coset certificate is not imported.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- The new labels of the 11 moved points in the degree-12 action. -/
private def pointLabels : Vector (Fin 12) 11 :=
  #v[4, 11, 1, 2, 9, 10, 5, 6, 8, 7, 3]

/-- The inverse labeling; the unused entry at the fixed point is zero. -/
private def inverseLabels : Vector (Fin 11) 12 :=
  #v[0, 2, 3, 10, 0, 6, 7, 9, 8, 4, 5, 1]

/-- The explicit relabeling of the M11 points as the nonzero M12 points. -/
def m11ToM12PointEquiv : Fin 11 ≃ {x : Fin 12 // x ≠ 0} where
  toFun i := ⟨pointLabels[i], by
    have h : ∀ j : Fin 11, pointLabels[j] ≠ 0 := by decide +kernel
    exact h i⟩
  invFun x := inverseLabels[x.val]
  left_inv i := by
    have h : ∀ j : Fin 11, inverseLabels[pointLabels[j]] = j := by decide +kernel
    exact h i
  right_inv x := by
    apply Subtype.ext
    have h : ∀ j : Fin 12, j ≠ 0 → pointLabels[inverseLabels[j]] = j := by decide +kernel
    exact h x.val x.property

/-- Extend a permutation through the explicit relabeling, fixing the remaining point 0. -/
def m11ToM12PermHom : Equiv.Perm (Fin 11) →* Equiv.Perm (Fin 12) :=
  Equiv.Perm.extendDomainHom m11ToM12PointEquiv

/-- The extension acts on moved points according to the explicit relabeling. -/
theorem m11ToM12PermHom_apply (g : Equiv.Perm (Fin 11)) (i : Fin 11) :
    m11ToM12PermHom g (m11ToM12PointEquiv i) = m11ToM12PointEquiv (g i) :=
  Equiv.Perm.extendDomain_apply_image g m11ToM12PointEquiv i

/-- Every extended permutation fixes the distinguished point. -/
theorem m11ToM12PermHom_zero (g : Equiv.Perm (Fin 11)) : m11ToM12PermHom g 0 = 0 :=
  Equiv.Perm.extendDomain_apply_not_subtype g m11ToM12PointEquiv (not_not_intro rfl)

/-- Relabeling and adjoining a fixed point preserve distinct permutations. -/
theorem m11ToM12PermHom_injective : Function.Injective m11ToM12PermHom :=
  Equiv.Perm.extendDomainHom_injective m11ToM12PointEquiv

/-- The two M12 generators and their inverses, used as certificate letters. -/
private def m12Letter (i : Fin 4) : m12Presentation.Group :=
  let a : Fin m12Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  let b : Fin m12Presentation.generatorCount := ⟨1, by simp [GroupPresentation.generatorCount]⟩
  if i.val = 0 then PresentedGroup.of a
  else if i.val = 1 then PresentedGroup.of b
  else if i.val = 2 then (PresentedGroup.of a)⁻¹
  else (PresentedGroup.of b)⁻¹

/-- The permutation values of the four M12 certificate letters. -/
private def m12LetterImage (i : Fin 4) : Equiv.Perm (Fin 12) :=
  let a : Fin m12Presentation.generatorCount := ⟨0, by simp [GroupPresentation.generatorCount]⟩
  let b : Fin m12Presentation.generatorCount := ⟨1, by simp [GroupPresentation.generatorCount]⟩
  if i.val = 0 then m12GeneratorImages a
  else if i.val = 1 then m12GeneratorImages b
  else if i.val = 2 then (m12GeneratorImages a)⁻¹
  else (m12GeneratorImages b)⁻¹

/-- The M12 words witnessing membership of the two relabeled M11 generators. -/
private def generatorWords : Vector (List (Fin 4)) 2 :=
  #v[
    [2, 1, 1, 0, 1, 2, 3, 0, 1, 0],
    [3, 2, 2, 3, 2, 2, 1, 0, 3, 0, 0]]

private theorem map_word (w : List (Fin 4)) :
    m12PermutationHom (w.map m12Letter).prod = (w.map m12LetterImage).prod := by
  simp only [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, m12Letter, m12LetterImage]
  split_ifs <;> simp only [m12PermutationHom_of, map_inv]

private theorem generator_word_image (i : Fin m11Presentation.generatorCount) :
    m11ToM12PermHom (m11GeneratorImages i) =
      (generatorWords[(⟨i.val,
        by simpa [GroupPresentation.generatorCount] using i.isLt⟩ : Fin 2)].map
        m12LetterImage).prod := by
  have h : ∀ (j : Fin 2) (x : Fin 12),
      m11ToM12PermHom
        (m11GeneratorImages ⟨j.val, by simpa [GroupPresentation.generatorCount] using j.isLt⟩) x =
      (generatorWords[j].map m12LetterImage).prod x := by
    decide +kernel
  exact Equiv.ext (h ⟨i.val, by simpa [GroupPresentation.generatorCount] using i.isLt⟩)

private theorem generator_mem (i : Fin m11Presentation.generatorCount) :
    m11ToM12PermHom (m11GeneratorImages i) ∈ m12PermutationHom.range := by
  rw [generator_word_image]
  refine ⟨(generatorWords[(⟨i.val,
    by simpa [GroupPresentation.generatorCount] using i.isLt⟩ : Fin 2)].map m12Letter).prod, ?_⟩
  exact map_word _

private theorem image_mem (g : m11PermutationHom.range) :
    m11ToM12PermHom g.val ∈ m12PermutationHom.range := by
  obtain ⟨x, hx⟩ := g.property
  rw [← hx]
  apply PresentedGroup.generated_by m11Presentation.relatorSet
    (m12PermutationHom.range.comap (m11ToM12PermHom.comp m11PermutationHom))
  intro i
  change m11ToM12PermHom (m11PermutationHom (PresentedGroup.of i)) ∈ m12PermutationHom.range
  rw [m11PermutationHom_of]
  exact generator_mem i

/-- The explicit homomorphism from the M11 image to the point-0 stabilizer in the M12 image. -/
def m11ToM12Hom : m11PermutationHom.range →*
    MulAction.stabilizer m12PermutationHom.range (0 : Fin 12) where
  toFun g := ⟨⟨m11ToM12PermHom g.val, image_mem g⟩, m11ToM12PermHom_zero g.val⟩
  map_one' := Subtype.ext (Subtype.ext (map_one m11ToM12PermHom))
  map_mul' g h := Subtype.ext (Subtype.ext (map_mul m11ToM12PermHom g.val h.val))

/-- The subgroup homomorphism acts by the explicit relabeling on the 11 moved points. -/
theorem m11ToM12Hom_apply (g : m11PermutationHom.range) (i : Fin 11) :
    ((m11ToM12Hom g).val.val) (m11ToM12PointEquiv i) = m11ToM12PointEquiv (g.val i) :=
  m11ToM12PermHom_apply g.val i

/-- The explicit homomorphism embeds the exact M11 image in the exact M12 point stabilizer. -/
theorem m11ToM12Hom_injective : Function.Injective m11ToM12Hom := by
  intro g h heq
  apply Subtype.ext
  apply m11ToM12PermHom_injective
  exact congrArg (fun x ↦ x.val.val) heq

/-- Original M12 words taking point 0 to each of the twelve points. -/
private def orbitWords : Vector (List (Fin 4)) 12 :=
  #v[
    [],
    [2],
    [3, 0],
    [0, 3],
    [0],
    [1],
    [2, 1],
    [0, 0],
    [3],
    [3, 0, 0],
    [0, 1],
    [1, 0]]

/-- The exact M12 image acts transitively on its twelve points. -/
theorem m12PermutationHom_range_isPretransitive :
    MulAction.IsPretransitive m12PermutationHom.range (Fin 12) := by
  apply (MulAction.isPretransitive_iff_base (0 : Fin 12)).mpr
  intro x
  refine ⟨m12PermutationHom.rangeRestrict (orbitWords[x].map m12Letter).prod, ?_⟩
  change m12PermutationHom (orbitWords[x].map m12Letter).prod 0 = x
  rw [map_word]
  have h : ∀ y : Fin 12, (orbitWords[y].map m12LetterImage).prod 0 = y := by
    decide +kernel
  exact h x

/-- The point-0 stabilizer in the exact M12 image has 7920 elements. -/
theorem m12PermutationHom_stabilizer_zero_natCard :
    Nat.card (MulAction.stabilizer m12PermutationHom.range (0 : Fin 12)) = 7920 := by
  have := m12PermutationHom_range_isPretransitive
  have h := (MulAction.stabilizer m12PermutationHom.range (0 : Fin 12)).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_fin,
    m12PermutationHom_range_natCard] at h
  omega

/-- The embedding fills the point stabilizer, by its cardinality and the M11 lower bound. -/
theorem m11ToM12Hom_bijective : Function.Bijective m11ToM12Hom := by
  apply m11ToM12Hom_injective.bijective_of_nat_card_le
  rw [m12PermutationHom_stabilizer_zero_natCard]
  exact m11PermutationHom_range_natCard_ge

/-- The exact M11 permutation image is isomorphic to the point-0 stabilizer in the M12 image. -/
@[expose]
noncomputable def m11MulEquivM12Stabilizer : m11PermutationHom.range ≃*
    MulAction.stabilizer m12PermutationHom.range (0 : Fin 12) :=
  MulEquiv.ofBijective m11ToM12Hom m11ToM12Hom_bijective

/-- The stabilizer equivalence uses the explicitly certified embedding. -/
theorem m11MulEquivM12Stabilizer_apply (g : m11PermutationHom.range) :
    m11MulEquivM12Stabilizer g = m11ToM12Hom g := rfl

end TauCeti.Sporadic.Mathieu
