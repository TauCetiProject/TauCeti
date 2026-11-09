/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeAlgebra
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD

/-!
# Words in a free algebra

Mathlib's free-monoid basis vector is the ordered product of the generators in its word
(`TauCeti.basisFreeMonoid_apply`). This identity converts basis evaluations into ordered word
products, for instance when proving that word moments determine a linear functional on a free
algebra.

The words `TauCeti.FreeAlgebra.word R w = ι a₁ * ⋯ * ι aₙ` form a basis of `FreeAlgebra R A`, so a
linear map out of the free algebra is determined by, and may be prescribed by, its values on words
(`TauCeti.FreeAlgebra.linearMap_ext_word`, `TauCeti.FreeAlgebra.ofWords`). In the free algebra
the letters of a word are not yet multilinear, so operations on the letters of a word, which are
not well defined on the tensor algebra, extend linearly from words. This file defines the operations
of the bar construction of a differential algebra `(A, d)` in this way:

* `TauCeti.FreeAlgebra.deconcat`: the splitting of a word into a prefix and a suffix in all ways,
  `a₁ ⋯ aₙ ↦ ∑ᵢ a₁ ⋯ aᵢ ⊗ aᵢ₊₁ ⋯ aₙ`;
* `TauCeti.FreeAlgebra.diffLetters`: the letters differentiated one at a time,
  `a₁ ⋯ aₙ ↦ ∑ᵢ a₁ ⋯ (d aᵢ) ⋯ aₙ`;
* `TauCeti.FreeAlgebra.mergeAdjacent`: adjacent letters multiplied, one pair at a time,
  `a₁ ⋯ aₙ ↦ ∑ᵢ a₁ ⋯ (aᵢ aᵢ₊₁) ⋯ aₙ`.

Each is characterised by its value on the empty word and a recursion for appending letters, for
instance `Δ (s * ι a) = Δ s * (1 ⊗ ι a) + (s * ι a) ⊗ 1` for the deconcatenation `Δ`
(`TauCeti.FreeAlgebra.deconcat_mul_ι`).
-/

public section

noncomputable section

open Finset TensorProduct

namespace TauCeti

/-- A free-monoid basis vector is the ordered product of the generators in its word. -/
@[simp]
theorem basisFreeMonoid_apply (R ι : Type*) [CommSemiring R] (w : FreeMonoid ι) :
    FreeAlgebra.basisFreeMonoid R ι w = (w.toList.map (FreeAlgebra.ι R)).prod := by
  simp [FreeAlgebra.basisFreeMonoid, FreeAlgebra.equivMonoidAlgebraFreeMonoid,
    FreeMonoid.lift_apply]

namespace FreeAlgebra

section Words

variable (R : Type*) {A : Type*} [CommSemiring R]

/-- The word `ι a₁ * ⋯ * ι aₙ` of the free algebra. -/
def word (w : List A) : FreeAlgebra R A :=
  (w.map (FreeAlgebra.ι R)).prod

@[simp]
theorem word_nil : word R ([] : List A) = 1 :=
  (rfl)

@[simp]
theorem word_singleton (a : A) : word R [a] = FreeAlgebra.ι R a := by
  simp [word]

theorem word_append_singleton (w : List A) (a : A) :
    word R (w ++ [a]) = word R w * FreeAlgebra.ι R a := by
  simp [word]

variable [AddCommMonoid A] [Module R A] in
@[simp]
theorem toTensor_word (w : List A) :
    FreeAlgebra.toTensor (word R w) = (w.map (TensorAlgebra.ι R)).prod := by
  simp [word, map_list_prod, List.map_map, Function.comp_def, FreeAlgebra.toTensor_ι]

variable {R}

/-- Linear maps out of the free algebra agree when they agree on words. -/
theorem linearMap_ext_word {P : Type*} [AddCommMonoid P] [Module R P]
    {f g : FreeAlgebra R A →ₗ[R] P} (h : ∀ w, f (word R w) = g (word R w)) : f = g :=
  (FreeAlgebra.basisFreeMonoid R A).ext fun w => by
    rw [basisFreeMonoid_apply]
    exact h _

variable (R) in
/-- The linear map out of the free algebra with prescribed values on words. -/
def ofWords {P : Type*} [AddCommMonoid P] [Module R P] (f : List A → P) :
    FreeAlgebra R A →ₗ[R] P :=
  (FreeAlgebra.basisFreeMonoid R A).constr R fun w => f w.toList

@[simp]
theorem ofWords_word {P : Type*} [AddCommMonoid P] [Module R P] (f : List A → P)
    (w : List A) : ofWords R f (word R w) = f w := by
  have h := (FreeAlgebra.basisFreeMonoid R A).constr_basis R (fun w => f w.toList)
    (FreeMonoid.ofList w)
  rwa [basisFreeMonoid_apply, FreeMonoid.toList_ofList] at h

end Words

/-! ### The bar operations on words -/

section Deconcat

variable (R : Type*) {A : Type*} [CommSemiring R]

/-- The **deconcatenation**: the splitting of a word into a prefix and a suffix in all ways. -/
def deconcat : FreeAlgebra R A →ₗ[R] FreeAlgebra R A ⊗[R] FreeAlgebra R A :=
  ofWords R fun w => ∑ i ∈ range (w.length + 1), word R (w.take i) ⊗ₜ[R] word R (w.drop i)

theorem deconcat_word (w : List A) :
    deconcat R (word R w) =
      ∑ i ∈ range (w.length + 1), word R (w.take i) ⊗ₜ[R] word R (w.drop i) :=
  ofWords_word _ w

private theorem deconcat_word_append_singleton (w : List A) (a : A) :
    deconcat R (word R (w ++ [a])) =
      deconcat R (word R w) * (1 ⊗ₜ FreeAlgebra.ι R a) + word R (w ++ [a]) ⊗ₜ[R] 1 := by
  rw [deconcat_word, deconcat_word, List.length_append, List.length_singleton, sum_range_succ,
    sum_mul]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi : i ≤ w.length := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [List.take_append_of_le_length hi, List.drop_append_of_le_length hi,
      word_append_singleton, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · simp [List.take_of_length_le]

/-- Splitting a word ending in `a`: the splittings of `s a` are those of `s` with `a` appended to
the suffix, and the splitting with empty suffix. -/
theorem deconcat_mul_ι (s : FreeAlgebra R A) (a : A) :
    deconcat R (s * FreeAlgebra.ι R a) =
      deconcat R s * (1 ⊗ₜ FreeAlgebra.ι R a) + (s * FreeAlgebra.ι R a) ⊗ₜ 1 := by
  have h : (deconcat R).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)) =
      (LinearMap.mulRight R (1 ⊗ₜ[R] FreeAlgebra.ι R a)).comp (deconcat R) +
        ((TensorProduct.mk R _ _).flip 1).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)) := by
    refine linearMap_ext_word fun w => ?_
    simpa [← word_append_singleton] using deconcat_word_append_singleton R w a
  exact LinearMap.congr_fun h s

@[simp]
theorem deconcat_one :
    deconcat R (1 : FreeAlgebra R A) = (1 : FreeAlgebra R A ⊗[R] FreeAlgebra R A) := by
  rw [← word_nil R, deconcat_word]
  simp [Algebra.TensorProduct.one_def]

end Deconcat

section DiffLetters

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

/-- The letters of a word differentiated one at a time by `d`. -/
def diffLetters (d : A →ₗ[R] A) : FreeAlgebra R A →ₗ[R] FreeAlgebra R A :=
  ofWords R fun w => ∑ i ∈ range w.length,
    word R (w.take i) * FreeAlgebra.ι R (d (w.getD i 0)) * word R (w.drop (i + 1))

theorem diffLetters_word (d : A →ₗ[R] A) (w : List A) :
    diffLetters d (word R w) = ∑ i ∈ range w.length,
      word R (w.take i) * FreeAlgebra.ι R (d (w.getD i 0)) * word R (w.drop (i + 1)) :=
  ofWords_word _ w

private theorem diffLetters_word_append_singleton (d : A →ₗ[R] A) (w : List A) (a : A) :
    diffLetters d (word R (w ++ [a])) =
      diffLetters d (word R w) * FreeAlgebra.ι R a + word R w * FreeAlgebra.ι R (d a) := by
  rw [diffLetters_word, diffLetters_word, List.length_append, List.length_singleton,
    sum_range_succ, sum_mul]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi : i < w.length := mem_range.1 hi
    rw [List.take_append_of_le_length hi.le, List.getD_append _ _ _ _ hi,
      List.drop_append_of_le_length hi, word_append_singleton, mul_assoc _ (word R _)]
  · simp

/-- Differentiating the letters of a word ending in `a`. -/
theorem diffLetters_mul_ι (d : A →ₗ[R] A) (s : FreeAlgebra R A) (a : A) :
    diffLetters d (s * FreeAlgebra.ι R a) =
      diffLetters d s * FreeAlgebra.ι R a + s * FreeAlgebra.ι R (d a) := by
  have h : (diffLetters d).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)) =
      (LinearMap.mulRight R (FreeAlgebra.ι R a)).comp (diffLetters d) +
        LinearMap.mulRight R (FreeAlgebra.ι R (d a)) := by
    refine linearMap_ext_word fun w => ?_
    simpa [← word_append_singleton] using diffLetters_word_append_singleton d w a
  exact LinearMap.congr_fun h s

@[simp]
theorem diffLetters_one (d : A →ₗ[R] A) : diffLetters d (1 : FreeAlgebra R A) = 0 := by
  rw [← word_nil R, diffLetters_word]
  simp

end DiffLetters

section MergeAdjacent

variable (R : Type*) {A : Type*} [CommSemiring R] [MulZeroClass A]

/-- Adjacent letters of a word multiplied, one pair at a time. -/
def mergeAdjacent : FreeAlgebra R A →ₗ[R] FreeAlgebra R A :=
  ofWords R fun w => ∑ i ∈ range (w.length - 1),
    word R (w.take i) * FreeAlgebra.ι R (w.getD i 0 * w.getD (i + 1) 0) * word R (w.drop (i + 2))

theorem mergeAdjacent_word (w : List A) :
    mergeAdjacent R (word R w) = ∑ i ∈ range (w.length - 1),
      word R (w.take i) * FreeAlgebra.ι R (w.getD i 0 * w.getD (i + 1) 0) *
        word R (w.drop (i + 2)) :=
  ofWords_word _ w

private theorem mergeAdjacent_word_append_pair (w : List A) (a b : A) :
    mergeAdjacent R (word R (w ++ [a] ++ [b])) =
      mergeAdjacent R (word R (w ++ [a])) * FreeAlgebra.ι R b +
        word R w * FreeAlgebra.ι R (a * b) := by
  rw [mergeAdjacent_word, mergeAdjacent_word]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [sum_range_succ, sum_mul]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi : i < w.length := mem_range.1 hi
    have hi' : i + 1 < (w ++ [a]).length := by simp; omega
    rw [List.take_append_of_le_length (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ hi', List.drop_append_of_le_length (by simp; omega),
      word_append_singleton, mul_assoc _ (word R _)]
  · simp

/-- Multiplying adjacent letters of a word ending in `a b`. -/
theorem mergeAdjacent_mul_ι_mul_ι (s : FreeAlgebra R A) (a b : A) :
    mergeAdjacent R (s * FreeAlgebra.ι R a * FreeAlgebra.ι R b) =
      mergeAdjacent R (s * FreeAlgebra.ι R a) * FreeAlgebra.ι R b +
        s * FreeAlgebra.ι R (a * b) := by
  have h : (mergeAdjacent R).comp
        ((LinearMap.mulRight R (FreeAlgebra.ι R b)).comp
          (LinearMap.mulRight R (FreeAlgebra.ι R a))) =
      ((LinearMap.mulRight R (FreeAlgebra.ι R b)).comp
          ((mergeAdjacent R).comp (LinearMap.mulRight R (FreeAlgebra.ι R a)))) +
        LinearMap.mulRight R (FreeAlgebra.ι R (a * b)) := by
    refine linearMap_ext_word fun w => ?_
    simpa [← word_append_singleton] using mergeAdjacent_word_append_pair R w a b
  exact LinearMap.congr_fun h s

@[simp]
theorem mergeAdjacent_one : mergeAdjacent R (1 : FreeAlgebra R A) = 0 := by
  rw [← word_nil R, mergeAdjacent_word]
  simp

@[simp]
theorem mergeAdjacent_ι (a : A) : mergeAdjacent R (FreeAlgebra.ι R a) = 0 := by
  rw [← word_singleton R, mergeAdjacent_word]
  simp

end MergeAdjacent

end FreeAlgebra

end TauCeti
